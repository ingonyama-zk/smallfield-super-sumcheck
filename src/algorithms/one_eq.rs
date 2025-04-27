use merlin::Transcript;

use crate::btf_transcript::TFTranscriptProtocol;
use crate::data_structures::LinearLagrangeList;
use crate::data_structures::eq_poly::EqPoly;
use crate::prover::ProverState;
use crate::tower_fields::TowerField;
use crate::IPForMLSumcheck;
use rayon::prelude::*;

impl<EF: TowerField, BF: TowerField> IPForMLSumcheck<EF, BF> {
    /// Computes the round polynomial using Algorithm 1 (collapsing arrays) where
    /// the polynomial is of the form `eq(X) * combine(state_polys(X))`.
    /// The degree of the combined polynomial is `d+1` where `d = round_polynomial_degree`.
    /// This algorithm does **not** use any optimization for `eq_polynomial`
    /// (either Gruen's optimization or our split eq-poly optimization).
    ///
    /// Computes evaluations at points {0, ∞, 2, ..., d} and stores them in that order.
    pub fn compute_round_polynomial_with_eq<C, F>(
        round_number: usize,
        state_polynomials: &Vec<LinearLagrangeList<F>>,
        eq_polynomial: &LinearLagrangeList<EF>,
        round_polynomials: &mut Vec<Vec<EF>>,
        round_polynomial_degree: usize, // This is 'd' in the paper for the combine function
        combine_function: &C,
        transcript: &mut Transcript,
    ) -> EF
    where
        C: Fn(&Vec<F>) -> EF + Sync,
        F: TowerField + Sync,
        EF: Send + Sync,
    {
        // Degree 0 polynomial doesn't make sense for combine_function.
        debug_assert!(round_polynomial_degree > 0, "polynomial degree must be > 0");

        // The resulting polynomial s_i(X) = eq * combine(...) has degree d+1.
        // We need d+2 evaluations to determine it. We use {∞, 0, 2, ..., d}.
        // Note: s_i(1) is derived by the verifier.
        let s_degree = round_polynomial_degree + 1;
        let d = round_polynomial_degree;
        let state_polynomial_len = state_polynomials[0].list.len();

        // Parallel computation of contributions using map-reduce
        let summed_contributions = (0..state_polynomial_len)
            .into_par_iter()
            .map(|i| {
                // Vector holds contributions in order [s(0), s(∞), s(2), ..., s(d)]
                let mut contributions = vec![EF::zero(); s_degree];
                let mut evals_at_0: Vec<F> = Vec::with_capacity(d);
                let mut evals_at_infty: Vec<F> = Vec::with_capacity(d);

                // Precompute evaluations for state polynomials at 0 and infinity
                for k in 0..d {
                    let even_val = state_polynomials[k].list[i].even;
                    let odd_val = state_polynomials[k].list[i].odd;
                    evals_at_0.push(even_val); // eval at 0
                    evals_at_infty.push(odd_val - even_val); // eval at infinity
                }

                // Precompute evaluations for the eq polynomial at 0 and infinity
                let eq_eval_at_0 = eq_polynomial.list[i].even;
                let eq_eval_at_infty = eq_polynomial.list[i].odd - eq_eval_at_0;

                // Compute and store s(0) = eq(0) * combine(state_polys(0)) at index 0
                contributions[0] = eq_eval_at_0 * combine_function(&evals_at_0);

                // Compute and store s(∞) = eq(∞) * combine(state_polys(∞)) at index 1
                contributions[1] = eq_eval_at_infty * combine_function(&evals_at_infty);

                // Compute contributions for s(2), ..., s(d)
                // Start recurrence from state poly evals at 1 and eq eval at 1
                let mut current_evals: Vec<F> = evals_at_0
                    .iter()
                    .zip(&evals_at_infty)
                    .map(|(e0, einf)| *e0 + *einf)
                    .collect(); // p_k(1) = p_k(0) + p_k(inf)
                let mut current_eq_eval = eq_eval_at_0 + eq_eval_at_infty; // eq(1) = eq(0) + eq(inf)

                // Compute contributions for u = 2 to d
                for u_val in 2..=d { // u = 2..d
                    // Update state polynomial evaluations for point u
                    for k in 0..d {
                        current_evals[k] += evals_at_infty[k]; // p_k(u) = p_k(u-1) + p_k(inf)
                    }
                    // Update eq polynomial evaluation for point u
                    current_eq_eval += eq_eval_at_infty; // eq(u) = eq(u-1) + eq(inf)

                    // Store s(u) = eq(u) * combine(state_polys(u)) at index u_val
                    contributions[u_val] = current_eq_eval * combine_function(&current_evals);
                }
                contributions // Return contributions in order [s(0), s(∞), s(2), ..., s(d)]
            })
            .reduce(
                || vec![EF::zero(); s_degree], // Identity: zero vector
                |mut acc, item| {
                    // Reduction step: Sum contribution vectors
                    for idx in 0..s_degree {
                        acc[idx] += item[idx];
                    }
                    acc
                },
            );

        // summed_contributions is already in the desired order [s(0), s(∞), s(2), ..., s(d)]
        round_polynomials[round_number - 1] = summed_contributions;

        // append the round polynomial (i.e. prover message) to the transcript
        <Transcript as TFTranscriptProtocol<EF, BF>>::append_scalars(
            transcript,
            b"r_poly",
            // Send evaluations in the order [s(0), s(∞), s(2), ..., s(d)]
            &round_polynomials[round_number - 1],
        );

        // generate challenge α_i = H( transcript );
        let alpha: EF = <Transcript as TFTranscriptProtocol<EF, BF>>::challenge_scalar(
            transcript,
            b"challenge_nextround",
        );

        return alpha;
    }

    /// Algorithm 1: This algorithm is split into two computation phases.
    ///   Phase 1: Compute round 1 polynomial with only bb multiplications
    ///   Phase 2: Compute round 2, 3, ..., n polynomials with only ee multiplications
    /// This is the unoptimized version for g(X) = eq(w,X) * product(p_k(X)).
    pub fn prove_with_eq_naive_algorithm<EC, BC, T>(
        prover_state: &mut ProverState<EF, BF>,
        ef_combine_function: &EC,
        // Note: bc_combine_function is not needed as eq makes everything EF
        transcript: &mut Transcript,
        round_polynomials: &mut Vec<Vec<EF>>,
        to_ef: &T,
    ) where
        EC: Fn(&Vec<EF>) -> EF + Sync,
        BC: Fn(&Vec<BF>) -> EF + Sync,
        T: Fn(&BF) -> EF + Sync,
        BF: Send + Sync,
        EF: Send + Sync,
    {
        // Compute the equality polynomial from its basis.
        assert!(
            prover_state.eq_challenges.is_some(),
            "Equality poly challenges cannot be `None`."
        );
        let eq_poly = EqPoly::new(prover_state.eq_challenges.clone().unwrap().to_vec());
        let eq_evals = eq_poly.compute_evals(false);
        let mut eq_state_poly = LinearLagrangeList::from_vector(&eq_evals);

        // The degree of the round polynomial combine function part.
        let r_degree = prover_state.state_polynomials.len();

        // For all rounds, all of the data will be extension field elements as we're multiplying base
        // field polynomials with the extension field eq polynomial. So we copy all of the prover state polynomials
        // to a new data structure of extension field elements. This is because all of the data would be folded
        // using a challenge (an extension field element). So we update the prover state polynomials as follows.
        // Parallelize conversion
        let mut ef_state_polynomials: Vec<LinearLagrangeList<EF>> = prover_state
            .state_polynomials
            .par_iter()
            .map(|list| list.convert(&to_ef))
            .collect();

        // Process all the rounds with only ee multiplications.
        for round_number in 1..=prover_state.num_vars {
            let alpha = Self::compute_round_polynomial_with_eq::<EC, EF>(
                round_number,
                &ef_state_polynomials,
                &eq_state_poly,
                round_polynomials,
                r_degree,
                &ef_combine_function,
                transcript,
            );

            // update the state polynomials and eq polynomial in parallel
            ef_state_polynomials
                .par_iter_mut()
                .for_each(|poly| poly.fold_in_half(alpha));
            eq_state_poly.fold_in_half(alpha); // eq_state_poly fold is usually fast, might not need parallelization itself
        }
    }

    // --- Stubs for Optimized Algorithms ---

    /// Computes the sumcheck proof using Gruen's optimization.
    /// This involves factoring the round polynomial s_i(X) into l_i(X) * t_i(X),
    /// computing evaluations of t_i(X) (degree d), and deriving s_i(X).
    /// This implementation does NOT use the split eq-poly optimization.
    pub fn prove_with_gruen_optimization<EC, BC, T>(
        prover_state: &mut ProverState<EF, BF>,
        ef_combine_function: &EC,
        // Note: bc_combine_function is not needed as eq makes everything EF
        transcript: &mut Transcript,
        round_polynomials: &mut Vec<Vec<EF>>, // Still stores s_i evaluations
        to_ef: &T,
    ) where
        EC: Fn(&Vec<EF>) -> EF + Sync,
        BC: Fn(&Vec<BF>) -> EF + Sync, // Kept for signature compatibility
        T: Fn(&BF) -> EF + Sync,
        BF: Send + Sync,
        EF: Send + Sync,
    {
        // The degree of the combine function part.
        let r_degree = prover_state.state_polynomials.len();

        // Ensure eq challenges are present
        assert!(
            prover_state.eq_challenges.is_some(),
            "Equality poly challenges cannot be `None` for Gruen opt."
        );
        let w = prover_state.eq_challenges.as_ref().unwrap();

        // TODO: Precompute eq(w_{[<i]}, r_{[<i]}) iteratively? Or eq(w_[>i], x')?
        // Need to manage the state for eq(w_[>i], x') across rounds.
        let mut eq_suffix_state_poly: LinearLagrangeList<EF> = todo!();

        // Convert state polynomials to EF initially
        let mut ef_state_polynomials: Vec<LinearLagrangeList<EF>> = prover_state
            .state_polynomials
            .par_iter()
            .map(|list| list.convert(&to_ef))
            .collect();

        let mut challenges: Vec<EF> = Vec::with_capacity(prover_state.num_vars);

        // Process all the rounds
        for round_number in 1..=prover_state.num_vars {
            // TODO: Compute l_i(X) = eq(w_{[<i]}, r_{[<i]}) * eq(w_i, X)
            // Requires challenges from previous rounds.
            let l_i_eval_0: EF = todo!();
            let l_i_eval_1: EF = todo!();

            // TODO: Compute t_i(u) for u in {∞, 0, 2, ..., d-1}
            // This involves summing eq(w_[>i], x') * product(p_k(...))
            // Needs a helper like compute_t_i_evaluations(...)
            let t_i_evals_minus_1: Vec<EF> = todo!(); // Evals at {∞, 0, 2, ..., d-1}

            // TODO: Derive t_i(1) using claimed sum C_{i-1} = s_i(0) + s_i(1)
            // C_{i-1} = l_i(0)*t_i(0) + l_i(1)*t_i(1)
            // Need to get C_{i-1} from transcript state or previous round.
            let C_im1: EF = todo!(); // Claimed sum from previous round
            let t_i_eval_0 = t_i_evals_minus_1[1]; // Assuming index 1 corresponds to u=0
            let t_i_eval_1: EF = todo!(); // Calculate using C_im1, l_i(0), l_i(1), t_i(0)

            // TODO: Combine t_i evals {∞, 0, 1, 2, ..., d-1} into a full set for U_d
            let t_i_evals_full: Vec<EF> = todo!(); // Evals at {∞, 0, 1, 2, ..., d-1}

            // TODO: Interpolate t_i(X) from t_i_evals_full
            // TODO: Compute s_i(X) = l_i(X) * t_i(X)
            // TODO: Extract evaluations s_i(u) for u in {∞, 0, 2, ..., d}

            let s_i_prover_message: Vec<EF> = todo!(); // Evals s_i(∞), s_i(0), s_i(2), ..., s_i(d)
            round_polynomials[round_number - 1] = s_i_prover_message.clone();

            // Append s_i evaluations to transcript
            <Transcript as TFTranscriptProtocol<EF, BF>>::append_scalars(
                transcript,
                b"r_poly",
                &s_i_prover_message,
            );

            // Generate challenge α_i = H( transcript );
            let alpha: EF = <Transcript as TFTranscriptProtocol<EF, BF>>::challenge_scalar(
                transcript,
                b"challenge_nextround",
            );
            challenges.push(alpha);

            // Update the state polynomials
            ef_state_polynomials
                .par_iter_mut()
                .for_each(|poly| poly.fold_in_half(alpha));

            // TODO: Update the state for eq(w_[>i], x') needed for the next round
            // This might involve folding the eq_suffix_state_poly or recalculating.
            eq_suffix_state_poly.fold_in_half(alpha); // Placeholder? Need careful handling.
        }
        todo!("Gruen optimization proof generation not fully implemented");
    }

    /// Computes the sumcheck proof using both Gruen's optimization and the
    /// split equality polynomial optimization (Algorithm 5 from paper).
    /// Factors s_i(X) = l_i(X) * t_i(X).
    /// Computes t_i(X) efficiently using precomputed split eq tables for w_L and w_R.
    pub fn prove_with_gruen_and_split_eq<EC, BC, T>(
        prover_state: &mut ProverState<EF, BF>,
        ef_combine_function: &EC,
        // Note: bc_combine_function is not needed as eq makes everything EF
        transcript: &mut Transcript,
        round_polynomials: &mut Vec<Vec<EF>>, // Still stores s_i evaluations
        to_ef: &T,
    ) where
        EC: Fn(&Vec<EF>) -> EF + Sync,
        BC: Fn(&Vec<BF>) -> EF + Sync, // Kept for signature compatibility
        T: Fn(&BF) -> EF + Sync,
        BF: Send + Sync,
        EF: Send + Sync,
    {
        let l = prover_state.num_vars;
        let l_by_2 = l / 2; // Assuming l is even
        assert!(l % 2 == 0, "Algorithm 5 requires even number of variables");

        // The degree of the combine function part.
        let r_degree = prover_state.state_polynomials.len();

        // Ensure eq challenges are present
        assert!(
            prover_state.eq_challenges.is_some(),
            "Equality poly challenges cannot be `None` for Algo 5."
        );
        let w = prover_state.eq_challenges.as_ref().unwrap();
        let (w_l_challenges, w_r_challenges) = w.split_at(l_by_2); // Example split

        // TODO: Precompute split eq polynomial evaluations using memoized approach
        // Need tables E_L = { eq(w_L[i..], x_L) } and E_R = { eq(w_R[i..], x_R) }
        // Store these, potentially in ProverState or compute here.
        let eq_l_tables: Vec<Vec<EF>> = todo!("Precompute EqPoly evals for w_L");
        let eq_r_tables: Vec<Vec<EF>> = todo!("Precompute EqPoly evals for w_R");

        // Convert state polynomials to EF initially
        let mut ef_state_polynomials: Vec<LinearLagrangeList<EF>> = prover_state
            .state_polynomials
            .par_iter()
            .map(|list| list.convert(&to_ef))
            .collect();

        let mut challenges: Vec<EF> = Vec::with_capacity(prover_state.num_vars);

        // Process all the rounds
        for round_number in 1..=prover_state.num_vars {
            // TODO: Compute l_i(X) = eq(w_{[<i]}, r_{[<i]}) * eq(w_i, X)
            // Requires challenges from previous rounds.
            let l_i_eval_0: EF = todo!();
            let l_i_eval_1: EF = todo!();

            // TODO: Compute t_i(u) for u in {∞, 0, 2, ..., d-1} using Algorithm 5 formula
            // Needs a helper function compute_t_i_evaluations_split(...)
            // This helper will use the precomputed eq_l_tables and eq_r_tables.
            // Logic differs for rounds i < l/2 and i >= l/2.
            let t_i_evals_minus_1: Vec<EF> = todo!(); // Evals at {∞, 0, 2, ..., d-1}

            // TODO: Derive t_i(1) using claimed sum C_{i-1} = s_i(0) + s_i(1)
            let C_im1: EF = todo!(); // Claimed sum from previous round
            let t_i_eval_0 = t_i_evals_minus_1[1]; // Assuming index 1 corresponds to u=0
            let t_i_eval_1: EF = todo!(); // Calculate using C_im1, l_i(0), l_i(1), t_i(0)

            // TODO: Combine t_i evals {∞, 0, 1, 2, ..., d-1} into a full set for U_d
            let t_i_evals_full: Vec<EF> = todo!(); // Evals at {∞, 0, 1, 2, ..., d-1}

            // TODO: Interpolate t_i(X) from t_i_evals_full
            // TODO: Compute s_i(X) = l_i(X) * t_i(X)
            // TODO: Extract evaluations s_i(u) for u in {∞, 0, 2, ..., d}

            let s_i_prover_message: Vec<EF> = todo!(); // Evals s_i(∞), s_i(0), s_i(2), ..., s_i(d)
            round_polynomials[round_number - 1] = s_i_prover_message.clone();

            // Append s_i evaluations to transcript
            <Transcript as TFTranscriptProtocol<EF, BF>>::append_scalars(
                transcript,
                b"r_poly",
                &s_i_prover_message,
            );

            // Generate challenge α_i = H( transcript );
            let alpha: EF = <Transcript as TFTranscriptProtocol<EF, BF>>::challenge_scalar(
                transcript,
                b"challenge_nextround",
            );
            challenges.push(alpha);

            // Update the state polynomials
            ef_state_polynomials
                .par_iter_mut()
                .for_each(|poly| poly.fold_in_half(alpha));

            // Note: No explicit eq folding needed here as we use precomputed tables.
        }

        todo!("Algorithm 5 (Gruen + Split Eq) proof generation not fully implemented");
    }
}
