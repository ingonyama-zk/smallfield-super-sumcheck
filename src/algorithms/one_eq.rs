use std::sync::Mutex;

use ark_std::log2;
use merlin::Transcript;

use crate::data_structures::LinearLagrangeList;
use crate::eq_poly::EqPoly;
use crate::prover::ProverState;
use crate::tower_fields::TowerField;
use crate::IPForMLSumcheck;
use crate::{
    btf_transcript::TFTranscriptProtocol, verifier::barycentric_interpolation_with_infinity,
};
use rayon::prelude::*;

impl<EF: TowerField, BF: TowerField> IPForMLSumcheck<EF, BF> {
    /// Computes the round polynomial using Algorithm 1 (collapsing arrays) where
    /// the polynomial is of the form `eq(X) * combine(state_polys(X))`.
    /// The degree of the combined polynomial is `round_polynomial_degree + 1`.
    /// This algorithm does **not** use any optimization for `eq_polynomial`
    /// (either Gruen's optimization or our split eq-poly optimization).
    pub fn compute_round_polynomial_with_eq<C, F>(
        round_number: usize,
        state_polynomials: &Vec<LinearLagrangeList<F>>,
        eq_polynomial: &LinearLagrangeList<EF>,
        round_polynomials: &mut Vec<Vec<EF>>,
        round_polynomial_degree: usize,
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

        let state_polynomial_len = state_polynomials[0].list.len();
        let num_state_polynomials = state_polynomials.len();
        debug_assert!(
            round_polynomial_degree == num_state_polynomials + 1,
            "Number of state polynomials + eq poly must be equal to the round polynomial degree."
        );

        // Compute the evaluations s_i(0), s_i(2), ..., s_i(d - 1), and s_i(∞)
        // d = 1 ==> evaluation points: 0
        // d = 2 ==> evaluation points: 0 ∞
        // d = 3 ==> evaluation points: 0 2 ∞
        // d = 4 ==> evaluation points: 0 2 3 ∞
        let prover_message = (0..state_polynomial_len)
            .into_par_iter()
            .map(|i| {
                let mut contributions = vec![EF::zero(); round_polynomial_degree];
                let mut evals_at_0: Vec<F> = Vec::with_capacity(num_state_polynomials);
                let mut evals_at_1: Vec<F> = Vec::with_capacity(num_state_polynomials);
                let mut evals_at_infty: Vec<F> = Vec::with_capacity(num_state_polynomials);

                // Precompute evaluations for state polynomials at 0, 1, and ∞
                for k in 0..num_state_polynomials {
                    let even_val = state_polynomials[k].list[i].even;
                    let odd_val = state_polynomials[k].list[i].odd;
                    evals_at_0.push(even_val);
                    evals_at_1.push(odd_val);
                    evals_at_infty.push(odd_val - even_val);
                }

                // Precompute evaluations for the eq polynomial at 0, 1 and ∞
                let eq_eval_at_0 = eq_polynomial.list[i].even;
                let eq_eval_at_1 = eq_polynomial.list[i].odd;
                let eq_eval_at_infty = eq_eval_at_1 - eq_eval_at_0;

                // Combine for k = 0: eq(0) * combine(state_polys(0))
                contributions[0] = eq_eval_at_0 * combine_function(&evals_at_0);

                // Combine for k = ∞ only if d > 1: eq(∞) * combine(state_polys(∞))
                if round_polynomial_degree > 1 {
                    contributions[round_polynomial_degree - 1] =
                        eq_eval_at_infty * combine_function(&evals_at_infty);
                }

                // Combine for k = 2, 3, ..., d - 1: eq(u) * combine(state_polys(u))
                let mut current_evals = evals_at_1;
                let mut current_eq_eval = eq_eval_at_1;
                for u in 2..round_polynomial_degree {
                    for k in 0..num_state_polynomials {
                        // `evals_at_(u) = evals_at_(u-1) + evals_at_infty`
                        current_evals[k] += evals_at_infty[k];
                    }
                    current_eq_eval += eq_eval_at_infty;

                    contributions[u - 1] = current_eq_eval * combine_function(&current_evals);
                }
                contributions
            })
            .reduce(
                || (vec![EF::zero(); round_polynomial_degree]), // Inlined identity
                |mut acc, item| {
                    for idx in 0..round_polynomial_degree {
                        acc[idx] += item[idx];
                    }
                    acc
                },
            );

        round_polynomials[round_number - 1] = prover_message;

        // append the round polynomial (i.e. prover message) to the transcript
        <Transcript as TFTranscriptProtocol<EF, BF>>::append_scalars(
            transcript,
            b"r_poly",
            &round_polynomials[round_number - 1],
        );

        // generate challenge α_i = H( transcript );
        let alpha: EF = <Transcript as TFTranscriptProtocol<EF, BF>>::challenge_scalar(
            transcript,
            b"challenge_nextround",
        );

        return alpha;
    }

    /// Evaluates the round polynomial at a challenge point using barycentric interpolation.
    ///
    /// This function:
    /// 1. Prepares the polynomial evaluations including the evaluation at k=1
    /// 2. Handles the point at infinity separately
    /// 3. Uses barycentric interpolation to compute the evaluation at the challenge point
    ///
    /// # Arguments
    /// * `round_polynomials` - The vector of round polynomial evaluations
    /// * `round_num` - The current round number (1-indexed)
    /// * `derived_round_poly_evaluation_at_1` - Evaluation of the round polynomial at k=1
    /// * `alpha` - The challenge point at which to evaluate the polynomial
    ///
    /// # Returns
    /// * The evaluation of the round polynomial at the challenge point
    pub fn evaluate_round_poly_at_challenge(
        round_polynomials: &[Vec<EF>],
        round_num: usize,
        derived_round_poly_evaluation_at_1: EF,
        alpha: EF,
    ) -> EF {
        // Prepare the polynomial evaluations for interpolation
        let mut current_round_poly_evals = round_polynomials[round_num - 1].clone();

        // Insert the evaluation at k=1
        current_round_poly_evals.insert(1, derived_round_poly_evaluation_at_1);

        // Extract the evaluation at infinity and remove it from the regular evaluations
        let current_round_poly_at_infty = current_round_poly_evals.pop().unwrap();

        // Compute r_{i}(α_i) using the interpolation formula with infinity
        barycentric_interpolation_with_infinity(
            &current_round_poly_evals,   // s(0), s(1), ..., s(d)
            current_round_poly_at_infty, // s(inf)
            alpha,                       // α_i
        )
    }

    /// Computes the final round polynomial evaluation and updates the current sum for the next round.
    ///
    /// This function:
    /// 1. Derives the evaluation of the round polynomial at k = 1
    /// 2. Computes the intermediate round polynomial evaluation at various points
    /// 3. Interpolates the intermediate round polynomial at k = d
    /// 4. Computes the final round polynomial evaluation
    ///
    /// # Arguments
    /// * `round_num` - Current round number
    /// * `num_witness_polys` - Number of witness polynomials
    /// * `current_sum` - The current sum from previous rounds
    /// * `scaled_determinant` - The scaled determinant for adjusting the current sum
    /// * `eq_challenge_value` - The equality challenge value for this round
    /// * `round_polynomials` - Mutable reference to the round polynomials
    /// * `intermediate_round_polynomial` - ref to intermediate round polynomial
    ///
    pub fn compute_final_round_poly_evaluation(
        round_num: usize,
        num_witness_polys: usize,
        current_sum: &EF,
        scaled_determinant: &EF,
        eq_challenge_value: &EF,
        round_polynomials: &mut Vec<Vec<EF>>,
        intermediate_round_polynomial: &Vec<EF>,
    ) -> EF {
        // Calculate the modified current sum
        let modified_current_sum = *scaled_determinant * *current_sum;

        // Derive the round polynomial evaluation at k = 1
        let derived_round_poly_evaluation_at_1 =
            modified_current_sum - round_polynomials[round_num - 1][0];

        // Calculate intermediate round polynomial evaluation at k = 1
        let derived_intermediate_round_poly_evaluation_at_1 =
            derived_round_poly_evaluation_at_1 * eq_challenge_value.inverse().unwrap();

        // Extract and prepare the intermediate round polynomial
        let mut intermediate_round_poly = intermediate_round_polynomial.clone();
        intermediate_round_poly.insert(1, derived_intermediate_round_poly_evaluation_at_1);
        let intermediate_round_poly_evaluation_at_infty = intermediate_round_poly.pop().unwrap();

        // Interpolate the intermediate round polynomial to get its evaluation at k = d
        let intermediate_round_poly_final_eval = barycentric_interpolation_with_infinity(
            &intermediate_round_poly,
            intermediate_round_poly_evaluation_at_infty,
            EF::new(num_witness_polys as u128, Some(2)),
        );

        // Compute the eq1 center evaluation at k = d: (1 - k)(1 - e) + ke
        let final_k_val = EF::new(num_witness_polys as u128, Some(3));
        let k_times_eq_challenge_value = final_k_val * *eq_challenge_value;
        let eq_1_center_evaluation = k_times_eq_challenge_value + k_times_eq_challenge_value
            - EF::new(num_witness_polys as u128, None)
            - *eq_challenge_value
            + EF::one();

        // Compute the final round polynomial evaluation
        let final_round_poly_eval = eq_1_center_evaluation * intermediate_round_poly_final_eval;

        // Update the round polynomials with the final evaluation
        round_polynomials[round_num - 1].insert(num_witness_polys - 1, final_round_poly_eval);

        // Verify the round polynomial length
        debug_assert!(
            round_polynomials[round_num - 1].len() == num_witness_polys + 1,
            "Round polynomial length mismatch"
        );

        derived_round_poly_evaluation_at_1
    }

    /// Computes the split equality polynomials for the split sumcheck protocol.
    ///
    /// This function splits the eq challenges into two parts and computes:
    /// 1. eq_1_right_staged_evals - Right evaluations for the first half of rounds
    /// 2. eq_2_evals - Complete evaluations for the second polynomial
    ///
    /// # Arguments
    /// * `eq_challenges` - Vector of equality polynomial challenges
    ///
    /// # Returns
    /// * A tuple containing (eq_1_right_staged_evals, eq_2_evals)
    pub fn precompute_split_equality_polynomials(eq_challenges: &[EF]) -> (Vec<Vec<EF>>, Vec<EF>) {
        // Number of eq challenges must be equal to the number of rounds
        let num_vars = eq_challenges.len();

        // Split the eq challenges into two parts at the midpoint
        let (eq_1_basis, eq_2_basis) = eq_challenges.split_at(num_vars / 2);

        // Prepare the right basis (remove the first element and reverse)
        let mut eq_1_right_basis = if eq_1_basis.len() > 1 {
            eq_1_basis[1..].to_vec()
        } else {
            Vec::new()
        };
        eq_1_right_basis.reverse();

        // Compute right staged evaluations and append final value
        let eq_1_right_poly = EqPoly::new(eq_1_right_basis);
        let mut eq_1_right_staged_evals = eq_1_right_poly.compute_staged_evals(true);
        eq_1_right_staged_evals.reverse();
        eq_1_right_staged_evals.push(vec![EF::one()]);

        // Second equality polynomial handling
        let eq_2_poly = EqPoly::new(eq_2_basis.to_vec());
        let eq_2_evals = eq_2_poly.compute_evals(false);

        // Assert that the number of evaluations is correct
        for i in 0..eq_1_right_staged_evals.len() {
            let len_eq_1_right = eq_1_right_staged_evals[i].len(); // 2^{n/2 - i - 1}
            let log_len_eq_1 = log2(len_eq_1_right) as usize; // n/2 - i - 1
            let log_len_eq_2 = log2(eq_2_evals.len()) as usize; // n/2
            debug_assert!(
                log_len_eq_1 == (num_vars / 2 - 1 - i),
                "Log length of eq_1_right does not match for index {}",
                i
            );
            debug_assert!(
                log_len_eq_1 + log_len_eq_2 == num_vars - 1 - i,
                "Log lengths do not match for index {}",
                i
            );
        }

        (eq_1_right_staged_evals, eq_2_evals)
    }

    ///
    ///
    /// The round polynomial is of the form:
    ///
    /// s_i(k) = eq1_left * eq1_center * ∑ ∑ ... ∑ round_challenge_terms * pre_computed_i(k)
    ///          \______/   \________/   \________________________________________________/
    ///         cumulative     local              witness-challenge multiplication
    ///            (A)          (B)                              (C)
    ///
    pub fn compute_round_polynomial_with_split_eq<C, F>(
        round_number: usize,
        state_polynomials: &Vec<LinearLagrangeList<F>>,
        eq_1_left_cumulative: &EF,
        eq_1_center_challenge: &EF,
        eq_polynomial_1: &Vec<EF>,
        eq_polynomial_2: &Vec<EF>,
        round_polynomials: &mut Vec<Vec<EF>>,
        current_sum: &EF,
        num_evals: usize,
        combine_function: &C,
        transcript: &mut Transcript,
    ) -> (EF, EF)
    where
        C: Fn(&Vec<F>) -> EF + Sync,
        F: TowerField + Sync,
        EF: Send + Sync,
    {
        // Degree 0 polynomial doesn't make sense for combine_function.
        debug_assert!(num_evals > 0, "number of evaluations must be > 0");

        // Round number: p, state polynomial size: 2^(n - p)
        let state_polynomial_len = state_polynomials[0].list.len();
        let num_witness_polynomials = state_polynomials.len();
        debug_assert!(
            num_evals >= num_witness_polynomials,
            "Number of evaluations must be greater than or equal to the number of witness polynomials."
        );

        // Assertions on the eq polynomial sizes
        // eq_1: 2^(n/2 - p)     =: M
        // eq_2: 2^(n - n/2)     =: E
        //
        // eq_1 * eq_2: 2^(n/2 - p) * 2^(n - n/2) = 2^(n - p)
        // state poly size: 2^(n - p)
        // ==> eq_1 * eq_2 = state_polynomial_len
        let eq_1_len = eq_polynomial_1.len();
        let eq_2_len = eq_polynomial_2.len();
        debug_assert!(
            eq_1_len * eq_2_len == state_polynomial_len,
            "eq_polynomial_1 must have the same length as the state polynomials."
        );

        let final_result_mutex = Mutex::new(vec![EF::zero(); num_evals]);

        // Process M chunks in parallel
        (0..eq_1_len).into_par_iter().for_each(|chunk_idx| {
            // For each chunk, process E elements
            let start_idx = chunk_idx * eq_2_len;
            let end_idx = start_idx + eq_2_len;

            // Process the E elements in this chunk in parallel and reduce directly
            let chunk_result = (start_idx..end_idx)
                .into_par_iter()
                .map(|i| {
                    // Compute the sums on evaluation points: 0, 2, ..., d - 1, and ∞
                    // d = 1 ==> evaluation points: 0
                    // d = 2 ==> evaluation points: 0 ∞
                    // d = 3 ==> evaluation points: 0 2 ∞
                    // d = 4 ==> evaluation points: 0 2 3 ∞
                    let mut contributions = vec![EF::zero(); num_evals];
                    let mut evals_at_0: Vec<F> = Vec::with_capacity(num_witness_polynomials);
                    let mut evals_at_1: Vec<F> = Vec::with_capacity(num_witness_polynomials);
                    let mut evals_at_infty: Vec<F> = Vec::with_capacity(num_witness_polynomials);

                    // Precompute evaluations for state polynomials at 0, 1, and ∞
                    for k in 0..num_witness_polynomials {
                        let even_val = state_polynomials[k].list[i].even;
                        let odd_val = state_polynomials[k].list[i].odd;
                        evals_at_0.push(even_val);
                        evals_at_1.push(odd_val);
                        evals_at_infty.push(odd_val - even_val);
                    }

                    // Compute contributions and 0 and ∞
                    contributions[0] = combine_function(&evals_at_0);
                    if num_evals > 1 {
                        contributions[num_evals - 1] = combine_function(&evals_at_infty);
                    }

                    // Compute contributions for k = 2, 3, ..., d - 1
                    let mut current_evals = evals_at_1;
                    for u in 2..num_evals {
                        for k in 0..num_witness_polynomials {
                            current_evals[k] += evals_at_infty[k];
                        }
                        contributions[u - 1] = combine_function(&current_evals);
                    }

                    // Apply eq_2 factor immediately
                    let eq_2_idx = i % eq_2_len;
                    let eq_2_factor = eq_polynomial_2[eq_2_idx];
                    for idx in 0..num_evals {
                        contributions[idx] *= eq_2_factor;
                    }

                    contributions
                })
                .reduce(
                    || vec![EF::zero(); num_evals],
                    |mut acc, contributions| {
                        for idx in 0..num_evals {
                            acc[idx] += contributions[idx];
                        }
                        acc
                    },
                );

            // Apply eq_1 factor and accumulate to final result
            let eq_1_factor = eq_polynomial_1[chunk_idx];

            // Lock final_result to update it
            let mut final_result = final_result_mutex.lock().unwrap();
            for idx in 0..num_evals {
                final_result[idx] += chunk_result[idx] * eq_1_factor;
            }
        });

        let mut intermediate_round_polynomial = vec![EF::zero(); num_witness_polynomials];

        for (k, witness_challenge_term) in final_result_mutex.lock().unwrap().iter().enumerate() {
            // Compute the intermediate term as: eq_left_cumulative * pc_witness_challenge_term
            let intermediate_term = *eq_1_left_cumulative * *witness_challenge_term;
            intermediate_round_polynomial.push(intermediate_term);

            // eq1 center evaluation is:
            // (1 - k)(1 - e) + ke = 2ke - k - e + 1
            let k_val = EF::new(k as u128, Some(3));
            let k_times_eq_challenge_value = k_val * *eq_1_center_challenge;
            let eq_1_center_evaluation = k_times_eq_challenge_value + k_times_eq_challenge_value
                - EF::new(k as u128, None)
                - *eq_1_center_challenge
                + EF::one();

            // Compute the round polynomial as: eq_1_left_cumulative * eq_1_center_evaluation * pc_witness_challenge_term
            round_polynomials[round_number - 1][k] = eq_1_center_evaluation * intermediate_term;
        }

        // Compute the final round polynomial evaluation
        let round_poly_eval_at_1 = Self::compute_final_round_poly_evaluation(
            round_number,
            num_witness_polynomials,
            current_sum,
            &eq_1_left_cumulative,
            &eq_1_center_challenge,
            round_polynomials,
            &intermediate_round_polynomial,
        );

        // append the round polynomial (i.e. prover message) to the transcript
        <Transcript as TFTranscriptProtocol<EF, BF>>::append_scalars(
            transcript,
            b"r_poly",
            &round_polynomials[round_number - 1], // (d + 1) evaluations
        );

        // generate challenge α_i = H( transcript );
        let alpha: EF = <Transcript as TFTranscriptProtocol<EF, BF>>::challenge_scalar(
            transcript,
            b"challenge_nextround",
        );

        return (alpha, round_poly_eval_at_1);
    }

    /// Algorithm 1: This algorithm is split into two computation phases.
    ///   Phase 1: Compute round 1 polynomial with only bb multiplications
    ///   Phase 2: Compute round 2, 3, ..., n polynomials with only ee multiplications
    pub fn prove_with_eq_naive_algorithm<EC, BC, T>(
        prover_state: &mut ProverState<EF, BF>,
        ef_combine_function: &EC,
        transcript: &mut Transcript,
        round_polynomials: &mut Vec<Vec<EF>>,
        claimed_sum: EF,
        to_ef: &T,
    ) where
        EC: Fn(&Vec<EF>) -> EF + Sync,
        BC: Fn(&Vec<BF>) -> EF + Sync,
        T: Fn(&BF) -> EF + Sync,
        BF: Send + Sync,
        EF: Send + Sync,
    {
        // Extract the equality polynomial from the prover state
        let eq_challenges = prover_state.eq_challenges.clone().unwrap();
        debug_assert_eq!(
            eq_challenges.len(),
            prover_state.num_vars,
            "Number of equality challenges must match the number of variables"
        );

        // Precompute the equality polynomial evaluations
        let (eq_1_right_staged_evals, eq_2_evals) =
            Self::precompute_split_equality_polynomials(&eq_challenges);

        // The degree of the round polynomial is the number of polynomials being multiplied.
        // Plus one for the eq polynomial.
        let num_witness_polynomials = prover_state.state_polynomials.len();
        let r_degree = num_witness_polynomials + 1;

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

        // The round polynomial is of the form:
        //
        // s_i(k) = eq1_left * eq1_center * ∑ ∑ ... ∑ round_challenge_terms * pre_computed_i(k)
        //          \______/   \________/   \________________________________________________/
        //         cumulative     local              witness-challenge multiplication
        //            (A)          (B)                              (C)
        //
        let round_split = prover_state.num_vars / 2;
        let mut challenge_vector: Vec<EF> = Vec::with_capacity(round_split);
        let mut eq_1_left_cumulative = EF::one();
        let mut current_sum = claimed_sum;
        for round_num in 1..=round_split {
            // Compute the current eq1 left and challenge value
            // Denoted by (A) in the equation above
            if round_num > 1 {
                let eq_challenge = eq_challenges[round_num - 2];
                let prev_round_challenge = challenge_vector.last().unwrap();

                // (1 - e)(1 - r) = 1 - e - r + er
                let eq_times_prev_round_challenge = eq_challenge * *prev_round_challenge;
                let eq_1_left_and_challenge = eq_times_prev_round_challenge
                    + eq_times_prev_round_challenge
                    - eq_challenge
                    - *prev_round_challenge
                    + EF::one();
                eq_1_left_cumulative = eq_1_left_cumulative * eq_1_left_and_challenge;
            }

            let (alpha, rp_at_1) = Self::compute_round_polynomial_with_split_eq::<EC, EF>(
                round_num,
                &ef_state_polynomials,
                &eq_1_left_cumulative,
                &eq_challenges[round_num - 1],
                &eq_1_right_staged_evals[round_num - 1],
                &eq_2_evals,
                round_polynomials,
                &current_sum,
                num_witness_polynomials,
                ef_combine_function,
                transcript,
            );

            challenge_vector.push(alpha);

            // Update the current sum
            current_sum = Self::evaluate_round_poly_at_challenge(
                round_polynomials,
                round_num,
                rp_at_1,
                alpha,
            );

            // update the state polynomials in parallel
            ef_state_polynomials
                .par_iter_mut()
                .for_each(|poly| poly.fold_in_half(alpha));
        }

        // Before we process the last (n / 2) rounds using the naive algorithm, we need to update
        // the equality polynomial. Let's first update the eq1 cumulative value using the latest challenge.
        let eq_challenge = eq_challenges[prover_state.num_vars / 2 - 1];
        let prev_round_challenge = challenge_vector.last().unwrap();
        let eq_times_prev_round_challenge = eq_challenge * *prev_round_challenge;
        let eq_1_left_and_challenge = eq_times_prev_round_challenge + eq_times_prev_round_challenge
            - eq_challenge
            - *prev_round_challenge
            + EF::one();
        eq_1_left_cumulative = eq_1_left_cumulative * eq_1_left_and_challenge;

        // Now lets update the eq2 polynomial by multiplying it with the eq1 cumulative value
        let mut eq_2_for_final_rounds = eq_2_evals.clone();
        for i in 0..eq_2_evals.len() {
            eq_2_for_final_rounds[i] = eq_1_left_cumulative * eq_2_for_final_rounds[i];
        }
        let mut eq_state_poly = LinearLagrangeList::from_vector(&eq_2_for_final_rounds);

        // Process all the rounds with only ee multiplications.
        for round_number in (prover_state.num_vars / 2 + 1)..=prover_state.num_vars {
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
            eq_state_poly.fold_in_half(alpha);
        }
    }
}
