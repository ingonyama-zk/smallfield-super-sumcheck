use merlin::Transcript;

use crate::btf_transcript::TFTranscriptProtocol;
use crate::data_structures::LinearLagrangeList;
use crate::eq_poly::EqPoly;
use crate::prover::ProverState;
use crate::tower_fields::TowerField;
use crate::IPForMLSumcheck;
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

    /// Algorithm 1: This algorithm is split into two computation phases.
    ///   Phase 1: Compute round 1 polynomial with only bb multiplications
    ///   Phase 2: Compute round 2, 3, ..., n polynomials with only ee multiplications
    pub fn prove_with_eq_naive_algorithm<EC, BC, T>(
        prover_state: &mut ProverState<EF, BF>,
        ef_combine_function: &EC,
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

        // The degree of the round polynomial is the number of polynomials being multiplied.
        // Plus one for the eq polynomial.
        let r_degree = prover_state.state_polynomials.len() + 1;

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
}
