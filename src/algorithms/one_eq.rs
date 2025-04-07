use merlin::Transcript;

use crate::btf_transcript::TFTranscriptProtocol;
use crate::data_structures::LinearLagrangeList;
use crate::eq_poly::EqPoly;
use crate::prover::ProverState;
use crate::tower_fields::TowerField;
use crate::IPForMLSumcheck;
use rayon::prelude::*;

impl<EF: TowerField, BF: TowerField> IPForMLSumcheck<EF, BF> {
    /// Computes the round polynomial using the algorithm 1 (collapsing arrays) where
    /// the polynomial is of the form `eq_polynomial * state_polynomial_1 * ... * state_polynomial_d`
    /// This algorithm does **not** use any optimization for `eq_polynomial`
    /// (either Gruen's optimization or our split eq-poly optimization).
    /// This version parallelizes the computation of contributions across different `i` values.
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
        let state_polynomial_len = state_polynomials[0].list.len();

        // Define the identity element for the reduction (a vector of zeros)
        let identity_vec = vec![EF::zero(); round_polynomial_degree + 1];

        // Parallel computation of contributions using map-reduce
        let summed_contributions = (0..state_polynomial_len)
            .into_par_iter()
            .map(|i| {
                // For each `i`, compute the contribution vector [s_i(0), s_i(1), ..., s_i(degree)]
                let mut contributions = vec![EF::zero(); round_polynomial_degree + 1];
                let mut evals_at_0: Vec<F> = Vec::with_capacity(round_polynomial_degree);
                let mut evals_at_1: Vec<F> = Vec::with_capacity(round_polynomial_degree);
                let mut evals_at_infty: Vec<F> = Vec::with_capacity(round_polynomial_degree);

                // Precompute evaluations for state polynomials at 0, 1, and infinity
                for k in 0..round_polynomial_degree {
                    let even_val = state_polynomials[k].list[i].even;
                    let odd_val = state_polynomials[k].list[i].odd;
                    evals_at_0.push(even_val);
                    evals_at_1.push(odd_val);
                    evals_at_infty.push(odd_val - even_val);
                }

                // Precompute evaluations for the eq polynomial at 0, 1, and infinity
                let eq_eval_at_0 = eq_polynomial.list[i].even;
                let eq_eval_at_1 = eq_polynomial.list[i].odd;
                let eq_eval_at_infty = eq_eval_at_1 - eq_eval_at_0;

                // Compute s_i(0) = eq(0) * combine(evals_at_0)
                contributions[0] = eq_eval_at_0 * combine_function(&evals_at_0);

                // Compute s_i(1) = eq(1) * combine(evals_at_1)
                contributions[1] = eq_eval_at_1 * combine_function(&evals_at_1);

                // Re-use evals_at_1 vector and track eq_eval_at_u
                let mut evals_at_u = evals_at_1;
                let mut eq_eval_at_u = eq_eval_at_1;

                // Compute s_i(u) = eq(u) * combine(evals_at_u) for u = 2 to round_polynomial_degree
                for u in 2..=round_polynomial_degree {
                    // Update state polynomial evaluations for point u
                    for k in 0..round_polynomial_degree {
                        evals_at_u[k] += evals_at_infty[k];
                    }
                    // Update eq polynomial evaluation for point u
                    eq_eval_at_u += eq_eval_at_infty;

                    contributions[u] = eq_eval_at_u * combine_function(&evals_at_u);
                }
                contributions // Return the contribution vector for this `i`
            })
            .reduce(
                || identity_vec.clone(), // Provide a fresh identity vector for each thread
                |mut vec_a, vec_b| {
                    // Reduction step: Sum the contribution vectors element-wise
                    for (a, b) in vec_a.iter_mut().zip(vec_b.iter()) {
                        *a += *b;
                    }
                    vec_a
                },
            );

        // Assign the final summed contributions to the corresponding round polynomial.
        // This handles the case where state_polynomial_len is 0, as reduce returns the identity.
        round_polynomials[round_number - 1] = summed_contributions;

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
        eq_challenges: &Vec<EF>,
        to_ef: &T,
    ) where
        EC: Fn(&Vec<EF>) -> EF + Sync,
        BC: Fn(&Vec<BF>) -> EF + Sync,
        T: Fn(&BF) -> EF + Sync,
        BF: Send + Sync,
        EF: Send + Sync,
    {
        // Compute the equality polynomial from its basis.
        let eq_poly = EqPoly::new(eq_challenges.to_vec());
        let eq_evals = eq_poly.compute_evals(false);
        let mut eq_state_poly = LinearLagrangeList::from_vector(&eq_evals);

        // The degree of the round polynomial is the highest-degree multiplicand in the combine function.
        let r_degree = prover_state.max_multiplicands;

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
