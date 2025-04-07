use crate::eq_poly::EqPoly;

use ark_ff::{Field, PrimeField};
use merlin::Transcript;

use crate::data_structures::LinearLagrangeList;
use crate::extension_transcript::ExtensionTranscriptProtocol;
use crate::prover::ProverState;
use crate::IPForMLSumcheck;
use rayon::prelude::*;

impl<EF: Field, BF: PrimeField> IPForMLSumcheck<EF, BF> {
    /// Computes the round polynomial using the algorithm 1 (collapsing arrays) from the paper
    /// https://github.com/ingonyama-zk/papers/blob/main/sumcheck_201_chapter_1.pdf
    ///
    /// Outputs the challenge (which is an extension field element).
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
        F: Field,
    {
        let state_polynomial_len = state_polynomials[0].list.len();

        // Parallel computation of contributions
        let computed_contributions: Vec<Vec<EF>> = (0..=round_polynomial_degree)
            .into_par_iter()
            .map(|k| {
                // For each `k`, collect contributions from all state polynomials
                let mut contributions = vec![EF::zero(); state_polynomial_len];
                for i in 0..state_polynomial_len {
                    let evaluations_at_k: Vec<F> = state_polynomials
                        .iter()
                        .map(|state_poly| {
                            let o = state_poly.list[i].odd;
                            let e = state_poly.list[i].even;
                            let k_field = F::from(k as u32);
                            (F::one() - k_field) * e + k_field * o
                        })
                        .collect();

                    let k_field = EF::from(k as u32);
                    let eq_evaluation_at_k = (EF::one() - k_field) * eq_polynomial.list[i].even
                        + k_field * eq_polynomial.list[i].odd;

                    // Apply combine function
                    contributions[i] = eq_evaluation_at_k * combine_function(&evaluations_at_k);
                }
                contributions
            })
            .collect();

        // Now, sequentially merge the computed contributions into round_polynomials
        for (k, contributions) in computed_contributions.into_iter().enumerate() {
            for contribution in contributions {
                round_polynomials[round_number - 1][k] += contribution;
            }
        }

        // append the round polynomial (i.e. prover message) to the transcript
        <Transcript as ExtensionTranscriptProtocol<EF, BF>>::append_scalars(
            transcript,
            b"r_poly",
            &round_polynomials[round_number - 1],
        );

        // generate challenge α_i = H( transcript );
        let alpha: EF = <Transcript as ExtensionTranscriptProtocol<EF, BF>>::challenge_scalar(
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
        let mut ef_state_polynomials: Vec<LinearLagrangeList<EF>> = prover_state
            .state_polynomials
            .iter()
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

            // update the state polynomials
            for j in 0..ef_state_polynomials.len() {
                ef_state_polynomials[j].fold_in_half(alpha);
            }
            eq_state_poly.fold_in_half(alpha);
        }
    }
}
