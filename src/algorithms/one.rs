use std::time::Instant;

use ark_ff::{Field, PrimeField};
use merlin::Transcript;

use crate::data_structures::LinearLagrangeList;
use crate::extension_transcript::ExtensionTranscriptProtocol;
use crate::prover::ProverState;
use crate::IPForMLSumcheck;

impl<EF: Field, BF: PrimeField> IPForMLSumcheck<EF, BF> {
    /// Computes the round polynomial using the algorithm 1 (collapsing arrays) from the paper
    /// https://github.com/ingonyama-zk/papers/blob/main/sumcheck_201_chapter_1.pdf
    ///
    /// Outputs the challenge (which is an extension field element).
    pub fn compute_round_polynomial<C, F>(
        round_number: usize,
        state_polynomials: &Vec<LinearLagrangeList<F>>,
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
        for k in 0..(round_polynomial_degree + 1) {
            for i in 0..state_polynomial_len {
                let evaluations_at_k = state_polynomials
                    .iter()
                    .map(|state_poly| {
                        // evaluate given state polynomial at x_1 = k
                        let o = state_poly.list[i].odd;
                        let e = state_poly.list[i].even;
                        (F::one() - F::from(k as u32)) * e + F::from(k as u32) * o
                    })
                    .collect::<Vec<F>>();

                // apply combine function
                round_polynomials[round_number - 1][k] += combine_function(&evaluations_at_k);
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
    pub fn prove_with_naive_algorithm<EC, BC, T>(
        prover_state: &mut ProverState<EF, BF>,
        ef_combine_function: &EC,
        bf_combine_function: &BC,
        transcript: &mut Transcript,
        round_polynomials: &mut Vec<Vec<EF>>,
        to_ef: &T,
    ) where
        EC: Fn(&Vec<EF>) -> EF + Sync,
        BC: Fn(&Vec<BF>) -> EF + Sync,
        T: Fn(&BF) -> EF + Sync,
    {
        let start_algo1 = Instant::now();
        // The degree of the round polynomial is the highest-degree multiplicand in the combine function.
        let r_degree = prover_state.max_multiplicands;

        // Phase 1: Process round 1 separately as we need to only perform bb multiplications.
        let alpha = Self::compute_round_polynomial::<BC, BF>(
            1,
            &prover_state.state_polynomials,
            round_polynomials,
            r_degree,
            &bf_combine_function,
            transcript,
        );

        // From the next round onwards, all of the data will be extension field elements.
        // We copy all of the prover state polynomials to a new data structure of extension field elements.
        // This is because all of the data would be folded using a challenge (an extension field element).
        // So we update the prover state polynomials as follows.
        let mut ef_state_polynomials: Vec<LinearLagrangeList<EF>> = prover_state
            .state_polynomials
            .iter()
            .map(|list| list.convert(&to_ef))
            .collect();
        for j in 0..prover_state.state_polynomials.len() {
            ef_state_polynomials[j].fold_in_half(alpha);
        }

        // Phase 2: Process the subsequent rounds with only ee multiplications.
        for round_number in 2..=prover_state.num_vars {
            let alpha = Self::compute_round_polynomial::<EC, EF>(
                round_number,
                &ef_state_polynomials,
                round_polynomials,
                r_degree,
                &ef_combine_function,
                transcript,
            );

            // update the state polynomials
            for j in 0..ef_state_polynomials.len() {
                ef_state_polynomials[j].fold_in_half(alpha);
            }
        }
        let end = start_algo1.elapsed();
        println!("prove_algo1: {:?}", end);
    }
}
