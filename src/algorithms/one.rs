use merlin::Transcript;

use crate::btf_transcript::TFTranscriptProtocol;
use crate::data_structures::LinearLagrangeList;
use crate::prover::ProverState;
use crate::tower_fields::TowerField;
use crate::IPForMLSumcheck;
use rayon::prelude::*;

impl<EF: TowerField, BF: TowerField> IPForMLSumcheck<EF, BF> {
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
        F: TowerField,
    {
        // Degree 0 polynomial is constant, sumcheck doesn't make sense.
        debug_assert!(
            round_polynomial_degree > 0,
            "Round polynomial degree must be > 0"
        );

        let state_polynomial_len = state_polynomials[0].list.len();

        // Compute the evaluations s_i(0), s_i(2), ..., s_i(d - 1), and s_i(∞)
        // d = 1 ==> evaluation points: 0
        // d = 2 ==> evaluation points: 0 ∞
        // d = 3 ==> evaluation points: 0 2 ∞
        // d = 4 ==> evaluation points: 0 2 3 ∞
        let prover_message = (0..state_polynomial_len)
            .into_par_iter()
            .map(|i| {
                let mut contributions = vec![EF::zero(); round_polynomial_degree];
                let mut evals_at_0: Vec<F> = Vec::with_capacity(round_polynomial_degree);
                let mut evals_at_1: Vec<F> = Vec::with_capacity(round_polynomial_degree);
                let mut evals_at_infty: Vec<F> = Vec::with_capacity(round_polynomial_degree);

                for k in 0..round_polynomial_degree {
                    let even_val = state_polynomials[k].list[i].even;
                    let odd_val = state_polynomials[k].list[i].odd;
                    evals_at_0.push(even_val);
                    evals_at_1.push(odd_val);
                    evals_at_infty.push(odd_val - even_val);
                }

                // Combine for k = 0
                contributions[0] = combine_function(&evals_at_0);

                // Combine for k = ∞ only if d > 1
                if round_polynomial_degree > 1 {
                    contributions[round_polynomial_degree - 1] = combine_function(&evals_at_infty);
                }

                // Combine for k = 2, 3, ..., d - 1
                let mut current_evals = evals_at_1;
                for u in 2..round_polynomial_degree {
                    for k in 0..round_polynomial_degree {
                        // `evals_at_(u) = evals_at_(u-1) + evals_at_infty`
                        current_evals[k] += evals_at_infty[k];
                    }
                    contributions[u - 1] = combine_function(&current_evals);
                }
                contributions
            })
            .reduce(
                || (vec![EF::zero(); round_polynomial_degree]), // Inlined identity
                |mut acc, item| {
                    for idx in 0..round_polynomial_degree - 1 {
                        acc[idx] += item[idx];
                    }
                    acc
                },
            );

        round_polynomials[round_number - 1] = prover_message;

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
        // The degree of the round polynomial is the number of polynomials being multiplied.
        let r_degree = prover_state.state_polynomials.len();

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
    }
}
