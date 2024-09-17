use ark_ff::{Field, PrimeField};
use ark_poly::DenseMultilinearExtension;
use merlin::Transcript;
use std::time::Instant;

use crate::data_structures::{
    bit_extend, bit_extend_and_insert, LinearLagrangeList, MatrixPolynomial, MatrixPolynomialInt,
};
use crate::extension_transcript::ExtensionTranscriptProtocol;
use crate::prover::ProverState;
use crate::IPForMLSumcheck;

impl<EF: Field, BF: PrimeField> IPForMLSumcheck<EF, BF> {
    /// Algorithm 3
    pub fn prove_with_precomputation_agorithm<BE, EE, BB, EC>(
        prover_state: &mut ProverState<EF, BF>,
        transcript: &mut Transcript,
        round_polynomials: &mut Vec<Vec<EF>>,
        round_t: usize,
        mult_be: &BE,
        mult_ee: &EE,
        mult_bb: &BB,
        ef_combine_function: &EC,
    ) where
        BE: Fn(&BF, &EF) -> EF + Sync,
        EE: Fn(&EF, &EF) -> EF + Sync,
        BB: Fn(&BF, &BF) -> BF + Sync,
        EC: Fn(&Vec<EF>) -> EF + Sync,
    {
        // Create and fill witness matrix polynomials.
        // We need to represent state polynomials in matrix form for this algorithm because:
        // Round 1:
        // row 0: [ p(0, x) ]
        // row 1: [ p(1, x) ]
        //
        // Round 2:
        // row 0: [ p(0, 0, x) ]
        // row 1: [ p(0, 1, x) ]
        // row 0: [ p(1, 0, x) ]
        // row 1: [ p(1, 1, x) ]
        //
        // and so on.
        let r_degree = prover_state.max_multiplicands;
        let mut matrix_polynomials: Vec<MatrixPolynomial<BF>> = Vec::with_capacity(r_degree);
        let mut matrix_polynomials_int: Vec<MatrixPolynomialInt<i64>> =
            Vec::with_capacity(r_degree);

        for i in 0..r_degree {
            matrix_polynomials.push(MatrixPolynomial::from_linear_lagrange_list(
                &prover_state.state_polynomials[i],
            ));
            matrix_polynomials_int.push(MatrixPolynomialInt::from_evaluations(
                &prover_state.state_polynomials_int[i],
            ))
        }

        // Pre-compute bb multiplications upto round t
        // For this, we first fold the witness matrices to get their dimension: 2^t  x  (N / 2^t)
        for _ in 2..=round_t {
            for matrix in &mut matrix_polynomials {
                matrix.heighten();
            }

            for matrix_int in &mut matrix_polynomials_int {
                matrix_int.heighten();
            }
        }
        let start_bb = Instant::now();

        let precomputed_array =
            MatrixPolynomial::tensor_inner_product::<_>(&matrix_polynomials, &mult_bb);

        let elapsed_bb = start_bb.elapsed();
        println!("bb_mults: {:?}", elapsed_bb);
        assert_eq!(
            precomputed_array.len(),
            (1 as usize) << (round_t * r_degree)
        );

        // println!("array_bf = {:?}", precomputed_array);

        let start_int = Instant::now();

        let precomputed_array_int =
            MatrixPolynomialInt::tensor_inner_product(&matrix_polynomials_int);

        let elapsed_int = start_int.elapsed();
        println!("int_mults: {:?}", elapsed_int);
        assert_eq!(
            precomputed_array_int.len(),
            (1 as usize) << (round_t * r_degree)
        );

        // println!("array_int = {:?}", precomputed_array_int);

        // This matrix will store challenges in the form:
        // [ (1-α_1)(1-α_2)...(1-α_m) ]
        // [ (1-α_1)(1-α_2)...(α_m) ]
        // [ .. ]
        // [ .. ]
        // [ (α_1)(α_2)...(α_m) ]
        let mut challenge_matrix_polynomial: MatrixPolynomial<EF> = MatrixPolynomial::one();

        let two_power_t = (1 as usize) << round_t;
        let sum_power_t = (precomputed_array.len() - 1) / (two_power_t - 1);
        // Process first t rounds
        for round_num in 1..=round_t {
            let round_size = (1 as usize) << (round_num * r_degree);
            let mut precomputed_array_for_this_round: Vec<BF> = vec![BF::zero(); round_size];

            // Fetch 2^{r * d} terms from
            let remainder_size = (1 as usize) << (round_t - round_num);
            for i in 0..round_size {
                let bit_extended_index = bit_extend(i, round_num * r_degree, round_num, round_t);
                for j in 0..remainder_size {
                    let index = j * sum_power_t + bit_extended_index;
                    precomputed_array_for_this_round[i] += precomputed_array[index];
                }
            }

            // Compute challenge terms for 2^{r * d - 1} terms
            let mut gamma_matrix = challenge_matrix_polynomial.clone();
            for _ in 1..r_degree {
                gamma_matrix =
                    gamma_matrix.tensor_hadamard_product(&challenge_matrix_polynomial, &mult_ee);
            }

            // Combine precomputed_array_for_this_round[i] and precomputed_array_for_this_round[i + 1]
            // substituting X = k.
            for k in 0..(r_degree + 1) as u64 {
                // Compute scalar vector:
                // For d = 2: [(1 - k)²,  (1 - k)k,  k(1 - k), k²]
                // For d = 3: [(1 - k)³,  (1 - k)²k,  (1 - k)k(1 - k),  (1 - k)k²,  k(1 - k)², k(1 - k)k, k²(1 - k), k³]
                let scalar_tuple = DenseMultilinearExtension::from_evaluations_vec(
                    1,
                    vec![BF::ONE - BF::from(k), BF::from(k)],
                );
                let scalar_tuple_matrix = MatrixPolynomial::from_dense_mle(&scalar_tuple);
                let mut scalar_matrix = scalar_tuple_matrix.clone();
                for _ in 1..r_degree {
                    scalar_matrix =
                        scalar_matrix.tensor_hadamard_product(&scalar_tuple_matrix, &mult_bb);
                }
                let two_pow_degree = (1 as usize) << r_degree;
                assert_eq!(scalar_matrix.no_of_columns, 1);
                assert_eq!(scalar_matrix.no_of_rows, two_pow_degree);

                for (idx, challenge_multiplicand) in gamma_matrix.evaluation_rows.iter().enumerate()
                {
                    let mut scalar_accumulator = BF::zero();
                    for j in 0..two_pow_degree {
                        let total_input_bit_len = r_degree * (round_num - 1);
                        let bit_extended_index = bit_extend_and_insert(
                            idx,
                            total_input_bit_len,
                            j,
                            r_degree,
                            round_num - 1,
                            round_num,
                        );
                        scalar_accumulator += scalar_matrix.evaluation_rows[j][0]
                            * precomputed_array_for_this_round[bit_extended_index];
                    }

                    // Accumulate round polynomial evaluation at k
                    round_polynomials[round_num - 1][k as usize] +=
                        mult_be(&scalar_accumulator, &challenge_multiplicand[0]);
                }

                // Ensure Γ has only 1 column and Γ.
                assert_eq!(gamma_matrix.no_of_columns, 1);
            }

            // append the round polynomial (i.e. prover message) to the transcript
            <Transcript as ExtensionTranscriptProtocol<EF, BF>>::append_scalars(
                transcript,
                b"r_poly",
                &round_polynomials[round_num - 1],
            );

            // generate challenge α_i = H( transcript );
            let alpha = <Transcript as ExtensionTranscriptProtocol<EF, BF>>::challenge_scalar(
                transcript,
                b"challenge_nextround",
            );

            // Update challenge matrix with new challenge
            let challenge_tuple =
                DenseMultilinearExtension::from_evaluations_vec(1, vec![EF::ONE - alpha, alpha]);
            let challenge_tuple_matrix = MatrixPolynomial::from_dense_mle(&challenge_tuple);
            challenge_matrix_polynomial = challenge_matrix_polynomial
                .tensor_hadamard_product(&challenge_tuple_matrix, &mult_ee);
        }

        // We will now switch back to Algorithm 1: so we compute the arrays A_i such that
        // A_i = [ p_i(α_1, α_2, ..., α_j, x) for all x ∈ {0, 1}^{l - j} ]
        // for each witness polynomial p_i.
        let mut ef_state_polynomials: Vec<LinearLagrangeList<EF>> = matrix_polynomials
            .iter()
            .map(|matrix_poly| matrix_poly.scale_and_squash(&challenge_matrix_polynomial, &mult_be))
            .collect();

        // Process remaining rounds by switching to Algorithm 1
        for round_num in (round_t + 1)..=prover_state.num_vars {
            let alpha = Self::compute_round_polynomial::<EC, EF>(
                round_num,
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
