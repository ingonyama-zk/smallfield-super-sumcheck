use ark_ff::{Field, PrimeField};
use ark_poly::DenseMultilinearExtension;
use merlin::Transcript;

use crate::data_structures::{LinearLagrangeList, MatrixPolynomial, MatrixPolynomialInt};
use crate::extension_transcript::ExtensionTranscriptProtocol;
use crate::prover::ProverState;
use crate::IPForMLSumcheck;

impl<EF: Field, BF: PrimeField> IPForMLSumcheck<EF, BF> {
    /// Algorithm 4
    pub fn prove_with_toom_cook_agorithm<BE, EE, BB, EC>(
        prover_state: &mut ProverState<EF, BF>,
        transcript: &mut Transcript,
        round_polynomials: &mut Vec<Vec<EF>>,
        round_t: usize,
        mult_be: &BE,
        mult_ee: &EE,
        mult_bb: &BB,
        mappings: &Vec<Box<dyn Fn(&BF, &BF) -> BF>>,
        mappings_int: &Vec<Box<dyn Fn(&i64, &i64) -> i64 + Send + Sync>>,
        projection_mapping_indices: &Vec<usize>,
        interpolation_maps_bf: &Vec<Box<dyn Fn(&Vec<BF>) -> BF>>,
        interpolation_maps_ef: &Vec<Box<dyn Fn(&Vec<EF>) -> EF>>,
        ef_combine_function: &EC,
    ) where
        BE: Fn(&BF, &EF) -> EF + Sync,
        EE: Fn(&EF, &EF) -> EF + Sync,
        BB: Fn(&BF, &BF) -> BF + Sync,
        EC: Fn(&Vec<EF>) -> EF + Sync,
    {
        // Assertions
        assert_eq!(projection_mapping_indices.len(), 2);

        // Create and fill witness matrix polynomials.
        // We need to represent state polynomials in matrix form for this algorithm because:
        // Pre-round:
        // row 0: [ p(x) ]
        //
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
            ));
        }

        // Pre-compute bb multiplications upto round t
        // For this, we first fold the witness matrices to get their dimension: 2^t  x  2^{l - t}
        // Lets say t = 2 and d = 3. We want to pre-compute the terms:
        //
        // Σ_x ∏_i merkle( p_i(:, :, x), j)
        //
        // for all j = 0, 1, ..., (d + 1)^t. More explicitly, we wish to compute:
        // Input state:
        // p_i(0, 0, x)
        // p_i(0, 1, x)
        // p_i(1, 0, x)
        // p_i(1, 1, x)
        //
        // Output products:
        // +-----------------------------------------------------------------------------------+
        //  j    j_2  j_1  product
        // +-----------------------------------------------------------------------------------+
        //  0    0    0    Σ_x ∏_i p_i(0, 0, x)
        //  1    0    1    Σ_x ∏_i p_i(0, 0, x) + p_i(0, 1, x)
        //  2    0    2    Σ_x ∏_i p_i(0, 0, x) - p_i(0, 1, x)
        //  3    0    3    Σ_x ∏_i p_i(0, 1, x)
        //  4    1    0    Σ_x ∏_i p_i(0, 0, x) + p_i(1, 0, x)
        //  5    1    1    Σ_x ∏_i p_i(0, 0, x) + p_i(1, 0, x) + p_i(0, 1, x) + p_i(1, 1, x)
        //  6    1    2    Σ_x ∏_i p_i(0, 0, x) + p_i(1, 0, x) - p_i(0, 1, x) - p_i(1, 1, x)
        //  7    1    3    Σ_x ∏_i p_i(0, 1, x) + p_i(1, 1, x)
        //  8    2    0    Σ_x ∏_i p_i(0, 0, x) - p_i(1, 0, x)
        //  9    2    1    Σ_x ∏_i p_i(0, 0, x) - p_i(1, 0, x) + p_i(0, 1, x) - p_i(1, 1, x)
        //  10   2    2    Σ_x ∏_i p_i(0, 0, x) - p_i(1, 0, x) - p_i(0, 1, x) + p_i(1, 1, x)
        //  11   2    3    Σ_x ∏_i p_i(0, 1, x) - p_i(1, 1, x)
        //  12   3    0    Σ_x ∏_i p_i(1, 0, x)
        //  13   3    1    Σ_x ∏_i p_i(1, 0, x) + p_i(1, 1, x)
        //  14   3    2    Σ_x ∏_i p_i(1, 0, x) - p_i(1, 1, x)
        //  15   3    3    Σ_x ∏_i p_i(1, 1, x)
        // +-----------------------------------------------------------------------------------+
        //
        // If I wish to get the products for any round r < t, I can use the pre-computed products.
        // For example, if r = 1, we want the following products:
        // +-----------------------------------------------------------------------------------------------------------------------------------+
        //  j_1  product                          equals                                                                         pre-computed
        // +-----------------------------------------------------------------------------------------------------------------------------------+
        //  0    Σ_y ∏_i p_i(0, y)                Σ_x ∏_i p_i(0, 0, x)                 +  Σ_x ∏_i p_i(0, 1, x)                   C[0] + C[3]
        //  1    Σ_y ∏_i p_i(0, y) + p_i(1, y)    Σ_x ∏_i p_i(0, 0, x) + p_i(1, 0, x)  +  Σ_x ∏_i p_i(0, 1, x) + p_i(1, 1, x)    C[4] + C[7]
        //  2    Σ_y ∏_i p_i(0, y) - p_i(1, y)    Σ_x ∏_i p_i(0, 0, x) - p_i(1, 0, x)  +  Σ_x ∏_i p_i(0, 1, x) - p_i(1, 1, x)    C[8] + C[11]
        //  3    Σ_y ∏_i p_i(1, y)                Σ_x ∏_i p_i(1, 0, x)                 +  Σ_x ∏_i p_i(1, 1, x)                   C[12] + C[15]
        // +-----------------------------------------------------------------------------------------------------------------------------------+
        //
        for _ in 2..=round_t {
            for matrix in &mut matrix_polynomials {
                matrix.heighten();
            }

            for matrix_int in &mut matrix_polynomials_int {
                matrix_int.heighten();
            }
        }

        let num_evals = r_degree + 1;
        let num_product_terms = num_evals.pow(round_t as u32);

        // Pre-compute array (int operations)
        let mut precomputed_array_int: Vec<i64> = Vec::with_capacity(num_product_terms);
        for j in 0..num_product_terms {
            let mut product_terms_x: MatrixPolynomialInt<i64> =
                MatrixPolynomialInt::compute_merkle_roots(
                    &matrix_polynomials_int[0],
                    j,
                    mappings_int,
                );

            for i in 1..matrix_polynomials.len() {
                let matrix_terms_x = MatrixPolynomialInt::compute_merkle_roots(
                    &matrix_polynomials_int[i],
                    j,
                    mappings_int,
                );
                product_terms_x = product_terms_x.hadamard_product(&matrix_terms_x);
            }

            assert_eq!(product_terms_x.no_of_rows, 1);
            let sum_over_x = product_terms_x.evaluation_rows[0]
                .iter()
                .fold(0i64, |acc, px| acc + px);
            precomputed_array_int.push(sum_over_x);
        }

        let precomputed_array: Vec<BF> = precomputed_array_int
            .iter()
            .map(|&p| {
                let p_positive = BF::from(p.abs() as u64);
                let adjusted_value = if p < 0 { -p_positive } else { p_positive };
                adjusted_value
            })
            .collect();

        // Accumulate pre-computed values to be used in rounds.
        let precomputed_arrays_for_rounds = MatrixPolynomial::<BF>::merkle_sums(
            &precomputed_array,
            num_evals,
            projection_mapping_indices,
        );

        // Initialise empty challenge matrix
        let mut challenge_matrix: MatrixPolynomial<EF> = MatrixPolynomial::<EF> {
            no_of_rows: 0,
            no_of_columns: num_evals,
            evaluation_rows: Vec::with_capacity(round_t - 1),
        };

        // This matrix will store challenges in the form:
        // [ (1-α_1)(1-α_2)...(1-α_m) ]
        // [ (1-α_1)(1-α_2)...(α_m) ]
        // [ .. ]
        // [ .. ]
        // [ (α_1)(α_2)...(α_m) ]
        // ATTENTION: This is not used in the toom-cook algorithm, it is only required once we switch back to naive algorithm.
        let mut challenge_matrix_polynomial: MatrixPolynomial<EF> = MatrixPolynomial::one();

        // This matrix will store the challenge terms after applying interpolation maps and tensor-hadamard multiplications.
        //
        // ⌈ L₀(α₁) ⌉   ⌈ L₀(α₂) ⌉          ⌈ L₀(αₚ) ⌉
        // | L₁(α₁) |   | L₁(α₂) |          | L₁(αₚ) |
        // | L₂(α₁) |   | L₂(α₂) |          | L₂(αₚ) |
        // |  ....  | ⊛ |  ....  | ⊛ .... ⊛ |  ....  |
        // |  ....  |   |  ....  |          |  ....  |
        // |  ....  |   |  ....  |          |  ....  |
        // ⌊ Lₔ(α₁) ⌋   ⌊ Lₔ(α₂) ⌋          ⌊ Lₔ(αₚ) ⌋
        //
        let mut interpolated_challenge_matrix_polynomial: MatrixPolynomial<EF> =
            MatrixPolynomial::one();

        // Process first t rounds
        for round_num in 1..=round_t {
            let round_size = num_evals.pow(round_num as u32);

            // Fetch (d + 1)^p witness terms using only bb additions
            // We use given projection mapping indices to know which witness terms to combine from
            // the pre-computed array of size (d + 1)^t
            let precomputed_array_for_this_round: &Vec<BF> =
                &precomputed_arrays_for_rounds[round_num];
            assert_eq!(precomputed_array_for_this_round.len(), round_size);
            assert_eq!(challenge_matrix.evaluation_rows.len(), round_num - 1);

            for k in 0..num_evals as u64 {
                let mut scalar_matrix: MatrixPolynomial<BF> = MatrixPolynomial::<BF> {
                    no_of_rows: 0,
                    no_of_columns: num_evals,
                    evaluation_rows: Vec::with_capacity(1),
                };
                let mult_bb_local = |a: &BF, b: &BF| -> BF { (*a) * (*b) };
                scalar_matrix.update_with_challenge(
                    BF::from(k),
                    &interpolation_maps_bf,
                    &mult_bb_local,
                );

                //
                // Decompose j as (j_p, j_{p-1}, ...., j_2, j_1)
                // j_1 is used to compute L_{j_1}(k) so we treat it separately
                // Rest of the indices are used to fetch respective challenge terms
                // Thus, we iterate over only (j_2, j_3, ..., j_p) in round p.
                // This results in a total of (d + 1)ᵖ⁻¹ be multiplications in round p.
                //
                for j in 0..(round_size / num_evals) {
                    // Extract j_1 to process the scalar separately
                    let mut local_witness_accumulator = BF::zero();
                    for j_1 in 0..num_evals {
                        local_witness_accumulator += scalar_matrix.evaluation_rows[0][j_1]
                            * precomputed_array_for_this_round[j * num_evals + j_1];
                    }

                    // Fetch the following term using j from the already-computed array
                    // that contains multiplications of challenge terms.
                    //
                    // Lⱼ₂(αₚ₋₁) * Lⱼ₃(αₚ₋₂) * ... * Lⱼₚ(α₁)
                    //
                    // where j ≡ (jₚ || jₚ₋₁ || ... || j₂).
                    //
                    let local_interpolated_challenge =
                        interpolated_challenge_matrix_polynomial.evaluation_rows[j][0];

                    // Accumulate round polynomial evaluation at k
                    round_polynomials[round_num - 1][k as usize] +=
                        mult_be(&local_witness_accumulator, &local_interpolated_challenge);
                }
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

            // Update the challenge matrix with the new challenge row
            // This computes the following terms for the newly computed challenge αᵢ
            //
            // [ L₀(αᵢ),  L₁(αᵢ),  L₂(αᵢ), ..., Lₔ(αᵢ) ]
            //
            challenge_matrix.update_with_challenge(alpha, &interpolation_maps_ef, mult_ee);

            // Update the interpolated challenge matrix with new challenge
            // This computes the hadamard product of the current matrix with the new challenge column:
            // [ L₀(αᵢ),  L₁(αᵢ),  L₂(αᵢ), ..., Lₔ(αᵢ) ].
            //
            let current_challenge_idx = challenge_matrix.no_of_rows - 1;
            let current_challenge_row = &challenge_matrix.evaluation_rows[current_challenge_idx];
            let interpolated_challenge_matrix =
                MatrixPolynomial::from_evaluations_vec(current_challenge_row);
            interpolated_challenge_matrix_polynomial = interpolated_challenge_matrix_polynomial
                .tensor_hadamard_product(&interpolated_challenge_matrix, &mult_ee);

            // Update challenge matrix with new challenge
            // TODO: See if we can get rid of the second challenge matrix.
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
