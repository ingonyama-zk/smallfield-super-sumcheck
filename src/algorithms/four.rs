use merlin::Transcript;
use rayon::iter::{IntoParallelIterator, ParallelIterator};

use crate::btf_transcript::TFTranscriptProtocol;
use crate::data_structures::{LinearLagrangeList, MatrixPolynomial};
use crate::prover::ProverState;
use crate::tower_fields::TowerField;
use crate::IPForMLSumcheck;

impl<EF: TowerField, BF: TowerField> IPForMLSumcheck<EF, BF> {
    /// Algorithm 4
    pub fn prove_with_toom_cook_agorithm<BE, EE, BB, EC>(
        prover_state: &mut ProverState<EF, BF>,
        transcript: &mut Transcript,
        round_polynomials: &mut Vec<Vec<EF>>,
        round_t: usize,
        mult_be: &BE,
        mult_ee: &EE,
        mult_bb: &BB,
        mappings: &Vec<Box<dyn Fn(&BF, &BF) -> BF + Send + Sync>>,
        projection_mapping_indices: &Vec<usize>,
        interpolation_maps_bf: &Vec<Box<dyn Fn(&Vec<BF>) -> BF>>,
        interpolation_maps_ef: &Vec<Box<dyn Fn(&Vec<EF>) -> EF>>,
        ef_combine_function: &EC,
        scaled_determinant: &BF,
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
        //
        // The degree of the round polynomial is the number of polynomials being multiplied since
        // we are only dealing with product-sumcheck. In other cases, number of polynomials may not equal the degree.
        let r_degree = prover_state.state_polynomials.len();
        let num_witness_poly = prover_state.state_polynomials.len();
        let mut matrix_polynomials: Vec<MatrixPolynomial<BF>> =
            Vec::with_capacity(num_witness_poly);

        for i in 0..num_witness_poly {
            matrix_polynomials.push(MatrixPolynomial::from_linear_lagrange_list(
                &prover_state.state_polynomials[i],
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
        }

        let num_evals = r_degree + 1;
        let num_product_terms = num_evals.pow(round_t as u32);

        // Parallelize over `j`
        let precomputed_array: Vec<BF> = (0..num_product_terms)
            .into_par_iter()
            .map(|j| {
                // Parallelize matrices_terms_x computation for each `j`
                let matrices_terms_x: Vec<Vec<BF>> = (0..matrix_polynomials.len())
                    .into_par_iter() // Parallelize over matrix_polynomials
                    .map(|i| {
                        MatrixPolynomial::compute_merkle_roots(&matrix_polynomials[i], j, mappings)
                            .evaluation_rows[0]
                            .to_vec()
                    })
                    .collect();

                // Assuming all rows have the same number of columns
                let num_columns = matrices_terms_x[0].len();

                // Squash each column by multiplying elements across rows in parallel
                let sum_over_x: BF = (0..num_columns)
                    .into_par_iter()
                    .map(|i| {
                        matrices_terms_x
                            .iter()
                            .map(|row| row[i])
                            .fold(BF::one(), |acc, val| mult_bb(&acc, &val))
                    })
                    .sum();

                sum_over_x // Return the sum for this `j`
            })
            .collect(); // Collect the result of each `j` into the vector

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
            // Original precomputed array:       [ p(ε₁, ε₂, ......., εₜ) ] ∀ εᵢ ∈ {0, 1, ..., d - 1, ∞}
            // Precomputed array for this round: [ p(ε₁, ε₂, ..., εₚ) ]
            let precomputed_array_for_this_round: &Vec<BF> =
                &precomputed_arrays_for_rounds[round_num];
            assert_eq!(precomputed_array_for_this_round.len(), round_size);
            assert_eq!(challenge_matrix.evaluation_rows.len(), round_num - 1);

            // To compute the round polynomial at given k, we first compute the following witness accumulator:
            //
            //     p(ε₁, ε₂, ..., εₚ₋₁, k) := Σₘ Lₘ(k) ∏_i p_i(ε₁, ε₂, ..., εₚ₋₁, m)
            //
            // Note that we want to compute evaluations for k = 0, 2, ..., d - 1, ∞ (i.e., d evaluations)
            // d = 1 ==> evaluation points: 0
            // d = 2 ==> evaluation points: 0 ∞
            // d = 3 ==> evaluation points: 0 2 ∞
            // d = 4 ==> evaluation points: 0 2 3 ∞
            // We skip k = 1 as it can be computed by the verifier. Also, if d = 1, we only compute for k = 0.
            // We want to compute the Lagrange evaluations at a given k, i.e., Lₘ(k) ∀m.
            //
            // [L₀(k), L₁(k), L₂(k), ..., Lₔ(k)] =  [1, k, k², ..., kᵈ] * ⌈  1  0  0  0  0 ⌉   ⌈   6   0   0   0   0 ⌉
            //                                                            │ -4  1  0  0  0 │   │  -3   6  -2  -1  12 │
            //                                                            │  6 -3  1  0  0 │ * │  -6   3   3   0  -6 │
            //                                                            │ -4  3 -2  1  0 │   │   3  -3  -1   1 -12 │
            //                                                            ⌊  1 -1  1 -1  1 ⌋   ⌊   0   0   0   0   6 ⌋
            //                                                            |<-- bin_exp --->|   |<-- interpolation -->|
            //
            // The interpolation maps encodes the matrix I' := (binomial_exp * interpolation) in the above equation.
            // We can avoid a few multiplications for the k = 0 and k = ∞ cases.
            //
            // Case k = 0: We have [1, k, k², ..., kᵈ] = [1, 0, 0, ..., 0], thus:
            // [L₀(0), L₁(0), L₂(0), ..., Lₔ(0)] := [ I'[0][0]  0  0  0  0 ]
            // and the first entry in the I' matrix is the scaled determinant.
            //
            // Case k = ∞: We have [1, k, k², ..., kᵈ] = [0, 0, 0, ..., 1], thus:
            // [L₀(∞), L₁(∞), L₂(∞), ..., Lₔ(∞)] := [ I'[d][0]  I'[d][1]  ....  I'[d][d] ] (i.e., the last row of I')
            //
            // Decompose j as (j_p, j_{p-1}, ...., j_2, j_1)
            // j_1 is used to compute L_{j_1}(k) so we treat it separately
            // Rest of the indices are used to fetch respective challenge terms
            // Thus, we iterate over only (j_2, j_3, ..., j_p) in round p.
            // This results in a total of (d + 1)ᵖ⁻¹ be multiplications in round p.
            //
            for j in 0..(round_size / num_evals) {
                // Fetch the following term using j from the already-computed array
                // that contains multiplications of challenge terms.
                //
                // Lⱼ₂(αₚ₋₁) * Lⱼ₃(αₚ₋₂) * ... * Lⱼₚ(α₁)
                //
                // where j ≡ (jₚ || jₚ₋₁ || ... || j₂).
                //
                let local_interpolated_challenge =
                    interpolated_challenge_matrix_polynomial.evaluation_rows[j][0];

                // Process k = 0
                let local_witness_accumulator_zero =
                    *scaled_determinant * precomputed_array_for_this_round[j * num_evals];
                round_polynomials[round_num - 1][0] += mult_be(
                    &local_witness_accumulator_zero,
                    &local_interpolated_challenge,
                );

                if r_degree > 1 {
                    // Process k = ∞ only if degree > 1
                    let local_witness_accumulator_infty = interpolation_maps_bf.last().unwrap()(
                        &precomputed_array_for_this_round[j * num_evals..].to_vec(),
                    );
                    round_polynomials[round_num - 1][r_degree - 1] += mult_be(
                        &local_witness_accumulator_infty,
                        &local_interpolated_challenge,
                    );
                }

                // Process k = 2, 3, ..., d - 1 (total d - 2 evaluations)
                for k in 2..r_degree {
                    // Compute scalar matrix for (k + 1)
                    let mut scalar_matrix: MatrixPolynomial<BF> = MatrixPolynomial::<BF> {
                        no_of_rows: 0,
                        no_of_columns: num_evals,
                        evaluation_rows: Vec::with_capacity(1),
                    };
                    let mult_bb_local = |a: &BF, b: &BF| -> BF { (*a) * (*b) };

                    // We make a minor assumption here. We assume that k is a 4-bit number, i.e. k ∈ {0, 1, ..., 15}
                    // since it's reasonable to assume num_evals would be always less than 16.
                    // This matters because the size of k will affect the multiplication with the scalar terms (1 - k) and (k)
                    // and we want these terms to be as "small" as possible.
                    scalar_matrix.update_with_challenge(
                        BF::new(k as u128, Some(2)),
                        &interpolation_maps_bf,
                        &mult_bb_local,
                    );

                    // Extract j_1 to process the scalar separately
                    let mut local_witness_accumulator = BF::zero();
                    for j_1 in 0..num_evals {
                        local_witness_accumulator += scalar_matrix.evaluation_rows[0][j_1]
                            * precomputed_array_for_this_round[j * num_evals + j_1];
                    }

                    // Accumulate round polynomial evaluation at k
                    round_polynomials[round_num - 1][k as usize - 1] +=
                        mult_be(&local_witness_accumulator, &local_interpolated_challenge);
                }
            }

            // Now we've got: s(0) s(2) s(3) ... s(d - 1) s(∞) and the prover sends these d evaluations
            // append the round polynomial (i.e. prover message) to the transcript
            <Transcript as TFTranscriptProtocol<EF, BF>>::append_scalars(
                transcript,
                b"r_poly",
                &round_polynomials[round_num - 1],
            );

            // generate challenge α_i = H( transcript );
            let alpha = <Transcript as TFTranscriptProtocol<EF, BF>>::challenge_scalar(
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
            let challenge_tuple_matrix =
                MatrixPolynomial::from_evaluations_vec(&vec![EF::one() - alpha, alpha]);
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
