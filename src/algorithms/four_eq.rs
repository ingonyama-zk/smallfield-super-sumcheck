use ark_std::log2;
use merlin::Transcript;
use rayon::iter::{
    IndexedParallelIterator, IntoParallelIterator, IntoParallelRefIterator,
    IntoParallelRefMutIterator, ParallelIterator,
};

use crate::btf_transcript::TFTranscriptProtocol;
use crate::data_structures::{LinearLagrangeList, MatrixPolynomial};
use crate::eq_poly::EqPoly;
use crate::prover::ProverState;
use crate::tower_fields::TowerField;
use crate::verifier::barycentric_interpolation_with_infinity;
use crate::IPForMLSumcheck;

impl<EF: TowerField, BF: TowerField> IPForMLSumcheck<EF, BF> {
    /// Algorithm 4 with eq polynomial
    pub fn prove_with_eq_toom_cook_agorithm<BE, EE, BB, EC>(
        prover_state: &mut ProverState<EF, BF>,
        transcript: &mut Transcript,
        round_polynomials: &mut Vec<Vec<EF>>,
        round_small_val: usize,
        mult_be: &BE,
        mult_ee: &EE,
        mult_bb: &BB,
        mappings: &Vec<Box<dyn Fn(&BF, &BF) -> BF + Send + Sync>>,
        projection_mapping_indices: &Vec<usize>,
        interpolation_maps_bf: &Vec<Box<dyn Fn(&Vec<BF>) -> BF>>,
        interpolation_maps_ef: &Vec<Box<dyn Fn(&Vec<EF>) -> EF>>,
        ef_combine_function: &EC,
        scaled_determinant: &BF,
        claimed_sum: EF,
    ) where
        BE: Fn(&BF, &EF) -> EF + Sync,
        EE: Fn(&EF, &EF) -> EF + Sync,
        BB: Fn(&BF, &BF) -> BF + Sync,
        EC: Fn(&Vec<EF>) -> EF + Sync,
    {
        // We apply small value sumcheck for first t rounds
        // and we apply small space sumcheck for first (n / 2) rounds
        // We must ensure t ≤ n/2
        debug_assert!(round_small_val <= prover_state.num_vars / 2);

        // Number of eq challenges must be equal to the number of rounds
        debug_assert!(
            prover_state.eq_challenges.is_some(),
            "Equality poly challenges cannot be `None`."
        );
        let eq_challenges = prover_state.eq_challenges.clone().unwrap();
        debug_assert_eq!(eq_challenges.len(), prover_state.num_vars);

        // First, lets compute the challenge pre-computation terms
        //
        // Split the eq challenges into two parts: first eq contains
        let (eq_1_basis, eq_2_basis) = eq_challenges.split_at(prover_state.num_vars / 2);

        // First equality polynomial is of the form: [ α_1, α_2, ..., α_{n/2} ]
        // In round i, we further split it into three parts L (left), C (centre) and R (right) as follows:
        // eq1 L: [ α_1, α_2, ..., α_{i-1} ]
        // eq1 C: [ α_i ]
        // eq1 R: [ α_{i+1}, α_{i+2}, ..., α_{n/2} ]
        // We compute the evaluations of eq1 L and eq1 R in the pre-computation phase.
        // Note that we reverse the eq1 R basis so that we get the required evaluations using staged evaluations.
        //
        // For example for n = 8, if the first eq is [ α_1, α_2, α_3, α_4 ] we get the following evaluations:
        //
        // +-----+-----------------------------+--------------------+--------------------+-----------------------------+
        // | Eq1 | Round 1                     | Round 2            | Round 3            | Round 4                     |
        // +-----+-----------------------------+--------------------+--------------------+-----------------------------+
        // |     | 1                           | (1 - α_1)          | (1 - α_1)(1 - α_2) | (1 - α_1)(1 - α_2)(1 - α_3) |
        // |     |                             | (α_1)              | (1 - α_1)(α_2)     | (1 - α_1)(1 - α_2)(α_3)     |
        // |     |                             |                    | (α_1)(1 - α_2)     | (1 - α_1)(α_2)(1 - α_3)     |
        // | L   |                             |                    | (α_1)(α_2)         | (1 - α_1)(α_2)(α_3)         |
        // |     |                             |                    |                    | (α_1)(1 - α_2)(1 - α_3)     |
        // |     |                             |                    |                    | (α_1)(1 - α_2)(α_3)         |
        // |     |                             |                    |                    | (α_1)(α_2)(1 - α_3)         |
        // |     |                             |                    |                    | (α_1)(α_2)(α_3)             |
        // +-----+-----------------------------+--------------------+--------------------+-----------------------------+
        // | C   | (1 - α_1)                   | (1 - α_2)          | (1 - α_3)          | (1 - α_4)                   |
        // |     | (α_1)                       | (α_2)              | (α_3)              | (α_4)                       |
        // +-----+-----------------------------+--------------------+--------------------+-----------------------------+
        // |     | (1 - α_2)(1 - α_3)(1 - α_4) | (1 - α_3)(1 - α_4) | (1 - α_4)          | 1                           |
        // |     | (1 - α_2)(1 - α_3)(α_4)     | (1 - α_3)(α_4)     | (α_4)              |                             |
        // | R   | (1 - α_2)(α_3)(1 - α_4)     | (α_3)(1 - α_4)     |                    |                             |
        // |     | (1 - α_2)(α_3)(α_4)         | (α_3)(α_4)         |                    |                             |
        // |     | (α_2)(1 - α_3)(1 - α_4)     |                    |                    |                             |
        // |     | (α_2)(1 - α_3)(α_4)         |                    |                    |                             |
        // |     | (α_2)(α_3)(1 - α_4)         |                    |                    |                             |
        // |     | (α_2)(α_3)(α_4)             |                    |                    |                             |
        // +-----+-----------------------------+--------------------+--------------------+-----------------------------+
        //
        // TODO: Can we optimise by trying to compute L and R using common multiplications?
        //
        let mut eq_1_right_basis = eq_1_basis[1..].to_vec();
        eq_1_right_basis.reverse();

        let eq_1_right_poly = EqPoly::new(eq_1_right_basis);
        let mut eq_1_right_staged_evals = eq_1_right_poly.compute_staged_evals(true);
        eq_1_right_staged_evals.reverse();
        eq_1_right_staged_evals.push(vec![EF::one()]);

        // Second equality polynomial is of the form: [ α_{n/2 + 1}, α_{n/2 + 2}, ..., α_n ]
        //
        // For example, for n = 6, the second eq is [ α_5, α_6, α_7, α_8 ]
        // and we get the following evaluations (without storing intermediate evaluations):
        //
        // (1 - α_5)(1 - α_6)(1 - α_7)(1 - α_8)
        // (1 - α_5)(1 - α_6)(1 - α_7)(α_8)
        // (1 - α_5)(1 - α_6)(α_7)(1 - α_8)
        // (1 - α_5)(1 - α_6)(α_7)(α_8)
        // (1 - α_5)(α_6)(1 - α_7)(1 - α_8)
        // (1 - α_5)(α_6)(1 - α_7)(α_8)
        // (1 - α_5)(α_6)(α_7)(1 - α_8)
        // (1 - α_5)(α_6)(α_7)(α_8)
        // (α_5)(1 - α_6)(1 - α_7)(1 - α_8)
        // (α_5)(1 - α_6)(1 - α_7)(α_8)
        // (α_5)(1 - α_6)(α_7)(1 - α_8)
        // (α_5)(1 - α_6)(α_7)(α_8)
        // (α_5)(α_6)(1 - α_7)(1 - α_8)
        // (α_5)(α_6)(1 - α_7)(α_8)
        // (α_5)(α_6)(α_7)(1 - α_8)
        // (α_5)(α_6)(α_7)(α_8)
        //
        // Note that second eq polynomial is constant in first n/2 rounds.
        //
        let eq_2_basis = eq_2_basis.to_vec();
        let eq_2_poly = EqPoly::new(eq_2_basis);
        let eq_2_evals = eq_2_poly.compute_evals(false);

        // Assert that the number of evaluations is correct
        for i in 0..eq_1_right_staged_evals.len() {
            let len_eq_1_right = eq_1_right_staged_evals[i].len(); // 2^{n/2 - i - 1}
            debug_assert_eq!(
                log2(len_eq_1_right) as usize,
                (prover_state.num_vars / 2 - 1 - i)
            );
        }

        // Create and fill witness matrix polynomials.
        // We need to represent state polynomials in matrix form for this algorithm because:
        // +---------------------+-------------------------+----------------------------+
        // | Round 1:            |  Round 2:               |  Round 3:                  |
        // +---------------------+-------------------------+----------------------------+
        // | row 0: [ p(0, x) ]  |  row 0: [ p(0, 0, x) ]  |  row 0: [ p(0, 0, 0, x) ]  |
        // | row 1: [ p(1, x) ]  |  row 1: [ p(0, 1, x) ]  |  row 1: [ p(0, 0, 1, x) ]  |
        // |                     |  row 2: [ p(1, 0, x) ]  |  row 2: [ p(0, 1, 0, x) ]  |
        // |                     |  row 3: [ p(1, 1, x) ]  |  row 3: [ p(0, 1, 1, x) ]  |
        // |                     |                         |  row 4: [ p(1, 0, 0, x) ]  |
        // |                     |                         |  row 5: [ p(1, 0, 1, x) ]  |
        // |                     |                         |  row 6: [ p(1, 1, 0, x) ]  |
        // |                     |                         |  row 7: [ p(1, 1, 1, x) ]  |
        // +---------------------+-------------------------+----------------------------+
        //
        // and so on.
        let mut matrix_polynomials = prover_state
            .state_polynomials
            .iter()
            .map(|witness_poly| MatrixPolynomial::from_linear_lagrange_list(witness_poly))
            .collect::<Vec<_>>();

        // For this, we first fold the witness matrices to get their dimension: 2^t  x  (N / 2^t)
        for _ in 2..=round_small_val {
            for matrix in &mut matrix_polynomials {
                matrix.heighten();
            }
        }

        // Pre-compute the witness terms (toom-cook multiplication of witness polynomials)
        let num_witness_polys = prover_state.state_polynomials.len();
        let num_evals = num_witness_polys + 1;
        let num_product_terms = num_evals.pow(round_small_val as u32);

        // Each column of the resulting matrix will be of the form (note: x ⋹ {0, 1}^{n - t}):
        // +-----------------------------------------------------------------------------------+
        //  j    j_2  j_1  product
        // +-----------------------------------------------------------------------------------+
        //  0    0    0    ∏_i p_i(0, 0, x)
        //  1    0    1    ∏_i p_i(0, 0, x) + p_i(0, 1, x)
        //  2    0    2    ∏_i p_i(0, 0, x) - p_i(0, 1, x)
        //  3    0    3    ∏_i p_i(0, 1, x)
        //  4    1    0    ∏_i p_i(0, 0, x) + p_i(1, 0, x)
        //  5    1    1    ∏_i p_i(0, 0, x) + p_i(1, 0, x) + p_i(0, 1, x) + p_i(1, 1, x)
        //  6    1    2    ∏_i p_i(0, 0, x) + p_i(1, 0, x) - p_i(0, 1, x) - p_i(1, 1, x)
        //  7    1    3    ∏_i p_i(0, 1, x) + p_i(1, 1, x)
        //  8    2    0    ∏_i p_i(0, 0, x) - p_i(1, 0, x)
        //  9    2    1    ∏_i p_i(0, 0, x) - p_i(1, 0, x) + p_i(0, 1, x) - p_i(1, 1, x)
        //  10   2    2    ∏_i p_i(0, 0, x) - p_i(1, 0, x) - p_i(0, 1, x) + p_i(1, 1, x)
        //  11   2    3    ∏_i p_i(0, 1, x) - p_i(1, 1, x)
        //  12   3    0    ∏_i p_i(1, 0, x)
        //  13   3    1    ∏_i p_i(1, 0, x) + p_i(1, 1, x)
        //  14   3    2    ∏_i p_i(1, 0, x) - p_i(1, 1, x)
        //  15   3    3    ∏_i p_i(1, 1, x)
        // +-----------------------------------------------------------------------------------+
        //
        let mut precomputed_witness_matrix = MatrixPolynomial::<BF> {
            no_of_rows: num_product_terms,
            no_of_columns: 1 << (prover_state.num_vars - round_small_val),
            evaluation_rows: Vec::with_capacity(num_product_terms),
        };
        for j in 0..num_product_terms {
            // [.. p(0) ..] n
            // [.. p(1) ..] n
            // [.. p(2) ..] n
            // total = 2n bb mult
            let mut cumulative_matrix_row_for_j =
                MatrixPolynomial::compute_merkle_roots(&matrix_polynomials[0], j, mappings)
                    .evaluation_rows[0]
                    .to_vec();

            for i in 1..matrix_polynomials.len() {
                let matrix_row_for_j =
                    MatrixPolynomial::compute_merkle_roots(&matrix_polynomials[i], j, mappings)
                        .evaluation_rows[0]
                        .to_vec();
                debug_assert_eq!(cumulative_matrix_row_for_j.len(), matrix_row_for_j.len());
                debug_assert_eq!(
                    cumulative_matrix_row_for_j.len(),
                    1 << (prover_state.num_vars - round_small_val)
                );
                cumulative_matrix_row_for_j
                    .iter_mut()
                    .zip(&matrix_row_for_j)
                    .for_each(|(a, b)| *a = mult_bb(a, b));
            }
            precomputed_witness_matrix
                .evaluation_rows
                .push(cumulative_matrix_row_for_j);
        }

        // Sanity checks
        let round_small_evals_size = 1 << (prover_state.num_vars - round_small_val);
        debug_assert_eq!(precomputed_witness_matrix.no_of_rows, num_product_terms);
        debug_assert_eq!(
            precomputed_witness_matrix.no_of_columns,
            round_small_evals_size
        );
        debug_assert!(precomputed_witness_matrix.no_of_columns % eq_2_evals.len() == 0);

        // Let us compute the witness multiplied by eq2 evaluations
        // The precomputed witness matrix is of size: 2^t x (N / 2^t)
        let num_columns_in_compressed_witness =
            precomputed_witness_matrix.no_of_columns / eq_2_evals.len();
        let mut compressed_witness_with_eq_2 = MatrixPolynomial::<EF> {
            no_of_rows: precomputed_witness_matrix.no_of_rows,
            no_of_columns: num_columns_in_compressed_witness,
            evaluation_rows: vec![
                vec![EF::zero(); num_columns_in_compressed_witness];
                precomputed_witness_matrix.no_of_rows
            ],
        };

        // Process columns in parallel first, then rows
        let compressed_eq_2_results: Vec<Vec<EF>> = (0..num_columns_in_compressed_witness)
            .into_par_iter()
            .map(|chunk_idx| {
                let col_start = chunk_idx * eq_2_evals.len();
                let col_end = (chunk_idx + 1) * eq_2_evals.len();

                // Create a vector to hold results for each row in this column chunk
                let mut column_results = vec![EF::zero(); precomputed_witness_matrix.no_of_rows];

                // Process each row for this column chunk
                for row_idx in 0..precomputed_witness_matrix.no_of_rows {
                    let witness_row = &precomputed_witness_matrix.evaluation_rows[row_idx];

                    // Since we know witness_chunk is exactly divided by eq_2_len,
                    // we can directly take the slice without bounds checking
                    let witness_chunk = &witness_row[col_start..col_end];

                    // Compute inner product with eq_2_evals
                    let inner_product = witness_chunk
                        .iter()
                        .zip(&eq_2_evals)
                        .map(|(w_val, eq_2_challenge)| mult_be(w_val, eq_2_challenge))
                        .sum();

                    // Store the result for this row
                    column_results[row_idx] = inner_product;
                }
                column_results
            })
            .collect();

        // Store the results in the compressed_witness_with_eq_2 matrix
        for row_idx in 0..precomputed_witness_matrix.no_of_rows {
            for chunk_idx in 0..num_columns_in_compressed_witness {
                compressed_witness_with_eq_2.evaluation_rows[row_idx][chunk_idx] =
                    compressed_eq_2_results[chunk_idx][row_idx];
            }
        }

        // Let us iterate over the precomputed matrix and compute the witness terms
        let mut pre_computed_array_with_eq: Vec<Vec<EF>> = vec![vec![]; round_small_val];

        // We need to process rounds sequentially because each depends on the previous
        // Actually, we can parallelize this as well but since round_small_val is typically
        // a small number, we can just do it sequentially
        for round_number in (1..=round_small_val).rev() {
            // Get the eq 1 right evaluations for this round
            let eq_1_right_for_round = &eq_1_right_staged_evals[round_number - 1];
            let eq_1_right_size = eq_1_right_for_round.len();
            let round_size = num_evals.pow(round_number as u32);

            // Verify matrix dimensions
            debug_assert_eq!(compressed_witness_with_eq_2.no_of_rows, round_size);
            debug_assert_eq!(compressed_witness_with_eq_2.no_of_columns, eq_1_right_size);

            // Parallelize the inner product computation
            let compressed_witness_eq_1_eq_2: Vec<EF> = compressed_witness_with_eq_2
                .evaluation_rows
                .par_iter()
                .map(|witness_row| {
                    debug_assert_eq!(witness_row.len(), eq_1_right_size);
                    // Compute inner product with eq1 evaluations
                    witness_row
                        .par_iter()
                        .zip(eq_1_right_for_round.par_iter())
                        .map(|(w_val, eq_1_challenge)| mult_ee(w_val, eq_1_challenge))
                        .sum()
                })
                .collect();

            // Store the result for this round
            pre_computed_array_with_eq[round_number - 1] = compressed_witness_eq_1_eq_2;

            // Update the witness matrix for the next round
            // This step needs to be sequential since it modifies the matrix in-place
            compressed_witness_with_eq_2.extract_submatrix(num_evals, projection_mapping_indices);
        }

        // Now we will start the actual sumcheck protocol
        // Initialise empty challenge matrix
        let mut challenge_matrix: MatrixPolynomial<EF> = MatrixPolynomial::<EF> {
            no_of_rows: 0,
            no_of_columns: num_evals,
            evaluation_rows: Vec::with_capacity(round_small_val - 1),
        };

        // This matrix will store challenges in the form:
        // [ (1-α_1)(1-α_2)...(1-α_m) ]
        // [ (1-α_1)(1-α_2)...(α_m) ]
        // [ .. ]
        // [ .. ]
        // [ (α_1)(α_2)...(α_m) ]
        // ATTENTION: This is not used in the toom-cook algorithm, it is only required once we switch back to naive algorithm.
        let mut challenge_matrix_polynomial: MatrixPolynomial<EF> = MatrixPolynomial::one();
        let mut challenge_vector: Vec<EF> = Vec::with_capacity(round_small_val);

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

        // Round computation starts here for first t rounds:
        // The round polynomial is of the form:
        //
        // s_i(k) = eq1_left * eq1_center * ∑ ∑ ... ∑ round_challenge_terms * pre_computed_i(k)
        //          \______/   \________/   \________________________________________________/
        //         cumulative     local              witness-challenge multiplication
        //            (A)          (B)                              (C)
        //
        // We will compute the equality terms first and then compute the inner sum for each k.
        //
        let mut eq_1_left_cumulative = EF::one();
        let mut current_sum = claimed_sum;
        for round_num in 1..=round_small_val {
            // Constants
            let round_size = num_evals.pow(round_num as u32);

            // Compute the current eq1 left and challenge value
            // Denoted by (A) in the equation above
            if round_num > 1 {
                let eq_challenge = eq_challenges[round_num - 2];
                let prev_round_challenge = challenge_vector.last().unwrap();

                // (1 - e)(1 - r) = 1 - e - r + er
                let eq_times_prev_round_challenge = mult_ee(&eq_challenge, prev_round_challenge);
                let eq_1_left_and_challenge = eq_times_prev_round_challenge
                    + eq_times_prev_round_challenge
                    - eq_challenge
                    - *prev_round_challenge
                    + EF::one();
                eq_1_left_cumulative = mult_ee(&eq_1_left_cumulative, &eq_1_left_and_challenge);
            }

            // Fetch (d + 1)^r witness terms using only bb additions
            // We use given projection mapping indices to know which witness terms to combine from
            // the pre-computed array of size (d + 1)^t
            let precomputed_array_for_this_round: &Vec<EF> =
                &pre_computed_array_with_eq[round_num - 1];
            debug_assert_eq!(precomputed_array_for_this_round.len(), round_size);
            debug_assert_eq!(challenge_matrix.evaluation_rows.len(), round_num - 1);

            // Compute the intermediate round polynomial
            //
            // d = 1 ==> evaluation points: 0
            // d = 2 ==> evaluation points: 0 ∞
            // d = 3 ==> evaluation points: 0 2 ∞
            // d = 4 ==> evaluation points: 0 2 3 ∞
            //
            // Decompose j as (j_p, j_{p-1}, ...., j_2, j_1)
            // j_1 is used to compute L_{j_1}(k) so we treat it separately
            // Rest of the indices are used to fetch respective challenge terms
            // Thus, we iterate over only (j_2, j_3, ..., j_p) in round p.
            // This results in a total of (d + 1)ᵖ⁻¹ be multiplications in round p.
            //
            let mut precomputed_array_and_challege_values = vec![EF::zero(); num_witness_polys];
            let mut eq_1_center_evaluations = vec![EF::zero(); num_witness_polys];
            let mut intermediate_round_poly: Vec<EF> = Vec::with_capacity(num_witness_polys);
            let eq_challenge_value = eq_challenges[round_num - 1];
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

                //
                // Process k = 0 in two steps:
                // 1. Compute the witness-challenge multiplication term for this round
                // 2. Compute the eq1 center evaluation for k = 0: (1 - k)(1 - e) + ke = 1 - e
                //
                let local_witness_accumulator_zero = mult_be(
                    scaled_determinant,
                    &precomputed_array_for_this_round[j * num_evals],
                );
                precomputed_array_and_challege_values[0] += mult_ee(
                    &local_witness_accumulator_zero,
                    &local_interpolated_challenge,
                );
                eq_1_center_evaluations[0] = EF::one() - eq_challenge_value;

                if num_witness_polys > 1 {
                    //
                    // Process k = ∞ only if d > 1
                    // 1. Compute the witness-challenge multiplication term for this round
                    // 2. Compute the eq1 center evaluation for k = ∞: (1 - k)(1 - e) + ke = 2ke - k - e + 1 = 2e - 1
                    //
                    let local_witness_accumulator_infty = interpolation_maps_ef.last().unwrap()(
                        &precomputed_array_for_this_round[j * num_evals..(j + 1) * num_evals]
                            .to_vec(),
                    );
                    precomputed_array_and_challege_values[num_witness_polys - 1] += mult_ee(
                        &local_witness_accumulator_infty,
                        &local_interpolated_challenge,
                    );
                    eq_1_center_evaluations[num_witness_polys - 1] =
                        eq_challenge_value + eq_challenge_value - EF::one();
                }

                // Process k = 2, 3, ..., d - 1 (total d - 2 evaluations)
                for k in 2..num_witness_polys {
                    // Compute the witness-challenge multiplication term for this round
                    // Note this is denoted by (C) in the equation above
                    //
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
                    let mut local_witness_accumulator = EF::zero();
                    for j_1 in 0..num_evals {
                        local_witness_accumulator += mult_be(
                            &scalar_matrix.evaluation_rows[0][j_1],
                            &precomputed_array_for_this_round[j * num_evals + j_1],
                        );
                    }

                    // Update the precomputed_array_and_challege_value term for k
                    precomputed_array_and_challege_values[k as usize - 1] +=
                        mult_ee(&local_witness_accumulator, &local_interpolated_challenge);

                    // For k = 2, 3, ..., d - 1, eq1 center evaluation is:
                    // (1 - k)(1 - e) + ke = 2ke - k - e + 1
                    let k_val = BF::new(k as u128, Some(3));
                    let eq_challenge_value = eq_challenges[round_num - 1];
                    let k_times_eq_challenge_value = mult_be(&k_val, &eq_challenge_value);
                    let eq_1_center_evaluation = k_times_eq_challenge_value
                        + k_times_eq_challenge_value
                        - EF::new(k as u128, None)
                        - eq_challenge_value
                        + EF::one();
                    eq_1_center_evaluations[k as usize - 1] = eq_1_center_evaluation;
                }
            }

            // Now we have the precomputed array and challenge values for this round
            // We need to compute the round polynomial evaluations for this round
            // The round polynomial is of the form:
            // s_i(k) = eq1_left * eq1_center * pc(...)
            // for k = 0, 2, ..., d - 1, ∞.
            for (k, (eq_1_centre_eval, pc_witness_challenge_term)) in
                precomputed_array_and_challege_values
                    .iter()
                    .zip(eq_1_center_evaluations.iter())
                    .enumerate()
            {
                // The round polynomial value is simply the product of the:
                // eq1 left value, eq 1 centre value and the precomputed array value
                let intermediate_round_poly_evaluation =
                    mult_ee(&eq_1_left_cumulative, &pc_witness_challenge_term);

                round_polynomials[round_num - 1][k as usize] =
                    mult_ee(&eq_1_centre_eval, &intermediate_round_poly_evaluation);

                intermediate_round_poly.push(intermediate_round_poly_evaluation);
            }

            // Now we have a slightly tricky situation. We can derive the evaluation of the round polynomial
            // at k = 1 from the claimed sum, but we need to find the evaluation of the intermediate round polynomial
            // at k = 1. We can see that for k = 1:
            // s_i(1) = w_i * irp_i(1)
            // where w_i is i-th eq challenge and irp_i(k) is the intermediate round polynomial
            // because eq_1_centre = (1 - k)(1 - e) + ke = e when k = 1.
            // So we can compute the evaluation of the intermediate round polynomial at k = 1 by
            // irp_i(1) = s_i(1) / w_i
            // and then we can interpolate the intermediate round polynomial to get its evaluation at k = d.
            //
            // Note: see verifier for why we multiply the current sum with the scaled determinant.
            let modified_current_sum = mult_be(scaled_determinant, &current_sum);
            let derived_round_poly_evaluation_at_1 =
                modified_current_sum - round_polynomials[round_num - 1][0];
            // TODO: send eq i inverses as input to prover
            let derived_intermediate_round_poly_evaluation_at_1 =
                derived_round_poly_evaluation_at_1 * eq_challenge_value.inverse().unwrap();
            intermediate_round_poly.insert(1, derived_intermediate_round_poly_evaluation_at_1);
            let intermediate_round_poly_evaluation_at_infty =
                intermediate_round_poly.pop().unwrap();

            // Interpolate the intermediate round polynomial to get its evaluation at k = d
            let intermediate_round_poly_final_eval = barycentric_interpolation_with_infinity(
                &intermediate_round_poly,
                intermediate_round_poly_evaluation_at_infty,
                EF::new(num_witness_polys as u128, Some(2)),
            );

            // Compute the eq1 centre evaluation at k = d: (1 - k)(1 - e) + ke
            let final_k_val = BF::new(num_witness_polys as u128, Some(2));
            let k_times_eq_challenge_value = mult_be(&final_k_val, &eq_challenge_value);
            let eq_1_center_evaluation = k_times_eq_challenge_value + k_times_eq_challenge_value
                - EF::new(num_witness_polys as u128, None)
                - eq_challenge_value
                + EF::one();

            // Compute and insert the final round polynomial evaluation
            // Round polynomial will be of the form: s(0) s(2) ... s(d - 1) s(d) s(∞)
            let final_round_poly_eval =
                mult_ee(&eq_1_center_evaluation, &intermediate_round_poly_final_eval);
            round_polynomials[round_num - 1].insert(num_witness_polys - 1, final_round_poly_eval);
            debug_assert_eq!(
                round_polynomials[round_num - 1].len(),
                num_witness_polys + 1
            );

            // Update the current sum for the next round
            let mut current_round_poly_evals = round_polynomials[round_num - 1].clone();
            current_round_poly_evals.insert(1, derived_round_poly_evaluation_at_1);
            let current_round_poly_at_infty = current_round_poly_evals.pop().unwrap();

            // append the round polynomial (i.e. prover message) to the transcript
            <Transcript as TFTranscriptProtocol<EF, BF>>::append_scalars(
                transcript,
                b"r_poly",
                &round_polynomials[round_num - 1], // (d + 1) evaluations
            );

            // generate challenge α_i = H( transcript );
            let alpha = <Transcript as TFTranscriptProtocol<EF, BF>>::challenge_scalar(
                transcript,
                b"challenge_nextround",
            );

            // Compute r_{i}(α_i) using the interpolation formula with infinity
            current_sum = barycentric_interpolation_with_infinity(
                &current_round_poly_evals,   // s(0), s(1), ..., s(d)
                current_round_poly_at_infty, // s(inf)
                alpha,                       // α_i
            );

            // Store the challenge in the challenge vector
            challenge_vector.push(alpha);

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

        // Okay so we've computed the first t rounds using the small-value trick (with eq polynomial).
        // Next, we need to compute the next (n / 2 - t) rounds using just the eq trick.
        // To do so, we update the witness polynomials to substitute the round challenges:
        //
        // A_i := w_i(α_1, α_2, ..., α_j, x) for all x ∈ {0, 1}^{l - j} ]
        //
        // for all witness polynomials (i.e., i ∈ {1, 2, ..., d})
        //
        let mut ef_state_polynomials: Vec<LinearLagrangeList<EF>> = matrix_polynomials
            .into_par_iter()
            .map(|matrix_poly| matrix_poly.scale_and_squash(&challenge_matrix_polynomial, &mult_be))
            .collect();

        // Process next rounds until the (n / 2)th round
        for round_num in (round_small_val + 1)..=(prover_state.num_vars / 2) {
            // Compute the current eq1 left and challenge value
            // er + (1 - e)(1 - r) = 2er - e - r + 1
            let eq_challenge = eq_challenges[round_num - 2];
            let prev_round_challenge = challenge_vector.last().unwrap();
            let eq_times_prev_round_challenge = mult_ee(&eq_challenge, prev_round_challenge);
            let eq_1_left_and_challenge = eq_times_prev_round_challenge
                + eq_times_prev_round_challenge
                - eq_challenge
                - *prev_round_challenge
                + EF::one();
            eq_1_left_cumulative = mult_ee(&eq_1_left_cumulative, &eq_1_left_and_challenge);

            let state_poly_size = ef_state_polynomials[0].list.len();
            debug_assert_eq!(state_poly_size, 1 << (prover_state.num_vars - round_num));

            let (alpha, rp_at_1) = Self::compute_round_polynomial_with_split_eq::<EC, EF>(
                round_num,
                &ef_state_polynomials,
                &eq_1_left_cumulative,
                &eq_challenges[round_num - 1],
                &eq_1_right_staged_evals[round_num - 1],
                &eq_2_evals,
                round_polynomials,
                &current_sum,
                num_witness_polys,
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
        let eq_times_prev_round_challenge = mult_ee(&eq_challenge, prev_round_challenge);
        let eq_1_left_and_challenge = eq_times_prev_round_challenge + eq_times_prev_round_challenge
            - eq_challenge
            - *prev_round_challenge
            + EF::one();
        eq_1_left_cumulative = mult_ee(&eq_1_left_cumulative, &eq_1_left_and_challenge);

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
                num_witness_polys + 1,
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
