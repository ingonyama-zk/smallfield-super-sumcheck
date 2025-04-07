use ark_ff::{Field, PrimeField};
use ark_std::log2;
use merlin::Transcript;

use crate::data_structures::{LinearLagrangeList, MatrixPolynomial, MatrixPolynomialInt};
use crate::eq_poly::EqPoly;
use crate::extension_transcript::ExtensionTranscriptProtocol;
use crate::prover::ProverState;
use crate::verifier::barycentric_interpolation;
use crate::IPForMLSumcheck;

impl<EF: Field, BF: PrimeField> IPForMLSumcheck<EF, BF> {
    /// Algorithm 4 with eq polynomial
    pub fn prove_with_eq_toom_cook_agorithm<BE, EE, BB, EC>(
        prover_state: &mut ProverState<EF, BF>,
        transcript: &mut Transcript,
        round_polynomials: &mut Vec<Vec<EF>>,
        eq_challenges: &Vec<EF>,
        round_small_val: usize,
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
        // We apply small value sumcheck for first t rounds
        // and we apply small space sumcheck for first (n / 2) rounds
        // We must ensure t ≤ n/2
        assert!(round_small_val <= prover_state.num_vars / 2);

        // Number of eq challenges must be equal to the number of rounds
        assert_eq!(eq_challenges.len(), prover_state.num_vars);

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
        let mut eq_1_left_basis = eq_1_basis.to_vec();
        eq_1_left_basis.pop();
        let mut eq_1_right_basis = eq_1_basis[1..].to_vec();
        eq_1_right_basis.reverse();

        let eq_1_left_poly = EqPoly::new(eq_1_left_basis);
        let mut eq_1_left_staged_evals = eq_1_left_poly.compute_staged_evals(false);
        eq_1_left_staged_evals.insert(0, vec![EF::one()]);

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
        assert_eq!(eq_1_left_staged_evals.len(), eq_1_right_staged_evals.len());
        for i in 0..eq_1_right_staged_evals.len() {
            let len_eq_1_left = eq_1_left_staged_evals[i].len(); // 2^{i}
            let len_eq_1_right = eq_1_right_staged_evals[i].len(); // 2^{n/2 - i - 1}
            let log_len_eq_1 = log2(len_eq_1_left * len_eq_1_right) as usize; // n/2 - 1
            let log_len_eq_2 = log2(eq_2_evals.len()) as usize; // n/2
            assert_eq!(log_len_eq_1, (prover_state.num_vars / 2 - 1));
            assert_eq!(log_len_eq_1 + log_len_eq_2, prover_state.num_vars - 1);
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

        let mut matrix_polynomials_int: Vec<MatrixPolynomialInt<i64>> = prover_state
            .state_polynomials_int
            .iter()
            .map(|witness_poly_int| MatrixPolynomialInt::from_evaluations(witness_poly_int))
            .collect::<Vec<_>>();

        // For this, we first fold the witness matrices to get their dimension: 2^t  x  (N / 2^t)
        for _ in 2..=round_small_val {
            for matrix in &mut matrix_polynomials {
                matrix.heighten();
            }

            for matrix in &mut matrix_polynomials_int {
                matrix.heighten();
            }
        }

        // Pre-compute the witness terms (toom-cook multiplication of witness polynomials)
        let r_degree = prover_state.max_multiplicands;
        let num_witness_polys = prover_state.state_polynomials.len();
        assert_eq!(r_degree, num_witness_polys + 1); // sumcheck_poly = eq * w_1 * ... * w_d

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
            let mut cumulative_matrix_int_row_for_j = MatrixPolynomialInt::compute_merkle_roots(
                &matrix_polynomials_int[0],
                j,
                mappings_int,
            )
            .evaluation_rows[0]
                .to_vec();

            for i in 1..matrix_polynomials.len() {
                let matrix_int_row_for_j = MatrixPolynomialInt::compute_merkle_roots(
                    &matrix_polynomials_int[i],
                    j,
                    mappings_int,
                )
                .evaluation_rows[0]
                    .to_vec();

                assert_eq!(
                    cumulative_matrix_int_row_for_j.len(),
                    matrix_int_row_for_j.len()
                );
                assert_eq!(
                    cumulative_matrix_int_row_for_j.len(),
                    1 << (prover_state.num_vars - round_small_val)
                );
                cumulative_matrix_int_row_for_j
                    .iter_mut()
                    .zip(&matrix_int_row_for_j)
                    .for_each(|(a, &b)| *a *= b);
            }

            // Convert the integer row to a field row
            let cumulative_matrix_row_for_j: Vec<BF> = cumulative_matrix_int_row_for_j
                .iter()
                .map(|&p| {
                    let p_positive = BF::from(p.abs() as u64);
                    let adjusted_value = if p < 0 { -p_positive } else { p_positive };
                    adjusted_value
                })
                .collect();

            precomputed_witness_matrix
                .evaluation_rows
                .push(cumulative_matrix_row_for_j);
        }

        // Santiy checks
        let round_small_evals_size = 1 << (prover_state.num_vars - round_small_val);
        assert_eq!(precomputed_witness_matrix.no_of_rows, num_product_terms);
        assert_eq!(
            precomputed_witness_matrix.no_of_columns,
            round_small_evals_size
        );
        assert!(precomputed_witness_matrix.no_of_columns % eq_2_evals.len() == 0);

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

        for (row_idx, witness_row) in precomputed_witness_matrix
            .evaluation_rows
            .iter()
            .enumerate()
        {
            for (chunk_idx, witness_chunk) in witness_row.chunks(eq_2_evals.len()).enumerate() {
                compressed_witness_with_eq_2.evaluation_rows[row_idx][chunk_idx] = witness_chunk
                    .iter()
                    .zip(&eq_2_evals)
                    .map(|(w_val, eq_2_challenge)| mult_be(w_val, eq_2_challenge))
                    .sum();
            }
        }

        // Let us iterate over the precomputed matrix and compute the witness terms
        // for each round.
        let mut pre_computed_array_with_eq: Vec<Vec<EF>> = vec![vec![]; round_small_val];

        for round_number in (1..=round_small_val).rev() {
            // Now lets squash the compressed witness matrix rows to get a single row
            // Get the eq 1 right evaluations for this round
            // Lets start by some assertions on the sizes
            let eq_1_right_for_round = &eq_1_right_staged_evals[round_number - 1];
            let eq_1_right_size = eq_1_right_for_round.len();
            let round_size = num_evals.pow(round_number as u32);
            assert_eq!(compressed_witness_with_eq_2.no_of_rows, round_size);
            assert_eq!(compressed_witness_with_eq_2.no_of_columns, eq_1_right_size);

            // Now multiply the resulting matrix with the eq1 evaluations
            let mut compressed_witness_eq_1_eq_2: Vec<EF> = Vec::with_capacity(round_size);
            for witness_row in compressed_witness_with_eq_2.evaluation_rows.iter() {
                assert_eq!(witness_row.len(), eq_1_right_size);
                let ip = witness_row
                    .iter()
                    .zip(eq_1_right_for_round.iter())
                    .map(|(w_val, eq_1_challenge)| mult_ee(w_val, eq_1_challenge))
                    .sum();
                compressed_witness_eq_1_eq_2.push(ip);
            }

            // Push the compressed witness matrix for this round to the pre-computed array
            pre_computed_array_with_eq[round_number - 1] = compressed_witness_eq_1_eq_2;

            // Update extracted witness for next round
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
        for round_num in 1..=round_small_val {
            // Constants
            let round_size = num_evals.pow(round_num as u32);

            // Compute the current eq1 left and challenge value
            // Denoted by (A) in the equation above
            if round_num > 1 {
                let eq_challenge = eq_challenges[round_num - 2];
                let one_minus_eq_challenge = EF::one() - eq_challenge;
                let prev_round_challenge = challenge_vector.last().unwrap();
                let one_minus_prev_round_challenge = EF::one() - *prev_round_challenge;

                // TODO: can use one ee_mult instead of two here!
                let eq_1_left_and_challenge = mult_ee(&eq_challenge, &prev_round_challenge)
                    + mult_ee(&one_minus_eq_challenge, &one_minus_prev_round_challenge);
                eq_1_left_cumulative = mult_ee(&eq_1_left_cumulative, &eq_1_left_and_challenge);
            }

            // Fetch (d + 1)^r witness terms using only bb additions
            // We use given projection mapping indices to know which witness terms to combine from
            // the pre-computed array of size (d + 1)^t
            let precomputed_array_for_this_round: &Vec<EF> =
                &pre_computed_array_with_eq[round_num - 1];
            assert_eq!(precomputed_array_for_this_round.len(), round_size);
            assert_eq!(challenge_matrix.evaluation_rows.len(), round_num - 1);

            let mut intermediate_round_poly: Vec<EF> = Vec::with_capacity(num_evals as usize);
            for k in 0..num_evals as u64 {
                //
                // Lets start with the outer equality polynomial terms:
                // +------------+----------------------------+------------------------+
                // |            | Eq challenges              | Round challenges       |
                // +------------+----------------------------+------------------------+
                // | eq1 left   | α_1, α_2, ..., α_{i-1} ]   | r_1, r_2, ..., r_{i-1} |
                // | eq1 center | α_i                        | r_i                    |
                // +------------+----------------------------+------------------------+
                //
                // We have the eq1 left evaluation in the eq1_left_cumulative variable
                // Lets compute the eq1 centre evaluation (denoted by (B) in the equation above)
                // TODO: can use one be_mult instead of two here!
                let k_val = BF::from(k as u32);
                let one_minus_k_val = BF::one() - k_val;
                let eq_challenge_value = eq_challenges[round_num - 1];
                let one_minus_eq_challenge_value = EF::one() - eq_challenge_value;
                let eq_1_center_evaluation =
                    mult_be(&one_minus_k_val, &one_minus_eq_challenge_value)
                        + mult_be(&k_val, &eq_challenge_value);

                //
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
                    BF::from(k as u32),
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
                let mut precomputed_array_and_challege_value = EF::zero();
                for j in 0..(round_size / num_evals) {
                    // Extract j_1 to process the scalar separately
                    let mut local_witness_accumulator = EF::zero();
                    for j_1 in 0..num_evals {
                        local_witness_accumulator += mult_be(
                            &scalar_matrix.evaluation_rows[0][j_1],
                            &precomputed_array_for_this_round[j * num_evals + j_1],
                        );
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

                    // Update the precomputed_array_and_challege_value term
                    precomputed_array_and_challege_value +=
                        mult_ee(&local_witness_accumulator, &local_interpolated_challenge);

                    // Accumulate round polynomial evaluation at k
                    round_polynomials[round_num - 1][k as usize] +=
                        mult_ee(&local_witness_accumulator, &local_interpolated_challenge);
                }

                // The round polynomial value is simply the product of the:
                // eq1 left value, eq 1 centre value and the precomputed array value
                let intermediate_round_poly_evaluation =
                    mult_ee(&eq_1_left_cumulative, &precomputed_array_and_challege_value);

                round_polynomials[round_num - 1][k as usize] =
                    mult_ee(&eq_1_center_evaluation, &intermediate_round_poly_evaluation);

                intermediate_round_poly.push(intermediate_round_poly_evaluation);
            }

            // Now we need to compute the final evaluation of the round polynomial at k = (d + 1)
            // To do that, we need to interpolate the intermediate round polynomial and compute
            // its evaluation at k = (d + 1)
            // Then we can simply compute the final round polynomial evaluation as
            // eq1(w_i, k) * s'_i(d + 1)
            //
            let intermediate_round_poly_final_eval =
                barycentric_interpolation(&intermediate_round_poly, EF::from(num_evals as u64));

            // Compute the eq1 centre evaluation at k = (d + 1)
            let final_k_val = BF::from(num_evals as u64);
            let one_minus_final_k_val = BF::one() - final_k_val;
            let one_minus_eq_challenge_value = EF::one() - eq_challenges[round_num - 1];
            let eq_challenge_value = eq_challenges[round_num - 1];
            let eq_1_center_evaluation =
                mult_be(&one_minus_final_k_val, &one_minus_eq_challenge_value)
                    + mult_be(&final_k_val, &eq_challenge_value);

            let final_round_poly_eval =
                mult_ee(&eq_1_center_evaluation, &intermediate_round_poly_final_eval);
            round_polynomials[round_num - 1][num_evals] = final_round_poly_eval;

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
            .iter()
            .map(|matrix_poly| matrix_poly.scale_and_squash(&challenge_matrix_polynomial, &mult_be))
            .collect();

        // TODO: PLEASE TEST TILL HERE.

        // Process next rounds until the (n / 2)th round
        for round_num in (round_small_val + 1)..=(prover_state.num_vars / 2) {
            // Compute the current eq1 left and challenge value
            // TODO: can use one ee_mult instead of two here!
            let eq_challenge = eq_challenges[round_num - 2];
            let one_minus_eq_challenge = EF::one() - eq_challenge;
            let prev_round_challenge = challenge_vector.last().unwrap();
            let one_minus_prev_round_challenge = EF::one() - *prev_round_challenge;
            let eq_1_left_and_challenge = mult_ee(&eq_challenge, &prev_round_challenge)
                + mult_ee(&one_minus_eq_challenge, &one_minus_prev_round_challenge);
            eq_1_left_cumulative = mult_ee(&eq_1_left_cumulative, &eq_1_left_and_challenge);

            let state_poly_size = ef_state_polynomials[0].list.len();
            assert_eq!(state_poly_size, 1 << (prover_state.num_vars - round_num));

            let mut intermediate_round_poly: Vec<EF> = Vec::with_capacity(num_evals as usize);

            for k in 0..num_evals {
                // Compute the eq1 centre evaluation
                // TODO: can use one be_mult instead of two here!
                let k_val = BF::from(k as u32);
                let one_minus_k_val = BF::one() - k_val;
                let eq_challenge_value = eq_challenges[round_num - 1];
                let one_minus_eq_challenge_value = EF::one() - eq_challenge_value;
                let eq_1_center_evaluation =
                    mult_be(&one_minus_k_val, &one_minus_eq_challenge_value)
                        + mult_be(&k_val, &eq_challenge_value);

                // Evaluation points
                let k_val = EF::from(k as u32);
                let one_minus_k_val = EF::one() - k_val;

                // Compute the witness products
                let mut witness_products = vec![EF::one(); state_poly_size];
                for poly in &ef_state_polynomials {
                    for (i, witness) in poly.list.iter().enumerate() {
                        witness_products[i] = mult_ee(
                            &witness_products[i],
                            &(one_minus_k_val * witness.even + k_val * witness.odd),
                        );
                    }
                }

                // Now merge the witness products with the eq1 right and eq2 evaluations
                // Fetch the equality polynomials for this round
                let eq_1_right_for_round = &eq_1_right_staged_evals[round_num - 1];
                let eq_2_for_round = &eq_2_evals;
                assert_eq!(
                    witness_products.len(),                            // 2^{n - i}
                    eq_1_right_for_round.len() * eq_2_for_round.len() // 2^{n/2-i} * 2^{n/2} = 2^{n-i}
                );

                // Now multiply the witness products with eq2 evaluations
                let mut witness_prod_and_eq_2: Vec<EF> =
                    vec![EF::zero(); eq_1_right_for_round.len()];

                for (w_idx, witness_prod) in witness_products.iter().enumerate() {
                    let eq_2_idx = w_idx % eq_2_for_round.len();
                    let eq_1_right_idx = w_idx / eq_2_for_round.len();
                    witness_prod_and_eq_2[eq_1_right_idx] +=
                        mult_ee(witness_prod, &eq_2_for_round[eq_2_idx]);
                }

                // Now multiply the resulting vec with the eq1 evaluations
                let witness_prod_eq_1_eq_2: EF = witness_prod_and_eq_2
                    .iter()
                    .zip(eq_1_right_for_round.iter())
                    .map(|(witness_and_eq2_term, eq_1_right_term)| {
                        mult_ee(witness_and_eq2_term, eq_1_right_term)
                    })
                    .fold(EF::zero(), |acc, val| acc + val);

                // Push the intermediate round polynomial evaluation
                let intermediate_round_poly_evaluation =
                    mult_ee(&eq_1_left_cumulative, &witness_prod_eq_1_eq_2);
                intermediate_round_poly.push(intermediate_round_poly_evaluation);

                // Compute the round polynomial evaluation
                round_polynomials[round_num - 1][k as usize] =
                    mult_ee(&eq_1_center_evaluation, &intermediate_round_poly_evaluation);
            }

            // Now we need to compute the final evaluation of the round polynomial at k = (d + 1)
            // To do that, we need to interpolate the intermediate round polynomial and compute
            // its evaluation at k = (d + 1)
            // Then we can simply compute the final round polynomial evaluation as
            // eq1(w_i, k) * s'_i(d + 1)
            //
            let intermediate_round_poly_final_eval =
                barycentric_interpolation(&intermediate_round_poly, EF::from(num_evals as u64));

            // Compute the eq1 centre evaluation at k = (d + 1)
            let final_k_val = BF::from(num_evals as u64);
            let one_minus_final_k_val = BF::one() - final_k_val;
            let one_minus_eq_challenge_value = EF::one() - eq_challenges[round_num - 1];
            let eq_challenge_value = eq_challenges[round_num - 1];
            let eq_1_center_evaluation =
                mult_be(&one_minus_final_k_val, &one_minus_eq_challenge_value)
                    + mult_be(&final_k_val, &eq_challenge_value);

            let final_round_poly_eval =
                mult_ee(&eq_1_center_evaluation, &intermediate_round_poly_final_eval);
            round_polynomials[round_num - 1][num_evals] = final_round_poly_eval;

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

            // Store the challenge in the challenge vector
            challenge_vector.push(alpha);

            // update the state polynomials
            for j in 0..ef_state_polynomials.len() {
                ef_state_polynomials[j].fold_in_half(alpha);
            }
        }

        // Before we process the last (n / 2) rounds using the naive algorithm, we need to update
        // the equality polynomial. Let's first update the eq1 cumulative value using the latest challenge.
        let eq_challenge = eq_challenges[prover_state.num_vars / 2 - 1];
        let one_minus_eq_challenge = EF::one() - eq_challenge;
        let prev_round_challenge = challenge_vector.last().unwrap();
        let one_minus_prev_round_challenge = EF::one() - *prev_round_challenge;
        let eq_1_left_and_challenge = mult_ee(&eq_challenge, &prev_round_challenge)
            + mult_ee(&one_minus_eq_challenge, &one_minus_prev_round_challenge);
        eq_1_left_cumulative = mult_ee(&eq_1_left_cumulative, &eq_1_left_and_challenge);

        // Now lets update the eq2 polynomial by multiplying it with the eq1 cumulative value
        let mut eq_2_for_final_rounds = eq_2_evals.clone();
        for i in 0..eq_2_evals.len() {
            eq_2_for_final_rounds[i] = mult_ee(&eq_1_left_cumulative, &eq_2_for_final_rounds[i]);
        }

        // Add this eq2 polynomial to the state polynomials
        ef_state_polynomials.push(LinearLagrangeList::from_vector(&eq_2_for_final_rounds));

        // Check if all state polynomials have the same size
        for i in 0..ef_state_polynomials.len() {
            assert_eq!(
                ef_state_polynomials[i].list.len(),
                1 << (prover_state.num_vars - prover_state.num_vars / 2 - 1)
            );
        }

        // Process remaining rounds by switching to Algorithm 1
        for round_num in ((prover_state.num_vars / 2) + 1)..=prover_state.num_vars {
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
