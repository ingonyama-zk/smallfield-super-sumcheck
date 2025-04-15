use ark_std::log2;
use merlin::Transcript;

use crate::btf_transcript::TFTranscriptProtocol;
use crate::data_structures::{bit_extend_and_insert, LinearLagrangeList, MatrixPolynomial};
use crate::eq_poly::EqPoly;
use crate::prover::ProverState;
use crate::tower_fields::TowerField;
use crate::verifier::barycentric_interpolation;
use crate::IPForMLSumcheck;

impl<EF: TowerField, BF: TowerField> IPForMLSumcheck<EF, BF> {
    /// Algorithm 3
    pub fn prove_with_eq_precomputation_agorithm<BE, EE, BB, EC>(
        prover_state: &mut ProverState<EF, BF>,
        transcript: &mut Transcript,
        round_polynomials: &mut Vec<Vec<EF>>,
        round_small_val: usize,
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
        // We apply small value sumcheck for first t rounds
        // and we apply small space sumcheck for first (n / 2) rounds
        // We must ensure t ≤ n/2
        assert!(round_small_val <= prover_state.num_vars / 2);

        // Number of eq challenges must be equal to the number of rounds
        assert!(
            prover_state.eq_challenges.is_some(),
            "Equality poly challenges cannot be `None`."
        );
        let eq_challenges = prover_state.eq_challenges.clone().unwrap();
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

        // For this, we first fold the witness matrices to get their dimension: 2^t  x  (N / 2^t)
        for _ in 2..=round_small_val {
            for matrix in &mut matrix_polynomials {
                matrix.heighten();
            }
        }

        // Pre-compute bb multiplications upto round t
        let precomputed_for_round_small_val =
            MatrixPolynomial::tensor_column_products(&matrix_polynomials, mult_bb);

        // Pre-compute the witness terms multiplied by the eq1 and eq2 evaluations
        // TODO: we might be allocating unncecessary memory for the last round (i.e., round t)
        let num_witness_polys = prover_state.state_polynomials.len();

        let num_round_poly_evals = num_witness_polys + 1;
        let mut pre_computed_array_with_eq: Vec<Vec<Vec<EF>>> = vec![vec![]; num_round_poly_evals];
        for round_num in 1..=round_small_val {
            // ----------------------------------------------
            // Extract the witness terms for this round
            // ----------------------------------------------
            let extracted_witness_for_round = MatrixPolynomial::extract_subtensors_from_tensors(
                &precomputed_for_round_small_val,
                num_witness_polys,                  // degree d
                1 << (round_small_val - round_num), // 2^{t - i}
            );

            // Check if the number of extracted witness terms is correct
            assert_eq!(
                extracted_witness_for_round.len(),
                1 << (prover_state.num_vars - round_num) // 2^{n - i}
            );

            // Check if each vector in extracted witness terms has the correct length
            for witness in &extracted_witness_for_round {
                assert_eq!(witness.len(), 1 << (round_num * num_witness_polys));
                // 2^{r * d}
            }

            // Now lets compute the precomputed array for this round for each k
            // TODO: define evaluation point vector: [0, 2, 3, ...] because you can avoid computing for k = 1
            for k in 0..num_round_poly_evals as u64 {
                // Compute scalar vector:
                // For d = 1: [(1 - k), k]
                // For d = 2: [(1 - k)²,  (1 - k)k,  k(1 - k), k²]
                // For d = 3: [(1 - k)³,  (1 - k)²k,  (1 - k)k(1 - k),  (1 - k)k²,  k(1 - k)², k(1 - k)k, k²(1 - k), k³]
                let scalar_tuple_matrix = MatrixPolynomial::from_evaluations_vec(&vec![
                    BF::one() - BF::new(k as u128, Some(2)),
                    BF::new(k as u128, Some(2)),
                ]);
                let mut k_matrix = scalar_tuple_matrix.clone();
                for _ in 1..num_witness_polys {
                    k_matrix = k_matrix.tensor_hadamard_product(&scalar_tuple_matrix, &mult_bb);
                }
                let two_pow_degree = (1 as usize) << num_witness_polys;
                assert_eq!(k_matrix.no_of_columns, 1);
                assert_eq!(k_matrix.no_of_rows, two_pow_degree);

                // Define a temporary data structure to store the compressed witness terms
                // This would be a matrix of size: W x 2^{(r - 1) * d}
                // s.t. the given witness matrix is of size: W x 2^{r * d}
                let mut compressed_witness_for_k: Vec<Vec<BF>> =
                    Vec::with_capacity(extracted_witness_for_round.len());

                for row in extracted_witness_for_round.iter() {
                    let temp_num_cols = 1 << ((round_num - 1) * num_witness_polys);
                    let mut temp_row = Vec::with_capacity(temp_num_cols);
                    for idx in 0..temp_num_cols {
                        let mut scalar_accumulator = BF::zero();
                        for j in 0..two_pow_degree {
                            let total_input_bit_len = num_witness_polys * (round_num - 1);
                            let bit_extended_index = bit_extend_and_insert(
                                idx,
                                total_input_bit_len,
                                j,
                                num_witness_polys,
                                round_num - 1,
                                round_num,
                            );
                            scalar_accumulator +=
                                k_matrix.evaluation_rows[j][0] * row[bit_extended_index];
                        }
                        temp_row.push(scalar_accumulator);
                    }
                    compressed_witness_for_k.push(temp_row);
                }

                // Now lets squash the compressed witness matrix rows to get a single row
                // We do so by multiplying the compressed witness matrix with the eq1 and eq2 evaluations
                // Lets start by some assertions on the sizes
                // Fetch the equality polynomials for this round
                let eq_1_right_for_round = &eq_1_right_staged_evals[round_num - 1];
                let eq_2_for_round = &eq_2_evals;
                assert_eq!(
                    compressed_witness_for_k.len(),                    // 2^{n - i}
                    eq_1_right_for_round.len() * eq_2_for_round.len() // 2^{n/2-i} * 2^{n/2} = 2^{n-i}
                );

                // Now multiply the compressed witness matrix with eq2 evaluations
                let mut compressed_witness_and_eq_2: Vec<Vec<EF>> = vec![
                        vec![EF::zero(); compressed_witness_for_k[0].len()];
                        eq_1_right_for_round.len()
                    ];

                for (w_idx, witness_row) in compressed_witness_for_k.iter().enumerate() {
                    let eq_2_idx = w_idx % eq_2_for_round.len();
                    let eq_1_right_idx = w_idx / eq_2_for_round.len();
                    for (col, w_val) in witness_row.iter().enumerate() {
                        compressed_witness_and_eq_2[eq_1_right_idx][col] +=
                            mult_be(w_val, &eq_2_for_round[eq_2_idx]);
                    }
                }

                // Now multiply the resulting matrix with the eq1 evaluations
                let mut compressed_witness_eq_1_eq_2: Vec<EF> =
                    vec![EF::zero(); compressed_witness_and_eq_2[0].len()];

                compressed_witness_and_eq_2
                    .iter()
                    .zip(eq_1_right_for_round.iter())
                    .for_each(|(witness_row, eq_1_right_challenge)| {
                        for (col, w_val) in witness_row.iter().enumerate() {
                            compressed_witness_eq_1_eq_2[col] +=
                                mult_ee(w_val, eq_1_right_challenge);
                        }
                    });

                // Check if the resulting compressed witness matrix has the correct length
                assert_eq!(
                    compressed_witness_eq_1_eq_2.len(),
                    1 << ((round_num - 1) * num_witness_polys)
                );

                pre_computed_array_with_eq[k as usize].push(compressed_witness_eq_1_eq_2);
            }
        }

        // This matrix will store challenges in the form:
        // [ (1-α_1)(1-α_2)...(1-α_m) ]
        // [ (1-α_1)(1-α_2)...(α_m) ]
        // [ .. ]
        // [ .. ]
        // [ (α_1)(α_2)...(α_m) ]
        let mut challenge_matrix_polynomial: MatrixPolynomial<EF> = MatrixPolynomial::one();
        let mut challenge_vector: Vec<EF> = Vec::with_capacity(round_small_val);

        // Round computation starts here:
        // The round polynomial is of the form:
        //
        // s_i(k) = eq1_left * eq1_center * ∑ ∑ ... ∑ round_challenge_terms * pre_computed_i(k)
        //
        // We will compute the equality terms first and then compute the inner sum for each k.
        //
        let mut eq_1_left_cumulative = EF::one();
        for round_num in 1..=round_small_val {
            // Compute challenge terms for 2^{(r - 1) * d} terms
            let mut gamma_matrix = challenge_matrix_polynomial.clone();
            for _ in 1..num_witness_polys {
                gamma_matrix =
                    gamma_matrix.tensor_hadamard_product(&challenge_matrix_polynomial, &mult_ee);
            }

            if round_num > 1 {
                // Compute the current eq1 left and challenge value
                let eq_challenge = eq_challenges[round_num - 2];
                let one_minus_eq_challenge = EF::one() - eq_challenge;
                let prev_round_challenge = challenge_vector.last().unwrap();
                let one_minus_prev_round_challenge = EF::one() - *prev_round_challenge;

                // TODO: can use one ee_mult instead of two here!
                let eq_1_left_and_challenge = mult_ee(&eq_challenge, &prev_round_challenge)
                    + mult_ee(&one_minus_eq_challenge, &one_minus_prev_round_challenge);
                eq_1_left_cumulative = mult_ee(&eq_1_left_cumulative, &eq_1_left_and_challenge);
            }

            // Compute round polynomial at k ∈ [0, 1, ..., d]
            // The intermediate polynomial is s'_i(k) defined s.t.:
            //
            // s_i(k) = s'_i(k) * eq1_center.
            //
            // The degree of s'_i(k) is d (number of witness polynomials), so we can evaluate it at
            // d + 1 points (i.e., 0, 1, ..., d) and thus compute s_i(k) at those points.
            //
            // But since the degree of s_i(c) is (d + 1), we need its evaluation at one more point (i.e., k = d + 1)
            // To compute that, we interpolate the intermediate polynomial and compute its evaluation at k = d + 1
            // and recover s_i(d + 1) as:
            // s_i(d + 1) = s'_i(d + 1) * eq1_center(d + 1).
            //
            let mut intermediate_round_poly: Vec<EF> =
                Vec::with_capacity(num_round_poly_evals as usize);
            for k in 0..num_round_poly_evals {
                //
                // As the round polynomial is of the form:
                //
                // s_i(k) = eq1_left * eq1_center * ∑ ∑ ... ∑ round_challenge_terms * pre_computed_i(k)
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
                // Lets compute the eq1 centre evaluation
                // Compute the eq1 centre evaluation
                // TODO: can use one be_mult instead of two here!
                let k_val = BF::new(k as u128, Some(3));
                let one_minus_k_val = BF::one() - k_val;
                let eq_challenge_value = eq_challenges[round_num - 1];
                let one_minus_eq_challenge_value = EF::one() - eq_challenge_value;
                let eq_1_center_evaluation =
                    mult_be(&one_minus_k_val, &one_minus_eq_challenge_value)
                        + mult_be(&k_val, &eq_challenge_value);

                // Fetch the precomputed array for this round and k and compute the inner product with the gamma matrix
                let precomputed_array_for_k = &pre_computed_array_with_eq[k][round_num - 1];
                assert_eq!(precomputed_array_for_k.len(), gamma_matrix.no_of_rows);
                let precomputed_array_and_challege_value = gamma_matrix
                    .evaluation_rows
                    .iter()
                    .zip(precomputed_array_for_k.iter())
                    .map(|(challenge_multiplicand, witness_term)| {
                        mult_ee(witness_term, &challenge_multiplicand[0])
                    })
                    .fold(EF::zero(), |acc, val| acc + val);

                // The round polynomial value is simply the product of the:
                // eq1 left value, eq 1 centre value and the precomputed array value
                let intermediate_round_poly_evaluation =
                    mult_ee(&eq_1_left_cumulative, &precomputed_array_and_challege_value);

                round_polynomials[round_num - 1][k as usize] =
                    mult_ee(&eq_1_center_evaluation, &intermediate_round_poly_evaluation);

                intermediate_round_poly.push(intermediate_round_poly_evaluation);

                // Ensure Γ has only 1 column and Γ.
                assert_eq!(gamma_matrix.no_of_columns, 1);
            }

            // Now we need to compute the final evaluation of the round polynomial at k = (d + 1)
            // To do that, we need to interpolate the intermediate round polynomial and compute
            // its evaluation at k = (d + 1)
            // Then we can simply compute the final round polynomial evaluation as
            // eq1(w_i, k) * s'_i(d + 1)
            //
            let intermediate_round_poly_final_eval = barycentric_interpolation(
                &intermediate_round_poly,
                EF::new(num_round_poly_evals as u128, Some(2)),
            );

            // Compute the eq1 centre evaluation at k = (d + 1)
            let final_k_val = BF::new(num_round_poly_evals as u128, Some(2));
            let one_minus_final_k_val = BF::one() - final_k_val;
            let one_minus_eq_challenge_value = EF::one() - eq_challenges[round_num - 1];
            let eq_challenge_value = eq_challenges[round_num - 1];
            let eq_1_center_evaluation =
                mult_be(&one_minus_final_k_val, &one_minus_eq_challenge_value)
                    + mult_be(&final_k_val, &eq_challenge_value);

            let final_round_poly_eval =
                mult_ee(&eq_1_center_evaluation, &intermediate_round_poly_final_eval);
            round_polynomials[round_num - 1][num_round_poly_evals] = final_round_poly_eval;

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

            // Store the challenge in the challenge vector
            challenge_vector.push(alpha);

            // Update challenge matrix with new challenge
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

            let mut intermediate_round_poly: Vec<EF> =
                Vec::with_capacity(num_round_poly_evals as usize);

            for k in 0..num_round_poly_evals {
                // Compute the eq1 centre evaluation
                // TODO: can use one be_mult instead of two here!
                let k_val = BF::new(k as u128, Some(3));
                let one_minus_k_val = BF::one() - k_val;
                let eq_challenge_value = eq_challenges[round_num - 1];
                let one_minus_eq_challenge_value = EF::one() - eq_challenge_value;
                let eq_1_center_evaluation =
                    mult_be(&one_minus_k_val, &one_minus_eq_challenge_value)
                        + mult_be(&k_val, &eq_challenge_value);

                // Evaluation points
                let k_val = EF::new(k as u128, None);
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
            let intermediate_round_poly_final_eval = barycentric_interpolation(
                &intermediate_round_poly,
                EF::new(num_round_poly_evals as u128, Some(2)),
            );

            // Compute the eq1 centre evaluation at k = (d + 1)
            let final_k_val = BF::new(num_round_poly_evals as u128, Some(2));
            let one_minus_final_k_val = BF::one() - final_k_val;
            let one_minus_eq_challenge_value = EF::one() - eq_challenges[round_num - 1];
            let eq_challenge_value = eq_challenges[round_num - 1];
            let eq_1_center_evaluation =
                mult_be(&one_minus_final_k_val, &one_minus_eq_challenge_value)
                    + mult_be(&final_k_val, &eq_challenge_value);

            let final_round_poly_eval =
                mult_ee(&eq_1_center_evaluation, &intermediate_round_poly_final_eval);
            round_polynomials[round_num - 1][num_round_poly_evals] = final_round_poly_eval;

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
                num_witness_polys,
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
