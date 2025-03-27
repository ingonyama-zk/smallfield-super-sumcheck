use ark_std::log2;
use merlin::Transcript;

use crate::btf_transcript::TFTranscriptProtocol;
use crate::data_structures::{
    bit_extend_and_insert, print_collection, LinearLagrangeList, MatrixPolynomial,
};
use crate::eq_poly::EqPoly;
use crate::prover::ProverState;
use crate::tower_fields::TowerField;
use crate::IPForMLSumcheck;

impl<EF: TowerField, BF: TowerField> IPForMLSumcheck<EF, BF> {
    /// Algorithm 3
    pub fn prove_with_eq_precomputation_agorithm<BE, EE, BB, EC>(
        prover_state: &mut ProverState<EF, BF>,
        transcript: &mut Transcript,
        round_polynomials: &mut Vec<Vec<EF>>,
        eq_challenges: &Vec<EF>,
        round_small_val: usize,
        round_small_space: usize,
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
        // and we apply small space sumcheck for first l rounds
        // We must ensure t < l <= n
        assert!(round_small_val <= round_small_space);
        assert!(round_small_space <= prover_state.num_vars);

        // Number of eq challenges must be equal to the number of rounds
        assert_eq!(eq_challenges.len(), prover_state.num_vars);

        println!("witness poly: {:#?}", prover_state.state_polynomials);
        println!("eq challenges: {:#?}", eq_challenges);

        // First, lets compute the challenge pre-computation terms
        //
        // Split the eq challenges into two parts: first eq contains
        let (eq_1_basis, eq_2_basis) = eq_challenges.split_at(prover_state.num_vars / 2);

        // First equality polynomial is of the form: [ α_1, α_2, ..., α_{n/2} ]
        // In round i, we further split it into two parts L and R as follows:
        // eq1 L: [ α_1, α_2, ..., α_{i} ]
        // eq1 R: [ α_{i+1}, α_{i+2}, ..., α_{n/2} ]
        // We compute the evaluations of eq1 L and eq1 R in the pre-computation phase.
        // Note that we reverse the eq1 R basis so that we get the required evaluations using staged evaluations.
        //
        // For example for n = 6, if the first eq is [ α_1, α_2, α_3 ] we get the following evaluations:
        //
        // +-----+--------------------+----------------------+-------------------------------+
        // | Eq1 | Round 1            | Round 2              | Round 3                       |
        // +-----+--------------------+----------------------+-------------------------------+
        // |     | (1 - α_1)          | (1 - α_1)(1 - α_2)   | (1 - α_1)(1 - α_2)(1 - α_3)   |
        // |     | (α_1)              | (1 - α_1)(α_2)       | (1 - α_1)(1 - α_2)(α_3)       |
        // |     |                    | (α_1)(1 - α_2)       | (1 - α_1)(α_2)(1 - α_3)       |
        // | L   |                    | (α_1)(α_2)           | (1 - α_1)(α_2)(α_3)           |
        // |     |                    |                      | (α_1)(1 - α_2)(1 - α_3)       |
        // |     |                    |                      | (α_1)(1 - α_2)(α_3)           |
        // |     |                    |                      | (α_1)(α_2)(1 - α_3)           |
        // |     |                    |                      | (α_1)(α_2)(α_3)               |
        // +-----+--------------------+----------------------+-------------------------------+
        // |     | (1 - α_3)(1 - α_2) | (1 - α_3)            | 1                             |
        // |     | (1 - α_3)(α_2)     | (α_3)                |                               |
        // | R   | (α_3)(1 - α_2)     |                      |                               |
        // |     | (α_3)(α_2)         |                      |                               |
        // +-----+--------------------+----------------------+-------------------------------+
        //
        // TODO: Can we optimise by trying to compute L and R using common multiplications?
        //
        let eq_1_left_basis = eq_1_basis.to_vec();
        let mut eq_1_right_basis = eq_1_basis[1..].to_vec();
        eq_1_right_basis.reverse();

        println!("eq1 left basis: {:#?}", eq_1_left_basis);
        println!("eq1 right basis: {:#?}", eq_1_right_basis);

        let eq_1_left_poly = EqPoly::new(eq_1_left_basis);
        let eq_1_left_staged_evals = eq_1_left_poly.compute_staged_evals();

        let eq_1_right_poly = EqPoly::new(eq_1_right_basis);
        let mut eq_1_right_staged_evals = eq_1_right_poly.compute_staged_evals();
        eq_1_right_staged_evals.reverse();
        eq_1_right_staged_evals.push(vec![EF::from(1u64)]);

        println!("Round 1:");
        println!("eq1 left staged evals: {:#?}", eq_1_left_staged_evals[0]);
        println!("eq1 right staged evals: {:#?}", eq_1_right_staged_evals[0]);

        println!("Round 2:");
        println!("eq1 left staged evals: {:#?}", eq_1_left_staged_evals[1]);
        println!("eq1 right staged evals: {:#?}", eq_1_right_staged_evals[1]);

        // Second equality polynomial is of the form: [ α_{n/2 + 1}, α_{n/2 + 2}, ..., α_n ]
        //
        // For example, for n = 6, the second eq is [ α_4, α_5, α_6 ]
        // Second eq poly is of the form (i.e., we do not store intermediate evaluations):
        //
        // (1 - α_4)(1 - α_5)(1 - α_6)
        // (1 - α_4)(1 - α_5)( α_6)
        // (1 - α_4)(α_5)(1 - α_6)
        // (1 - α_4)(α_5)(α_6)
        // (α_4)(1 - α_5)(1 - α_6)
        // (α_4)(1 - α_5)(α_6)
        // (α_4)(α_5)(1 - α_6)
        // (α_4)(α_5)(α_6)
        //
        // Note that second eq polynomial is constant in first n/2 rounds.
        //
        let eq_2_basis = eq_2_basis.to_vec();
        println!("eq2 basis: {:#?}", eq_2_basis);
        let eq_2_poly = EqPoly::new(eq_2_basis);
        let eq_2_evals = eq_2_poly.compute_evals();

        println!("eq2 evals: {:#?}", eq_2_evals);

        // Assert that the number of evaluations is correct
        assert_eq!(eq_1_left_staged_evals.len(), eq_1_right_staged_evals.len());
        for i in 0..eq_1_right_staged_evals.len() {
            let len_eq_1_left = eq_1_left_staged_evals[i].len();
            let len_eq_1_right = eq_1_right_staged_evals[i].len();
            assert_eq!(len_eq_1_left * len_eq_1_right, eq_2_evals.len());
            assert_eq!(log2(eq_2_evals.len()) as usize, prover_state.num_vars / 2);
        }

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

        for i in 0..r_degree {
            matrix_polynomials.push(MatrixPolynomial::from_linear_lagrange_list(
                &prover_state.state_polynomials[i],
            ));
        }

        println!("round_t = {}", round_small_val);

        // For this, we first fold the witness matrices to get their dimension: 2^t  x  (N / 2^t)
        for i in 2..=round_small_val {
            println!("i = {}", i);
            println!("matrix polynomials: {:#?}", matrix_polynomials);
            for matrix in &mut matrix_polynomials {
                matrix.heighten();
            }
        }

        println!("matrix polynomials: {:#?}", matrix_polynomials);

        // Pre-compute bb multiplications upto round t
        let precomputed_for_round_small_val =
            MatrixPolynomial::tensor_column_products(&matrix_polynomials, mult_bb);

        println!("precomputed for round t:");
        print_collection(&precomputed_for_round_small_val, |col| col.get_val());

        // Pre-compute the witness terms multiplied by the eq1 and eq2 evaluations
        // TODO: we might be allocating unncecessary memory for the last round (i.e., round t)
        let num_round_poly_evals = r_degree + 1;
        let mut pre_computed_array_with_eq: Vec<Vec<Vec<EF>>> = vec![vec![]; num_round_poly_evals];
        let mut pre_computed_eq_1_left: Vec<Vec<Vec<EF>>> = vec![vec![]; num_round_poly_evals];
        for round_num in 1..=round_small_val {
            // *******************************************************************************
            // ----------------------------------------------
            // Extract the witness terms for this round
            // ----------------------------------------------
            let extracted_witness_for_round = MatrixPolynomial::extract_subtensors_from_tensors(
                &precomputed_for_round_small_val,
                r_degree,                           // degree d
                1 << (round_small_val - round_num), // 2^{t - i}
            );

            println!("\n--------\nround_num = {}", round_num);
            println!("extracted witness for round:");
            print_collection(&extracted_witness_for_round, |col| col.get_val());

            // Check if the number of extracted witness terms is correct
            assert_eq!(
                extracted_witness_for_round.len(),
                1 << (prover_state.num_vars - round_num) // 2^{n - i}
            );

            // Check if each vector in extracted witness terms has the correct length
            for witness in &extracted_witness_for_round {
                assert_eq!(witness.len(), 1 << (round_num * r_degree)); // 2^{r * d}
            }
            // *******************************************************************************

            // Now lets compute the precomputed array for this round for each k
            // TODO: define evaluation point vector: [0, 2, 3, ...] because you can avoid computing for k = 1
            for k in 0..(r_degree + 1) as u64 {
                // Compute scalar vector:
                // For d = 1: [(1 - k), k]
                // For d = 2: [(1 - k)²,  (1 - k)k,  k(1 - k), k²]
                // For d = 3: [(1 - k)³,  (1 - k)²k,  (1 - k)k(1 - k),  (1 - k)k²,  k(1 - k)², k(1 - k)k, k²(1 - k), k³]
                let scalar_tuple_matrix = MatrixPolynomial::from_evaluations_vec(&vec![
                    BF::one() - BF::new(k as u128, Some(2)),
                    BF::new(k as u128, Some(2)),
                ]);
                let mut k_matrix = scalar_tuple_matrix.clone();
                for _ in 1..r_degree {
                    k_matrix = k_matrix.tensor_hadamard_product(&scalar_tuple_matrix, &mult_bb);
                }
                let two_pow_degree = (1 as usize) << r_degree;
                assert_eq!(k_matrix.no_of_columns, 1);
                assert_eq!(k_matrix.no_of_rows, two_pow_degree);

                println!("\n----\nk = {}", k);

                println!("k_matrix:");
                print_collection(&k_matrix.evaluation_rows, |c| c.get_val());

                // Define a temporary data structure to store the compressed witness terms
                // This would be a matrix of size: W x 2^{(r - 1) * d}
                // s.t. the given witness matrix is of size: W x 2^{r * d}
                let mut compressed_witness_for_k: Vec<Vec<BF>> =
                    Vec::with_capacity(extracted_witness_for_round.len());

                for row in extracted_witness_for_round.iter() {
                    let temp_num_cols = 1 << ((round_num - 1) * r_degree);
                    let mut temp_row = Vec::with_capacity(temp_num_cols);
                    for idx in 0..temp_num_cols {
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
                println!("compressed witness for k:");
                print_collection(&compressed_witness_for_k, |c| c.get_val());

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
                    1 << ((round_num - 1) * r_degree)
                );

                pre_computed_array_with_eq[k as usize].push(compressed_witness_eq_1_eq_2);

                // Lets pre-compute the evaluations of eq1 left polynomial for this round
                let eq_1_left_for_round = &eq_1_left_staged_evals[round_num - 1];
                let one_minus_k_val = BF::one() - BF::new(k as u128, Some(2));
                let k_val = BF::new(k as u128, Some(2));
                let compressed_eq_1_left_for_round: Vec<EF> = eq_1_left_for_round
                    .chunks(2)
                    .map(|w| mult_be(&one_minus_k_val, &w[0]) + mult_be(&k_val, &w[1]))
                    .collect();

                println!("comp eq1 = {}", compressed_eq_1_left_for_round.len());

                // Check if the resulting compressed eq1 left vector has the correct length
                assert_eq!(compressed_eq_1_left_for_round.len(), 1 << (round_num - 1));

                pre_computed_eq_1_left[k as usize].push(compressed_eq_1_left_for_round);
            }
        }

        // This matrix will store challenges in the form:
        // [ (1-α_1)(1-α_2)...(1-α_m) ]
        // [ (1-α_1)(1-α_2)...(α_m) ]
        // [ .. ]
        // [ .. ]
        // [ (α_1)(α_2)...(α_m) ]
        let mut challenge_matrix_polynomial: MatrixPolynomial<EF> = MatrixPolynomial::one();

        for round_num in 1..=round_small_val {
            // Compute challenge terms for 2^{(r - 1) * d} terms
            let mut gamma_matrix = challenge_matrix_polynomial.clone();
            for _ in 1..r_degree {
                gamma_matrix =
                    gamma_matrix.tensor_hadamard_product(&challenge_matrix_polynomial, &mult_ee);
            }

            // Compute the challenge term mixed with the left eq1 polynomial

            // Compute round polynomial at k
            for k in 0..num_round_poly_evals {
                // Fetch the eq1 left evaluations for this round, and compute its inner product with the challenge matrix
                let eq_1_left_evals = &pre_computed_eq_1_left[k][round_num - 1];
                assert_eq!(
                    eq_1_left_evals.len(),
                    challenge_matrix_polynomial.no_of_rows
                );
                let eq_1_left_and_challenge_value = challenge_matrix_polynomial
                    .evaluation_rows
                    .iter()
                    .zip(eq_1_left_evals.iter())
                    .map(|(challenge_multiplicand, eq_val)| {
                        mult_ee(eq_val, &challenge_multiplicand[0])
                    })
                    .fold(EF::zero(), |acc, val| acc + val);

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
                // eq1 left value and the precomputed array value
                round_polynomials[round_num - 1][k as usize] = mult_ee(
                    &precomputed_array_and_challege_value,
                    &eq_1_left_and_challenge_value,
                );

                // Ensure Γ has only 1 column and Γ.
                assert_eq!(gamma_matrix.no_of_columns, 1);
            }

            // print round number and current round polynomial
            println!("Round number = {}", round_num);
            println!("round polynomial: {:#?}", round_polynomials[round_num - 1]);

            // append the round polynomial (i.e. prover message) to the transcript
            <Transcript as TFTranscriptProtocol<EF, BF>>::append_scalars(
                transcript,
                b"r_poly",
                &round_polynomials[round_num - 1],
            );

            // generate challenge α_i = H( transcript );
            let mut alpha = <Transcript as TFTranscriptProtocol<EF, BF>>::challenge_scalar(
                transcript,
                b"challenge_nextround",
            );

            alpha = EF::new(13, Some(4)) * EF::new(round_num as u128, Some(4));

            // Update challenge matrix with new challenge
            let challenge_tuple_matrix =
                MatrixPolynomial::from_evaluations_vec(&vec![EF::one() - alpha, alpha]);
            challenge_matrix_polynomial = challenge_matrix_polynomial
                .tensor_hadamard_product(&challenge_tuple_matrix, &mult_ee);
        }

        // TODO: see next steps in the paper

        // We will now switch back to Algorithm 1: so we compute the arrays A_i such that
        // A_i = [ p_i(α_1, α_2, ..., α_j, x) for all x ∈ {0, 1}^{l - j} ]
        // for each witness polynomial p_i.
        let mut ef_state_polynomials: Vec<LinearLagrangeList<EF>> = matrix_polynomials
            .iter()
            .map(|matrix_poly| matrix_poly.scale_and_squash(&challenge_matrix_polynomial, &mult_be))
            .collect();

        // Process remaining rounds by switching to Algorithm 1
        for round_num in (round_small_val + 1)..=prover_state.num_vars {
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
