use merlin::Transcript;

use crate::btf_transcript::TFTranscriptProtocol;
use crate::data_structures::{LinearLagrangeList, MatrixPolynomial};
use crate::eq_poly::EqPoly;
use crate::prover::ProverState;
use crate::tower_fields::TowerField;
use crate::IPForMLSumcheck;

impl<EF: TowerField, BF: TowerField> IPForMLSumcheck<EF, BF> {
    /// Algorithm 2
    pub fn prove_with_eq_witness_challenge_sep_agorithm<BC, BE, AEE, EE>(
        prover_state: &mut ProverState<EF, BF>,
        bf_combine_function: &BC,
        transcript: &mut Transcript,
        round_polynomials: &mut Vec<Vec<EF>>,
        mult_be: &BE,
        add_ee: &AEE,
        mult_ee: &EE,
    ) where
        BC: Fn(&Vec<BF>) -> EF + Sync,
        BE: Fn(&BF, &EF) -> EF + Sync,
        AEE: Fn(&EF, &EF) -> EF + Sync,
        EE: Fn(&EF, &EF) -> EF + Sync,
    {
        // Compute the equality polynomial from its basis.
        assert!(
            prover_state.eq_challenges.is_some(),
            "Equality poly challenges cannot be `None`."
        );
        let eq_poly = EqPoly::new(prover_state.eq_challenges.clone().unwrap().to_vec());
        let eq_evals = eq_poly.compute_evals(false);
        let eq_state_poly = LinearLagrangeList::from_vector(&eq_evals);

        // The degree of the round polynomial is the number of polynomials being multiplied since
        // we are only dealing with product-sumcheck. In other cases, number of polynomials may not equal the degree.
        let r_degree = prover_state.state_polynomials.len();
        let num_witness_poly = prover_state.state_polynomials.len();

        // Phase 1: Process round 1 separately as we need to only perform bb multiplications.
        // Note that we still need to multiply the equality polynomial with the base field polynomials.
        let alpha = Self::compute_round_polynomial_with_eq::<BC, BF>(
            1,
            &prover_state.state_polynomials,
            &eq_state_poly,
            round_polynomials,
            r_degree,
            &bf_combine_function,
            transcript,
        );

        // Create and fill matrix polynomials.
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
        let mut matrix_polynomials: Vec<MatrixPolynomial<BF>> =
            Vec::with_capacity(num_witness_poly);

        for i in 0..num_witness_poly {
            matrix_polynomials.push(MatrixPolynomial::from_linear_lagrange_list(
                &prover_state.state_polynomials[i],
            ));
        }

        let mut eq_matrix_polynomial = MatrixPolynomial::from_linear_lagrange_list(&eq_state_poly);

        // This matrix will store challenges in the form:
        // [ (1-α_1)(1-α_2)...(1-α_m) ]
        // [ (1-α_1)(1-α_2)...(α_m) ]
        // [ .. ]
        // [ .. ]
        // [ (α_1)(α_2)...(α_m) ]
        //
        // We initialise this with the first challenge as:
        // [ (1-α_1) ]
        // [ (α_1) ]
        //
        let mut challenge_matrix_polynomial =
            MatrixPolynomial::from_evaluations_vec(&vec![EF::one() - alpha, alpha]);

        // Iterate for rounds 2, 3, ..., log(n).
        // For each round i s.t. i ≥ 2, we compute the evaluation of the round polynomial as:
        //
        // r_i(k) = ∑_{x} p(r_1, r_2, ..., r_{i-1},  k,  x) *
        //                q(r_1, r_2, ..., r_{i-1},  k,  x) *
        //                h(r_1, r_2, ..., r_{i-1},  k,  x) * ...
        //
        // for each k = 0, 1, 2, ...
        // Thus, we iterate over each polynomial (p, q, h, ...) to compute:
        //
        // poly(r_1, r_2, ..., r_{i-1},  k,  x) := ∑_{y} eq(y, r_1, r_2, ..., r_{i-1}) * poly(y, k, x)
        //
        // To compute this, we compute the challenge term: eq(y, r_1, r_2, ..., r_{i-1}) in the challenge matrix polynomial.
        // Further, we multiply that with poly(y, k, x) and sum it over y to get polynomial evaluation at
        // (r_1, r_2, ..., r_{i-1},  k,  x).
        //
        for round_number in 2..=prover_state.num_vars {
            for k in 0..(r_degree + 1) {
                let poly_hadamard_product_len = matrix_polynomials[0].no_of_columns / 2;
                let mut poly_hadamard_product: Vec<EF> = vec![EF::one(); poly_hadamard_product_len];

                for matrix_poly in &matrix_polynomials {
                    let width = matrix_poly.no_of_columns;
                    let height = matrix_poly.no_of_rows;

                    // Assert that the number of rows in the challenge and witness matrix are equal.
                    assert_eq!(challenge_matrix_polynomial.no_of_rows, height);

                    // This will store poly(r_1, r_2, ..., r_{i-1},  k,  x) for x ∈ {0, 1}^{l - i}.
                    let mut poly_evaluation_at_k: Vec<EF> = vec![EF::zero(); width / 2];

                    for row_idx in 0..height {
                        let (even, odd) = matrix_poly.evaluation_rows[row_idx].split_at(width / 2);

                        let row_evaluation_at_k: Vec<BF> = even
                            .iter()
                            .zip(odd.iter())
                            .map(|(&e, &o)| {
                                (BF::one() - BF::new(k as u128, None)) * e
                                    + BF::new(k as u128, None) * o
                            })
                            .collect();

                        // ATTENTION: multiplication of base field element with extension field element (be)
                        let row_evaluation_at_k_mult_by_challenge: Vec<EF> = row_evaluation_at_k
                            .iter()
                            .map(|ek| {
                                mult_be(
                                    &ek,
                                    &challenge_matrix_polynomial.evaluation_rows[row_idx][0],
                                )
                            })
                            .collect();

                        // ATTENTION: addition of extension field elements
                        poly_evaluation_at_k
                            .iter_mut()
                            .zip(row_evaluation_at_k_mult_by_challenge.iter())
                            .for_each(|(p_acc, p_curr)| *p_acc = add_ee(p_acc, &p_curr));
                    }

                    // ATTENTION: multiplication of extension field elements (ee)
                    // TODO: We can use the combine function to generalise this.
                    poly_hadamard_product
                        .iter_mut()
                        .zip(poly_evaluation_at_k.iter())
                        .for_each(|(m_acc, m_curr)| *m_acc = mult_ee(m_acc, &m_curr));
                }

                // Now we need to multiply the equality polynomial with the base field polynomials.
                let mut eq_poly_evaluation_at_k: Vec<EF> =
                    vec![EF::zero(); eq_matrix_polynomial.evaluation_rows[0].len() / 2];
                for (row_idx, eq_row) in eq_matrix_polynomial.evaluation_rows.iter().enumerate() {
                    let width = eq_row.len();
                    let (even, odd) = eq_row.split_at(width / 2);

                    let eq_row_evaluation_at_k: Vec<EF> = even
                        .iter()
                        .zip(odd.iter())
                        .map(|(&e, &o)| {
                            (EF::one() - EF::new(k as u128, None)) * e
                                + EF::new(k as u128, None) * o
                        })
                        .collect();

                    // ATTENTION: ee multiplication
                    let eq_row_evaluation_at_k_mult_by_challenge: Vec<EF> = eq_row_evaluation_at_k
                        .iter()
                        .map(|ek| {
                            mult_ee(
                                &ek,
                                &challenge_matrix_polynomial.evaluation_rows[row_idx][0],
                            )
                        })
                        .collect();

                    // ATTENTION: addition of extension field elements
                    eq_poly_evaluation_at_k
                        .iter_mut()
                        .zip(eq_row_evaluation_at_k_mult_by_challenge.iter())
                        .for_each(|(m_acc, m_curr)| *m_acc = add_ee(m_acc, &m_curr));
                }

                // ATTENTION: multiplication of extension field elements (ee)
                // TODO: We can use the combine function to generalise this.
                poly_hadamard_product
                    .iter_mut()
                    .zip(eq_poly_evaluation_at_k.iter())
                    .for_each(|(m_acc, m_curr)| *m_acc = mult_ee(m_acc, &m_curr));

                // ATTENTION: addition of extension field elements
                round_polynomials[round_number - 1][k as usize] = poly_hadamard_product
                    .iter()
                    .fold(EF::zero(), |acc, val| add_ee(&acc, val));
            }

            // append the round polynomial (i.e. prover message) to the transcript
            <Transcript as TFTranscriptProtocol<EF, BF>>::append_scalars(
                transcript,
                b"r_poly",
                &round_polynomials[round_number - 1],
            );

            // generate challenge α_i = H( transcript );
            let alpha = <Transcript as TFTranscriptProtocol<EF, BF>>::challenge_scalar(
                transcript,
                b"challenge_nextround",
            );

            // Assert that challenge matrix has only one column.
            assert_eq!(challenge_matrix_polynomial.no_of_columns, 1);

            // Update challenge matrix with new challenge
            // ATTENTION: multiplication of extension field elements (ee)
            let challenge_tuple_matrix =
                MatrixPolynomial::from_evaluations_vec(&vec![EF::one() - alpha, alpha]);
            challenge_matrix_polynomial = challenge_matrix_polynomial
                .tensor_hadamard_product(&challenge_tuple_matrix, &mult_ee);

            // Heighten the witness polynomial matrices
            for j in 0..num_witness_poly {
                matrix_polynomials[j].heighten();
            }
            eq_matrix_polynomial.heighten();
        }
    }
}
