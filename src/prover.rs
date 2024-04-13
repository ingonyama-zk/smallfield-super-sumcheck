use crate::{
    data_structures::{bit_extend, bit_extend_and_insert, LinearLagrangeList, MatrixPolynomial},
    extension_transcript::ExtensionTranscriptProtocol,
    IPForMLSumcheck,
};
use ark_ff::{Field, PrimeField};
use ark_poly::DenseMultilinearExtension;
use ark_std::{log2, vec::Vec};
use flamer::flame;
use merlin::Transcript;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

// A sumcheck proof contains all round polynomials
#[derive(PartialEq, Debug)]
pub struct SumcheckProof<EF: Field> {
    pub(crate) num_vars: usize,
    pub(crate) degree: usize,
    pub(crate) round_polynomials: Vec<Vec<EF>>,
}

#[derive(PartialEq, Clone, Debug)]
pub enum AlgorithmType {
    Naive,
    WitnessChallengeSeparation,
    Precomputation,
    ToomCook,
}

/// Prover State
/// EF stands for extension field and BF stands for base field
/// bb = base-field element multiplied to a base-field element
/// be = base-field element multiplied to an extension-field element
/// ee = extension-field element multiplied to an extension-field element
pub struct ProverState<EF: Field, BF: PrimeField> {
    /// sampled randomness (for each round) given by the verifier
    pub randomness: Vec<EF>,
    /// Stores a list of multilinear extensions
    pub state_polynomials: Vec<LinearLagrangeList<BF>>,
    /// Number of variables
    pub num_vars: usize,
    /// Max number of multiplicands in a product
    pub max_multiplicands: usize,
    /// The current round number
    pub round: usize,
    /// Algorithm type for small field sumcheck
    pub algo: AlgorithmType,
}

impl<EF: Field, BF: PrimeField> IPForMLSumcheck<EF, BF> {
    /// Initialise prover state from a given set of polynomials (in their evaluation form).
    /// The degree of the sumcheck round polynomial also needs to be input.
    pub fn prover_init(
        polynomials: &Vec<LinearLagrangeList<BF>>,
        sumcheck_poly_degree: usize,
        algorithm: AlgorithmType,
    ) -> ProverState<EF, BF> {
        // sanity check 1: no polynomials case must not be allowed.
        if polynomials.len() == 0 {
            panic!("Cannot prove empty input polynomials.")
        }

        // sanity check 2: all polynomial evaluations must be of the same size.
        let problem_size = polynomials[0].size;
        let _ = polynomials.iter().enumerate().map(|(i, poly)| {
            if poly.size != problem_size {
                panic!("Polynomial size mismatch at {}", i)
            }
        });

        // sanity check 3: size must be a power of two.
        if !problem_size.is_power_of_two() {
            panic!("Number of polynomial evaluations must be a power of two.")
        }

        let num_variables: usize = log2(2 * problem_size).try_into().unwrap();
        ProverState {
            randomness: Vec::with_capacity(num_variables),
            state_polynomials: polynomials.to_vec(),
            num_vars: num_variables,
            max_multiplicands: sumcheck_poly_degree,
            round: 0,
            algo: algorithm,
        }
    }

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
    }

    pub fn prove_with_witness_challenge_sep_agorithm<BC, BE, AEE, EE>(
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
            Vec::with_capacity(prover_state.max_multiplicands);

        for i in 0..prover_state.max_multiplicands {
            matrix_polynomials.push(MatrixPolynomial::from_linear_lagrange_list(
                &prover_state.state_polynomials[i],
            ));
        }

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
        let challenge_tuple =
            DenseMultilinearExtension::from_evaluations_vec(1, vec![EF::ONE - alpha, alpha]);
        let mut challenge_matrix_polynomial = MatrixPolynomial::from_dense_mle(&challenge_tuple);

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
                let mut poly_hadamard_product: Vec<EF> = vec![EF::ONE; poly_hadamard_product_len];

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
                                (BF::ONE - BF::from(k as u32)) * e + BF::from(k as u32) * o
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

                // ATTENTION: addition of extension field elements
                round_polynomials[round_number - 1][k as usize] = poly_hadamard_product
                    .iter()
                    .fold(EF::zero(), |acc, val| add_ee(&acc, val));
            }

            // append the round polynomial (i.e. prover message) to the transcript
            <Transcript as ExtensionTranscriptProtocol<EF, BF>>::append_scalars(
                transcript,
                b"r_poly",
                &round_polynomials[round_number - 1],
            );

            // generate challenge α_i = H( transcript );
            let alpha = <Transcript as ExtensionTranscriptProtocol<EF, BF>>::challenge_scalar(
                transcript,
                b"challenge_nextround",
            );

            // Assert that challenge matrix has only one column.
            assert_eq!(challenge_matrix_polynomial.no_of_columns, 1);

            // Update challenge matrix with new challenge
            // ATTENTION: multiplication of extension field elements (ee)
            let challenge_tuple =
                DenseMultilinearExtension::from_evaluations_vec(1, vec![EF::ONE - alpha, alpha]);
            let challenge_tuple_matrix = MatrixPolynomial::from_dense_mle(&challenge_tuple);
            challenge_matrix_polynomial = challenge_matrix_polynomial
                .tensor_hadamard_product(&challenge_tuple_matrix, &mult_ee);

            // Heighten the witness polynomial matrices
            for j in 0..prover_state.max_multiplicands {
                matrix_polynomials[j].heighten();
            }
        }
    }

    /// Algorithm 3
    #[flame]
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

        for i in 0..r_degree {
            matrix_polynomials.push(MatrixPolynomial::from_linear_lagrange_list(
                &prover_state.state_polynomials[i],
            ));
        }

        // Pre-compute bb multiplications upto round t
        // For this, we first fold the witness matrices to get their dimension: 2^t  x  (N / 2^t)
        for _ in 2..=round_t {
            for matrix in &mut matrix_polynomials {
                matrix.heighten();
            }
        }
        let precomputed_array =
            MatrixPolynomial::tensor_inner_product::<_>(&matrix_polynomials, &mult_bb);
        assert_eq!(
            precomputed_array.len(),
            (1 as usize) << (round_t * r_degree)
        );

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

        for i in 0..r_degree {
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
        flame::start("precompute");
        for _ in 2..=round_t {
            for matrix in &mut matrix_polynomials {
                matrix.heighten();
            }
        }

        let num_evals = r_degree + 1;
        let num_product_terms = num_evals.pow(round_t as u32);
        let mut precomputed_array: Vec<BF> = Vec::with_capacity(num_product_terms);
        for j in 0..num_product_terms {
            let mut product_terms_x: MatrixPolynomial<BF> =
                MatrixPolynomial::ones(1, matrix_polynomials[0].no_of_columns);

            for i in 0..matrix_polynomials.len() {
                let matrix_terms_x =
                    MatrixPolynomial::apply_map(&matrix_polynomials[i], j, mappings);
                product_terms_x = product_terms_x.hadamard_product(&matrix_terms_x, mult_bb);
            }

            assert_eq!(product_terms_x.no_of_rows, 1);
            let sum_over_x = product_terms_x.evaluation_rows[0]
                .iter()
                .fold(BF::zero(), |acc, px| acc + px);
            precomputed_array.push(sum_over_x);
        }

        // Accumulate pre-computed values to be used in rounds.
        let precomputed_arrays_for_rounds = MatrixPolynomial::<BF>::merkle_sums(
            &precomputed_array,
            num_evals,
            projection_mapping_indices,
        );
        flame::end("precompute");

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

        // Process first t rounds
        for round_num in 1..=round_t {
            flame::start(format!("round {}", round_num));
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

                    // Extract (j_p, ...., j_2) to perform be multiplications
                    let mut local_challenge_accumulator = EF::one();
                    for p in 0..(round_num - 1) {
                        let j_p = (j / num_evals.pow(p as u32)) % num_evals;
                        local_challenge_accumulator = mult_ee(
                            &local_challenge_accumulator,
                            &challenge_matrix.evaluation_rows[round_num - 2 - (p as usize)][j_p],
                        );
                    }

                    // Accumulate round polynomial evaluation at k
                    round_polynomials[round_num - 1][k as usize] +=
                        mult_be(&local_witness_accumulator, &local_challenge_accumulator);
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
            flame::start("challenge");
            challenge_matrix.update_with_challenge(alpha, &interpolation_maps_ef, mult_ee);

            // Update challenge matrix with new challenge
            // TODO: See if we can get rid of the second challenge matrix.
            let challenge_tuple =
                DenseMultilinearExtension::from_evaluations_vec(1, vec![EF::ONE - alpha, alpha]);
            let challenge_tuple_matrix = MatrixPolynomial::from_dense_mle(&challenge_tuple);
            challenge_matrix_polynomial = challenge_matrix_polynomial
                .tensor_hadamard_product(&challenge_tuple_matrix, &mult_ee);

            flame::end("challenge");
            flame::end(format!("round {}", round_num));
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

    ///
    /// Creates a sumcheck proof consisting of `n` round polynomials each of degree `d` using Algorithm 1.
    /// We allow for any function `combine_function` on a set of MLE polynomials.
    ///
    /// We implement four algorithms to compute the sumcheck proof according to the algorithms in the small-field
    /// sumcheck paper by Justin Thaler: https://people.cs.georgetown.edu/jthaler/small-sumcheck.pdf
    ///
    pub fn prove<EC, BC, T, BE, AEE, EE, BB>(
        prover_state: &mut ProverState<EF, BF>,
        ef_combine_function: &EC, // TODO: Using two combines is bad, templatize it?
        bf_combine_function: &BC,
        transcript: &mut Transcript,
        to_ef: &T,
        mult_be: &BE,
        add_ee: &AEE,
        mult_ee: &EE,
        mult_bb: &BB,
        round_t: Option<usize>,
        mappings: Option<&Vec<Box<dyn Fn(&BF, &BF) -> BF>>>,
        projection_mapping_indices: Option<&Vec<usize>>,
        interpolation_maps_bf: Option<&Vec<Box<dyn Fn(&Vec<BF>) -> BF>>>,
        interpolation_maps_ef: Option<&Vec<Box<dyn Fn(&Vec<EF>) -> EF>>>,
    ) -> SumcheckProof<EF>
    where
        BC: Fn(&Vec<BF>) -> EF + Sync,
        EC: Fn(&Vec<EF>) -> EF + Sync,
        T: Fn(&BF) -> EF + Sync,
        BE: Fn(&BF, &EF) -> EF + Sync,
        AEE: Fn(&EF, &EF) -> EF + Sync,
        EE: Fn(&EF, &EF) -> EF + Sync,
        BB: Fn(&BF, &BF) -> BF + Sync,
    {
        // Initiate the transcript with the protocol name
        <Transcript as ExtensionTranscriptProtocol<EF, BF>>::sumcheck_proof_domain_sep(
            transcript,
            prover_state.num_vars as u64,
            prover_state.max_multiplicands as u64,
        );

        // Declare r_polys and initialise it with 0s
        let r_degree = prover_state.max_multiplicands;
        let mut r_polys: Vec<Vec<EF>> = (0..prover_state.num_vars)
            .map(|_| vec![EF::zero(); r_degree + 1])
            .collect();

        // Extract threshold round
        let round_threshold = match round_t {
            Some(t_value) => {
                if (prover_state.algo == AlgorithmType::Precomputation)
                    || (prover_state.algo == AlgorithmType::ToomCook)
                {
                    assert!(t_value <= prover_state.num_vars);
                    t_value
                } else {
                    prover_state.num_vars
                }
            }
            None => prover_state.num_vars,
        };

        match prover_state.algo {
            AlgorithmType::Naive => Self::prove_with_naive_algorithm::<EC, BC, T>(
                prover_state,
                &ef_combine_function,
                &bf_combine_function,
                transcript,
                &mut r_polys,
                to_ef,
            ),
            AlgorithmType::WitnessChallengeSeparation => {
                Self::prove_with_witness_challenge_sep_agorithm::<BC, BE, AEE, EE>(
                    prover_state,
                    &bf_combine_function,
                    transcript,
                    &mut r_polys,
                    &mult_be,
                    &add_ee,
                    &mult_ee,
                )
            }
            AlgorithmType::Precomputation => {
                Self::prove_with_precomputation_agorithm::<BE, EE, BB, EC>(
                    prover_state,
                    transcript,
                    &mut r_polys,
                    round_threshold,
                    mult_be,
                    mult_ee,
                    mult_bb,
                    ef_combine_function,
                )
            }
            AlgorithmType::ToomCook => Self::prove_with_toom_cook_agorithm::<BE, EE, BB, EC>(
                prover_state,
                transcript,
                &mut r_polys,
                round_threshold,
                mult_be,
                mult_ee,
                mult_bb,
                mappings.unwrap(),
                projection_mapping_indices.unwrap(),
                interpolation_maps_bf.unwrap(),
                interpolation_maps_ef.unwrap(),
                ef_combine_function,
            ),
        }

        SumcheckProof {
            num_vars: prover_state.num_vars,
            degree: r_degree,
            round_polynomials: r_polys,
        }
    }

    ///
    /// Proves the sumcheck relation for product of MLE polynomials using the witness-challenge
    /// separation algorithm (Algorithm 2 that uses pre-computations).
    ///
    pub fn prove_product<BE, EE, BB>(
        prover_state: &mut ProverState<EF, BF>,
        transcript: &mut Transcript,
        mult_be: &BE,
        mult_ee: &EE,
        mult_bb: &BB,
    ) -> SumcheckProof<EF>
    where
        BE: Fn(&BF, &EF) -> EF + Sync,
        EE: Fn(&EF, &EF) -> EF + Sync,
        BB: Fn(&BF, &BF) -> BF + Sync,
    {
        // Initiate the transcript with the protocol name
        <Transcript as ExtensionTranscriptProtocol<EF, BF>>::sumcheck_proof_domain_sep(
            transcript,
            prover_state.num_vars as u64,
            prover_state.max_multiplicands as u64,
        );

        // Declare r_polys and initialise it with 0s
        let r_degree = prover_state.max_multiplicands;
        let mut r_polys: Vec<Vec<EF>> = (0..prover_state.num_vars)
            .map(|_| vec![EF::zero(); r_degree + 1])
            .collect();

        // Create and fill matrix polynomials.
        let mut matrix_polynomials: Vec<MatrixPolynomial<BF>> =
            Vec::with_capacity(prover_state.max_multiplicands);

        for i in 0..prover_state.max_multiplicands {
            matrix_polynomials.push(MatrixPolynomial::from_linear_lagrange_list(
                &prover_state.state_polynomials[i],
            ));
        }

        // This matrix will store challenges in the form:
        // [ (1-α_1)(1-α_2)...(1-α_m) ]
        // [ (1-α_1)(1-α_2)...(α_m) ]
        // [ .. ]
        // [ .. ]
        // [ (α_1)(α_2)...(α_m) ]
        let mut challenge_matrix_polynomial: MatrixPolynomial<EF> = MatrixPolynomial::one();

        for round_index in 0..prover_state.num_vars {
            // Compute R = [P(1) ⊛ P(2) ⊛ ... ⊛ P(m)]
            let mut round_matrix_polynomial = matrix_polynomials[0].clone();
            for j in 1..prover_state.max_multiplicands {
                round_matrix_polynomial = round_matrix_polynomial
                    .tensor_hadamard_product(&matrix_polynomials[j], &mult_bb);
            }

            // Collapse R
            round_matrix_polynomial.collapse();

            for k in 0..(r_degree + 1) as u64 {
                let scalar_tuple = DenseMultilinearExtension::from_evaluations_vec(
                    1,
                    vec![EF::ONE - EF::from(k), EF::from(k)],
                );
                let scalar_tuple_matrix = MatrixPolynomial::from_dense_mle(&scalar_tuple);

                // Compute Γ = (Γ_i ⊛ Γ_i ⊛ ... ⊛ Γ_i)
                // where Γ_i = (Γ_challenges ⊛ Γ_scalar)
                let gamma_i_matrix = challenge_matrix_polynomial
                    .tensor_hadamard_product(&scalar_tuple_matrix, &mult_ee);
                let mut gamma_matrix = gamma_i_matrix.clone();

                for _ in 1..prover_state.max_multiplicands {
                    gamma_matrix = gamma_matrix.tensor_hadamard_product(&gamma_i_matrix, &mult_ee);
                }

                // Ensure Γ has only 1 column
                assert_eq!(gamma_matrix.no_of_columns, 1);

                // Compute round polynomial evaluation at k
                r_polys[round_index][k as usize] = MatrixPolynomial::dot_product(
                    &round_matrix_polynomial,
                    &gamma_matrix,
                    &mult_be,
                );
            }

            // append the round polynomial (i.e. prover message) to the transcript
            <Transcript as ExtensionTranscriptProtocol<EF, BF>>::append_scalars(
                transcript,
                b"r_poly",
                &r_polys[round_index],
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

            // Heighten the witness polynomial matrices
            for j in 0..prover_state.max_multiplicands {
                matrix_polynomials[j].heighten();
            }
        }

        SumcheckProof {
            num_vars: prover_state.num_vars,
            degree: r_degree,
            round_polynomials: r_polys,
        }
    }
}
