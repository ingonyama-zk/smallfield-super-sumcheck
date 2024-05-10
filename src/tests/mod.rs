mod baby_bear;
mod bls12_381;
pub mod fields;
mod goldilocks;
mod simple_tests;

pub mod test_helpers {
    use ark_ff::{Field, PrimeField};
    use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
    use ark_std::test_rng;
    use nalgebra::DMatrix;

    use crate::{
        data_structures::LinearLagrangeList,
        prover::{AlgorithmType, ProverState},
        IPForMLSumcheck,
    };

    /// Helper function to create sumcheck test multivariate polynomials of given degree.
    pub fn create_sumcheck_test_data<EF: Field, BF: PrimeField>(
        nv: usize,
        degree: usize,
        algorithm: AlgorithmType,
    ) -> (ProverState<EF, BF>, BF) {
        // Declare a randomness generation engine
        let mut rng = test_rng();

        let num_evaluations: usize = (1 as usize) << nv;
        let mut polynomials: Vec<LinearLagrangeList<BF>> = Vec::with_capacity(degree);
        let mut polynomial_hadamard: Vec<BF> = vec![BF::ONE; num_evaluations];
        for _ in 0..degree {
            let poly_i: DenseMultilinearExtension<BF> =
                DenseMultilinearExtension::rand(nv, &mut rng);
            polynomials.push(LinearLagrangeList::<BF>::from(&poly_i));
            polynomial_hadamard
                .iter_mut()
                .zip(poly_i.iter())
                .for_each(|(p_acc, p_curr)| *p_acc *= *p_curr);
        }
        let claimed_sum: BF = polynomial_hadamard
            .iter()
            .fold(BF::zero(), |acc, ph| acc + ph);

        let prover_state: ProverState<EF, BF> =
            IPForMLSumcheck::<EF, BF>::prover_init(&polynomials, degree, algorithm);

        (prover_state, claimed_sum)
    }

    /// Computes n!
    pub fn factorial(n: u64) -> u64 {
        (1..=n).product()
    }

    /// Computes ⁿCᵣ := n! / (r! * (n - r)!)
    pub fn count_combinations(n: u64, r: u64) -> u64 {
        factorial(n) / (factorial(r) * factorial(n - r))
    }

    /// Computes [ⁿC₀, ⁿC₁, ..., ⁿCₙ]
    pub fn get_binomial_combinations(n: u64) -> Vec<u64> {
        (0..n + 1).map(|k| count_combinations(n, k)).collect()
    }

    /// Generate binomial expansion matrix
    pub fn generate_binomial_expansion_matrix(degree: usize) -> DMatrix<i64> {
        let num_evals = degree + 1;
        let nrows = num_evals;
        let ncols = num_evals;

        let mut data: Vec<i64> = Vec::with_capacity(nrows * ncols);
        for i in (0..=degree).rev() {
            let combinations = get_binomial_combinations(i as u64);
            let signed_combinations: Vec<i64> = combinations
                .iter()
                .enumerate()
                .map(|(index, &value)| {
                    if index % 2 == 0 {
                        value as i64
                    } else {
                        -(value as i64)
                    }
                })
                .collect();

            let mut modified_signed_combinations: Vec<i64> = Vec::with_capacity(num_evals);
            modified_signed_combinations.resize(num_evals - signed_combinations.len(), 0);
            modified_signed_combinations.extend(signed_combinations.clone());

            data.extend(modified_signed_combinations);
        }

        let dmatrix = DMatrix::from_row_slice(nrows, ncols, &data);
        dmatrix.transpose()
    }

    // Helper function to generate evaluation matrix for Toom-Cook algorithm.
    pub fn generate_evaluation_matrix(degree: usize) -> Vec<Vec<i64>> {
        let num_evals = degree + 1;
        let mut eval_matrix: Vec<Vec<i64>> = Vec::with_capacity(num_evals);

        // Push first two rows for x = 0 and x = ∞
        // x = 0 => [1 0 0 ... 0]
        // x = ∞ => [0 0 0 ... 1]
        eval_matrix.push(vec![0; num_evals]);
        eval_matrix[0][0] = 1;
        eval_matrix.push(vec![0; num_evals]);
        eval_matrix[1][num_evals - 1] = 1;

        for i in 1..=(num_evals / 2) {
            // Push a row for x = i
            // x = i => [1 i i² i³ ... iᵈ⁺¹]
            if eval_matrix.len() < num_evals {
                let eval_row: Vec<i64> = (0..num_evals).map(|j| i.pow(j as u32) as i64).collect();
                eval_matrix.push(eval_row);
            }
            // Push a row for x = -i if we still need more rows
            // x = i => [1 i i² i³ ... iᵈ⁺¹]
            if eval_matrix.len() < num_evals {
                let eval_row: Vec<i64> = (0..num_evals)
                    .map(|j| (-(i as i64)).pow(j as u32) as i64)
                    .collect();
                eval_matrix.push(eval_row);
            }
        }
        eval_matrix
    }

    /// Helper function to compute adjugate of an integer matrix.
    pub fn adjugate(matrix: Vec<Vec<i64>>) -> (DMatrix<i64>, i64) {
        let nrows = matrix.len();
        let ncols = matrix[0].len();

        let mut data = Vec::with_capacity(nrows * ncols);
        for row in matrix {
            data.extend(row);
        }

        let dmatrix = DMatrix::from_row_slice(nrows, ncols, &data);
        let determinant = dmatrix.map(|x| x as f64).determinant().abs() as i64;
        let mut cofactor_matrix = DMatrix::zeros(nrows, ncols);

        for i in 0..nrows {
            for j in 0..ncols {
                let submatrix = dmatrix.clone().remove_row(i).remove_column(j);
                let submatrix_f64 = submatrix.map(|x| x as f64);
                let determinant = submatrix_f64.determinant().round() as i64;
                cofactor_matrix[(i, j)] = if (i + j) % 2 == 0 {
                    determinant
                } else {
                    -determinant
                };
            }
        }

        let adjugate_matrix = cofactor_matrix.transpose();
        (adjugate_matrix, determinant)
    }

    // Helper function to convert DMatrix to vector of vectors.
    pub fn matrix_to_vec_of_vec(matrix: &DMatrix<i64>) -> Vec<Vec<i64>> {
        let nrows = matrix.nrows();
        let ncols = matrix.ncols();
        let mut result = Vec::with_capacity(nrows);
        for i in 0..nrows {
            let mut row = Vec::with_capacity(ncols);
            for j in 0..ncols {
                row.push(matrix[(i, j)]);
            }
            result.push(row);
        }
        result
    }

    // Helper function to convert vector of vectors to DMatrix.
    pub fn vec_of_vec_to_matrix(matrix: &Vec<Vec<i64>>) -> DMatrix<i64> {
        let nrows = matrix.len();
        let ncols = matrix[0].len();

        let mut data = Vec::with_capacity(nrows * ncols);
        for row in matrix {
            data.extend(row);
        }
        let dmatrix = DMatrix::from_row_slice(nrows, ncols, &data);
        dmatrix
    }

    /// Helper function to compute the interpolation matrix (leaving determinant aside).
    /// Also outputs the determinant (appropriately scaled) of the interpolation matrix.
    /// WARNING: Works only for degree ≤ 8. For degree > 9, the computation of determinants
    /// for large matrices starts getting incorrect (due to overflows in f64). This is a
    /// problem with the underlying library nalgebra (trait: DMatrix).
    pub fn generate_interpolation_matrix_transpose(degree: usize) -> (Vec<Vec<i64>>, i64) {
        assert!(degree < 9);
        let eval_matrix = generate_evaluation_matrix(degree);
        let (adjugate_matrix, determinant) = adjugate(eval_matrix);
        let mut divisor = second_highest_magnitude(&adjugate_matrix).abs();
        if (degree + 1) % 2 == 1 {
            divisor = -divisor;
        }
        let mut scaled_adjugate_matrix =
            adjugate_matrix.map(|x| ((x / divisor) as f64).round() as i64);
        scaled_adjugate_matrix.transpose_mut();
        let scaled_determinant = (((determinant / divisor) as f64).round()).abs() as i64;
        (
            matrix_to_vec_of_vec(&scaled_adjugate_matrix),
            scaled_determinant,
        )
    }

    pub fn generate_binomial_interpolation_mult_matrix_transpose(
        degree: usize,
    ) -> (Vec<Vec<i64>>, i64) {
        let (inter_matrix, scaled_det) = generate_interpolation_matrix_transpose(degree);
        let inter_dmatrix = vec_of_vec_to_matrix(&inter_matrix).transpose();
        let binomial_dmatrix = generate_binomial_expansion_matrix(degree);
        let mult_dmatrix = (binomial_dmatrix * inter_dmatrix).transpose();

        (matrix_to_vec_of_vec(&mult_dmatrix), scaled_det)
    }

    // Finds the value with second highest magnitude in a matrix.
    pub fn second_highest_magnitude(matrix: &DMatrix<i64>) -> i64 {
        let mut values: Vec<i64> = matrix.iter().cloned().collect();
        values.sort_unstable_by_key(|&value| value.abs());
        values.dedup();
        values[1]
    }

    /// Converts a matrix into maps.
    pub fn get_maps_from_matrix<FF: Field>(
        matrix: &Vec<Vec<i64>>,
        divisor: i64,
    ) -> Vec<Box<dyn Fn(&Vec<FF>) -> FF>> {
        assert!(divisor > 0);
        let divisor_ff = FF::from(divisor.abs() as u32);
        let mut divisor_inv_ff = FF::ONE;
        if divisor != 1 {
            divisor_inv_ff = divisor_ff.inverse().unwrap();
        }
        matrix
            .iter()
            .map(|irow| {
                let irow_cloned = irow.clone();
                let imap: Box<dyn Fn(&Vec<FF>) -> FF> = Box::new(move |v: &Vec<FF>| -> FF {
                    v.iter()
                        .zip(irow_cloned.iter())
                        .fold(FF::zero(), |acc, (value, scalar)| {
                            let scalar_ff = FF::from((*scalar).abs() as u32);
                            let mut scalar_by_divisor = scalar_ff;
                            if divisor != 1 {
                                scalar_by_divisor *= divisor_inv_ff;
                            }
                            if *scalar < 0 {
                                acc - scalar_by_divisor * value
                            } else {
                                acc + scalar_by_divisor * value
                            }
                        })
                });
                imap
            })
            .collect::<Vec<Box<dyn Fn(&Vec<FF>) -> FF>>>()
    }
}

#[cfg(test)]
mod test {
    use nalgebra::DMatrix;
    use rand::Rng;

    use crate::tests::test_helpers::{
        generate_binomial_expansion_matrix, generate_evaluation_matrix,
        generate_interpolation_matrix_transpose, vec_of_vec_to_matrix,
    };

    #[test]
    fn test_interpolation_matrix() {
        for j in 1..9 {
            let eval_matrix = generate_evaluation_matrix(j);
            let (imatrix, scaled_det) = generate_interpolation_matrix_transpose(j);

            let eval_dmatrix = vec_of_vec_to_matrix(&eval_matrix);
            let i_dmatrix = vec_of_vec_to_matrix(&imatrix);
            let multplication = (eval_dmatrix * i_dmatrix.transpose()) / scaled_det;
            assert_eq!(multplication, DMatrix::identity(j + 1, j + 1));
        }
    }

    #[test]
    fn test_binomial_matrix() {
        for j in (1 as u32)..7 {
            let binomial_dmatrix = generate_binomial_expansion_matrix(j as usize);
            let mut rng = rand::thread_rng();
            let r_value: u8 = rng.gen();
            let mut r_powers = vec![1 as i64];
            for k in 1..=j {
                r_powers.push(r_powers[k as usize - 1] * (r_value as i64));
            }
            let r_powers_dmatrix = DMatrix::from_row_slice(1, (j + 1) as usize, &r_powers);
            let r_evals = r_powers_dmatrix * binomial_dmatrix;

            for l in 0..=(j as u32) {
                let r_bar = 1 as i64 - r_value as i64;
                let r_bar_pow = r_bar.pow((j - l) as u32);
                let r_pow = (r_value as i64).pow(l);
                let expected: i64 = r_bar_pow * r_pow;
                assert_eq!(r_evals[l as usize], expected);
            }
        }
    }
}
