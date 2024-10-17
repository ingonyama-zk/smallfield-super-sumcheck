mod btf_sumcheck;
mod simple_tests;

pub mod test_helpers {
    use nalgebra::DMatrix;

    use crate::{
        data_structures::LinearLagrangeList,
        prover::{AlgorithmType, ProverState},
        tower_fields::TowerField,
        IPForMLSumcheck,
    };

    /// Helper function to create sumcheck test multivariate polynomials of given degree.
    pub fn create_sumcheck_test_data<EF: TowerField, BF: TowerField>(
        nv: usize,
        degree: usize,
        algorithm: AlgorithmType,
    ) -> (ProverState<EF, BF>, BF) {
        let num_evaluations: usize = (1 as usize) << nv;
        let mut polynomials: Vec<LinearLagrangeList<BF>> = Vec::with_capacity(degree);
        let mut polynomial_hadamard: Vec<BF> = vec![BF::one(); num_evaluations];
        for _ in 0..degree {
            let poly_i_vec_bf = (0..num_evaluations).map(|_| BF::rand(Some(5))).collect();
            polynomials.push(LinearLagrangeList::<BF>::from_vector(&poly_i_vec_bf));
            polynomial_hadamard
                .iter_mut()
                .zip(poly_i_vec_bf.iter())
                .for_each(|(p_acc, p_curr)| *p_acc *= *p_curr);
        }
        let claimed_sum: BF = polynomial_hadamard
            .iter()
            .fold(BF::zero(), |acc, ph| acc + ph.clone());

        let prover_state: ProverState<EF, BF> =
            IPForMLSumcheck::<EF, BF>::prover_init(&polynomials, degree, algorithm);

        (prover_state, claimed_sum)
    }

    /// Computes n!
    pub fn factorial(n: u64) -> u64 {
        (1..=n).product()
    }

    /// Computes n! but in binary tower field
    pub fn factorial_btf<BF: TowerField>(n: BF) -> BF {
        if n.is_zero() || n.is_one() {
            return BF::one();
        }

        n * factorial_btf(BF::new(n.get_val() - 1, None))
    }

    /// Computes ⁿCᵣ := n! / (r! * (n - r)!)
    pub fn count_combinations(n: u64, r: u64) -> u64 {
        factorial(n) / (factorial(r) * factorial(n - r))
    }

    /// Computes [ⁿC₀, ⁿC₁, ..., ⁿCₙ]
    pub fn get_binomial_combinations(n: u64) -> Vec<u64> {
        (0..n + 1).map(|k| count_combinations(n, k)).collect()
    }

    /// Generate binomial expansion matrix for binomial tower field polynomials
    /// Let us write out (1 + r)ᵈ as a linear combination of [1, r, r², ..., rⁿ].
    /// (1 + r)^0 = [1]
    /// (1 + r)^1 = [1 1]
    /// (1 + r)^2 = [1 0 1]
    /// (1 + r)^3 = [1 1 1 1]
    /// (1 + r)^4 = [1 0 0 0 1]
    /// (1 + r)^5 = [1 1 0 0 1 1]
    /// ...
    /// ...
    /// (1 + r)^8 = [1 0 0 0 0 0 0 0 1]
    /// ...
    ///
    /// This forms exactly the same pattern as the Sierpinski gasket.
    /// Read more about it: http://www.danielmathews.info/wp-content/uploads/2001/06/pascal.pdf
    ///
    /// So to get the binomial expansion (1 + r)ᵈ in binary tower fields, all the binomial coefficients
    /// are boolean values, so we simply need to compute ⁿCᵣ mod 2.
    ///
    pub fn generate_binomial_expansion_matrix<BF: TowerField>(degree: usize) -> DMatrix<BF> {
        let num_evals = degree + 1;
        let nrows = num_evals;
        let ncols = num_evals;

        let mut data: Vec<BF> = Vec::with_capacity(nrows * ncols);
        for i in (0..=degree).rev() {
            let combinations = get_binomial_combinations(i as u64);

            let mut modified_combinations: Vec<BF> = Vec::with_capacity(num_evals);
            modified_combinations.resize(num_evals - combinations.len(), BF::zero());
            modified_combinations
                .extend(combinations.iter().map(|c| BF::new((*c & 1) as u128, None)));

            data.extend(modified_combinations);
        }

        let dmatrix: nalgebra::Matrix<
            BF,
            nalgebra::Dyn,
            nalgebra::Dyn,
            nalgebra::VecStorage<BF, nalgebra::Dyn, nalgebra::Dyn>,
        > = DMatrix::from_row_slice(nrows, ncols, &data);
        dmatrix.transpose()
    }

    // Helper function to generate evaluation matrix for Toom-Cook algorithm.
    pub fn generate_evaluation_matrix<BF: TowerField>(degree: usize) -> Vec<Vec<BF>> {
        let num_evals = degree + 1;
        let mut eval_matrix: Vec<Vec<BF>> = Vec::with_capacity(num_evals);

        // Push first two rows for x = 0 and x = ∞
        // x = 0 => [1 0 0 ... 0]
        // x = ∞ => [0 0 0 ... 1]
        eval_matrix.push(vec![BF::zero(); num_evals]);
        eval_matrix[0][0] = BF::one();
        // eval_matrix.push(vec![BF::zero(); num_evals]);
        // eval_matrix[1][num_evals - 1] = BF::one();

        for i in 1..(num_evals - 1) {
            // Push a row for x = i
            // x = i => [1 i i² i³ ... iᵈ]
            if eval_matrix.len() < num_evals {
                let eval_row: Vec<BF> = (0..num_evals)
                    .map(|j| (BF::new(i as u128, None)).pow(j as u32))
                    .collect();
                eval_matrix.push(eval_row);
            }
        }
        eval_matrix.push(vec![BF::zero(); num_evals]);
        eval_matrix[num_evals - 1][num_evals - 1] = BF::one();
        eval_matrix
    }

    // Custom determinant function using Laplace expansion
    pub fn custom_determinant<BF: TowerField>(matrix: &DMatrix<BF>) -> BF {
        let n = matrix.nrows();
        assert!(n == matrix.ncols(), "Matrix must be square.");

        if n == 1 {
            return matrix[(0, 0)];
        } else if n == 2 {
            return matrix[(0, 0)] * matrix[(1, 1)] - matrix[(0, 1)] * matrix[(1, 0)];
        }

        let mut det = BF::zero();
        for col in 0..n {
            let minor_matrix = matrix.clone().remove_row(0).remove_column(col);
            let sub_det = custom_determinant(&minor_matrix);
            // The sub-determinant is multiplied by (-1) for "odd" indices, but it doesn't matter for the case of the
            // binary tower fields.
            det += matrix[(0, col)] * sub_det;
        }
        det
    }

    /// Helper function to compute adjugate of an integer matrix.
    pub fn adjugate<BF: TowerField>(matrix: Vec<Vec<BF>>) -> (DMatrix<BF>, BF) {
        let nrows = matrix.len();
        let ncols = matrix[0].len();

        let mut data = Vec::with_capacity(nrows * ncols);
        for row in matrix {
            data.extend(row);
        }

        let dmatrix = DMatrix::from_row_slice(nrows, ncols, &data);
        let determinant = custom_determinant(&dmatrix);

        assert!(
            !determinant.is_zero(),
            "Matrix is not invertible as determinant is 0."
        );

        let mut cofactor_matrix = DMatrix::zeros(nrows, ncols);

        for i in 0..nrows {
            for j in 0..ncols {
                let submatrix = dmatrix.clone().remove_row(i).remove_column(j);
                let sub_determinant = custom_determinant(&submatrix);
                // The sub-determinant is multiplied by (-1) for "odd" indices, but it doesn't matter
                // for the case of the binary tower fields.
                cofactor_matrix[(i, j)] = sub_determinant;
            }
        }

        let adjugate_matrix = cofactor_matrix.transpose();
        (adjugate_matrix, determinant)
    }

    // Helper function to convert DMatrix to vector of vectors.
    pub fn matrix_to_vec_of_vec<BF: TowerField>(matrix: &DMatrix<BF>) -> Vec<Vec<BF>> {
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
    pub fn vec_of_vec_to_matrix<BF: TowerField>(matrix: &Vec<Vec<BF>>) -> DMatrix<BF> {
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
    /// Also outputs the determinant of the interpolation matrix.
    pub fn generate_interpolation_matrix_transpose<BF: TowerField>(
        degree: usize,
    ) -> (Vec<Vec<BF>>, BF) {
        // TODO: this bound on degree isn't needed? Degree could be > 9 for binary fields?
        // assert!(degree < 9);
        let eval_matrix = generate_evaluation_matrix::<BF>(degree);
        let (adjugate_matrix, determinant) = adjugate::<BF>(eval_matrix);
        (matrix_to_vec_of_vec(&adjugate_matrix), determinant)
    }

    /// Custom multiplication function for two DMatrices: A * B
    pub fn custom_matrix_mult<BF: TowerField>(
        matrix_a: &DMatrix<BF>,
        matrix_b: &DMatrix<BF>,
    ) -> DMatrix<BF> {
        let nrows_a = matrix_a.nrows();
        let ncols_a = matrix_a.ncols();
        let ncols_b = matrix_b.ncols();

        // Ensure that the number of columns in A equals the number of rows in B for matrix multiplication
        assert!(
            ncols_a == matrix_b.nrows(),
            "Matrix dimensions do not match for multiplication!"
        );

        // Initialize the result matrix
        let mut result_matrix = DMatrix::zeros(nrows_a, ncols_b);

        // Perform matrix multiplication with custom multiplication and addition logic
        for i in 0..nrows_a {
            for j in 0..ncols_b {
                let mut sum = BF::zero();
                for k in 0..ncols_a {
                    let product = matrix_a[(i, k)].clone() * matrix_b[(k, j)].clone();
                    sum += product;
                }
                result_matrix[(i, j)] = sum;
            }
        }

        result_matrix
    }

    pub fn generate_binomial_interpolation_mult_matrix_transpose<BF: TowerField>(
        degree: usize,
    ) -> (Vec<Vec<BF>>, BF) {
        let (inter_matrix, scaled_det) = generate_interpolation_matrix_transpose::<BF>(degree);
        let inter_dmatrix = vec_of_vec_to_matrix(&inter_matrix);
        let binomial_dmatrix = generate_binomial_expansion_matrix(degree);
        let mult_dmatrix = (custom_matrix_mult(&binomial_dmatrix, &inter_dmatrix)).transpose();

        (matrix_to_vec_of_vec(&mult_dmatrix), scaled_det)
    }

    /// Converts a matrix into maps.
    pub fn get_maps_from_matrix<FF: TowerField>(
        matrix: &Vec<Vec<FF>>,
    ) -> Vec<Box<dyn Fn(&Vec<FF>) -> FF>> {
        matrix
            .iter()
            .map(|irow| {
                let irow_cloned = irow.clone();
                let imap: Box<dyn Fn(&Vec<FF>) -> FF> = Box::new(move |v: &Vec<FF>| -> FF {
                    v.iter()
                        .zip(irow_cloned.iter())
                        .fold(FF::zero(), |acc, (value, scalar)| {
                            acc + (*scalar) * (*value)
                        })
                });
                imap
            })
            .collect::<Vec<Box<dyn Fn(&Vec<FF>) -> FF>>>()
    }

    /// Setup all mappings etc for the toom-cook algorithm.
    pub fn common_setup_for_toom_cook<BF: TowerField, EF: TowerField>(
        degree: usize,
    ) -> (
        Vec<Box<dyn Fn(&BF, &BF) -> BF + Send + Sync>>,
        Vec<usize>,
        Vec<Box<dyn Fn(&Vec<BF>) -> BF>>,
        Vec<Box<dyn Fn(&Vec<EF>) -> EF>>,
        BF,
    ) {
        // Define evaluation mappings
        // p(x) = p0 + p1.x
        let num_evals = degree + 1;
        let mut emaps_base: Vec<Box<dyn Fn(&BF, &BF) -> BF + Send + Sync>> =
            Vec::with_capacity(num_evals);
        emaps_base.push(Box::new(move |x: &BF, _y: &BF| -> BF { *x }));
        for i in 1..(num_evals - 1) {
            if emaps_base.len() < num_evals {
                let mapi =
                    Box::new(move |x: &BF, y: &BF| -> BF { *x + (*y * BF::new(i as u128, None)) });
                emaps_base.push(mapi);
            }
        }
        emaps_base.push(Box::new(move |_x: &BF, y: &BF| -> BF { *y }));

        let projective_map_indices = vec![0, degree];

        // Define interpolation mappings
        let (interpolation_matrix, det) =
            generate_binomial_interpolation_mult_matrix_transpose::<BF>(degree);

        let (interpolation_matrix_ef, _) =
            generate_binomial_interpolation_mult_matrix_transpose::<EF>(degree);

        let imaps_base = get_maps_from_matrix::<BF>(&interpolation_matrix);
        let imaps_ext = get_maps_from_matrix::<EF>(&interpolation_matrix_ef);

        (
            emaps_base,
            projective_map_indices,
            imaps_base,
            imaps_ext,
            det,
        )
    }
}

#[cfg(test)]
mod test {
    use nalgebra::DMatrix;
    use num::One;

    use crate::{
        tests::test_helpers::{
            custom_matrix_mult, factorial_btf, generate_binomial_expansion_matrix,
            generate_evaluation_matrix, generate_interpolation_matrix_transpose,
            vec_of_vec_to_matrix,
        },
        tower_fields::{binius::BiniusTowerField, TowerField},
    };

    use BiniusTowerField as BTF;

    #[test]
    fn test_factorial() {
        let mut expected = BTF::one();
        for i in 1..20 {
            assert_eq!(factorial_btf(BTF::new(i, Some(4))), expected);
            expected *= BTF::new(i + 1, None);
        }
    }

    #[test]
    fn test_interpolation_matrix() {
        for j in 1..10 {
            let eval_matrix = generate_evaluation_matrix::<BTF>(j);
            let (imatrix, det) = generate_interpolation_matrix_transpose::<BTF>(j);
            let inv_det = det.inverse().unwrap();

            let eval_dmatrix = vec_of_vec_to_matrix::<BTF>(&eval_matrix);
            let i_dmatrix = vec_of_vec_to_matrix::<BTF>(&imatrix);

            let multplication = custom_matrix_mult(&eval_dmatrix, &i_dmatrix) * inv_det;
            assert_eq!(multplication, DMatrix::identity(j + 1, j + 1));
        }
    }

    #[test]
    fn test_binomial_matrix() {
        for j in (1 as u32)..20 {
            let binomial_dmatrix = generate_binomial_expansion_matrix::<BTF>(j as usize);
            let r_value = BTF::rand(Some(4));
            let mut r_powers = vec![BTF::one()];
            for k in 1..=j {
                r_powers.push(r_powers[k as usize - 1] * r_value);
            }
            let r_powers_dmatrix = DMatrix::from_row_slice(1, (j + 1) as usize, &r_powers);
            let r_evals = custom_matrix_mult(&r_powers_dmatrix, &binomial_dmatrix);

            for l in 0..=(j as u32) {
                let r_bar = BTF::one() - r_value;
                let r_bar_pow = r_bar.pow((j - l) as u32);
                let r_pow = r_value.pow(l);
                let expected = r_bar_pow * r_pow;
                assert_eq!(r_evals[l as usize], expected);
            }
        }
    }
}
