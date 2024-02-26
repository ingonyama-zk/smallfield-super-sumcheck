use std::vec;

use ark_std::{
    fmt::{self, Formatter},
    iterable::Iterable,
    log2,
};

use ark_ff::Field;
use ark_poly::DenseMultilinearExtension;

pub fn bit_decompose(input: usize, input_bit_len: usize, slice_len: usize) -> Vec<usize> {
    let max_input = (1 as usize) << input_bit_len;
    assert!(input < max_input);
    assert!(slice_len <= input_bit_len);
    assert!(slice_len != 0);
    assert!(input_bit_len % slice_len == 0);

    let output_bit_mask = ((1 as usize) << slice_len) - 1;
    let output_len = input_bit_len / slice_len;
    let mut output = Vec::with_capacity(output_len);

    for i in 0..output_len {
        let offset = (output_len - i - 1) * slice_len;
        let output_val = (input >> offset) & output_bit_mask;
        output.push(output_val);
    }
    output
}

pub fn bit_extend(
    input: usize,
    input_bit_len: usize,
    source_slice_len: usize,
    target_slice_len: usize,
) -> usize {
    let input_bits = bit_decompose(input, input_bit_len, source_slice_len);
    let mut output: usize = 0;
    let mut offset = target_slice_len - source_slice_len;
    for i in 0..input_bits.len() {
        output += input_bits[input_bits.len() - i - 1] << offset;
        offset += target_slice_len;
    }
    output
}

pub fn bit_extend_and_insert(
    input: usize,
    input_bit_len: usize,
    value_to_insert: usize,
    value_to_insert_bit_len: usize,
    source_slice_len: usize,
    target_slice_len: usize,
) -> usize {
    assert!(target_slice_len > source_slice_len);

    let value_to_insert_bits = bit_decompose(
        value_to_insert,
        value_to_insert_bit_len,
        target_slice_len - source_slice_len,
    );

    let mut input_bits: Vec<usize> = vec![0; value_to_insert_bits.len()];
    if source_slice_len != 0 {
        input_bits = bit_decompose(input, input_bit_len, source_slice_len);
    }
    assert_eq!(input_bits.len(), value_to_insert_bits.len());
    let mut output: usize = 0;
    let mut insertion_output: usize = 0;
    let mut offset: usize = target_slice_len - source_slice_len;
    let mut insertion_offset: usize = 0;
    for i in 0..input_bits.len() {
        let idx = input_bits.len() - i - 1;
        output += input_bits[idx] << offset;
        offset += target_slice_len;
        insertion_output += value_to_insert_bits[idx] << insertion_offset;
        insertion_offset += target_slice_len;
    }
    output + insertion_output
}

/// Represents a pair of values (p(0), p(1)) where p(.) is a linear univariate polynomial of the form:
/// p(X) = p(0).(1 - X) + p(1).X
/// where X is any field element. So we have:
/// p(0) = `LinearLagrange.even`, p(1) = `LinearLagrange.odd`
#[derive(Clone, PartialEq, Eq)]
pub struct LinearLagrange<F: Field> {
    pub even: F,
    pub odd: F,
}

#[derive(Clone, PartialEq, Eq)]
/// Represents pairs of values (p(i), p(n/2 + i)) where p(.) multi-linear polynomial of the form: \newline
/// p(X_1, X_2, ..., X_m) = p(0).(1-X_1)(1-X_2)...(1-X_m) + p(1).(1-X_1)(1-X_2)...(X_m) + ...
/// where X_i can be any field elements. We pair values according to the first variable, i.e.
/// X_1 = 0 ==> p(i)
/// X_1 = 1 ==> p(n/2 + i)
/// This is particularly useful while working with sumcheck round computations.
pub struct LinearLagrangeList<F: Field> {
    pub size: usize,
    pub list: Vec<LinearLagrange<F>>,
}

impl<F: Field> LinearLagrange<F> {
    /// Define a new LinearLagrange instance: p(0).(1-X) + p(1).X as
    /// $`[e, o] \equiv [p(0), p(1)]`$
    pub fn new(even: &F, odd: &F) -> LinearLagrange<F> {
        LinearLagrange {
            even: *even,
            odd: *odd,
        }
    }
    /// Adds 2 LinearLagrange instances and outputs a resulting LinearLagrange instance.
    /// this is for instance the atomic operation in each step, and this should be parallelized
    /// per pair of instances.
    pub fn add(&self, other: &LinearLagrange<F>) -> LinearLagrange<F> {
        LinearLagrange {
            even: self.even + other.even,
            odd: self.odd + other.odd,
        }
    }

    /// Subtracts 2 LinearLagrange instances and outputs a new LinearLagrange instance
    pub fn sub(&self, other: &LinearLagrange<F>) -> LinearLagrange<F> {
        let even_result: F = self.even - other.even;
        let odd_result: F = self.odd - other.odd;
        LinearLagrange {
            even: even_result,
            odd: odd_result,
        }
    }

    /// Evaluates the linear polynomial at alpha and returns $`p(0) * (1 - \alpha) + p(1) * \alpha`$
    pub fn evaluate_at(&self, alpha: F) -> F {
        self.even.mul(F::ONE - alpha) + self.odd.mul(alpha)
    }
}

impl<F: Field> LinearLagrangeList<F> {
    /// Create a new list from evaluations of a dense MLE polynomial
    pub fn from(polynomial: &DenseMultilinearExtension<F>) -> LinearLagrangeList<F> {
        let list_size = polynomial.evaluations.len() / 2;
        let poly_list = (0..list_size)
            .map(|i| {
                LinearLagrange::new(
                    &polynomial.evaluations[i],
                    &polynomial.evaluations[i + list_size],
                )
            })
            .collect::<Vec<LinearLagrange<F>>>();
        LinearLagrangeList {
            size: list_size,
            list: poly_list,
        }
    }

    pub fn from_vector(list: &Vec<F>) -> LinearLagrangeList<F> {
        let list_size = list.len() / 2;
        let poly_list = (0..list_size)
            .map(|i| LinearLagrange::new(&list[i], &list[i + list_size]))
            .collect::<Vec<LinearLagrange<F>>>();
        LinearLagrangeList {
            size: list_size,
            list: poly_list,
        }
    }

    pub fn convert<OtherF, T>(self: &LinearLagrangeList<F>, to_ef: &T) -> LinearLagrangeList<OtherF>
    where
        OtherF: Field,
        T: Fn(&F) -> OtherF + Sync,
    {
        let list_size = self.size;
        let poly_list = (0..list_size)
            .map(|i| LinearLagrange::new(&(to_ef(&self.list[i].even)), &(to_ef(&self.list[i].odd))))
            .collect::<Vec<LinearLagrange<OtherF>>>();

        LinearLagrangeList::<OtherF> {
            size: list_size,
            list: poly_list,
        }
    }

    /// Create a new initialized list (create with vectors specified)
    pub fn new(list_size: &usize, poly_list: &Vec<LinearLagrange<F>>) -> LinearLagrangeList<F> {
        LinearLagrangeList {
            size: *list_size,
            list: poly_list.to_vec(),
        }
    }
    /// Create a new un-initialized list (create with zero vectors)    
    pub fn new_uninitialized(size: &usize) -> LinearLagrangeList<F> {
        let vec = LinearLagrange::new(&F::zero(), &F::zero());
        LinearLagrangeList {
            size: *size,
            list: vec![vec; *size],
        }
    }
    /// Accumulates the even and odd parts in a list
    pub fn list_accumulator(self: &LinearLagrangeList<F>) -> LinearLagrange<F> {
        let mut acc: LinearLagrange<F> = LinearLagrange::new(&F::zero(), &F::zero());
        for i in 0..=self.size - 1 {
            acc = acc.add(&self.list[i]);
        }
        acc
    }

    /// Folds a linear lagrange list in half according to the sumcheck protocol
    pub fn fold_in_half(self: &mut LinearLagrangeList<F>, challenge: F) {
        assert_ne!(self.size, 0);
        for linear_lagrange_instance in &mut self.list {
            linear_lagrange_instance.even *= F::one() - challenge;
            linear_lagrange_instance.odd *= challenge;
            linear_lagrange_instance.even += linear_lagrange_instance.odd;
        }

        for i in 0..(self.size / 2) {
            self.list[i].odd = self.list[i + self.size / 2].even;
        }
        self.size /= 2;
        self.list.truncate(self.size);
    }

    // Takes a structure and generates a new structure half the size (to add conditions)
    pub fn fold_list(input: &LinearLagrangeList<F>, challenge: F) -> LinearLagrangeList<F> {
        assert_ne!(input.size, 0);
        let mut poly_list: Vec<LinearLagrange<F>> = Vec::new();
        for i in (0..=input.size - 1).step_by(2) {
            poly_list.push(LinearLagrange {
                even: LinearLagrange::evaluate_at(&input.list[i], challenge),
                odd: LinearLagrange::evaluate_at(&input.list[i + 1], challenge),
            });
        }
        LinearLagrangeList {
            size: poly_list.len(),
            list: poly_list,
        }
    }
}

impl<F: Field> fmt::Debug for LinearLagrange<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "LinearLagrange(even = {}, odd = {})",
            self.even, self.odd
        )?;
        Ok(())
    }
}

impl<F: Field> fmt::Debug for LinearLagrangeList<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "LinearLagrangeList(size = {}, list = [", self.size)?;
        for i in 0..self.list.len() {
            write!(f, "({}, {}) ", self.list[i].even, self.list[i].odd)?;
        }
        write!(f, "])")?;
        Ok(())
    }
}

///
/// For sumcheck prover (algorithm 2), we need to represent polynomial evaluations in a matrix form.
///
#[derive(Clone, PartialEq, Eq)]
pub struct MatrixPolynomial<F: Field> {
    pub no_of_rows: usize,
    pub no_of_columns: usize,
    pub evaluation_rows: Vec<Vec<F>>,
}

impl<F: Field> MatrixPolynomial<F> {
    pub fn one() -> Self {
        MatrixPolynomial {
            no_of_rows: 1,
            no_of_columns: 1,
            evaluation_rows: vec![vec![F::ONE]],
        }
    }

    pub fn from_dense_mle(input_polynomial: &DenseMultilinearExtension<F>) -> Self {
        let n = input_polynomial.evaluations.len();
        let mid_point = n / 2;
        let (first_half, second_half) = input_polynomial.evaluations.split_at(mid_point);

        MatrixPolynomial {
            no_of_rows: 2,
            no_of_columns: mid_point,
            evaluation_rows: vec![first_half.to_vec(), second_half.to_vec()],
        }
    }

    pub fn from_linear_lagrange_list(input_polynomial: &LinearLagrangeList<F>) -> Self {
        let n_by_2 = input_polynomial.size;
        MatrixPolynomial {
            no_of_rows: 2,
            no_of_columns: n_by_2,
            evaluation_rows: vec![
                input_polynomial
                    .list
                    .iter()
                    .map(|ll_instance| ll_instance.even)
                    .collect(),
                input_polynomial
                    .list
                    .iter()
                    .map(|ll_instance| ll_instance.odd)
                    .collect(),
            ],
        }
    }

    pub fn heighten(&mut self) {
        // Update the dimensions of the original matrix
        self.no_of_rows *= 2;
        self.no_of_columns /= 2;
        let mid_point = self.no_of_columns;
        let end_point = mid_point * 2;

        for row_index in 0..(self.no_of_rows / 2) {
            let vector_to_add = self.evaluation_rows[2 * row_index][mid_point..end_point].to_vec();
            self.evaluation_rows
                .insert(2 * row_index + 1, vector_to_add);
            self.evaluation_rows[2 * row_index].truncate(mid_point);
        }
    }

    pub fn flatten(&mut self) {
        // Take ownership of the first row and replace it with an empty vector
        let mut flattened_row = std::mem::take(&mut self.evaluation_rows[0]);

        // Concatenate all other rows into the first row
        for row_index in 1..self.no_of_rows {
            flattened_row.extend_from_slice(&self.evaluation_rows[row_index]);
        }

        // Update the dimensions of the original matrix
        self.no_of_columns *= self.no_of_rows;
        self.no_of_rows = 1;

        // Replace the first row with the concatenated row
        self.evaluation_rows[0] = flattened_row;
    }

    pub fn tensor_hadamard_product<P>(
        &self,
        rhs: &MatrixPolynomial<F>,
        mult_bb: &P,
    ) -> MatrixPolynomial<F>
    where
        P: Fn(&F, &F) -> F,
    {
        assert_eq!(self.no_of_columns, rhs.no_of_columns);

        let mut output = MatrixPolynomial {
            no_of_rows: self.no_of_rows * rhs.no_of_rows,
            no_of_columns: self.no_of_columns,
            evaluation_rows: Vec::with_capacity(self.no_of_rows * rhs.no_of_rows),
        };

        for i in 0..self.no_of_rows {
            for j in 0..rhs.no_of_rows {
                let left_vec: &Vec<F> = &self.evaluation_rows[i];
                let right_vec: &Vec<F> = &rhs.evaluation_rows[j];
                let left_right_hadamard: Vec<F> = left_vec
                    .iter()
                    .zip(right_vec.iter())
                    .map(|(l, r)| mult_bb(l, r))
                    .collect();
                output.evaluation_rows.push(left_right_hadamard);
            }
        }
        output
    }

    pub fn tensor_inner_product<P>(matrices: &Vec<MatrixPolynomial<F>>, mult_bb: &P) -> Vec<F>
    where
        P: Fn(&F, &F) -> F,
    {
        let d = matrices.len();
        let row_count = matrices[0].no_of_rows;
        let col_count = matrices[0].no_of_columns;
        assert!(row_count.is_power_of_two());
        assert!(col_count.is_power_of_two());
        for i in 1..d {
            assert_eq!(matrices[i].no_of_rows, row_count);
            assert_eq!(matrices[i].no_of_columns, col_count);
        }

        let log_row_count = log2(row_count) as usize;
        let output_bit_len = log_row_count * d;
        let output_len = 1 << output_bit_len;
        let mut output = Vec::with_capacity(output_len);

        for i in 0..output_len {
            let mut local_output = vec![F::ONE; col_count];
            for j in 0..d {
                let offset = (d - j - 1) * log_row_count;
                let index = (i >> offset) & (row_count - 1);
                let matrix_row = &matrices[j].evaluation_rows[index];

                local_output
                    .iter_mut()
                    .zip(matrix_row.iter())
                    .for_each(|(m_acc, m_curr)| *m_acc = mult_bb(m_acc, &m_curr));
            }
            let local_sum = local_output.iter().fold(F::zero(), |sum, val| sum + val);
            output.push(local_sum);
        }

        output
    }

    pub fn collapse(&mut self) {
        if self.no_of_columns == 1 {
            return;
        } else {
            self.no_of_columns = 1;

            for i in 0..self.no_of_rows {
                let new_value: F = self.evaluation_rows[i]
                    .iter()
                    .fold(F::zero(), |sum, &r| sum + r);
                self.evaluation_rows[i] = vec![new_value];
            }
        }
    }

    pub fn dot_product<OtherF, P>(
        lhs: &MatrixPolynomial<F>,
        rhs: &MatrixPolynomial<OtherF>,
        mult_be: &P,
    ) -> OtherF
    where
        OtherF: Field,
        P: Fn(&F, &OtherF) -> OtherF + Sync,
    {
        assert_eq!(lhs.no_of_columns, rhs.no_of_columns);
        assert_eq!(lhs.no_of_rows, rhs.no_of_rows);

        lhs.evaluation_rows
            .iter()
            .zip(rhs.evaluation_rows.iter())
            .fold(OtherF::zero(), |acc, (l_row, r_row)| {
                acc + l_row
                    .iter()
                    .zip(r_row.iter())
                    .fold(OtherF::zero(), |sum, (&l_val, &r_val)| {
                        sum + mult_be(&l_val, &r_val)
                    })
            })
    }

    pub fn scale_and_squash<OtherF, P>(
        self: &MatrixPolynomial<F>,
        multiplicand: &MatrixPolynomial<OtherF>,
        mult_be: &P,
    ) -> LinearLagrangeList<OtherF>
    where
        OtherF: Field,
        P: Fn(&F, &OtherF) -> OtherF + Sync,
    {
        assert_eq!(self.no_of_rows, multiplicand.no_of_rows);
        assert_eq!(multiplicand.no_of_columns, 1);

        // ATTENTION: We are not counting ee additions here!
        let scaled_vec: Vec<OtherF> = (0..self.no_of_columns)
            .map(|col_index| {
                self.evaluation_rows
                    .iter()
                    .zip(multiplicand.evaluation_rows.iter())
                    .fold(OtherF::zero(), |acc, (b_row, e_row)| {
                        acc + mult_be(&b_row[col_index], &e_row[0])
                    })
            })
            .collect();

        LinearLagrangeList::<OtherF>::from_vector(&scaled_vec)
    }
}

impl<F: Field> fmt::Debug for MatrixPolynomial<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "MatrixPolynomial(cols = {}, rows = {}, evaluations:\n",
            self.no_of_columns, self.no_of_rows
        )?;
        for i in 0..self.evaluation_rows.len() {
            write!(f, "[")?;
            for j in 0..self.evaluation_rows[0].len() {
                write!(f, "{} ", self.evaluation_rows[i][j])?;
            }
            write!(f, "]\n")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::data_structures::{
        bit_extend, bit_extend_and_insert, LinearLagrange, LinearLagrangeList,
    };
    use ark_bls12_381::Fr as F;
    use ark_ff::{Field, Zero};
    use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
    use itertools::izip;
    use rand::Rng;

    use super::{bit_decompose, MatrixPolynomial};

    pub fn random_field_element<F: Field>() -> F {
        let mut rng = rand::thread_rng();
        let random_u128: u128 = rng.gen();
        F::from(random_u128)
    }

    pub fn get_random_linear_lagrange<F: Field>() -> LinearLagrange<F> {
        LinearLagrange::new(&random_field_element(), &random_field_element())
    }

    #[test]
    fn test_bit_decompose() {
        // (001)(010)(111)(110)(001)
        let value: usize = 5617;
        let bits = bit_decompose(value, 15, 3);
        assert_eq!(bits.len(), 5);
        assert_eq!(bits[0], 1);
        assert_eq!(bits[1], 2);
        assert_eq!(bits[2], 7);
        assert_eq!(bits[3], 6);
        assert_eq!(bits[4], 1);
    }

    #[test]
    fn test_bit_extend() {
        // 5617  =>  (001)(010)(111)(110)(001)
        let value: usize = 5617;
        // 4363923472  =>  (001[0000])(010[0000])(111[0000])(110[0000])(001[0000])
        let output = bit_extend(value, 15, 3, 7);
        assert_eq!(output, 4363923472);
    }

    #[test]
    fn test_bit_extend_and_insert() {
        // 5617  =>  (001)(010)(111)(110)(001)
        let value: usize = 5617;
        // 316679 => (0100)(1101)(0101)(0000)(0111)
        let value_to_insert = 316679;
        // 5465010199  =>  (001[0100])(010[1101])(111[0101])(110[0000])(001[0111])
        let output = bit_extend_and_insert(value, 15, value_to_insert, 20, 3, 7);
        assert_eq!(output, 5465010199);
    }

    #[test]
    fn test_linear_lagrange_add() {
        let r1: LinearLagrange<F> = get_random_linear_lagrange();
        let r2: LinearLagrange<F> = get_random_linear_lagrange();
        let addition = r1.add(&r2);
        assert_eq!(r1.odd + r2.odd, addition.odd);
        assert_eq!(r1.even + r2.even, addition.even);
    }

    #[test]
    fn test_linear_lagrange_sub() {
        let r1: LinearLagrange<F> = get_random_linear_lagrange();
        let r2: LinearLagrange<F> = get_random_linear_lagrange();
        let subtraction = r1.sub(&r2);
        assert_eq!(r1.odd - r2.odd, subtraction.odd);
        assert_eq!(r1.even - r2.even, subtraction.even);
    }

    #[test]
    fn test_linear_lagrange_accumulate() {
        let list_size = 10;
        let linear_lagrange_vec = (0..list_size)
            .map(|_| get_random_linear_lagrange::<F>())
            .collect::<Vec<LinearLagrange<F>>>();
        let lagrange_list: LinearLagrangeList<F> =
            LinearLagrangeList::new(&list_size, &linear_lagrange_vec);
        let accumulated = LinearLagrangeList::list_accumulator(&lagrange_list);

        let expected_even_sum = linear_lagrange_vec
            .iter()
            .fold(F::zero(), |sum, ll_instance| sum + ll_instance.even);

        let expected_odd_sum = linear_lagrange_vec
            .iter()
            .fold(F::zero(), |sum, ll_instance| sum + ll_instance.odd);

        assert_eq!(accumulated.even, expected_even_sum);
        assert_eq!(accumulated.odd, expected_odd_sum);
    }

    #[test]
    fn test_fold_list() {
        let list_size = 8;
        let linear_lagrange_vec = (0..list_size)
            .map(|_| get_random_linear_lagrange::<F>())
            .collect::<Vec<LinearLagrange<F>>>();
        let lagrange_list: LinearLagrangeList<F> =
            LinearLagrangeList::new(&list_size, &linear_lagrange_vec);

        let alpha: F = random_field_element();
        let folded_list = LinearLagrangeList::fold_list(&lagrange_list, alpha);

        for i in (0..lagrange_list.size).step_by(2) {
            let expected_even = lagrange_list.list[i].evaluate_at(alpha);
            let expected_odd = lagrange_list.list[i + 1].evaluate_at(alpha);
            assert_eq!(folded_list.list[i / 2].even, expected_even);
            assert_eq!(folded_list.list[i / 2].odd, expected_odd);
        }
    }

    #[test]
    fn test_fold_in_half() {
        let list_size = 8;
        let linear_lagrange_vec = (0..list_size)
            .map(|_| get_random_linear_lagrange::<F>())
            .collect::<Vec<LinearLagrange<F>>>();
        let mut lagrange_list: LinearLagrangeList<F> =
            LinearLagrangeList::new(&list_size, &linear_lagrange_vec);
        let size_before = lagrange_list.size;

        let alpha: F = random_field_element();
        lagrange_list.fold_in_half(alpha);
        let size_after = lagrange_list.size;
        assert_eq!(2 * size_after, size_before);

        for i in 0..lagrange_list.size {
            let expected_even =
                (F::ONE - alpha) * linear_lagrange_vec[i].even + alpha * linear_lagrange_vec[i].odd;
            let expected_odd = (F::ONE - alpha) * linear_lagrange_vec[size_after + i].even
                + alpha * linear_lagrange_vec[size_after + i].odd;

            assert_eq!(lagrange_list.list[i].even, expected_even);
            assert_eq!(lagrange_list.list[i].odd, expected_odd);
        }
    }

    #[test]
    fn test_matrix_polynomial_heighten() {
        let mut rng = rand::thread_rng();
        let poly = DenseMultilinearExtension::<F>::rand(3, &mut rng);
        let mut matrix_poly = MatrixPolynomial::from_dense_mle(&poly);
        let mid_point = poly.evaluations.len() / 2;
        let end_point = poly.evaluations.len();

        assert_eq!(matrix_poly.no_of_rows, 2);
        assert_eq!(matrix_poly.no_of_columns, mid_point);
        assert_eq!(
            matrix_poly.evaluation_rows[0],
            poly.evaluations[0..mid_point]
        );
        assert_eq!(
            matrix_poly.evaluation_rows[1],
            poly.evaluations[mid_point..end_point]
        );

        // Test if heighten works as intended
        matrix_poly.heighten();
        assert_eq!(matrix_poly.evaluation_rows[0], poly.evaluations[0..2]);
        assert_eq!(matrix_poly.evaluation_rows[1], poly.evaluations[2..4]);
        assert_eq!(matrix_poly.evaluation_rows[2], poly.evaluations[4..6]);
        assert_eq!(matrix_poly.evaluation_rows[3], poly.evaluations[6..8]);
    }

    #[test]
    fn test_matrix_polynomial_flatten() {
        let mut rng = rand::thread_rng();
        let poly = DenseMultilinearExtension::<F>::rand(4, &mut rng);
        let mut matrix_poly = MatrixPolynomial::from_dense_mle(&poly);

        // Test if flatten works as intended
        matrix_poly.flatten();
        assert_eq!(matrix_poly.evaluation_rows[0], poly.evaluations);
        assert_eq!(matrix_poly.no_of_columns, poly.evaluations.len());
        assert_eq!(matrix_poly.no_of_rows, 1);
    }

    pub fn vector_hadamard(a: &Vec<F>, b: &Vec<F>) -> Vec<F> {
        assert_eq!(a.len(), b.len());
        a.iter().zip(b.iter()).map(|(ai, bi)| ai * bi).collect()
    }

    #[test]
    fn test_matrix_polynomial_tensor_hadamard() {
        let mut rng = rand::thread_rng();
        let poly_a = DenseMultilinearExtension::<F>::rand(3, &mut rng);
        let matrix_poly_a = MatrixPolynomial::from_dense_mle(&poly_a);
        let poly_b = DenseMultilinearExtension::<F>::rand(4, &mut rng);
        let mut matrix_poly_b = MatrixPolynomial::from_dense_mle(&poly_b);
        fn mult_bb(left: &F, right: &F) -> F {
            left * right
        }

        // Reduce number of columns of b by half
        matrix_poly_b.heighten();

        // Perform tensor-hadamard product of a and b
        let matrix_poly_c = matrix_poly_a.tensor_hadamard_product(&matrix_poly_b, &mult_bb);

        assert_eq!(matrix_poly_b.no_of_columns, matrix_poly_a.no_of_columns);
        assert_eq!(matrix_poly_c.no_of_columns, matrix_poly_a.no_of_columns);
        assert_eq!(
            matrix_poly_c.no_of_rows,
            matrix_poly_a.no_of_rows * matrix_poly_b.no_of_rows
        );

        for i in 0..matrix_poly_b.no_of_rows {
            let a0_bi = vector_hadamard(
                &matrix_poly_a.evaluation_rows[0],
                &matrix_poly_b.evaluation_rows[i],
            );
            let a1_bi = vector_hadamard(
                &matrix_poly_a.evaluation_rows[1],
                &matrix_poly_b.evaluation_rows[i],
            );
            let offset = matrix_poly_b.no_of_rows;
            assert_eq!(matrix_poly_c.evaluation_rows[i], a0_bi);
            assert_eq!(matrix_poly_c.evaluation_rows[i + offset], a1_bi);
        }
    }

    #[test]
    fn test_matrix_polynomial_tensor_inner_product() {
        let num_variables = 3;
        let num_evaluations = (1 as u32) << num_variables;
        let evaluations_a: Vec<F> = (0..num_evaluations).map(|i| F::from(2 * i)).collect();
        let evaluations_b: Vec<F> = (0..num_evaluations).map(|i| F::from(i + 1)).collect();
        let evaluations_c: Vec<F> = (0..num_evaluations).map(|i| F::from(3 * i + 2)).collect();
        fn mult_bb(left: &F, right: &F) -> F {
            left * right
        }

        let poly_a =
            DenseMultilinearExtension::<F>::from_evaluations_vec(num_variables, evaluations_a);
        let poly_b =
            DenseMultilinearExtension::<F>::from_evaluations_vec(num_variables, evaluations_b);
        let poly_c =
            DenseMultilinearExtension::<F>::from_evaluations_vec(num_variables, evaluations_c);
        let mut matrix_poly_a = MatrixPolynomial::from_dense_mle(&poly_a);
        let mut matrix_poly_b = MatrixPolynomial::from_dense_mle(&poly_b);
        let mut matrix_poly_c = MatrixPolynomial::from_dense_mle(&poly_c);

        // First flatten all matrix polynomials
        matrix_poly_a.flatten();
        matrix_poly_b.flatten();
        matrix_poly_c.flatten();

        let output_1 = MatrixPolynomial::tensor_inner_product(
            &vec![
                matrix_poly_a.clone(),
                matrix_poly_b.clone(),
                matrix_poly_c.clone(),
            ],
            &mult_bb,
        );

        let mut expected = F::zero();
        for (a, b, c) in izip!(
            &poly_a.evaluations,
            &poly_b.evaluations,
            &poly_c.evaluations
        ) {
            expected += a * b * c;
        }
        assert_eq!(output_1.len(), 1);
        assert_eq!(expected, output_1[0]);

        // Now lets heighten and try the same operation again
        matrix_poly_a.heighten();
        matrix_poly_b.heighten();
        matrix_poly_c.heighten();

        let output_2 = MatrixPolynomial::tensor_inner_product(
            &vec![
                matrix_poly_a.clone(),
                matrix_poly_b.clone(),
                matrix_poly_c.clone(),
            ],
            &mult_bb,
        );
        assert_eq!(output_2.len(), 8);

        let num_rows = matrix_poly_a.no_of_rows;
        for i in 0..num_rows {
            for j in 0..num_rows {
                for k in 0..num_rows {
                    let mut expected = F::zero();
                    for (a, b, c) in izip!(
                        &matrix_poly_a.evaluation_rows[i as usize],
                        &matrix_poly_b.evaluation_rows[j as usize],
                        &matrix_poly_c.evaluation_rows[k as usize]
                    ) {
                        expected += a * b * c;
                    }
                    let index = k + j * num_rows + i * num_rows * num_rows;
                    assert_eq!(expected, output_2[index as usize]);
                }
            }
        }

        // Now lets heighten and try the same operation again
        matrix_poly_a.heighten();
        matrix_poly_b.heighten();
        matrix_poly_c.heighten();

        let output_3 = MatrixPolynomial::tensor_inner_product(
            &vec![
                matrix_poly_a.clone(),
                matrix_poly_b.clone(),
                matrix_poly_c.clone(),
            ],
            &mult_bb,
        );
        assert_eq!(output_3.len(), 64);

        let num_rows = matrix_poly_a.no_of_rows;
        for i in 0..num_rows {
            for j in 0..num_rows {
                for k in 0..num_rows {
                    let mut expected = F::zero();
                    for (a, b, c) in izip!(
                        &matrix_poly_a.evaluation_rows[i as usize],
                        &matrix_poly_b.evaluation_rows[j as usize],
                        &matrix_poly_c.evaluation_rows[k as usize]
                    ) {
                        expected += a * b * c;
                    }
                    let index = k + j * num_rows + i * num_rows * num_rows;
                    assert_eq!(expected, output_3[index as usize]);
                }
            }
        }
    }

    #[test]
    fn test_matrix_polynomial_collapse() {
        let mut rng = rand::thread_rng();
        let poly = DenseMultilinearExtension::<F>::rand(4, &mut rng);
        let mut matrix_poly = MatrixPolynomial::from_dense_mle(&poly);

        // Reduce number of columns by half
        matrix_poly.heighten();

        // Apply collapse function
        matrix_poly.collapse();

        assert_eq!(matrix_poly.no_of_columns, 1);
        assert_eq!(matrix_poly.no_of_rows, 4);
        assert_eq!(
            matrix_poly.evaluation_rows[0][0],
            poly.evaluations[0..4]
                .iter()
                .fold(F::zero(), |acc, e| acc + e)
        );
        assert_eq!(
            matrix_poly.evaluation_rows[1][0],
            poly.evaluations[4..8]
                .iter()
                .fold(F::zero(), |acc, e| acc + e)
        );
        assert_eq!(
            matrix_poly.evaluation_rows[2][0],
            poly.evaluations[8..12]
                .iter()
                .fold(F::zero(), |acc, e| acc + e)
        );
        assert_eq!(
            matrix_poly.evaluation_rows[3][0],
            poly.evaluations[12..16]
                .iter()
                .fold(F::zero(), |acc, e| acc + e)
        );
    }

    #[test]
    fn test_matrix_polynomial_dot_product() {
        let mut rng = rand::thread_rng();
        let poly_a = DenseMultilinearExtension::<F>::rand(4, &mut rng);
        let matrix_poly_a = MatrixPolynomial::from_dense_mle(&poly_a);
        let poly_b = DenseMultilinearExtension::<F>::rand(4, &mut rng);
        let matrix_poly_b = MatrixPolynomial::from_dense_mle(&poly_b);
        fn mult_be(left: &F, right: &F) -> F {
            left * right
        }

        let computed = MatrixPolynomial::dot_product(&matrix_poly_a, &matrix_poly_b, &mult_be);
        let expected = poly_a
            .evaluations
            .iter()
            .zip(poly_b.iter())
            .fold(F::zero(), |acc, (a, b)| acc + a * b);
        assert_eq!(computed, expected);
    }

    #[test]
    fn test_matrix_polynomial_scale_and_squash() {
        let mut rng = rand::thread_rng();
        let poly_a = DenseMultilinearExtension::<F>::rand(5, &mut rng);
        let mut matrix_poly_a = MatrixPolynomial::from_dense_mle(&poly_a);
        fn mult_be(left: &F, right: &F) -> F {
            left * right
        }

        // Heighten a
        matrix_poly_a.heighten(); // no of rows = 4
        matrix_poly_a.heighten(); // no of rows = 8

        // Create a challenge array with 4 rows, 1 column
        let poly_b = DenseMultilinearExtension::<F>::rand(3, &mut rng);
        let mut matrix_poly_b = MatrixPolynomial::from_dense_mle(&poly_b);
        matrix_poly_b.heighten(); // no of rows = 4
        matrix_poly_b.heighten(); // no of rows = 8
        assert_eq!(matrix_poly_b.no_of_columns, 1);

        // Test scale_by operation
        let computed = matrix_poly_a.scale_and_squash(&matrix_poly_b, &mult_be);

        // Manually scale to compare the result
        let col_size = matrix_poly_a.no_of_columns;
        let mut expected: Vec<F> = Vec::with_capacity(col_size);
        for j in 0..col_size {
            let chunk_j: Vec<_> = poly_a.iter().skip(j).step_by(col_size).cloned().collect();
            let expected_j = chunk_j
                .iter()
                .zip(poly_b.evaluations.iter())
                .fold(F::zero(), |acc, (a_val, b_val)| {
                    acc + mult_be(&a_val, &b_val)
                });
            expected.push(expected_j);
        }
        assert_eq!(computed, LinearLagrangeList::<F>::from_vector(&expected));
    }
}
