use std::{
    ops::{Add, AddAssign, Mul, MulAssign, Sub},
    vec,
};

use num::One;
use num::Zero;
use rayon::prelude::*;

use ark_std::{
    fmt::{self, Formatter},
    iterable::Iterable,
    log2,
};

use crate::tower_fields::TowerField;

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
pub struct LinearLagrange<F: TowerField> {
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
pub struct LinearLagrangeList<F: TowerField> {
    pub size: usize,
    pub list: Vec<LinearLagrange<F>>,
}

impl<F: TowerField> LinearLagrange<F> {
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
        self.even.mul(F::one() - alpha) + self.odd.mul(alpha)
    }
}

impl<F: TowerField> LinearLagrangeList<F> {
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

    pub fn to_vector(&self) -> Vec<F> {
        // Allocate space for the output vector
        let mut vec = Vec::with_capacity(self.size * 2);

        // First, extract the `even` elements
        for poly in &self.list {
            vec.push(poly.even.clone());
        }

        // Then, extract the `odd` elements
        for poly in &self.list {
            vec.push(poly.odd.clone());
        }
        vec
    }

    pub fn convert<OtherF, T>(self: &LinearLagrangeList<F>, to_ef: &T) -> LinearLagrangeList<OtherF>
    where
        OtherF: TowerField,
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

impl<F: TowerField> fmt::Debug for LinearLagrange<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "LinearLagrange(even = {}, odd = {})",
            self.even, self.odd
        )?;
        Ok(())
    }
}

impl<F: TowerField> fmt::Debug for LinearLagrangeList<F> {
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
pub struct MatrixPolynomial<F: TowerField> {
    pub no_of_rows: usize,
    pub no_of_columns: usize,
    pub evaluation_rows: Vec<Vec<F>>,
}

///
/// For sumcheck prover (algorithm 2), we need to represent polynomial evaluations in a matrix (integer) form.
///
#[derive(Clone, PartialEq, Eq)]
pub struct MatrixPolynomialInt<T> {
    pub no_of_rows: usize,
    pub no_of_columns: usize,
    pub evaluation_rows: Vec<Vec<T>>,
}

impl<T> MatrixPolynomialInt<T>
where
    T: Clone
        + Copy
        + Add<Output = T>
        + Mul<Output = T>
        + MulAssign
        + AddAssign
        + Sub<Output = T>
        + Zero
        + One
        + Send
        + Sync,
{
    pub fn from_evaluations(input_polynomial: &Vec<T>) -> Self {
        let n = input_polynomial.len();
        let mid_point = n / 2;
        let (first_half, second_half) = input_polynomial.split_at(mid_point);

        MatrixPolynomialInt {
            no_of_rows: 2,
            no_of_columns: mid_point,
            evaluation_rows: vec![first_half.to_vec(), second_half.to_vec()],
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

    pub fn tensor_inner_product(matrices: &Vec<MatrixPolynomialInt<T>>) -> Vec<T>
    where
        T: Send + Sync + std::ops::MulAssign + Copy + std::iter::Sum + 'static,
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

        // Use parallel iterator to compute output
        (0..output_len)
            .into_par_iter()
            .map(|i| {
                // Compute the tensor product for each `i` in parallel
                let mut local_output = vec![T::one(); col_count];
                for j in 0..d {
                    let offset = (d - j - 1) * log_row_count;
                    let index = (i >> offset) & (row_count - 1);
                    let matrix_row = &matrices[j].evaluation_rows[index];

                    local_output
                        .par_iter_mut()
                        .zip(matrix_row.par_iter())
                        .for_each(|(m_acc, m_curr)| *m_acc *= *m_curr);
                }

                // Sum up the local output
                local_output.iter().copied().sum()
            })
            .collect()
    }

    pub fn compute_merkle_roots(
        input_polynomial: &MatrixPolynomialInt<T>,
        index_j: usize,
        mappings: &Vec<Box<dyn Fn(&T, &T) -> T + Send + Sync>>,
    ) -> MatrixPolynomialInt<T> {
        // Fetch parameters.
        // num_maps: (d + 1)
        // depth: round number p
        // bitmask: (d + 1)-bit mask
        let num_maps = mappings.len();
        let depth = log2(input_polynomial.no_of_rows) as usize;
        // let bitmask = ((1 as usize) << num_maps) - 1;

        // Output is a vector: { merkle( f(*, x), j ) }
        // where x ∈ {0, 1}^{l - p}
        let mut output = MatrixPolynomialInt {
            no_of_rows: 1,
            no_of_columns: input_polynomial.no_of_columns,
            evaluation_rows: vec![Vec::with_capacity(input_polynomial.no_of_columns); 1],
        };

        // Parallelize the outer loop over x
        output.evaluation_rows[0] = (0..input_polynomial.no_of_columns)
            .into_par_iter() // Use parallel iterator
            .map(|x| {
                let mut layer_values: Vec<T> = input_polynomial
                    .evaluation_rows
                    .iter()
                    .map(|row| row[x].clone()) // Use clone if T doesn't implement Copy
                    .collect();

                for layer in 1..=depth {
                    let j_layer = (index_j / num_maps.pow((layer - 1) as u32)) % num_maps;
                    let mapping_for_this_layer = &mappings[j_layer];

                    let layer_size = 1 << (depth - layer);
                    for i in 0..layer_size {
                        let left = &layer_values[2 * i];
                        let right = &layer_values[2 * i + 1];
                        layer_values[i] = mapping_for_this_layer(left, right);
                    }
                    layer_values.truncate(layer_size);
                }
                layer_values[0].clone() // Return the root value for this x
            })
            .collect();
        output
    }

    pub fn hadamard_product(&self, rhs: &MatrixPolynomialInt<T>) -> MatrixPolynomialInt<T> {
        assert_eq!(self.no_of_columns, rhs.no_of_columns);
        assert_eq!(self.no_of_rows, rhs.no_of_rows);

        let mut output = MatrixPolynomialInt {
            no_of_rows: self.no_of_rows,
            no_of_columns: self.no_of_columns,
            evaluation_rows: Vec::with_capacity(self.no_of_rows),
        };

        for i in 0..self.no_of_rows {
            let left_vec: &Vec<T> = &self.evaluation_rows[i];
            let right_vec: &Vec<T> = &rhs.evaluation_rows[i];
            let left_right_hadamard: Vec<T> = left_vec
                .iter()
                .zip(right_vec.iter())
                .map(|(&l, &r)| l * r)
                .collect();
            output.evaluation_rows.push(left_right_hadamard);
        }
        output
    }

    pub fn merkle_sums(
        input: &Vec<T>,
        num_children: usize,
        indices_to_combine: &Vec<usize>,
    ) -> Vec<Vec<T>> {
        let input_size = input.len();
        let depth: usize = input_size.ilog(num_children) as usize;
        assert!(indices_to_combine.len() <= num_children);
        assert_eq!(input_size, num_children.pow(depth as u32));

        // Reserve space for the output in advance
        let mut output: Vec<Vec<T>> = Vec::with_capacity(depth + 1);
        output.push(input.clone());

        let mut layer = input.clone();
        let mut layer_size = input_size / num_children;

        for _ in 1..=depth {
            let mut next_layer = Vec::with_capacity(layer_size);

            // Combine the selected indices for each node
            for j in 0..layer_size {
                let mut layer_value = T::zero();

                // Precompute base index for performance
                let base_idx = num_children * j;
                for &idx in indices_to_combine.iter() {
                    layer_value += layer[base_idx + idx];
                }

                next_layer.push(layer_value);
            }

            output.push(next_layer.clone());
            layer = next_layer; // Move to the next layer
            layer_size /= num_children; // Update the layer size
        }
        output.reverse();
        output
    }
}

impl<F: TowerField> MatrixPolynomial<F>
where
    F: Send + Sync,
{
    pub fn one() -> Self {
        MatrixPolynomial {
            no_of_rows: 1,
            no_of_columns: 1,
            evaluation_rows: vec![vec![F::one()]],
        }
    }

    pub fn ones(given_no_of_rows: usize, given_no_of_columns: usize) -> Self {
        MatrixPolynomial {
            no_of_rows: given_no_of_rows,
            no_of_columns: given_no_of_columns,
            evaluation_rows: vec![vec![F::one(); given_no_of_columns]; given_no_of_rows],
        }
    }

    pub fn from_evaluations_vec(input_vec: &Vec<F>) -> Self {
        let n = input_vec.len();
        let mut eval_rows = Vec::with_capacity(n);
        for i in 0..n {
            eval_rows.push(vec![input_vec[i]]);
        }

        MatrixPolynomial {
            no_of_rows: n,
            no_of_columns: 1,
            evaluation_rows: eval_rows,
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

    pub fn hadamard_product<P>(&self, rhs: &MatrixPolynomial<F>, mult_bb: &P) -> MatrixPolynomial<F>
    where
        P: Fn(&F, &F) -> F,
    {
        assert_eq!(self.no_of_columns, rhs.no_of_columns);
        assert_eq!(self.no_of_rows, rhs.no_of_rows);

        let mut output = MatrixPolynomial {
            no_of_rows: self.no_of_rows,
            no_of_columns: self.no_of_columns,
            evaluation_rows: Vec::with_capacity(self.no_of_rows),
        };

        for i in 0..self.no_of_rows {
            let left_vec: &Vec<F> = &self.evaluation_rows[i];
            let right_vec: &Vec<F> = &rhs.evaluation_rows[i];
            let left_right_hadamard: Vec<F> = left_vec
                .iter()
                .zip(right_vec.iter())
                .map(|(l, r)| mult_bb(l, r))
                .collect();
            output.evaluation_rows.push(left_right_hadamard);
        }
        output
    }

    pub fn compute_merkle_roots(
        input_polynomial: &MatrixPolynomial<F>,
        index_j: usize,
        mappings: &Vec<Box<dyn Fn(&F, &F) -> F + Send + Sync>>,
    ) -> MatrixPolynomial<F> {
        // Fetch parameters.
        // num_maps: (d + 1)
        // depth: round number p
        // bitmask: (d + 1)-bit mask
        let num_maps = mappings.len();
        let depth = log2(input_polynomial.no_of_rows) as usize;
        // let bitmask = ((1 as usize) << num_maps) - 1;

        // Output is a vector: { merkle( f(*, x), j ) }
        // where x ∈ {0, 1}^{l - p}
        let mut output = MatrixPolynomial {
            no_of_rows: 1,
            no_of_columns: input_polynomial.no_of_columns,
            evaluation_rows: vec![Vec::with_capacity(input_polynomial.no_of_columns); 1],
        };

        // Outer loop over x
        for x in 0..input_polynomial.no_of_columns {
            // Fetch all input polynomial values for a given x: f(*, x)
            // where * represents p-bit integers: {0, 1, ..., 2^p - 1}.
            let mut layer_values: Vec<F> = input_polynomial
                .evaluation_rows
                .iter()
                .map(|row| row[x])
                .collect();

            // Start iterating over merkle tree layers starting with leaf values
            for layer in 1..=depth {
                let j_layer = (index_j / num_maps.pow((layer - 1) as u32)) % num_maps;
                let mapping_for_this_layer = &mappings[j_layer];

                let layer_size = (1 as usize) << (depth - layer);
                for i in 0..layer_size {
                    let left = layer_values[2 * i];
                    let right = layer_values[2 * i + 1];
                    layer_values[i] = mapping_for_this_layer(&left, &right);
                }
                layer_values.truncate(layer_size);
            }
            output.evaluation_rows[0].push(layer_values[0]);
        }
        output
    }

    pub fn merkle_sums(
        input: &Vec<F>,
        num_children: usize,
        indices_to_combine: &Vec<usize>,
    ) -> Vec<Vec<F>> {
        let input_size = input.len();
        let depth: usize = input_size.ilog(num_children) as usize;
        assert!(indices_to_combine.len() <= num_children);
        assert_eq!(input_size, num_children.pow(depth as u32));

        let mut output: Vec<Vec<F>> = Vec::with_capacity(depth + 1);
        output.push(input.clone());

        let mut layer = input.clone();
        let mut layer_size = layer.len() / num_children;
        for _ in 1..=depth {
            for j in 0..layer_size {
                let mut layer_value = F::zero();
                for p in 0..indices_to_combine.len() {
                    assert!(indices_to_combine[p] < num_children);
                    let value_to_add = layer[num_children * j + indices_to_combine[p]];
                    layer_value += value_to_add;
                }
                layer[j] = layer_value;
            }
            layer.truncate(layer_size);
            output.push(layer.clone());
            layer_size /= num_children;
        }
        output.reverse();
        output
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
            let mut local_output = vec![F::one(); col_count];
            for j in 0..d {
                let offset = (d - j - 1) * log_row_count;
                let index = (i >> offset) & (row_count - 1);
                let matrix_row = &matrices[j].evaluation_rows[index];

                local_output
                    .iter_mut()
                    .zip(matrix_row.iter())
                    .for_each(|(m_acc, m_curr)| *m_acc = mult_bb(m_acc, &m_curr));
            }
            let local_sum = local_output.iter().fold(F::zero(), |sum, val| sum + *val);
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
        OtherF: TowerField,
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
        OtherF: TowerField,
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

    /// Updates the challenge matrix with the terms required for computing round polynomial.
    /// Here's how it works: given a new challenge r, first we compute
    ///
    /// [1, r, r², ..., rᵈ]
    ///
    /// This should cost (d - 1) ee multiplications. Next we want to compute:
    ///
    /// [řᵈ,  řᵈ⁻¹.r,  řᵈ⁻².r²,  ...,  rᵈ]
    ///
    /// We use binomial expansion of řᵐ := (1 - r)ᵐ to compute the above terms without any
    /// additional ee multiplications (note that we will have constant times extension element).
    /// Applying a binomial expansion is basically a linear operation and hence we can represent it as
    /// vector-matrix product (eg d = 4).
    ///
    /// [řᵈ,  řᵈ⁻¹.r,  řᵈ⁻².r²,  ...,  rᵈ] = [1, r, r², ..., rᵈ] * ⌈  1  0  0  0  0 ⌉
    ///                                                            │ -4  1  0  0  0 │
    ///                                                            │  6 -3  1  0  0 │
    ///                                                            │ -4  3 -2  1  0 │
    ///                                                            ⌊  1 -1  1 -1  1 ⌋
    ///
    /// Now, we further want to apply interpolation maps on these values. Thus, we need:
    ///
    /// [L₀(r), L₁(r), L₂(r), ..., Lₔ(r)] =  [1, r, r², ..., rᵈ] * ⌈  1  0  0  0  0 ⌉   ⌈   6   0   0   0   0 ⌉
    ///                                                            │ -4  1  0  0  0 │   │  -3  12   6  -2  -1 │
    ///                                                            │  6 -3  1  0  0 │ * │  -6  -6   3   3   0 │
    ///                                                            │ -4  3 -2  1  0 │   │   3 -12  -3  -1   1 │
    ///                                                            ⌊  1 -1  1 -1  1 ⌋   ⌊   0   6   0   0   0 ⌋
    ///
    /// Note that we haven't shown the scaling factor (1/6) in the above equation.
    /// Our idea is to multiply the binomial and interpolation matrices beforehand, and use the
    /// result of that matrix multiplication (called as combined_binomial_and_interpolation_maps)
    /// to linearly combine challenge terms. This helps us save multiplications of negative numbers
    /// (when applying binomial maps) to challenges.
    ///
    pub fn update_with_challenge<P>(
        &mut self,
        challenge: F,
        interpolation_maps: &Vec<Box<dyn Fn(&Vec<F>) -> F>>,
        mult_fn: &P,
    ) where
        P: Fn(&F, &F) -> F,
    {
        let rows = self.no_of_rows;
        let cols = self.no_of_columns;
        assert_eq!(interpolation_maps.len(), cols);

        // Add a new row: [1, r, r^2, ..., r^{d-1}, r^d]
        self.evaluation_rows.push(vec![F::one()]);
        self.no_of_rows += 1;
        for i in 1..cols {
            let next_value = mult_fn(&self.evaluation_rows[rows][i - 1], &challenge);
            self.evaluation_rows[rows].push(next_value);
        }

        // Update the row with interpolation maps
        let original_row_clone = self.evaluation_rows[rows].clone();
        for i in 0..interpolation_maps.len() {
            self.evaluation_rows[rows][i] = interpolation_maps[i](&original_row_clone);
        }
    }
}

impl<F: TowerField> fmt::Debug for MatrixPolynomial<F> {
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
    use crate::{
        data_structures::{bit_extend, bit_extend_and_insert, LinearLagrange, LinearLagrangeList},
        tower_fields::{binius::BiniusTowerField, TowerField},
    };
    use itertools::izip;
    use rand::Rng;
    use BiniusTowerField as F;

    use super::{bit_decompose, MatrixPolynomial};

    pub fn random_field_element<F: TowerField>() -> F {
        let mut rng = rand::thread_rng();
        let random_u128: u128 = rng.gen();
        F::new(random_u128, None)
    }

    pub fn get_random_linear_lagrange<F: TowerField>() -> LinearLagrange<F> {
        LinearLagrange::new(&random_field_element(), &random_field_element())
    }

    pub fn flatten(input: &mut MatrixPolynomial<F>) {
        // Take ownership of the first row and replace it with an empty vector
        let mut flattened_row = std::mem::take(&mut input.evaluation_rows[0]);

        // Concatenate all other rows into the first row
        for row_index in 1..input.no_of_rows {
            flattened_row.extend_from_slice(&input.evaluation_rows[row_index]);
        }

        // Update the dimensions of the original matrix
        input.no_of_columns *= input.no_of_rows;
        input.no_of_rows = 1;

        // Replace the first row with the concatenated row
        input.evaluation_rows[0] = flattened_row;
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
            let expected_even = (F::one() - alpha) * linear_lagrange_vec[i].even
                + alpha * linear_lagrange_vec[i].odd;
            let expected_odd = (F::one() - alpha) * linear_lagrange_vec[size_after + i].even
                + alpha * linear_lagrange_vec[size_after + i].odd;

            assert_eq!(lagrange_list.list[i].even, expected_even);
            assert_eq!(lagrange_list.list[i].odd, expected_odd);
        }
    }

    #[test]
    fn test_matrix_polynomial_heighten() {
        let poly = F::rand_vector(8, Some(6));
        let mut matrix_poly = MatrixPolynomial::from_evaluations_vec(&poly);
        let mid_point = poly.len() / 2;
        let end_point = poly.len();

        assert_eq!(matrix_poly.no_of_rows, 2);
        assert_eq!(matrix_poly.no_of_columns, mid_point);
        assert_eq!(matrix_poly.evaluation_rows[0], poly[0..mid_point]);
        assert_eq!(matrix_poly.evaluation_rows[1], poly[mid_point..end_point]);

        // Test if heighten works as intended
        matrix_poly.heighten();
        assert_eq!(matrix_poly.evaluation_rows[0], poly[0..2]);
        assert_eq!(matrix_poly.evaluation_rows[1], poly[2..4]);
        assert_eq!(matrix_poly.evaluation_rows[2], poly[4..6]);
        assert_eq!(matrix_poly.evaluation_rows[3], poly[6..8]);
    }

    #[test]
    fn test_matrix_polynomial_flatten() {
        let poly = F::rand_vector(16, Some(4));
        let mut matrix_poly = MatrixPolynomial::from_evaluations_vec(&poly);

        // Test if flatten works as intended
        flatten(&mut matrix_poly);
        assert_eq!(matrix_poly.evaluation_rows[0], poly);
        assert_eq!(matrix_poly.no_of_columns, poly.len());
        assert_eq!(matrix_poly.no_of_rows, 1);
    }

    pub fn vector_hadamard(a: &Vec<F>, b: &Vec<F>) -> Vec<F> {
        assert_eq!(a.len(), b.len());
        a.iter().zip(b.iter()).map(|(ai, bi)| ai * bi).collect()
    }

    #[test]
    fn test_matrix_polynomial_tensor_hadamard() {
        let poly_a = F::rand_vector(8, Some(5));
        let matrix_poly_a = MatrixPolynomial::from_evaluations_vec(&poly_a);
        let poly_b = F::rand_vector(16, Some(5));
        let mut matrix_poly_b = MatrixPolynomial::from_evaluations_vec(&poly_b);
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
    fn test_merkle_sums() {
        let num_children: u64 = 5;
        let depth: u64 = 2;
        let num_evaluations: u64 = (num_children as usize).pow(depth as u32) as u64;
        let evaluations: Vec<F> = (0..num_evaluations)
            .map(|i: u64| F::from((i / num_children + 2) * (i % num_children + 1)))
            .collect();

        // Example tree of depth 2:
        //                                (a1 + a2 + b1 + b2)
        //
        //   [(a1 + a2)        (b1 + b2)       (c1 + c2)         (d1 + d2)        (e1 + e2)]
        //
        // [a1 a2 a3 a4 a5] [b1 b2 b3 b4 b5] [c1 c2 c3 c4 c5] [d1 d2 d3 d4 d5] [e1 e2 e3 e4 e5]
        // a(i) = 2i        b(i) = 3i        c(i) = 4i        d(i) = 5i        e(i) = 6i
        let merkle_sum_output =
            MatrixPolynomial::merkle_sums(&evaluations, num_children as usize, &vec![0, 1]);

        assert_eq!(merkle_sum_output.len(), depth as usize + 1);
        assert_eq!(merkle_sum_output[0], vec![F::from(15u64)]);
        assert_eq!(
            merkle_sum_output[1],
            vec![
                F::from(6u64),
                F::from(9u64),
                F::from(12u64),
                F::from(15u64),
                F::from(18u64)
            ]
        );
        assert_eq!(merkle_sum_output[2], evaluations);
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

        let mut matrix_poly_a = MatrixPolynomial::from_evaluations_vec(&evaluations_a);
        let mut matrix_poly_b = MatrixPolynomial::from_evaluations_vec(&evaluations_b);
        let mut matrix_poly_c = MatrixPolynomial::from_evaluations_vec(&evaluations_c);

        // First flatten all matrix polynomials
        flatten(&mut matrix_poly_a);
        flatten(&mut matrix_poly_b);
        flatten(&mut matrix_poly_c);

        let output_1 = MatrixPolynomial::tensor_inner_product(
            &vec![
                matrix_poly_a.clone(),
                matrix_poly_b.clone(),
                matrix_poly_c.clone(),
            ],
            &mult_bb,
        );

        let mut expected = F::zero();
        for (a, b, c) in izip!(&evaluations_a, &evaluations_b, &evaluations_c) {
            expected += a * b * c.clone();
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
                        expected += a * b * c.clone();
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
                        expected += a * b * c.clone();
                    }
                    let index = k + j * num_rows + i * num_rows * num_rows;
                    assert_eq!(expected, output_3[index as usize]);
                }
            }
        }
    }

    #[test]
    fn test_matrix_polynomial_collapse() {
        let poly = F::rand_vector(16, Some(4));
        let mut matrix_poly = MatrixPolynomial::from_evaluations_vec(&poly);

        // Reduce number of columns by half
        matrix_poly.heighten();

        // Apply collapse function
        matrix_poly.collapse();

        assert_eq!(matrix_poly.no_of_columns, 1);
        assert_eq!(matrix_poly.no_of_rows, 4);
        assert_eq!(
            matrix_poly.evaluation_rows[0][0],
            poly[0..4].iter().fold(F::zero(), |acc, e| acc + e.clone())
        );
        assert_eq!(
            matrix_poly.evaluation_rows[1][0],
            poly[4..8].iter().fold(F::zero(), |acc, e| acc + e.clone())
        );
        assert_eq!(
            matrix_poly.evaluation_rows[2][0],
            poly[8..12].iter().fold(F::zero(), |acc, e| acc + e.clone())
        );
        assert_eq!(
            matrix_poly.evaluation_rows[3][0],
            poly[12..16]
                .iter()
                .fold(F::zero(), |acc, e| acc + e.clone())
        );
    }

    #[test]
    fn test_matrix_polynomial_dot_product() {
        let poly_a = F::rand_vector(16, Some(4));
        let matrix_poly_a = MatrixPolynomial::from_evaluations_vec(&poly_a);
        let poly_b = F::rand_vector(16, Some(4));
        let matrix_poly_b = MatrixPolynomial::from_evaluations_vec(&poly_b);
        fn mult_be(left: &F, right: &F) -> F {
            left * right
        }

        let computed = MatrixPolynomial::dot_product(&matrix_poly_a, &matrix_poly_b, &mult_be);
        let expected = poly_a
            .iter()
            .zip(poly_b.iter())
            .fold(F::zero(), |acc, (a, b)| acc + a * b);
        assert_eq!(computed, expected);
    }

    #[test]
    fn test_matrix_polynomial_scale_and_squash() {
        let poly_a = F::rand_vector(32, Some(5));
        let mut matrix_poly_a = MatrixPolynomial::from_evaluations_vec(&poly_a);
        fn mult_be(left: &F, right: &F) -> F {
            left * right
        }

        // Heighten a
        matrix_poly_a.heighten(); // no of rows = 4
        matrix_poly_a.heighten(); // no of rows = 8

        // Create a challenge array with 4 rows, 1 column
        let poly_b = F::rand_vector(8, Some(4));
        let mut matrix_poly_b = MatrixPolynomial::from_evaluations_vec(&poly_b);
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
                .zip(poly_b.iter())
                .fold(F::zero(), |acc, (a_val, b_val)| {
                    acc + mult_be(&a_val, &b_val)
                });
            expected.push(expected_j);
        }
        assert_eq!(computed, LinearLagrangeList::<F>::from_vector(&expected));
    }

    #[test]
    fn test_update_with_challenge() {
        fn mult_bb(left: &F, right: &F) -> F {
            left * right
        }

        let col_size = 10;
        let mut sample: MatrixPolynomial<F> = MatrixPolynomial::<F> {
            no_of_rows: 0,
            no_of_columns: col_size,
            evaluation_rows: Vec::with_capacity(1),
        };

        // Simple map that chooses x[i + 2]
        fn get_projective_imap(index: usize) -> Box<dyn Fn(&Vec<F>) -> F> {
            let col_size = 10;
            Box::new(move |x: &Vec<F>| -> F { x[(index + 2) % col_size].clone() })
        }

        // Simple permutation map
        let interpolation_maps: Vec<Box<dyn Fn(&Vec<F>) -> F>> =
            (0..col_size).map(|i| get_projective_imap(i)).collect();

        let r: F = random_field_element();
        sample.update_with_challenge(r, &interpolation_maps, &mult_bb);
        assert_eq!(sample.no_of_rows, 1);
        assert_eq!(sample.no_of_columns, col_size);

        let mut multiplicand = F::one();
        for i in 0..col_size {
            let offset = col_size - 2;
            assert_eq!(
                sample.evaluation_rows[0][(offset + i) % col_size],
                multiplicand
            );
            multiplicand *= r;
        }
    }
}
