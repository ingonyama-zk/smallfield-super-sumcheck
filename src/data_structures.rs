use std::vec;

use ark_std::{
    fmt::{self, Formatter},
    iterable::Iterable,
    log2,
};

use ark_ff::Field;
use ark_poly::DenseMultilinearExtension;

/// Computes n!
fn factorial(n: u64) -> u64 {
    (1..=n).product()
}

/// Computes ⁿCᵣ := n! / (r! * (n - r)!)
fn count_combinations(n: u64, r: u64) -> u64 {
    factorial(n) / (factorial(r) * factorial(n - r))
}

/// Computes [ⁿC₀, ⁿC₁, ..., ⁿCₙ]
fn get_binomial_combinations(n: u64) -> Vec<u64> {
    (0..n + 1).map(|k| count_combinations(n, k)).collect()
}

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

pub fn bit_decompose_with_base(base: usize, input: usize, num_bytes: u32) -> Vec<usize> {
    let mut output: Vec<usize> = Vec::with_capacity(num_bytes as usize);
    let mut divisor = 1;
    for _ in 0..num_bytes {
        let byte_i = (input / divisor) % base;
        divisor *= base;
        output.push(byte_i);
    }
    output
}

pub fn bit_reverse(base: usize, input: usize, num_bytes: u32) -> usize {
    let mut result: usize = 0;
    let mut divisor = 1;
    let mut multiplicand = base.pow(num_bytes - 1);
    for _ in 0..num_bytes {
        let byte_i = (input / divisor) % base;
        result += byte_i * multiplicand;
        divisor *= base;
        multiplicand /= base;
    }
    result
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

    pub fn ones(given_no_of_rows: usize, given_no_of_columns: usize) -> Self {
        MatrixPolynomial {
            no_of_rows: given_no_of_rows,
            no_of_columns: given_no_of_columns,
            evaluation_rows: vec![vec![F::ONE; given_no_of_columns]; given_no_of_rows],
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

    #[flame]
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

    #[flame]
    pub fn get_combined_map(
        index_j: usize,
        depth: u32,
        mappings: &Vec<Box<dyn Fn(&F, &F) -> F>>,
    ) -> Vec<F> {
        let num_maps = mappings.len();
        let index_j_bytes = bit_decompose_with_base(num_maps, index_j, depth);
        let mut a_values: Vec<F> = Vec::with_capacity(depth as usize);
        let mut b_values: Vec<F> = Vec::with_capacity(depth as usize);
        for i in 0..depth {
            let index_byte = index_j_bytes[i as usize];
            let ai = mappings[index_byte](&F::ONE, &F::zero());
            let bi = mappings[index_byte](&F::zero(), &F::ONE);
            a_values.push(ai);
            b_values.push(bi);
        }

        let row_size = (1u32 << depth) as usize;
        let mut res: Vec<F> = Vec::with_capacity(row_size);
        for j in 0..row_size {
            let mut output_value = F::ONE;
            let j_bits = bit_decompose_with_base(2, j, depth);
            for k in 0..(depth as usize) {
                if j_bits[k] == 0 {
                    output_value *= a_values[k];
                } else {
                    output_value *= b_values[k];
                }
            }
            res.push(output_value);
        }
        res
    }

    #[flame]
    pub fn get_combined_map_u16(
        index_j: usize,
        depth: u32,
        mappings: &Vec<Box<dyn Fn(&F, &F) -> F>>,
    ) -> Vec<u16> {
        let num_maps = mappings.len();
        let index_j_bytes = bit_decompose_with_base(num_maps, index_j, depth);
        let mut a_values: Vec<u8> = Vec::with_capacity(depth as usize);
        let mut b_values: Vec<u8> = Vec::with_capacity(depth as usize);
        for i in 0..depth {
            let index_byte = index_j_bytes[i as usize];
            // Assuming `a` is your field element
            let ai = mappings[index_byte](&F::ONE, &F::zero());
            let mut a_buf = vec![];
            ai.serialize_compressed(&mut a_buf).unwrap();

            let bi = mappings[index_byte](&F::zero(), &F::ONE);
            let mut b_buf = vec![];
            bi.serialize_compressed(&mut b_buf).unwrap();

            a_values.push(a_buf[0]);
            b_values.push(b_buf[0]);
        }

        let row_size = (1u32 << depth) as usize;
        let mut res: Vec<u16> = Vec::with_capacity(row_size);
        for j in 0..row_size {
            let mut output_value = 1u16;
            let j_bits = bit_decompose_with_base(2, j, depth);
            for k in 0..(depth as usize) {
                if j_bits[k] == 0 {
                    output_value *= a_values[k] as u16;
                } else {
                    output_value *= b_values[k] as u16;
                }
            }
            res.push(output_value);
        }
        res
    }

    pub fn mult_small_with_big(small: &u16, big: &F) -> F {
        let mut accumulator = F::zero();
        let mut power = *big;
        let mut small_bits = bit_decompose(*small as usize, 16, 1);
        small_bits.reverse();

        for bit in small_bits {
            if bit == 1 {
                accumulator += power;
            }
            power += power;
        }
        accumulator
    }

    #[flame]
    pub fn apply_map_faster(
        input_polynomial: &MatrixPolynomial<F>,
        index_j: usize,
        mappings: &Vec<Box<dyn Fn(&F, &F) -> F>>,
    ) -> MatrixPolynomial<F> {
        // Fetch parameters.
        // num_maps: (d + 1)
        // depth: round number p
        let depth = log2(input_polynomial.no_of_rows);
        // let bitmask = ((1 as usize) << num_maps) - 1;

        // Output is a vector: { merkle( f(*, x), j ) }
        // where x ∈ {0, 1}^{l - p}
        let mut output = MatrixPolynomial {
            no_of_rows: 1,
            no_of_columns: input_polynomial.no_of_columns,
            evaluation_rows: vec![Vec::with_capacity(input_polynomial.no_of_columns); 1],
        };

        let combined_map_j = MatrixPolynomial::get_combined_map(index_j, depth, &mappings);
        flame::start("applying_maps");
        for col_idx in 0..input_polynomial.no_of_columns {
            let combined_map_times_input = input_polynomial
                .evaluation_rows
                .iter()
                .zip(combined_map_j.iter())
                .fold(F::zero(), |acc, (row, map_value)| {
                    acc + row[col_idx] * map_value
                });
            output.evaluation_rows[0].push(combined_map_times_input);
        }
        flame::end("applying_maps");
        output
    }

    #[flame]
    pub fn apply_map(
        input_polynomial: &MatrixPolynomial<F>,
        index_j: usize,
        mappings: &Vec<Box<dyn Fn(&F, &F) -> F>>,
    ) -> MatrixPolynomial<F> {
        // Fetch parameters.
        // num_maps: (d + 1)
        // depth: round number p
        let depth = log2(input_polynomial.no_of_rows);
        // let bitmask = ((1 as usize) << num_maps) - 1;

        // Output is a vector: { merkle( f(*, x), j ) }
        // where x ∈ {0, 1}^{l - p}
        let mut output = MatrixPolynomial {
            no_of_rows: 1,
            no_of_columns: input_polynomial.no_of_columns,
            evaluation_rows: vec![Vec::with_capacity(input_polynomial.no_of_columns); 1],
        };

        let combined_map_j = MatrixPolynomial::get_combined_map(index_j, depth, &mappings);
        flame::start("applying_maps");
        for col_idx in 0..input_polynomial.no_of_columns {
            let combined_map_times_input = input_polynomial
                .evaluation_rows
                .iter()
                .zip(combined_map_j.iter())
                .fold(F::zero(), |acc, (row, map_value)| {
                    acc + row[col_idx] * map_value
                });
            output.evaluation_rows[0].push(combined_map_times_input);
        }
        flame::end("applying_maps");
        output
    }

    ///
    /// a0 --
    ///      |-- [b0, b1, b2, b3, b4] --
    /// a1 --                           |
    ///                                 |-- [b0c0_0, b0c0_1, b0c0_2, b0c0_3, b0c0_4]
    ///                                 |   [b1c1_0, b1c1_1, b1c1_2, b1c1_3, b1c1_4]
    /// a2 --                           |
    ///      |-- [c0, c1, c2, c3, c4] --
    /// a3 --
    pub fn apply_recursive_maps(
        input: &Vec<F>,
        mappings: &Vec<Box<dyn Fn(&F, &F) -> F>>,
        projection_mapping_indices: &Vec<usize>,
    ) -> Vec<F> {
        let input_size = input.len();
        assert!(input_size.is_power_of_two());
        let num_maps = mappings.len();
        let num_proj_maps = projection_mapping_indices.len();
        assert!(num_proj_maps == 2);
        assert_eq!(projection_mapping_indices, &vec![0, 1]);

        let depth = log2(input_size) as usize;
        let mut intermediate = input.clone();
        for i in 0..depth {
            println!("inter[{}]\n{:?}", i, intermediate);
            assert!(intermediate.len() & 1 == 0);
            let step_size = intermediate.len() / 2;
            let mut temporary: Vec<F> = Vec::with_capacity(step_size * num_maps);
            for j in 0..step_size {
                let mut index_a = j;
                let mut index_b = j + step_size;
                if i == 0 {
                    index_a = 2 * j;
                    index_b = 2 * j + 1;
                }
                for map in mappings {
                    let map_result = map(&intermediate[index_a], &intermediate[index_b]);
                    temporary.push(map_result);
                }
            }
            intermediate = temporary;
        }
        intermediate
    }

    #[flame]
    pub fn compute_merkle_roots(
        input_polynomial: &MatrixPolynomial<F>,
        index_j: usize,
        mappings: &Vec<Box<dyn Fn(&F, &F) -> F>>,
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

    #[flame]
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

    #[flame]
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

    #[flame]
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

    #[flame]
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

    #[flame]
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
        self.evaluation_rows.push(vec![F::from(1 as u32)]);
        self.no_of_rows += 1;
        for i in 1..cols {
            let next_value = mult_fn(&self.evaluation_rows[rows][i - 1], &challenge);
            self.evaluation_rows[rows].push(next_value);
        }

        // Update the powers to:
        // 0:   ř^{d}
        // 1:   ř^{d-1} * r
        // 2:   ř^{d-2} * r^2
        // 3:   ř^{d-3} * r^3
        // ...
        // ...
        // d-1: ř^{1} * r^{d-1}
        // d:   r^{d}
        //
        // using binomial theorem.
        let mut updated_row: Vec<F> = Vec::with_capacity(cols);
        for i in 0..cols {
            let start_idx: usize = cols - i - 1;
            let end_idx: usize = cols - 1;

            let combinations = get_binomial_combinations(i as u64);
            assert_eq!(combinations.len(), i + 1);

            let mut result = F::from(0 as u32);
            for j in start_idx..=end_idx {
                let current_value = self.evaluation_rows[rows][j];
                let is_negative = (j - start_idx) & 1 == 1;
                if is_negative {
                    result -= current_value * F::from(combinations[j - start_idx]);
                } else {
                    result += current_value * F::from(combinations[j - start_idx]);
                }
            }
            updated_row.push(result);
        }
        updated_row.reverse();

        // Update the row with interpolation maps
        let updated_row_clone = updated_row.clone();
        for i in 0..interpolation_maps.len() {
            updated_row[i] = interpolation_maps[i](&updated_row_clone);
        }

        self.evaluation_rows[rows] = updated_row;
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
    use std::vec;

    use crate::data_structures::{
        bit_decompose_with_base, bit_extend, bit_extend_and_insert, LinearLagrange,
        LinearLagrangeList,
    };
    use ark_bls12_381::Fr as F;
    use ark_ff::{Field, Zero};
    use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
    use ark_std::log2;
    use itertools::izip;
    use rand::Rng;

    use super::{bit_decompose, bit_reverse, MatrixPolynomial};

    pub fn random_field_element<F: Field>() -> F {
        let mut rng = rand::thread_rng();
        let random_u128: u128 = rng.gen();
        F::from(random_u128)
    }

    pub fn get_random_linear_lagrange<F: Field>() -> LinearLagrange<F> {
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
    fn test_bit_decompose_with_base() {
        // 5617  =>  (001)(010)(111)(110)(001)
        let input: usize = 5617;
        let num_bytes = 5;
        let base = 8;
        let out1 = bit_decompose_with_base(base, input, num_bytes);
        assert_eq!(out1[0], 1);
        assert_eq!(out1[1], 6);
        assert_eq!(out1[2], 7);
        assert_eq!(out1[3], 2);
        assert_eq!(out1[4], 1);

        // input: 3 4 2 0 1 4 1
        let base2: usize = 5;
        let mut input2: usize = 0;
        input2 += 1 * base2.pow(0);
        input2 += 4 * base2.pow(1);
        input2 += 1 * base2.pow(2);
        input2 += 0 * base2.pow(3);
        input2 += 2 * base2.pow(4);
        input2 += 4 * base2.pow(5);
        input2 += 3 * base2.pow(6);

        let out2 = bit_decompose_with_base(base2, input2, 7);
        assert_eq!(out2[0], 1);
        assert_eq!(out2[1], 4);
        assert_eq!(out2[2], 1);
        assert_eq!(out2[3], 0);
        assert_eq!(out2[4], 2);
        assert_eq!(out2[5], 4);
        assert_eq!(out2[6], 3);
    }

    #[test]
    fn test_bit_reverse() {
        // 5617  =>  (001)(010)(111)(110)(001)
        let input: usize = 5617;
        let num_bytes = 5;
        let base = 8;
        let out1 = bit_reverse(base, input, num_bytes);
        // bit_reverse(5617) => (001)(110)(111)(010)(001)
        assert_eq!(out1, 7633);

        // input: 3 4 2 0 1 4 1
        let base2: usize = 5;
        let mut input2: usize = 0;
        input2 += 1 * base2.pow(0);
        input2 += 4 * base2.pow(1);
        input2 += 1 * base2.pow(2);
        input2 += 0 * base2.pow(3);
        input2 += 2 * base2.pow(4);
        input2 += 4 * base2.pow(5);
        input2 += 3 * base2.pow(6);

        let mut exp2 = 0;
        exp2 += 3 * base2.pow(0);
        exp2 += 4 * base2.pow(1);
        exp2 += 2 * base2.pow(2);
        exp2 += 0 * base2.pow(3);
        exp2 += 1 * base2.pow(4);
        exp2 += 4 * base2.pow(5);
        exp2 += 1 * base2.pow(6);
        let out2 = bit_reverse(base2, input2, 7);
        assert_eq!(out2, exp2);

        // input: 1 0
        let mut input3: usize = 0;
        input3 += 0 * base2.pow(0);
        input3 += 1 * base2.pow(1);

        // expect: 0 1
        let mut exp3 = 0;
        exp3 += 1 * base2.pow(0);
        exp3 += 0 * base2.pow(1);
        let out3 = bit_reverse(base2, input3, 2);
        assert_eq!(out3, exp3);
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
        flatten(&mut matrix_poly);
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
        assert_eq!(merkle_sum_output[0], vec![F::from(15)]);
        assert_eq!(
            merkle_sum_output[1],
            vec![
                F::from(6),
                F::from(9),
                F::from(12),
                F::from(15),
                F::from(18)
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

        fn get_projective_imap(index: usize) -> Box<dyn Fn(&Vec<F>) -> F> {
            Box::new(move |x: &Vec<F>| -> F { x[index].clone() })
        }

        let interpolation_maps: Vec<Box<dyn Fn(&Vec<F>) -> F>> =
            (0..col_size).map(|i| get_projective_imap(i)).collect();

        let r: F = random_field_element();
        sample.update_with_challenge(r, &interpolation_maps, &mult_bb);
        assert_eq!(sample.no_of_rows, 1);
        assert_eq!(sample.no_of_columns, col_size);

        let scaling_factor: F = (F::ONE - r) * r.inverse().unwrap();
        let mut r_pow_d = F::ONE;
        for _ in 1..col_size {
            r_pow_d *= r;
        }

        let mut multiplicand = F::ONE;
        for i in 0..col_size {
            assert_eq!(
                sample.evaluation_rows[0][col_size - i - 1],
                multiplicand * r_pow_d
            );
            multiplicand *= scaling_factor;
        }
    }

    #[test]
    fn test_get_combined_map() {
        let depth = 3;
        let num_evals = 5;
        let mut mappings: Vec<Box<dyn Fn(&F, &F) -> F>> = Vec::with_capacity(num_evals);
        mappings.push(Box::new(move |x: &F, _y: &F| -> F { *x }));
        mappings.push(Box::new(move |_x: &F, y: &F| -> F { *y }));
        mappings.push(Box::new(move |x: &F, y: &F| -> F { *x + F::from(2) * *y }));
        mappings.push(Box::new(move |x: &F, y: &F| -> F { F::from(5) * *x + *y }));
        mappings.push(Box::new(move |x: &F, y: &F| -> F { *x + *y }));

        let out1 = MatrixPolynomial::get_combined_map(17, depth, &mappings);
        println!("out1 = {:?}", out1);
    }

    #[test]
    fn test_get_combined_map_u16() {
        let depth = 3;
        let num_evals = 5;
        let mut mappings: Vec<Box<dyn Fn(&F, &F) -> F>> = Vec::with_capacity(num_evals);
        mappings.push(Box::new(move |x: &F, _y: &F| -> F { *x }));
        mappings.push(Box::new(move |_x: &F, y: &F| -> F { *y }));
        mappings.push(Box::new(move |x: &F, y: &F| -> F { *x + F::from(2) * *y }));
        mappings.push(Box::new(move |x: &F, y: &F| -> F { F::from(5) * *x + *y }));
        mappings.push(Box::new(move |x: &F, y: &F| -> F { *x + *y }));

        let out1 = MatrixPolynomial::get_combined_map_u16(17, depth, &mappings);
        println!("out1 = {:?}", out1);
    }

    #[test]
    fn test_mult_small_big() {
        let small: u16 = 7;
        let big: F = random_field_element();
        let output: F = MatrixPolynomial::mult_small_with_big(&small, &big);
        let expected: F = F::from(small) * big;
        assert_eq!(output, expected);
    }

    #[test]
    fn test_apply_recursive_maps() {
        let input: Vec<F> = vec![
            F::from(2),
            F::from(7),
            F::from(12),
            F::from(9),
            F::from(1),
            F::from(4),
            F::from(5),
            F::from(8),
            F::from(2),
            F::from(7),
            F::from(12),
            F::from(9),
            F::from(1),
            F::from(4),
            F::from(5),
            F::from(8),
        ];
        let num_vars = log2(input.len());
        let num_evals = 5;
        let mut mappings: Vec<Box<dyn Fn(&F, &F) -> F>> = Vec::with_capacity(num_evals);
        mappings.push(Box::new(move |x: &F, _y: &F| -> F { *x }));
        mappings.push(Box::new(move |_x: &F, y: &F| -> F { *y }));
        mappings.push(Box::new(move |x: &F, y: &F| -> F { *x + F::from(2) * *y }));
        mappings.push(Box::new(move |x: &F, y: &F| -> F { F::from(5) * *x + *y }));
        mappings.push(Box::new(move |x: &F, y: &F| -> F { *x + *y }));

        let out = MatrixPolynomial::apply_recursive_maps(&input, &mappings, &vec![0, 1]);
        println!("output = {:?}", out);
        println!("out_len = {}", out.len());

        let mut input_matrix = MatrixPolynomial::from_dense_mle(
            &DenseMultilinearExtension::from_evaluations_vec(num_vars as usize, input.clone()),
        );
        input_matrix.heighten();
        input_matrix.heighten();
        let num_product_terms = num_evals.pow(num_vars);
        let mut merkle_vec: Vec<F> = Vec::with_capacity(num_product_terms);
        let mut other_vec: Vec<F> = Vec::with_capacity(num_product_terms);
        for j in 0..num_product_terms {
            let merkle_root = MatrixPolynomial::compute_merkle_roots(&input_matrix, j, &mappings);
            let apply_map_to_input = MatrixPolynomial::apply_map(&input_matrix, j, &mappings);
            merkle_vec.push(merkle_root.evaluation_rows[0][0]);
            other_vec.push(apply_map_to_input.evaluation_rows[0][0]);
        }
        println!("merkle:\n{:?}", merkle_vec);
        println!("merkle_len = {}", merkle_vec.len());
        println!("other:\n{:?}", other_vec);
        println!("other_len = {}", other_vec.len());
        println!("var = {}", num_vars);
        assert_eq!(merkle_vec, other_vec);

        // // let factor = num_product_terms / num_evals;
        // for i in 0..num_product_terms {
        //     // factor /= num_evals;
        //     println!("i = {}", i);
        //     let irev = bit_reverse(num_evals, i, num_vars);
        //     println!("irev = {}", irev);
        //     // println!("factor = {}", factor);
        //     assert_eq!(merkle_vec[i], out[irev]);
        // }
    }
}
