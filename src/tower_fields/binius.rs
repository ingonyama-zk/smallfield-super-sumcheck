use std::{
    fmt,
    iter::{Product, Sum},
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub},
};

use num::{One, Zero};
use rand::Rng;

use super::TowerField;

/// The constant lookup table for inverses in F(2^4)
/// Elements 1 through 15 correspond to the field elements 1, ..., 15 in F(2^4)
/// Invserse of 0 should throw an error.
const F2_4_INVERSE: [u128; 15] = [1, 3, 2, 6, 14, 4, 15, 13, 10, 9, 12, 11, 8, 5, 7];

/// Precomputed multiplication table for GF(16) (Level 2)
/// `GF16_MULT_TABLE[a][b]` gives a * b in GF(16).
const GF16_MULT_TABLE: [[u8; 16]; 16] = [
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [0, 2, 3, 1, 8, 10, 11, 9, 12, 14, 15, 13, 4, 6, 7, 5],
    [0, 3, 1, 2, 12, 15, 13, 14, 4, 7, 5, 6, 8, 11, 9, 10],
    [0, 4, 8, 12, 9, 13, 1, 5, 14, 10, 6, 2, 7, 3, 15, 11],
    [0, 5, 10, 15, 13, 8, 7, 2, 6, 3, 12, 9, 11, 14, 1, 4],
    [0, 6, 11, 13, 1, 7, 10, 12, 2, 4, 9, 15, 3, 5, 8, 14],
    [0, 7, 9, 14, 5, 2, 12, 11, 10, 13, 3, 4, 15, 8, 6, 1],
    [0, 8, 12, 4, 14, 6, 2, 10, 7, 15, 11, 3, 9, 1, 5, 13],
    [0, 9, 14, 7, 10, 3, 4, 13, 15, 6, 1, 8, 5, 12, 11, 2],
    [0, 10, 15, 5, 6, 12, 9, 3, 11, 1, 4, 14, 13, 7, 2, 8],
    [0, 11, 13, 6, 2, 9, 15, 4, 3, 8, 14, 5, 1, 10, 12, 7],
    [0, 12, 4, 8, 7, 11, 3, 15, 9, 5, 13, 1, 14, 2, 10, 6],
    [0, 13, 6, 11, 3, 14, 5, 8, 1, 12, 7, 10, 2, 15, 4, 9],
    [0, 14, 7, 9, 15, 1, 8, 6, 5, 11, 2, 12, 10, 4, 13, 3],
    [0, 15, 5, 10, 11, 4, 14, 1, 13, 2, 8, 7, 6, 9, 3, 12],
];

#[derive(Copy, Clone, Eq)]
pub struct BiniusTowerField {
    val: u128,         // To store the value in the field
    num_levels: usize, // Number of levels in the binary tower
    num_bits: usize,   // Number of bits based on num_levels
}

impl TowerField for BiniusTowerField {
    // Constructor
    fn new(val: u128, num_levels: Option<usize>) -> Self {
        let computed_levels = match num_levels {
            Some(levels) => levels,
            None => {
                let log2_val = (val as f64).log2().log2().ceil();
                log2_val as usize + 1
            }
        };

        assert!(computed_levels < 8, "Number of bits cannot exceed 128.");

        let num_bits = 1 << computed_levels;
        let modulus_mask = if num_bits >= 128 {
            u128::MAX
        } else {
            (1u128 << num_bits) - 1u128
        };

        BiniusTowerField {
            val: val & modulus_mask,
            num_levels: computed_levels,
            num_bits,
        }
    }

    // Generate a random BiniusTowerField with a random value
    // TODO: add rng as a param.
    fn rand(num_levels: Option<usize>) -> Self {
        let mut rng = rand::thread_rng();
        let random_val = rng.gen::<u128>(); // Generate a random u128 value
        BiniusTowerField::new(random_val, num_levels) // Use the constructor with the random value
    }

    // Generate a vector of random BiniusTowerField elements
    fn rand_vector(size: usize, num_levels: Option<usize>) -> Vec<Self> {
        (0..size)
            .map(|_| BiniusTowerField::rand(num_levels)) // Generate random elements
            .collect() // Collect them into a vector
    }

    // Generate a random BiniusTowerField with a non-zero value
    // TODO: add rng as a param.
    fn rand_non_zero(num_levels: Option<usize>) -> Self {
        let mut rng = rand::thread_rng();
        // Generate a non-zero random value
        loop {
            let val = rng.gen::<u128>();
            let output = BiniusTowerField::new(val, num_levels);
            if output.get_val() != 0u128 {
                return output;
            }
        }
    }

    // New implementation for non-zero random vector generation
    fn rand_vector_non_zero(size: usize, num_levels: Option<usize>) -> Vec<Self> {
        (0..size)
            .map(|_| BiniusTowerField::rand_non_zero(num_levels))
            .collect()
    }

    // Extend the number of levels in the tower
    fn extend_num_levels(&mut self, new_levels: usize) {
        assert!(self.num_levels <= new_levels);
        self.set_num_levels(new_levels);
    }

    // Set new levels
    fn set_num_levels(&mut self, new_levels: usize) {
        self.num_levels = new_levels;
        self.num_bits = 1 << self.num_levels;
    }

    // Get the value (equivalent to val method)
    fn get_val(&self) -> u128 {
        self.val
    }

    // Return the binary representation of the value, padded with zeros
    fn bin(&self) -> String {
        format!("{:0width$b}", self.val, width = self.num_bits)
    }

    // Split the value into high and low parts
    fn split(&self) -> (BiniusTowerField, BiniusTowerField) {
        let bin_val = self.bin();
        let half_bits = self.num_bits / 2;

        let hi_val = u128::from_str_radix(&bin_val[..half_bits], 2).unwrap();
        let lo_val = u128::from_str_radix(&bin_val[half_bits..], 2).unwrap();

        let hi = BiniusTowerField::new(hi_val, Some(self.num_levels - 1));
        let lo = BiniusTowerField::new(lo_val, Some(self.num_levels - 1));

        (hi, lo)
    }

    // Joins high and low parts
    fn join(&self, other: &Self) -> Self {
        let hi = self.clone();
        let lo = other.clone();
        assert_eq!(hi.num_levels, lo.num_levels);
        assert_eq!(hi.num_bits, lo.num_bits);
        Self::new((hi.val << hi.num_bits) + lo.val, Some(hi.num_levels + 1))
    }

    // Equality check
    fn equals(&self, other: &BiniusTowerField) -> bool {
        self.val == other.get_val()
    }

    fn inverse(&self) -> Option<Self> {
        // Inverse of 0 doesn't exist, exit right away.
        if self.equals(&BiniusTowerField::new(0u128, Some(0))) {
            return None;
        }

        // Base case: 4-bit inverses are stored in a lookup table.
        if self.num_levels <= 2 {
            return Some(BiniusTowerField::new(
                F2_4_INVERSE[self.val as usize - 1],
                Some(2),
            ));
        }

        // Recursion:
        let (a_hi, a_lo) = self.split();
        let two_pow_k_minus_one = Self::new(1 << (self.num_bits / 4), Some(self.num_levels - 1));

        // a = a_hi * x_k  +  a_lo
        // a_lo_next = a_hi * x_{k - 1}  +  a_lo
        let a_lo_next = a_lo.clone() + a_hi.clone() * two_pow_k_minus_one;

        // Δ = a_lo * a_lo_next + a_hi^2
        let delta = a_lo.clone() * a_lo_next.clone() + a_hi.clone() * a_hi.clone();
        let delta_inverse = delta.inverse().unwrap();

        let out_hi = delta_inverse.clone() * a_hi;
        let out_lo = delta_inverse * a_lo_next;
        Some(out_hi.join(&out_lo))
    }

    fn pow(&self, exp: u32) -> Self {
        let mut output = Self::one();
        // Original simple iterative pow for BiniusTowerField
        for _ in 0..exp {
            output *= self.clone();
        }
        output
    }

    fn mul_abstract(
        a_hi: &Self,
        a_lo: &Self,
        a_sum: &Self,
        b_hi: &Self,
        b_lo: &Self,
        b_sum: &Self,
    ) -> Self {
        // Perform modular operations based on: x_i^2 = x_i * x_{i-1} + 1
        let mut mx = a_hi * b_hi; // mx = a_hi * b_hi
        let mut lo = a_lo * b_lo; // lo = a_lo * b_lo
        let mx_num_levels = mx.num_levels;
        let mx_num_bits = mx.num_bits;
        lo += mx.clone();

        // mx * 2^(mx.num_half_bits())
        mx = mx * Self::new(1 << (mx_num_bits / 2), Some(mx_num_levels));

        // Perform hi operations
        let mut hi = a_sum * b_sum; // hi = a_sum * b_sum
        hi = hi + (lo.clone() + mx); // hi += lo + mx

        // Concatenate hi and lo by shifting hi to make space for lo
        hi.join(&lo)
    }
}

// Implementing the `Zero` trait for `BiniusTowerField`
impl Zero for BiniusTowerField {
    // Returns the "zero" value for BiniusTowerField
    fn zero() -> Self {
        Self::new(0u128, Some(0))
    }

    // Checks if the value is zero
    fn is_zero(&self) -> bool {
        *self == Self::zero()
    }
}

// Implementing the `One` trait for `BiniusTowerField`
impl One for BiniusTowerField {
    // Returns the "zero" value for BiniusTowerField
    fn one() -> Self {
        Self::new(1u128, Some(0))
    }

    // Checks if the value is zero
    fn is_one(&self) -> bool {
        *self == Self::one()
    }
}

impl AddAssign for BiniusTowerField {
    fn add_assign(&mut self, other: BiniusTowerField) {
        let mut other_copy = other.clone();

        // Align num_levels to max
        if self.num_levels > other_copy.num_levels {
            other_copy.extend_num_levels(self.num_levels);
        } else if other_copy.num_levels > self.num_levels {
            self.extend_num_levels(other_copy.num_levels);
        }

        // XOR the values for addition and mutate `self`
        self.val ^= other_copy.val;
    }
}

impl Add for BiniusTowerField {
    type Output = BiniusTowerField;

    fn add(mut self, other: BiniusTowerField) -> BiniusTowerField {
        self += other; // This uses `add_assign` internally
        self
    }
}

impl<'a> Add<&'a BiniusTowerField> for &'a BiniusTowerField {
    type Output = BiniusTowerField;

    fn add(self, other: &BiniusTowerField) -> BiniusTowerField {
        let mut result = self.clone(); // Clone self to avoid mutation
        result += other.clone(); // Use add_assign for addition logic
        result
    }
}

// Alias subtraction to addition
impl Sub for BiniusTowerField {
    type Output = BiniusTowerField;

    fn sub(self, other: BiniusTowerField) -> BiniusTowerField {
        self + other
    }
}

// Implementing Neg
impl Neg for BiniusTowerField {
    type Output = BiniusTowerField;

    fn neg(self) -> BiniusTowerField {
        self
    }
}

impl MulAssign for BiniusTowerField {
    // TODO: check why (a * b) * c ≠ a * (b * c) in some cases
    fn mul_assign(&mut self, other: BiniusTowerField) {
        let mut other_copy = other.clone();

        // Align num_levels to max
        // TODO: can make mult more efficient by performing "partial" mult, i.e. a * b
        // where a is "smaller" than b (in terms of num_levels).
        if self.num_levels > other_copy.num_levels {
            other_copy.extend_num_levels(self.num_levels);
        } else if other_copy.num_levels > self.num_levels {
            self.extend_num_levels(other_copy.num_levels);
        }

        // Optimizations for 0 or 1
        if self.val == 0 || other_copy.val == 1 {
            return;
        } else if self.val == 1 || other_copy.val == 0 {
            *self = other_copy;
            return;
        }

        // If num_levels is greater than 1, perform higher-order multiplication
        if self.num_levels > 1 || other_copy.num_levels > 1 {
            let (a_hi, a_lo) = self.split();
            let (b_hi, b_lo) = other_copy.split();
            let a_sum = a_hi.clone() + a_lo.clone();
            let b_sum = b_hi.clone() + b_lo.clone();

            *self = BiniusTowerField::mul_abstract(&a_hi, &a_lo, &a_sum, &b_hi, &b_lo, &b_sum);
        } else {
            // 2-bit multiplication case
            let a_hi = u128::from_str_radix(&self.bin()[..1], 2).unwrap();
            let a_lo = u128::from_str_radix(&self.bin()[1..2], 2).unwrap();
            let b_hi = u128::from_str_radix(&other_copy.bin()[..1], 2).unwrap();
            let b_lo = u128::from_str_radix(&other_copy.bin()[1..2], 2).unwrap();

            let a_sum = a_hi ^ a_lo;
            let b_sum = b_hi ^ b_lo;

            let lo = a_lo * b_lo;
            let hi = (a_sum * b_sum) ^ lo;
            let lo = (a_hi * b_hi) ^ lo;

            *self = BiniusTowerField::new(2 * hi + lo, Some(1));
        }
    }
}

impl Mul for BiniusTowerField {
    type Output = BiniusTowerField;

    fn mul(mut self, other: BiniusTowerField) -> BiniusTowerField {
        self *= other; // This uses `mul_assign` internally
        self
    }
}

impl<'a> Mul<&'a BiniusTowerField> for &'a BiniusTowerField {
    type Output = BiniusTowerField;

    fn mul(self, other: &BiniusTowerField) -> BiniusTowerField {
        let mut result = self.clone(); // Clone self to avoid mutation
        result *= other.clone(); // Use mul_assign for multiplication logic
        result
    }
}

// Implement the Product trait for BiniusTowerField
impl Product for BiniusTowerField {
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        iter.fold(BiniusTowerField::one(), |acc, x| acc * x)
    }
}

impl Sum for BiniusTowerField {
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        iter.fold(BiniusTowerField::zero(), |acc, x| acc + x)
    }
}

impl From<u128> for BiniusTowerField {
    fn from(val: u128) -> Self {
        BiniusTowerField::new(val, Some(7))
    }
}

impl From<u64> for BiniusTowerField {
    fn from(val: u64) -> Self {
        BiniusTowerField::new(val as u128, Some(6))
    }
}

impl From<u32> for BiniusTowerField {
    fn from(val: u32) -> Self {
        BiniusTowerField::new(val as u128, Some(5))
    }
}

impl From<u16> for BiniusTowerField {
    fn from(val: u16) -> Self {
        BiniusTowerField::new(val as u128, Some(4))
    }
}

impl From<u8> for BiniusTowerField {
    fn from(val: u8) -> Self {
        BiniusTowerField::new(val as u128, Some(3))
    }
}

// To make BiniusTowerField printable
impl fmt::Display for BiniusTowerField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.val)
    }
}

impl fmt::Debug for BiniusTowerField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BiniusTowerField")
            .field("val", &self.val)
            .field("num_levels", &self.num_levels)
            .field("num_bits", &self.num_bits)
            .finish()
    }
}

// Implementing PartialEq to enable == comparison with integers and other BiniusTowerField instances
impl PartialEq<u128> for BiniusTowerField {
    fn eq(&self, other: &u128) -> bool {
        self.val == *other
    }
}

// TODO: Must also check num_levels and num_bits
impl PartialEq for BiniusTowerField {
    fn eq(&self, other: &Self) -> bool {
        self.val == other.get_val()
    }
}

#[cfg(test)]
mod tests {
    use num::{One, Zero};
    use std::time::Instant;

    use rand::Rng;

    use super::BiniusTowerField as BTF;
    use crate::tower_fields::TowerField;

    fn test_mul_helper(a: BTF, b: BTF, expected: BTF) -> bool {
        let result = a * b;
        result == expected
    }

    // Function to generate a random `BiniusTowerField` with specified `num_levels`
    fn random_binius_tower_field(num_levels: usize) -> BTF {
        let mut rng = rand::thread_rng();
        let random_val = rng.gen::<u128>();
        BTF::new(random_val, Some(num_levels))
    }

    // Test non-zero random vector
    #[test]
    fn test_non_zero_random() {
        for lvl in 0..8 {
            let random_values = BTF::rand_vector_non_zero(1000, Some(lvl));
            for r_val in random_values.iter() {
                assert!(!r_val.is_zero());
            }
        }
    }

    #[test]
    fn test_mult_bb_ee() {
        const N: u32 = 10000; // Number of iterations
        let mut total_time = 0u128;

        for _ in 0..N {
            let a = random_binius_tower_field(0);
            let b = random_binius_tower_field(0);

            let start_time = Instant::now();
            let _a_mul_b = a.clone() * b.clone();
            let duration = start_time.elapsed();

            total_time += duration.as_nanos(); // Add the elapsed time to the total
        }

        let avg_time = (total_time as f64) / N as f64;
        println!("0 bit - 0 bit mult: {} ns", avg_time);

        total_time = 0;
        for _ in 0..N {
            let a = random_binius_tower_field(7);
            let b = random_binius_tower_field(7);

            let start_time = Instant::now();
            let _a_mul_b = a.clone() * b.clone();
            let duration = start_time.elapsed();

            total_time += duration.as_nanos();
        }

        let avg_time = (total_time as f64) / N as f64;
        println!("128 bit - 128 bit mult: {} ns", avg_time);
    }

    #[test]
    fn test_new() {
        let field = BTF::new(5, Some(3));
        assert_eq!(field.val, 5);
        assert_eq!(field.num_levels, 3);
        assert_eq!(field.num_bits, 8);
    }

    #[test]
    fn test_zero() {
        let field = BTF::zero();
        assert_eq!(field.val, 0);
        assert_eq!(field.num_levels, 0);
    }

    #[test]
    fn test_one() {
        let field = BTF::one();
        assert_eq!(field.val, 1);
        assert_eq!(field.num_levels, 0);
    }

    #[test]
    fn test_add() {
        let field1 = BTF::new(3, Some(2));
        let field2 = BTF::new(5, Some(2));
        let result = field1 + field2;
        assert_eq!(result.val, 6); // 3 XOR 5 = 6
    }

    #[test]
    fn test_add_assign() {
        let mut field1 = BTF::new(3, Some(2));
        let field2 = BTF::new(5, Some(2));
        field1 += field2;
        assert_eq!(field1.val, 6); // 3 XOR 5 = 6
    }

    #[test]
    fn test_sub() {
        let field1 = BTF::new(3, Some(2));
        let field2 = BTF::new(5, Some(2));
        let result = field1 - field2; // Alias of add, 3 XOR 5 = 6
        assert_eq!(result.val, 6);
    }

    #[test]
    fn test_generate_inv_base_case() {
        for j in 1..16 {
            let field = BTF::new(j as u128, Some(2));
            for i in 1..(1 << field.num_bits) {
                let candidate = BTF::new(i as u128, Some(2));
                if field.clone() * candidate.clone() == BTF::new(1, Some(2)) {
                    println!("{}^(-1) = {}", field, candidate);
                }
            }
        }
    }

    #[test]
    fn test_inverse_for_zero() {
        for i in 2..6 {
            let zero_field = BTF::new(0u128, Some(i));
            let result = zero_field.inverse();
            assert!(result.is_none());
        }
    }

    #[test]
    fn test_inverse() {
        let mut rng = rand::thread_rng();

        for _ in 0..10 {
            // Test for element in F(2^4)
            let random_input_u16 = rng.gen_range(1..=((1 << 16) - 1));
            let a = BTF::new(random_input_u16 as u128, Some(4));
            let inv_a = a.inverse().expect("Inverse should exist");
            let result = a.clone() * inv_a;
            // TODO: use BTF::one()?
            assert_eq!(result, BTF::new(1u128, Some(4)));

            // Test for element in F(2^3)
            let random_input_u8 = rng.gen_range(1..=((1 << 8) - 1));
            let a = BTF::new(random_input_u8 as u128, Some(3));
            let inv_a = a.inverse().expect("Inverse should exist");
            let result = a.clone() * inv_a;
            assert_eq!(result, BTF::new(1u128, Some(3)));

            // Test for element in F(2^2)
            let random_input_u4 = rng.gen_range(1..=((1 << 4) - 1));
            let a = BTF::new(random_input_u4 as u128, Some(2));
            let inv_a = a.inverse().expect("Inverse should exist");
            let result = a.clone() * inv_a;
            assert_eq!(result, BTF::new(1u128, Some(3)));
        }
    }

    #[test]
    fn test_mul() {
        //
        // F4: [0, 1, x, x + 1]
        // a = mx + c ==> a = (x)
        // b = mx + c ==> b = (x + 1)
        // a * b = x * (1 + x)
        //       = x + x^2
        //       = 1                  since (x^2 + x + 1 = 0)
        //
        let field1 = BTF::new(2, Some(1));
        let field2 = BTF::new(3, Some(1));
        let expected = BTF::new(1, Some(1));
        assert!(test_mul_helper(field1, field2, expected));

        // F4: [0, 1, x, x + 1]
        //
        // F8: my + c such that m and c \in F4
        // 13 ==> 1101 ==> (3 || 1) ==> (1) + y * (x + 1)
        // 11 ==> 1011 ==> (2 || 3) ==> (x + 1) + y * (x)
        //
        // 13 * 11 = ((1) + y * (x + 1)) * ((x + 1) + y * (x))
        //         = (x + 1) +
        //           (x + 1)^2 * y +
        //           y * x  +
        //           y^2 * (x + 1) * x
        //         = (x + 1) +
        //           (x^2 + x + 1 + x) * y +
        //           y * x +
        //           y^2 * (x^2 + x)
        //
        // Since x^2 + x + 1 = 0 and y^2 + yx + 1 = 0
        //
        // 13 * 11 = (x + 1) +
        //           x * y +
        //           y * x
        //           y^2
        //         = (x + 1) + y * x + 1
        //         = x + y * x
        //         ==> (2 || 2) ==> 1010 ==> 10 (decimal)
        let field1 = BTF::new(13, Some(2));
        let field2 = BTF::new(11, Some(2));
        let expected = BTF::new(10, Some(2));
        assert!(test_mul_helper(field1, field2, expected));
    }

    #[test]
    fn test_mul_commutative() {
        for _ in 0..10000 {
            let field1: BTF = BTF::rand(Some(3));
            let field2: BTF = BTF::rand(Some(6));
            let field3: BTF = BTF::rand(Some(4));

            assert_eq!(field1 * field2 * field3, field2 * field1 * field3);
        }
    }

    #[test]
    fn test_add_commutative() {
        for _ in 0..100000 {
            let field1: BTF = BTF::rand(Some(3));
            let field2: BTF = BTF::rand(Some(6));
            let field3: BTF = BTF::rand(Some(4));

            assert_eq!(field1 + field2 + field3, field2 + field1 + field3);
            assert_eq!(field1 + field2 + field3, field3 + field2 + field1);
        }
    }

    #[test]
    fn test_mul_assign() {
        let mut field1 = BTF::new(2, Some(1)); // binary 10
        let field2 = BTF::new(3, Some(1)); // binary 11
        field1 *= field2;
        assert_eq!(field1.val, 1); // 2 * 3 = 1
    }

    #[test]
    fn test_neg() {
        let field = BTF::new(5, Some(2));
        let negated_field = -field; // Negation is a no-op
        assert_eq!(negated_field.val, 5);
    }

    #[test]
    fn test_split() {
        let field = BTF::new(15, Some(2)); // binary 1111
        let (hi, lo) = field.split();
        assert_eq!(hi.val, 3); // binary 11
        assert_eq!(lo.val, 3); // binary 11
    }

    #[test]
    fn test_extend_num_levels() {
        let mut field = BTF::new(3, Some(1));
        field.extend_num_levels(2);
        assert_eq!(field.num_levels, 2);
        assert_eq!(field.num_bits, 4);
    }

    #[test]
    fn test_bin_representation() {
        let field = BTF::new(5, Some(3)); // binary 101
        assert_eq!(field.bin(), "00000101"); // 8-bit zero-padded binary
    }

    #[test]
    fn test_equality() {
        let field1 = BTF::new(5, Some(3));
        let field2 = BTF::new(5, Some(3));
        let field3 = BTF::new(6, Some(3));

        assert!(field1.equals(&field2));
        assert!(!field1.equals(&field3));
    }

    #[test]
    fn test_pow() {
        let field1 = BTF::new(5, Some(3));

        let mut multiplicand = BTF::one();
        for i in 0..100 {
            assert_eq!(field1.pow(i), multiplicand);
            multiplicand *= field1;
        }
    }

    #[test]
    fn test_display() {
        let field = BTF::new(42, Some(3));
        assert_eq!(format!("{}", field), "42");
    }

    #[test]
    fn test_debug() {
        let field = BTF::new(42, Some(3));
        let debug_str = format!("{:?}", field);
        assert!(debug_str.contains("BiniusTowerField"));
        assert!(debug_str.contains("val"));
        assert!(debug_str.contains("num_levels"));
        assert!(debug_str.contains("num_bits"));
    }
}

#[cfg(test)]
mod compare_implementations {
    use super::BiniusLevel;
    use super::{BiniusTowerField as LegacyBTF, OptimizedBiniusTowerField as OptBTF};
    use crate::tower_fields::TowerField;
    use num::Zero;
    use rand::Rng;
    use std::time::Instant;

    const TEST_ITERATIONS: usize = 100;
    const BENCH_ITERATIONS: usize = 1000;

    // Helper to create corresponding fields
    fn create_pair(val: u128, level: usize) -> (LegacyBTF, OptBTF) {
        (
            LegacyBTF::new(val, Some(level)),
            OptBTF::new(val, Some(level)),
        )
    }

    // Helper to assert equivalence
    fn assert_equivalent(legacy: &LegacyBTF, opt: &OptBTF, context: &str) {
        assert_eq!(
            legacy.get_val(),
            opt.get_val(),
            "Value mismatch in {}",
            context
        );
        // Legacy uses num_levels, Opt uses level enum
        assert_eq!(
            legacy.num_levels, opt.level as usize,
            "Level mismatch in {}",
            context
        );
        // Check optimized validity
        assert!(
            opt.is_valid(),
            "Optimized field is not valid in {}",
            context
        );
    }

    // Helper for random generation
    fn rand_pair(level: usize) -> (LegacyBTF, OptBTF) {
        let num_bits = 1 << level;
        let val = if num_bits >= 128 {
            rand::thread_rng().gen::<u128>()
        } else {
            let max_val = (1u128 << num_bits).saturating_sub(1);
            rand::thread_rng().gen_range(0..=max_val)
        };
        create_pair(val, level)
    }

    #[test]
    fn test_equivalence_init() {
        for level in 0..=7 {
            let (l, o) = create_pair(0, level);
            assert_equivalent(&l, &o, "init zero");

            let (l, o) = create_pair(1, level);
            assert_equivalent(&l, &o, "init one");

            let (l, o) = rand_pair(level);
            assert_equivalent(&l, &o, "init random");
        }
    }

    #[test]
    fn test_equivalence_add() {
        for level1 in 0..=7 {
            for level2 in 0..=7 {
                for _ in 0..TEST_ITERATIONS {
                    let (l1, o1) = rand_pair(level1);
                    let (l2, o2) = rand_pair(level2);

                    let l_res = l1 + l2;
                    let o_res = o1 + o2;

                    assert_equivalent(&l_res, &o_res, "add result");
                }
            }
        }
    }

    #[test]
    fn test_equivalence_mul() {
        for level1 in 2..=5 {
            // Limit levels to keep test time reasonable
            for level2 in 2..=5 {
                for _ in 0..TEST_ITERATIONS {
                    let (l1, o1) = rand_pair(level1);
                    let (l2, o2) = rand_pair(level2);

                    let l_res = l1 * l2;
                    let o_res = o1 * o2;

                    assert_equivalent(&l_res, &o_res, "mul result");
                }
            }
        }
    }

    #[test]
    fn test_equivalence_inverse() {
        for level in 2..=5 {
            // Limit levels
            for _ in 0..TEST_ITERATIONS {
                let (l1, o1) = rand_pair(level);

                // Ensure non-zero for inverse
                if l1.is_zero() {
                    continue;
                }
                assert!(!o1.is_zero());

                let l_inv = l1.inverse();
                let o_inv = o1.inverse();

                match (l_inv, o_inv) {
                    (Some(li), Some(oi)) => assert_equivalent(&li, &oi, "inverse result"),
                    (None, None) => { /* Both correctly return None (e.g., for 0) */ }
                    _ => panic!("Inverse results differ (Some vs None) for level {}", level),
                }
            }
        }
        // Test zero explicitly
        let (l0, o0) = create_pair(0, 3);
        assert!(l0.inverse().is_none());
        assert!(o0.inverse().is_none());
    }

    #[test]
    fn test_equivalence_pow() {
        for level in 2..=5 {
            // Limit levels
            for exp in [0, 1, 2, 5, 10].iter() {
                for _ in 0..TEST_ITERATIONS {
                    let (l1, o1) = rand_pair(level);

                    let l_pow = l1.pow(*exp);
                    let o_pow = o1.pow(*exp);

                    assert_equivalent(&l_pow, &o_pow, &format!("pow exp {}", exp));
                }
            }
        }
    }

    // --- Benchmarks ---

    fn benchmark_op<FL, FO, FU>(name: &str, level: usize, legacy_op: FL, opt_op: FO, unopt_op: FU)
    where
        FL: Fn() -> (),
        FO: Fn() -> (),
        FU: Fn() -> (),
    {
        let start_legacy = Instant::now();
        for _ in 0..BENCH_ITERATIONS {
            legacy_op();
        }
        let time_legacy = start_legacy.elapsed();

        let start_opt = Instant::now();
        for _ in 0..BENCH_ITERATIONS {
            opt_op();
        }
        let time_opt = start_opt.elapsed();

        let start_unopt = Instant::now();
        for _ in 0..BENCH_ITERATIONS {
            unopt_op();
        }
        let time_unopt = start_unopt.elapsed();

        // Print full results only for Mul, otherwise skip Unoptimized
        if name.starts_with("Mul") {
            println!(
                "Bench L{}: {:<15} | Legacy: {:>10.2?} | Optimized: {:>10.2?} | Unoptimized: {:>10.2?}",
                level,
                name,
                time_legacy / BENCH_ITERATIONS as u32,
                time_opt / BENCH_ITERATIONS as u32,
                time_unopt / BENCH_ITERATIONS as u32
            );
        } else {
            println!(
                "Bench L{}: {:<15} | Legacy: {:>10.2?} | Optimized: {:>10.2?}",
                level,
                name,
                time_legacy / BENCH_ITERATIONS as u32,
                time_opt / BENCH_ITERATIONS as u32
            );
        }
    }

    // Helper function to run benchmarks for a specific level
    fn run_level_benchmarks(level: usize, exp_factor: u32) {
        let iterations = BENCH_ITERATIONS;
        println!(
            "\n--- Benchmarking Level {} ({} iterations) ---",
            level,
            iterations // Use actual iterations here
        );
        let (l1, o1) = rand_pair(level);
        let (l2, o2) = rand_pair(level);
        let exp = 10 * exp_factor; // Scale exponent roughly with level

        // Add
        benchmark_op(
            "Add",
            level,
            || {
                let _ = l1 + l2;
            },
            || {
                let _ = o1 + o2;
            },
            || { /* Placeholder */ },
        );
        // Inverse (skip for 0)
        let l1_clone = l1.clone(); // Clone before move into closure
        let o1_clone = o1.clone();
        benchmark_op(
            "Inverse",
            level,
            move || {
                let _ = l1_clone.inverse();
            },
            move || {
                let _ = o1_clone.inverse();
            },
            || { /* Placeholder */ },
        );
        // Pow
        let l1_clone_pow = l1.clone();
        let o1_clone_pow = o1.clone();
        benchmark_op(
            "Pow",
            level,
            move || {
                let _ = l1_clone_pow.pow(exp);
            },
            move || {
                let _ = o1_clone_pow.pow(exp);
            },
            || { /* Placeholder */ },
        );
    }

    #[test]
    fn benchmark_levels() {
        run_level_benchmarks(3, 2);
        run_level_benchmarks(5, 3);
        run_level_benchmarks(7, 5);
    }

    #[test]
    fn benchmark_mul() {
        // Renamed and consolidated function
        println!(
            "\n--- Benchmarking Multiplication ({} iterations) ---",
            BENCH_ITERATIONS
        );

        // Equal levels
        for level in [3, 5, 7] {
            println!("\nBenchmarking L{} * L{}", level, level);
            let (l_a, o_a) = rand_pair(level);
            let (l_b, o_b) = rand_pair(level);

            benchmark_op(
                &format!("Mul L{}*L{}", level, level),
                level,
                || {
                    let _ = l_a * l_b;
                },
                || {
                    let _ = o_a * o_b;
                },
                || {
                    let _ = OptBTF::mul_unoptimized(o_a, o_b);
                },
            );
        }

        // Mixed levels
        let pairs_to_bench = [(3, 5), (3, 7), (5, 7), (6, 7)];
        for (level_a, level_b) in pairs_to_bench {
            println!("\nBenchmarking L{} * L{}", level_a, level_b);
            let (l_a, o_a) = rand_pair(level_a);
            let (l_b, o_b) = rand_pair(level_b);
            let result_level = std::cmp::max(level_a, level_b);

            // Benchmark a * b
            benchmark_op(
                &format!("Mul L{}*L{}", level_a, level_b),
                result_level, // Label with result level
                || {
                    let _ = l_a * l_b;
                },
                || {
                    let _ = o_a * o_b;
                },
                || {
                    let _ = OptBTF::mul_unoptimized(o_a, o_b);
                },
            );

            // Benchmark b * a
            benchmark_op(
                &format!("Mul L{}*L{}", level_b, level_a),
                result_level, // Label with result level
                || {
                    let _ = l_b * l_a;
                },
                || {
                    let _ = o_b * o_a;
                },
                || {
                    let _ = OptBTF::mul_unoptimized(o_b, o_a);
                },
            );
        }
    }

    #[test]
    #[ignore] // Only run this manually to generate the table
    fn test_generate_gf16_mult_table() {
        let level = 2;
        let mut table = [[0u8; 16]; 16]; // Changed to 2D array
        println!("Generating GF(16) Multiplication Table ({}x{})...", 16, 16);

        for a_val in 0u8..=15 {
            for b_val in 0u8..=15 {
                let a = OptBTF::new(a_val as u128, Some(level));
                let b = OptBTF::new(b_val as u128, Some(level));

                let result = a * b;

                // Verify result is L2 and fits in u8
                assert_eq!(
                    result.level,
                    BiniusLevel::L2,
                    "Result level mismatch for {}*{}",
                    a_val,
                    b_val
                );
                assert!(result.is_valid(), "Result invalid for {}*{}", a_val, b_val);
                let result_val = result.get_value_as_u8();

                table[a_val as usize][b_val as usize] = result_val;
            }
        }

        // Print the table in Rust const format
        println!("\nconst GF16_MULT_TABLE: [[u8; 16]; 16] = ["); // Changed type in signature
        for r in 0..16 {
            print!("    ["); // Start of inner array
            for c in 0..16 {
                print!("{:3},", table[r][c]); // Index into 2D array
            }
            println!("],"); // End of inner array, add comma
        }
        println!("];");
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Ord, PartialOrd)]
pub enum BiniusLevel {
    L0, // 1 bit (GF(2^1))   - fits in u8
    L1, // 2 bits (GF(2^2))   - fits in u8
    L2, // 4 bits (GF(2^4))   - fits in u8
    L3, // 8 bits (GF(2^8))   - fits in u8
    L4, // 16 bits (GF(2^16))  - fits in u16
    L5, // 32 bits (GF(2^32))  - fits in u32
    L6, // 64 bits (GF(2^64))  - fits in u64
    L7, // 128 bits (GF(2^128)) - fits in u128
}

impl BiniusLevel {
    /// Returns the number of bits required for this level.
    pub fn num_bits(&self) -> usize {
        1 << (*self as usize)
    }

    /// Creates a BiniusLevel from a level number (0-7).
    pub fn from_level(level: usize) -> Option<Self> {
        match level {
            0 => Some(BiniusLevel::L0),
            1 => Some(BiniusLevel::L1),
            2 => Some(BiniusLevel::L2),
            3 => Some(BiniusLevel::L3),
            4 => Some(BiniusLevel::L4),
            5 => Some(BiniusLevel::L5),
            6 => Some(BiniusLevel::L6),
            7 => Some(BiniusLevel::L7),
            _ => None, // Invalid level
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum BiniusValue {
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct OptimizedBiniusTowerField {
    level: BiniusLevel,
    value: BiniusValue,
}

// Helper functions and implementations for OptimizedBiniusTowerField

impl OptimizedBiniusTowerField {
    /// Helper to get the value as u128, regardless of the internal storage type.
    fn get_value_as_u128(&self) -> u128 {
        match self.value {
            BiniusValue::U8(v) => v as u128,
            BiniusValue::U16(v) => v as u128,
            BiniusValue::U32(v) => v as u128,
            BiniusValue::U64(v) => v as u128,
            BiniusValue::U128(v) => v,
        }
    }

    /// Safely gets value as u64, casting smaller types up.
    fn get_value_as_u64_safe(&self) -> u64 {
        match self.value {
            BiniusValue::U8(v) => v as u64,
            BiniusValue::U16(v) => v as u64,
            BiniusValue::U32(v) => v as u64,
            BiniusValue::U64(v) => v,
            BiniusValue::U128(v) => v as u64, // Note: Potential truncation if > u64::MAX, but logic should prevent this path
        }
    }

    /// Safely gets value as u32, casting smaller types up.
    fn get_value_as_u32_safe(&self) -> u32 {
        match self.value {
            BiniusValue::U8(v) => v as u32,
            BiniusValue::U16(v) => v as u32,
            BiniusValue::U32(v) => v,
            BiniusValue::U64(v) => v as u32,
            BiniusValue::U128(v) => v as u32,
        }
    }

    /// Safely gets value as u16, casting smaller types up.
    fn get_value_as_u16_safe(&self) -> u16 {
        match self.value {
            BiniusValue::U8(v) => v as u16,
            BiniusValue::U16(v) => v,
            BiniusValue::U32(v) => v as u16,
            BiniusValue::U64(v) => v as u16,
            BiniusValue::U128(v) => v as u16,
        }
    }

    /// Safely gets value as u8, casting smaller types up (only U8 possible).
    fn get_value_as_u8_safe(&self) -> u8 {
        match self.value {
            BiniusValue::U8(v) => v,
            // Casts from larger types are inherently lossy and indicate a logic error elsewhere
            _ => self.get_value_as_u128() as u8, // Fallback with potential truncation
        }
    }

    /// Helper to get the value as u8. Panics if stored value is larger.
    fn get_value_as_u8(&self) -> u8 {
        match self.value {
            BiniusValue::U8(v) => v,
            // Casts from larger types are inherently lossy and indicate a logic error elsewhere
            _ => self.get_value_as_u128() as u8, // Fallback with potential truncation
        }
    }

    /// Helper to create the appropriate BiniusValue enum variant based on level and value.
    /// Masks the value to fit the number of bits for the level.
    fn create_value(val: u128, level: BiniusLevel) -> BiniusValue {
        let num_bits = level.num_bits();
        let modulus_mask = if num_bits >= 128 {
            u128::MAX
        } else {
            (1u128 << num_bits) - 1u128
        };
        let masked_val = val & modulus_mask;

        match level {
            BiniusLevel::L0 | BiniusLevel::L1 | BiniusLevel::L2 | BiniusLevel::L3 => {
                BiniusValue::U8(masked_val as u8)
            }
            BiniusLevel::L4 => BiniusValue::U16(masked_val as u16),
            BiniusLevel::L5 => BiniusValue::U32(masked_val as u32),
            BiniusLevel::L6 => BiniusValue::U64(masked_val as u64),
            BiniusLevel::L7 => BiniusValue::U128(masked_val),
        }
    }

    /// Actual constructor logic.
    fn construct(val: u128, level_opt: Option<usize>) -> Self {
        let level_num = level_opt.unwrap_or_else(|| {
            // Basic estimation based on bits needed - might need refinement
            if val == 0 {
                0
            } else {
                (128 - val.leading_zeros()).div_ceil(2) as usize
            } // Rough log2(log2(val))
            .min(7) // Cap at max level 7
        });

        let level = BiniusLevel::from_level(level_num)
            .expect("Level calculation resulted in invalid level");

        let value = Self::create_value(val, level);

        OptimizedBiniusTowerField { level, value }
    }

    /// Checks if the internal value representation is consistent with the level.
    pub fn is_valid(&self) -> bool {
        match self.level {
            BiniusLevel::L0 | BiniusLevel::L1 | BiniusLevel::L2 | BiniusLevel::L3 => {
                matches!(self.value, BiniusValue::U8(_))
            }
            BiniusLevel::L4 => matches!(self.value, BiniusValue::U16(_)),
            BiniusLevel::L5 => matches!(self.value, BiniusValue::U32(_)),
            BiniusLevel::L6 => matches!(self.value, BiniusValue::U64(_)),
            BiniusLevel::L7 => matches!(self.value, BiniusValue::U128(_)),
        }
    }

    /// Helper: Multiplies two elements assumed to be at the same level.
    fn mul_equal_levels(a: Self, b: Self) -> Self {
        debug_assert_eq!(a.level, b.level, "mul_equal_levels requires equal levels");
        debug_assert!(a.is_valid());
        debug_assert!(b.is_valid());

        let level = a.level;

        // Handle 0 and 1 optimizations
        if a.is_zero() || b.is_one() {
            return a;
        }
        if a.is_one() || b.is_zero() {
            return b;
        }

        // Base case: Levels 0, 1, 2 (GF(2), GF(4), GF(16)) - Use lookup table
        if level <= BiniusLevel::L2 {
            let val_a = a.get_value_as_u8();
            let val_b = b.get_value_as_u8();
            let result_val = GF16_MULT_TABLE[val_a as usize][val_b as usize];
            return OptimizedBiniusTowerField {
                level: level, // Keep original level
                value: BiniusValue::U8(result_val),
            };
        }

        // Recursive step (Karatsuba-like) for levels > L2
        let (a_hi, a_lo) = a.split();
        let (b_hi, b_lo) = b.split();
        let a_sum = a_hi + a_lo;
        let b_sum = b_hi + b_lo;

        let result = Self::mul_abstract(&a_hi, &a_lo, &a_sum, &b_hi, &b_lo, &b_sum);
        debug_assert!(result.is_valid());
        result
    }

    /// Helper: Recursive multiplication potentially handling different levels.
    /// Computes a * b, assuming level(a) <= level(b).
    fn mul_recursive_optimized(a: Self, b: Self) -> Self {
        let level_a = a.level;
        let level_b = b.level;

        if level_b == level_a {
            // Base case: Levels are equal
            Self::mul_equal_levels(a, b)
        } else if level_b > level_a {
            // Recursive step: b has higher level
            let (b_hi, b_lo) = b.split();
            let res_hi = Self::mul_recursive_optimized(a, b_hi);
            let res_lo = Self::mul_recursive_optimized(a, b_lo);
            res_hi.join(&res_lo)
        } else {
            // Should not happen if called correctly from mul_assign
            panic!("mul_recursive_optimized called with level(a) > level(b)");
        }
    }

    /// Standalone multiplication that mimics the behavior BEFORE optimizing for unequal levels.
    /// Always aligns levels first, then multiplies.
    #[allow(dead_code)]
    fn mul_unoptimized(a_orig: Self, b_orig: Self) -> Self {
        let mut a = a_orig;
        let mut b = b_orig;

        // 1. Align levels (The key difference)
        let max_level = std::cmp::max(a.level, b.level);
        if a.level < max_level {
            a.extend_num_levels(max_level as usize);
        }
        if b.level < max_level {
            b.extend_num_levels(max_level as usize);
        }

        // 2. Multiply at the aligned level
        Self::mul_equal_levels(a, b)
    }
}

// --- Trait Implementations ---

impl Zero for OptimizedBiniusTowerField {
    fn zero() -> Self {
        OptimizedBiniusTowerField {
            level: BiniusLevel::L0, // Smallest level for zero
            value: BiniusValue::U8(0),
        }
    }

    fn is_zero(&self) -> bool {
        self.get_value_as_u128() == 0
    }
}

impl One for OptimizedBiniusTowerField {
    fn one() -> Self {
        OptimizedBiniusTowerField {
            level: BiniusLevel::L0, // Smallest level for one
            value: BiniusValue::U8(1),
        }
    }

    fn is_one(&self) -> bool {
        // Check level 0 and value 1 specifically
        self.level == BiniusLevel::L0 && self.get_value_as_u128() == 1
    }
}

impl AddAssign for OptimizedBiniusTowerField {
    fn add_assign(&mut self, other: Self) {
        // Optimized AddAssign to avoid create_value and use minimal types
        // debug_assert!(self.is_valid());
        // debug_assert!(other.is_valid());

        let max_level = std::cmp::max(self.level, other.level);

        // Perform XOR using the minimal required type based on max_level
        let new_value = match max_level {
            BiniusLevel::L0 | BiniusLevel::L1 | BiniusLevel::L2 | BiniusLevel::L3 => {
                // Max level requires u8 or less
                let self_v = self.get_value_as_u8_safe(); // Safe cast up if needed
                let other_v = other.get_value_as_u8_safe();
                BiniusValue::U8(self_v ^ other_v)
            }
            BiniusLevel::L4 => {
                // Max level requires u16
                let self_v = self.get_value_as_u16_safe();
                let other_v = other.get_value_as_u16_safe();
                BiniusValue::U16(self_v ^ other_v)
            }
            BiniusLevel::L5 => {
                // Max level requires u32
                let self_v = self.get_value_as_u32_safe();
                let other_v = other.get_value_as_u32_safe();
                BiniusValue::U32(self_v ^ other_v)
            }
            BiniusLevel::L6 => {
                // Max level requires u64
                let self_v = self.get_value_as_u64_safe();
                let other_v = other.get_value_as_u64_safe();
                BiniusValue::U64(self_v ^ other_v)
            }
            BiniusLevel::L7 => {
                // Max level requires u128
                let self_v = self.get_value_as_u128(); // Already handles casting up
                let other_v = other.get_value_as_u128();
                BiniusValue::U128(self_v ^ other_v)
            }
        };

        // Update level and value directly
        self.level = max_level;
        self.value = new_value;

        // debug_assert!(self.is_valid());
    }
}

impl Add for OptimizedBiniusTowerField {
    type Output = Self;
    fn add(mut self, other: Self) -> Self {
        self += other;
        self
    }
}

// Implement Add for references
impl<'a> Add<&'a OptimizedBiniusTowerField> for &'a OptimizedBiniusTowerField {
    type Output = OptimizedBiniusTowerField;

    fn add(self, other: &OptimizedBiniusTowerField) -> OptimizedBiniusTowerField {
        let mut result = self.clone();
        result += other.clone();
        result
    }
}

impl Sub for OptimizedBiniusTowerField {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        self + other // Subtraction is the same as addition in F_2^n
    }
}

impl Neg for OptimizedBiniusTowerField {
    type Output = Self;
    fn neg(self) -> Self {
        self // Negation is identity in F_2^n
    }
}

// --- From Traits ---
// Note: These create fields with a default level based on the input type size.
// This might differ from the original which used fixed levels.
impl From<u128> for OptimizedBiniusTowerField {
    fn from(val: u128) -> Self {
        // Level 7 requires u128
        OptimizedBiniusTowerField {
            level: BiniusLevel::L7,
            value: BiniusValue::U128(val),
        }
    }
}
impl From<u64> for OptimizedBiniusTowerField {
    fn from(val: u64) -> Self {
        // Level 6 requires u64
        OptimizedBiniusTowerField {
            level: BiniusLevel::L6,
            value: BiniusValue::U64(val),
        }
    }
}
impl From<u32> for OptimizedBiniusTowerField {
    fn from(val: u32) -> Self {
        // Level 5 requires u32
        OptimizedBiniusTowerField {
            level: BiniusLevel::L5,
            value: BiniusValue::U32(val),
        }
    }
}
impl From<u16> for OptimizedBiniusTowerField {
    fn from(val: u16) -> Self {
        // Level 4 requires u16
        OptimizedBiniusTowerField {
            level: BiniusLevel::L4,
            value: BiniusValue::U16(val),
        }
    }
}
impl From<u8> for OptimizedBiniusTowerField {
    // u8 can represent levels 0 through 3. Default to L3 (8 bits).
    fn from(val: u8) -> Self {
        // Level 3 requires u8
        OptimizedBiniusTowerField {
            level: BiniusLevel::L3,
            value: BiniusValue::U8(val),
        }
    }
}

// --- Display & PartialEq ---

impl fmt::Display for OptimizedBiniusTowerField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.get_value_as_u128())
    }
}

// --- Sum ---
impl Sum for OptimizedBiniusTowerField {
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        iter.fold(OptimizedBiniusTowerField::zero(), |acc, x| acc + x)
    }
}

// --- Multiplication Traits ---
impl MulAssign for OptimizedBiniusTowerField {
    fn mul_assign(&mut self, other: Self) {
        // debug_assert!(self.is_valid());
        // debug_assert!(other.is_valid());

        let level_a = self.level;
        let level_b = other.level;

        let result = if level_a == level_b {
            // Levels are equal, use direct same-level multiplication logic
            Self::mul_equal_levels(*self, other)
        } else if level_a < level_b {
            // Self (a) has lower level, multiply into higher-level other (b)
            Self::mul_recursive_optimized(*self, other)
        } else {
            // Other (b) has lower level, multiply into higher-level self (a)
            Self::mul_recursive_optimized(other, *self)
        };

        // Update self with the computed result
        *self = result;
        // debug_assert!(self.is_valid());
    }
}

impl Mul for OptimizedBiniusTowerField {
    type Output = Self;
    fn mul(mut self, other: Self) -> Self {
        self *= other;
        self
    }
}

impl<'a> Mul<&'a OptimizedBiniusTowerField> for &'a OptimizedBiniusTowerField {
    type Output = OptimizedBiniusTowerField;
    fn mul(self, other: &OptimizedBiniusTowerField) -> OptimizedBiniusTowerField {
        let mut result = self.clone();
        result *= other.clone();
        result
    }
}

impl Product for OptimizedBiniusTowerField {
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        // TODO: Check if Self::one() needs specific level adjustment?
        // The fold handles level promotion correctly via AddAssign/MulAssign.
        iter.fold(Self::one(), |acc, x| acc * x)
    }
}

// --- TowerField Trait Implementation ---

impl TowerField for OptimizedBiniusTowerField {
    fn new(val: u128, num_levels: Option<usize>) -> Self {
        Self::construct(val, num_levels)
    }

    fn rand(num_levels: Option<usize>) -> Self {
        let level_num = num_levels.unwrap_or_else(|| rand::thread_rng().gen_range(0..=7));
        let level = BiniusLevel::from_level(level_num).unwrap();
        let num_bits = level.num_bits();

        let random_val: u128 = if num_bits >= 128 {
            rand::thread_rng().gen::<u128>()
        } else {
            let max_val = (1u128 << num_bits) - 1;
            rand::thread_rng().gen_range(0..=max_val)
        };

        Self::construct(random_val, Some(level_num))
    }

    fn rand_vector(size: usize, num_levels: Option<usize>) -> Vec<Self> {
        (0..size).map(|_| Self::rand(num_levels)).collect()
    }

    fn rand_non_zero(num_levels: Option<usize>) -> Self {
        let mut rng = rand::thread_rng();
        let level_num = num_levels.unwrap_or_else(|| rng.gen_range(0..=7));
        let level = BiniusLevel::from_level(level_num).unwrap();
        let num_bits = level.num_bits();

        // Generate a non-zero random value
        loop {
            let val: u128 = if num_bits >= 128 {
                rng.gen::<u128>()
            } else {
                let max_val = (1u128 << num_bits) - 1;
                rng.gen_range(0..=max_val)
            };
            let output = Self::construct(val, Some(level_num));
            if output.get_value_as_u128() != 0u128 {
                return output;
            }
        }
    }

    fn rand_vector_non_zero(size: usize, num_levels: Option<usize>) -> Vec<Self> {
        (0..size).map(|_| Self::rand_non_zero(num_levels)).collect()
    }

    fn extend_num_levels(&mut self, new_level_num: usize) {
        // Use debug_assert for internal consistency checks
        debug_assert!(
            new_level_num >= self.level as usize,
            "Cannot extend to a lower level."
        );
        debug_assert!(new_level_num <= 7, "Level cannot exceed 7.");

        if new_level_num > self.level as usize {
            let new_level = BiniusLevel::from_level(new_level_num).unwrap();
            // Value itself doesn't change, but its interpretation/storage might
            let current_val = self.get_value_as_u128();
            self.level = new_level;
            self.value = Self::create_value(current_val, new_level);
        }
    }

    fn set_num_levels(&mut self, new_level_num: usize) {
        // Use debug_assert for internal consistency check
        debug_assert!(new_level_num <= 7, "Level cannot exceed 7.");
        let new_level = BiniusLevel::from_level(new_level_num).unwrap();
        let current_val = self.get_value_as_u128();
        self.level = new_level;
        self.value = Self::create_value(current_val, new_level); // Re-mask value for the new level
    }

    fn get_val(&self) -> u128 {
        self.get_value_as_u128()
    }

    fn bin(&self) -> String {
        format!(
            "{:0width$b}",
            self.get_value_as_u128(),
            width = self.level.num_bits()
        )
    }

    fn split(&self) -> (Self, Self) {
        // Use debug_assert for internal consistency check
        debug_assert!(
            self.level > BiniusLevel::L0,
            "Cannot split field at level 0"
        );
        debug_assert!(self.is_valid());

        let lower_level_num = self.level as usize - 1;
        let lower_level = BiniusLevel::from_level(lower_level_num).unwrap();
        let half_bits = self.level.num_bits() / 2; // Bits in each half (lo/hi)

        // Perform split based on the native type
        let (hi, lo) = match self.value {
            BiniusValue::U8(v) => {
                // Splitting L1, L2, L3 (results are L0, L1, L2 - all fit in U8)
                let mask = (1u8 << half_bits).wrapping_sub(1);
                let lo_val = v & mask;
                let hi_val = v >> half_bits;
                let hi_value = BiniusValue::U8(hi_val);
                let lo_value = BiniusValue::U8(lo_val);
                (
                    Self {
                        level: lower_level,
                        value: hi_value,
                    },
                    Self {
                        level: lower_level,
                        value: lo_value,
                    },
                )
            }
            BiniusValue::U16(v) => {
                // Splitting L4 (results are L3 - fit in U8)
                let mask = (1u16 << half_bits).wrapping_sub(1);
                let lo_val = v & mask;
                let hi_val = v >> half_bits;
                let hi_value = BiniusValue::U8(hi_val as u8);
                let lo_value = BiniusValue::U8(lo_val as u8);
                (
                    Self {
                        level: lower_level,
                        value: hi_value,
                    },
                    Self {
                        level: lower_level,
                        value: lo_value,
                    },
                )
            }
            BiniusValue::U32(v) => {
                // Splitting L5 (results are L4 - fit in U16)
                let mask = (1u32 << half_bits).wrapping_sub(1);
                let lo_val = v & mask;
                let hi_val = v >> half_bits;
                let hi_value = BiniusValue::U16(hi_val as u16);
                let lo_value = BiniusValue::U16(lo_val as u16);
                (
                    Self {
                        level: lower_level,
                        value: hi_value,
                    },
                    Self {
                        level: lower_level,
                        value: lo_value,
                    },
                )
            }
            BiniusValue::U64(v) => {
                // Splitting L6 (results are L5 - fit in U32)
                let mask = (1u64 << half_bits).wrapping_sub(1);
                let lo_val = v & mask;
                let hi_val = v >> half_bits;
                let hi_value = BiniusValue::U32(hi_val as u32);
                let lo_value = BiniusValue::U32(lo_val as u32);
                (
                    Self {
                        level: lower_level,
                        value: hi_value,
                    },
                    Self {
                        level: lower_level,
                        value: lo_value,
                    },
                )
            }
            BiniusValue::U128(v) => {
                // Splitting L7 (results are L6 - fit in U64)
                let mask = (1u128 << half_bits).wrapping_sub(1);
                let lo_val = v & mask;
                let hi_val = v >> half_bits;
                let hi_value = BiniusValue::U64(hi_val as u64);
                let lo_value = BiniusValue::U64(lo_val as u64);
                (
                    Self {
                        level: lower_level,
                        value: hi_value,
                    },
                    Self {
                        level: lower_level,
                        value: lo_value,
                    },
                )
            }
        };

        debug_assert!(hi.is_valid());
        debug_assert!(lo.is_valid());
        (hi, lo)
    }

    fn join(&self, other: &Self) -> Self {
        // Use debug_assert for internal consistency checks
        debug_assert_eq!(
            self.level, other.level,
            "Cannot join fields of different levels"
        );
        debug_assert!(
            self.level < BiniusLevel::L7,
            "Cannot join fields at max level 7"
        );
        debug_assert!(self.is_valid());
        debug_assert!(other.is_valid());

        let higher_level_num = self.level as usize + 1;
        let higher_level = BiniusLevel::from_level(higher_level_num).unwrap();
        let lower_bits = self.level.num_bits(); // Bits in each component (hi/lo)

        // Perform join based on the native type
        let joined_value = match (self.value, other.value) {
            (BiniusValue::U8(hi_v), BiniusValue::U8(lo_v)) => {
                // Joining L0, L1, L2 -> L1, L2, L3 (all fit in U8)
                // or Joining L3 -> L4 (requires U16)
                if higher_level <= BiniusLevel::L3 {
                    BiniusValue::U8(((hi_v as u8) << lower_bits) | lo_v)
                } else {
                    // Must be joining L3->L4
                    BiniusValue::U16(((hi_v as u16) << lower_bits) | (lo_v as u16))
                }
            }
            (BiniusValue::U16(hi_v), BiniusValue::U16(lo_v)) => {
                // Joining L4 -> L5 (requires U32)
                BiniusValue::U32(((hi_v as u32) << lower_bits) | (lo_v as u32))
            }
            (BiniusValue::U32(hi_v), BiniusValue::U32(lo_v)) => {
                // Joining L5 -> L6 (requires U64)
                BiniusValue::U64(((hi_v as u64) << lower_bits) | (lo_v as u64))
            }
            (BiniusValue::U64(hi_v), BiniusValue::U64(lo_v)) => {
                // Joining L6 -> L7 (requires U128)
                BiniusValue::U128(((hi_v as u128) << lower_bits) | (lo_v as u128))
            }
            // Mismatched types shouldn't happen if levels are equal and is_valid holds
            _ => panic!("Inconsistent BiniusValue types during join despite equal levels"),
        };

        let result = Self {
            level: higher_level,
            value: joined_value,
        };
        debug_assert!(result.is_valid());
        result
    }

    fn equals(&self, other: &Self) -> bool {
        self == other // Use the derived PartialEq
    }

    // Implementation of Karatsuba-like multiplication step for tower fields.
    // Based on x_k^2 = x_k * x_{k-1} + 1 relation.
    fn mul_abstract(
        a_hi: &Self,
        a_lo: &Self,
        a_sum: &Self,
        b_hi: &Self,
        b_lo: &Self,
        b_sum: &Self,
    ) -> Self {
        // Assert components are one level lower and have same level
        debug_assert!(a_hi.level == a_lo.level && a_lo.level == a_sum.level);
        debug_assert!(
            a_hi.level == b_hi.level && a_hi.level == b_lo.level && a_hi.level == b_sum.level
        );

        // Recursive multiplications at level k-1
        let mut mx = *a_hi * *b_hi; // mx = a_hi * b_hi
        let lo = *a_lo * *b_lo; // lo = a_lo * b_lo
        let hi_term = *a_sum * *b_sum; // hi_term = (a_hi + a_lo) * (b_hi + b_lo)

        let lower_level = mx.level; // Level k-1
        let lower_num_bits = lower_level.num_bits();
        let half_lower_bits = lower_num_bits / 2; // This corresponds to the power for x_{k-1}

        // Calculate the low part of the result: lo_res = lo + mx
        let lo_res = lo + mx;

        // Calculate the high part: hi_res = hi_term + lo_res + mx * x_{k-1}
        // Multiplication by x_{k-1} (element 2^{2^{k-2}} at level k-1)
        // is equivalent to multiplying by (1 << half_lower_bits) at level k-1.
        let x_k_minus_1 = Self::construct(1u128 << half_lower_bits, Some(lower_level as usize));
        mx *= x_k_minus_1; // mx = mx * x_{k-1}

        let hi_res = hi_term + lo_res + mx;

        // Join hi and lo to get the result at level k
        hi_res.join(&lo_res)
    }

    fn inverse(&self) -> Option<Self> {
        // debug_assert!(self.is_valid());

        // Inverse of 0 doesn't exist.
        if self.is_zero() {
            return None;
        }

        // Base case: Level 2 (GF(16) / 4-bit)
        if self.level <= BiniusLevel::L2 {
            // Ensure we are at least L2 if not L0 or L1 (which should be handled by the condition)
            let mut field_l2 = self.clone();
            if field_l2.level < BiniusLevel::L2 {
                field_l2.extend_num_levels(2);
            }
            let val_u8 = field_l2.get_value_as_u8();
            if val_u8 == 0 {
                return None;
            } // Should be caught by is_zero, but double-check

            // Lookup table uses 1-based indexing for values 1-15.
            let inv_val_u8 = F2_4_INVERSE[val_u8 as usize - 1] as u8;
            return Some(OptimizedBiniusTowerField {
                level: BiniusLevel::L2,
                value: BiniusValue::U8(inv_val_u8),
            });
        }

        // Recursive step:
        let (a_hi, a_lo) = self.split(); // These are at level k-1
        let lower_level = a_hi.level;
        let half_lower_bits = lower_level.num_bits() / 2; // Power for x_{k-1}

        // Calculate x_{k-1} = 2^{2^{k-2}} at level k-1
        let x_k_minus_1 = Self::construct(1u128 << half_lower_bits, Some(lower_level as usize));

        // Calculate a_lo_next = a_lo + a_hi * x_{k-1}
        let a_lo_next = a_lo + a_hi * x_k_minus_1;

        // Calculate delta = a_lo * a_lo_next + a_hi^2
        let delta = (a_lo * a_lo_next) + (a_hi * a_hi);

        // Recursively find inverse of delta
        let delta_inverse = delta
            .inverse()
            .expect("Delta should be invertible if self is non-zero in higher fields");

        // Calculate output components
        let out_hi = delta_inverse * a_hi;
        let out_lo = delta_inverse * a_lo_next;

        // Join to get result at level k
        Some(out_hi.join(&out_lo))
    }

    fn pow(&self, exp: u32) -> Self {
        // debug_assert!(self.is_valid());

        // Handle exp = 0 case first: always return 1 at level 0
        if exp == 0 {
            return Self::one();
        }

        let mut res = Self::one();
        // Ensure 'one' starts at the correct level for subsequent multiplications
        if res.level < self.level {
            res.extend_num_levels(self.level as usize);
        }

        let mut base = *self;
        let mut e = exp;

        // Square-and-multiply algorithm
        while e > 0 {
            if e % 2 == 1 {
                res *= base;
            }
            base *= base;
            e /= 2;
        }
        // debug_assert!(res.is_valid());
        res
    }
}
