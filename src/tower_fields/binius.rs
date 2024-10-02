use std::{
    fmt,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub},
};

#[derive(Clone, Eq)]
pub struct BiniusTowerField {
    val: u128,         // To store the value in the field
    num_levels: usize, // Number of levels in the binary tower
    num_bits: usize,   // Number of bits based on num_levels
}

impl BiniusTowerField {
    // Constructor
    pub fn new(val: u128, num_levels: Option<usize>) -> Self {
        let computed_levels = match num_levels {
            Some(levels) => levels,
            None => {
                let log2_val = (val as f64).log2().log2().ceil();
                log2_val as usize + 1
            }
        };

        let num_bits = 1 << computed_levels;
        let modulus = 1u128 << num_bits;

        BiniusTowerField {
            val: val % modulus,
            num_levels: computed_levels,
            num_bits,
        }
    }

    // Zero function
    pub fn zero(&mut self) {
        self.val = 0;
    }

    // One function
    pub fn one(&mut self) {
        self.val = 1;
    }

    // Extend the number of levels in the tower
    pub fn extend_num_levels(&mut self, new_levels: usize) {
        assert!(self.num_levels <= new_levels);
        self.set_num_levels(new_levels);
    }

    // Set new levels
    fn set_num_levels(&mut self, new_levels: usize) {
        self.num_levels = new_levels;
        self.num_bits = 1 << self.num_levels;
    }

    // Get the value (equivalent to val method)
    pub fn get_val(&self) -> u128 {
        self.val
    }

    // Return the binary representation of the value, padded with zeros
    pub fn bin(&self) -> String {
        format!("{:0width$b}", self.val, width = self.num_bits)
    }

    // Split the value into high and low parts
    pub fn split(&self) -> (BiniusTowerField, BiniusTowerField) {
        let bin_val = self.bin();
        let half_bits = self.num_bits / 2;

        let hi_val = u128::from_str_radix(&bin_val[..half_bits], 2).unwrap();
        let lo_val = u128::from_str_radix(&bin_val[half_bits..], 2).unwrap();

        let hi = BiniusTowerField::new(hi_val, Some(self.num_levels - 1));
        let lo = BiniusTowerField::new(lo_val, Some(self.num_levels - 1));

        (hi, lo)
    }

    // Equality check
    pub fn equals(&self, other: &BiniusTowerField) -> bool {
        self.val == other.get_val()
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
        let lo_val = lo.val;

        // mx * 2^(mx.num_half_bits())
        mx = mx * Self::new(1 << (mx_num_bits / 2), Some(mx_num_levels));

        // Perform hi operations
        let mut hi = a_sum * b_sum; // hi = a_sum * b_sum
        hi = hi + (lo + mx); // hi += lo + mx

        // Concatenate hi and lo by shifting hi to make space for lo
        Self::new((hi.val << hi.num_bits) + lo_val, Some(hi.num_levels + 1))
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
    fn mul_assign(&mut self, other: BiniusTowerField) {
        let mut other_copy = other.clone();

        // Align num_levels to max
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

impl PartialEq for BiniusTowerField {
    fn eq(&self, other: &Self) -> bool {
        self.val == other.get_val()
    }
}

#[cfg(test)]
mod tests {
    use super::BiniusTowerField as BTF;

    fn test_mul_helper(a: BTF, b: BTF, expected: BTF) -> bool {
        let result = a * b;
        result == expected
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
        let mut field = BTF::new(10, Some(2));
        field.zero();
        assert_eq!(field.val, 0);
    }

    #[test]
    fn test_one() {
        let mut field = BTF::new(10, Some(2));
        field.one();
        assert_eq!(field.val, 1);
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
    fn test_mul() {
        // TODO: add explanation of how this works
        let field1 = BTF::new(2, Some(1)); // binary 10
        let field2 = BTF::new(3, Some(1)); // binary 11
        let expected = BTF::new(1, Some(1)); // binary 01
        assert!(test_mul_helper(field1, field2, expected));

        let field1 = BTF::new(13, Some(2)); // binary 10
        let field2 = BTF::new(11, Some(2)); // binary 11
        let expected = BTF::new(10, Some(2)); // binary 11
        assert!(test_mul_helper(field1, field2, expected));
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
