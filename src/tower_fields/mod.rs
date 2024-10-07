// mod.rs

use std::fmt::{Debug, Display};
use std::iter::{Product, Sum};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub};

// Declare the `binius` module where the struct is defined.
pub mod binius;

// Define the trait TowerField, which will be implemented by the struct in `binius.rs`.
pub trait TowerField:
    'static
    + Copy
    + Clone
    + Debug
    + Add<Self, Output = Self>
    + Sub<Self, Output = Self>
    + Mul<Self, Output = Self>
    + AddAssign<Self>
    + MulAssign<Self>
    + AddAssign
    + Sub
    + Mul
    + MulAssign
    + Product
    + Sum
    + From<u128>
    + From<u64>
    + From<u32>
    + From<u16>
    + From<u8>
    + Neg<Output = Self>
    + Send
    + Sync
    + Sized
    + Display
    + PartialEq
{
    fn new(val: u128, num_levels: Option<usize>) -> Self;
    fn zero() -> Self;
    fn is_zero(&self) -> bool;
    fn one() -> Self;
    fn rand(num_levels: Option<usize>) -> Self;
    fn rand_vector(size: usize, num_levels: Option<usize>) -> Vec<Self>;
    fn extend_num_levels(&mut self, new_levels: usize);
    fn set_num_levels(&mut self, new_levels: usize);
    fn get_val(&self) -> u128;
    fn bin(&self) -> String;
    fn split(&self) -> (Self, Self);
    fn join(&self, other: &Self) -> Self;
    fn equals(&self, other: &Self) -> bool;
    fn mul_abstract(
        a_hi: &Self,
        a_lo: &Self,
        a_sum: &Self,
        b_hi: &Self,
        b_lo: &Self,
        b_sum: &Self,
    ) -> Self;
    fn inverse(&self) -> Option<Self>;
}
