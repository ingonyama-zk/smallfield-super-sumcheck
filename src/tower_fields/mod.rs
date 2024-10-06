// mod.rs

use std::fmt::Debug;
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub};

// Declare the `binius` module where the struct is defined.
pub mod binius;

// Define the trait TowerField, which will be implemented by the struct in `binius.rs`.
pub trait TowerField: Clone + Debug + Add + AddAssign + Sub + Mul + MulAssign + Sized {
    fn new(val: u128, num_levels: Option<usize>) -> Self;
    fn zero(&mut self);
    fn one(&mut self);
    fn extend_num_levels(&mut self, new_levels: usize);
    fn set_num_levels(&mut self, new_levels: usize);
    fn get_val(&self) -> u128;
    fn bin(&self) -> String;
    fn split(&self) -> (Self, Self);
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
