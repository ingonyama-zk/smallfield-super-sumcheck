pub mod linear_lagrange;
pub mod matrix_polynomial;
pub mod eq_poly;
pub mod split_eq_poly;

pub use linear_lagrange::{LinearLagrange, LinearLagrangeList};
pub use matrix_polynomial::{MatrixPolynomial, MatrixPolynomialInt};
pub use eq_poly::EqPoly;
pub use split_eq_poly::SplitEqPoly;
