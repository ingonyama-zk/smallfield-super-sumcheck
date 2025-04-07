pub mod data_structures;
pub mod eq_poly;
pub mod error;
mod extension_transcript;
pub mod prover;
pub mod tests;
mod transcript;
pub mod verifier;

pub mod algorithms {
    pub mod four;
    pub mod four_eq;
    pub mod one;
    pub mod one_eq;
    pub mod three;
    pub mod three_eq;
    pub mod two;
    pub mod two_eq;
}

use ark_ff::{Field, PrimeField};
use ark_std::marker::PhantomData;

/// Interactive Proof for Multilinear Sumcheck
/// Same as arkworks ML sumcheck implementation
pub struct IPForMLSumcheck<EF: Field, BF: PrimeField> {
    #[doc(hidden)]
    _marker: PhantomData<EF>,
    _other_marker: PhantomData<BF>,
}
