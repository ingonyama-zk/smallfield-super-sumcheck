pub mod data_structures;
pub mod error;
mod extension_transcript;
pub mod prover;
pub mod tests;
mod transcript;
pub mod verifier;

pub mod algorithms {
    pub mod four;
    pub mod one;
    pub mod three;
    pub mod two;
}

pub mod tower_fields {
    pub mod binius;
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
