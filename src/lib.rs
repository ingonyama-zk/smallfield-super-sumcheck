pub mod data_structures;
pub mod error;
mod extension_test;
mod extension_transcript;
pub mod helpers;
pub mod prover;
mod test;
pub mod tests;
mod transcript;
pub mod utils;
pub mod verifier;

use ark_ff::{Field, PrimeField};
use ark_std::marker::PhantomData;

/// Interactive Proof for Multilinear Sumcheck
/// Same as arkworks ML sumcheck implementation
pub struct IPForMLSumcheck<EF: Field, BF: PrimeField> {
    #[doc(hidden)]
    _marker: PhantomData<EF>,
    _other_marker: PhantomData<BF>,
}
