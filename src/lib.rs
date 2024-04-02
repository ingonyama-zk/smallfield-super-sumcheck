mod data_structures;
mod extension_test;
mod extension_transcript;
mod prover;
mod test;
mod transcript;
mod verifier;

use ark_ff::{Field, PrimeField};
use ark_std::marker::PhantomData;

/// Interactive Proof for Multilinear Sumcheck
/// Same as arkworks ML sumcheck implementation
pub struct IPForMLSumcheck<EF: Field, BF: PrimeField> {
    #[doc(hidden)]
    _marker: PhantomData<EF>,
    _other_marker: PhantomData<BF>,
}
