pub mod algorithms;
pub mod btf_transcript;
pub mod data_structures;
// pub mod eq_poly;
// pub mod error;
pub mod extension_transcript;
pub mod prover;
pub mod tests;
pub mod tower_fields;
pub mod transcript;
pub mod utils;
pub mod verifier;

use crate::tower_fields::TowerField;
use ark_std::marker::PhantomData;

/// Interactive Proof for Multilinear Sumcheck
/// Same as arkworks ML sumcheck implementation
pub struct IPForMLSumcheck<EF: TowerField, BF: TowerField> {
    #[doc(hidden)]
    _marker: PhantomData<EF>,
    _other_marker: PhantomData<BF>,
}
