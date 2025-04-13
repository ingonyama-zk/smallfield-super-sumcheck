mod btf_transcript;
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

pub mod tower_fields;

use humansize::{format_size, BINARY};
use std::time::Instant;

use ark_std::marker::PhantomData;
use tower_fields::TowerField;

/// Interactive Proof for Multilinear Sumcheck
/// Same as arkworks ML sumcheck implementation
pub struct IPForMLSumcheck<EF: TowerField, BF: TowerField> {
    #[doc(hidden)]
    _marker: PhantomData<EF>,
    _other_marker: PhantomData<BF>,
}

use stats_alloc::{Region, Stats, INSTRUMENTED_SYSTEM};

#[global_allocator]
static GLOBAL: &stats_alloc::StatsAlloc<std::alloc::System> = &INSTRUMENTED_SYSTEM;

fn track_algorithm_memory<F, R>(algorithm_name: &str, f: F) -> R
where
    F: FnOnce() -> R,
{
    let region = Region::new(&GLOBAL);
    let start = Instant::now();

    let result = f();

    let duration = start.elapsed();
    let stats = region.change();

    println!("\n╔═══ Memory Profile: {} ═══", algorithm_name);
    println!("║ Time: {:?}", duration);
    println!(
        "║ Bytes Allocated: {}",
        format_size(stats.bytes_allocated, BINARY)
    );
    println!(
        "║ Bytes Deallocated: {}",
        format_size(stats.bytes_deallocated, BINARY)
    );
    println!(
        "║ Bytes Reallocated: {}",
        format_size(stats.bytes_reallocated as usize, BINARY)
    );
    result
}
