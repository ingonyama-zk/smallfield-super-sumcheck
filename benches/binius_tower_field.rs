#[macro_use]
extern crate criterion;

use criterion::{black_box, BenchmarkId, Criterion};
use rand::Rng;
use smallfield_sumcheck::tower_fields::{binius::BiniusTowerField, TowerField};

// Function to generate a random `BiniusTowerField` with specified `num_levels`
fn random_binius_tower_field(num_levels: usize) -> BiniusTowerField {
    let mut rng = rand::thread_rng();
    let random_val = rng.gen::<u128>();
    BiniusTowerField::new(random_val, Some(num_levels))
}

// Helper function to run the `add` benchmark for specified `num_levels_a` and `num_levels_b`
fn btf_add_bench(c: &mut Criterion, num_levels_a: usize, num_levels_b: usize) {
    let mut group = c.benchmark_group("BiniusTowerField add");
    group.bench_with_input(
        BenchmarkId::from_parameter(format!("{}-{}", num_levels_a, num_levels_b)),
        &(num_levels_a, num_levels_b),
        |bencher, _params| {
            let a = random_binius_tower_field(num_levels_a);
            let b = random_binius_tower_field(num_levels_b);

            bencher.iter(|| {
                let _ = black_box(a.clone() + b.clone());
            });
        },
    );
    group.finish();
}

// Helper function to run the `add` benchmark for specified `num_levels_a` and `num_levels_b`
fn btf_mul_bench(c: &mut Criterion, num_levels_a: usize, num_levels_b: usize) {
    let mut group = c.benchmark_group("BiniusTowerField mul");
    group.bench_with_input(
        BenchmarkId::from_parameter(format!("{}-{}", num_levels_a, num_levels_b)),
        &(num_levels_a, num_levels_b),
        |bencher, _params| {
            let a = random_binius_tower_field(num_levels_a);
            let b = random_binius_tower_field(num_levels_b);

            bencher.iter(|| {
                let _ = black_box(a.clone() * b.clone());
            });
        },
    );
    group.finish();
}

// Main benchmark function for `add`, running different configurations of `num_levels`
fn bench_add(c: &mut Criterion) {
    // Call `btf_add_bench` with different configurations of `num_levels`
    btf_add_bench(c, 0, 0);
    btf_add_bench(c, 1, 1);
    btf_add_bench(c, 2, 2);
    btf_add_bench(c, 6, 6);
    btf_add_bench(c, 1, 6);
}

// Main benchmark function for `add`, running different configurations of `num_levels`
fn bench_mul(c: &mut Criterion) {
    // Call `btf_add_bench` with different configurations of `num_levels`
    btf_mul_bench(c, 0, 0);
    btf_mul_bench(c, 1, 1);
    btf_mul_bench(c, 2, 2);
    btf_mul_bench(c, 6, 6);
    btf_mul_bench(c, 1, 6);
}

// Criterion benchmark group
criterion_group!(benches, bench_add, bench_mul);
criterion_main!(benches);
