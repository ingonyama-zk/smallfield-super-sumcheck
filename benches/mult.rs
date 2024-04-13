use ark_ff::Field;
use criterion::{black_box, Criterion};
use rand::Rng;
use smallfield_sumcheck::data_structures::MatrixPolynomial;

#[macro_use]
extern crate criterion;
extern crate ark_bls12_381;
extern crate smallfield_sumcheck;

type F = ark_bls12_381::Fq;

pub fn random_field_element<F: Field>() -> F {
    let mut rng = rand::thread_rng();
    let random_u128: u128 = rng.gen();
    F::from(random_u128)
}

// Benchmarking function
fn compare_functions(c: &mut Criterion) {
    let mut rng = rand::thread_rng();
    let n: u16 = black_box(rng.gen()); // Use `black_box` to prevent constant folding
    let n_field = F::from(n);
    let f: F = black_box(random_field_element());

    c.bench_function("function1", |b| {
        b.iter(|| MatrixPolynomial::mult_small_with_big(&n, &f))
    });
    c.bench_function("function2", |b| b.iter(|| n_field * f));
}

criterion_group!(benches, compare_functions);
criterion_main!(benches);
