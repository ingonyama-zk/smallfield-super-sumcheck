#[macro_use]
extern crate criterion;
extern crate ark_bls12_381;
extern crate smallfield_sumcheck;

mod helper;
use criterion::Criterion;
use helper::*;
use smallfield_sumcheck::prover::AlgorithmType;

fn bench_degree_1(c: &mut Criterion) {
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::NaiveWithEq, 1);
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::PrecomputationWithEq, 1);
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::ToomCookWithEq, 1);
}

fn bench_degree_2(c: &mut Criterion) {
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::NaiveWithEq, 1);
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::PrecomputationWithEq, 1);
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::ToomCookWithEq, 1);
}

fn bench_degree_3(c: &mut Criterion) {
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::NaiveWithEq, 1);
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::PrecomputationWithEq, 1);
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::ToomCookWithEq, 1);
}

fn bench_degree_4(c: &mut Criterion) {
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::NaiveWithEq, 1);
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::PrecomputationWithEq, 1);
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::ToomCookWithEq, 1);
}

criterion_group!(
    benches,
    bench_degree_1,
    bench_degree_2,
    bench_degree_3,
    bench_degree_4
);
criterion_main!(benches);
