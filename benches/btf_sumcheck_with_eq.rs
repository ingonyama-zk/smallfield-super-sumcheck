#[macro_use]
extern crate criterion;
extern crate ark_bls12_381;
extern crate smallfield_sumcheck;

mod helper;
use criterion::Criterion;
use helper::*;
use smallfield_sumcheck::prover::AlgorithmType;

fn bench_degree_1_bool(c: &mut Criterion) {
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::NaiveWithEq, 1);
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::WitnessChallengeSeparationWithEq, 1);
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::PrecomputationWithEq, 1);
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::ToomCookWithEq, 1);
}

fn bench_degree_2_bool(c: &mut Criterion) {
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::NaiveWithEq, 1);
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::WitnessChallengeSeparationWithEq, 1);
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::PrecomputationWithEq, 1);
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::ToomCookWithEq, 1);
}

fn bench_degree_3_bool(c: &mut Criterion) {
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::NaiveWithEq, 1);
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::WitnessChallengeSeparationWithEq, 1);
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::PrecomputationWithEq, 1);
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::ToomCookWithEq, 1);
}

fn bench_degree_4_bool(c: &mut Criterion) {
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::NaiveWithEq, 1);
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::WitnessChallengeSeparationWithEq, 1);
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::PrecomputationWithEq, 1);
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::ToomCookWithEq, 1);
}

fn bench_degree_1_u32(c: &mut Criterion) {
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::NaiveWithEq, 5);
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::WitnessChallengeSeparationWithEq, 5);
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::PrecomputationWithEq, 5);
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::ToomCookWithEq, 5);
}

fn bench_degree_2_u32(c: &mut Criterion) {
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::NaiveWithEq, 5);
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::WitnessChallengeSeparationWithEq, 5);
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::PrecomputationWithEq, 5);
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::ToomCookWithEq, 5);
}

fn bench_degree_3_u32(c: &mut Criterion) {
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::NaiveWithEq, 5);
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::WitnessChallengeSeparationWithEq, 5);
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::PrecomputationWithEq, 5);
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::ToomCookWithEq, 5);
}

fn bench_degree_4_u32(c: &mut Criterion) {
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::NaiveWithEq, 5);
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::WitnessChallengeSeparationWithEq, 5);
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::PrecomputationWithEq, 5);
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::ToomCookWithEq, 5);
}

criterion_group!(
    benches,
    bench_degree_1_bool,
    bench_degree_2_bool,
    bench_degree_3_bool,
    bench_degree_4_bool,
    bench_degree_1_u32,
    bench_degree_2_u32,
    bench_degree_3_u32,
    bench_degree_4_u32,
);
criterion_main!(benches);
