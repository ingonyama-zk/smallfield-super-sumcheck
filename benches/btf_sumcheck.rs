#[macro_use]
extern crate criterion;
extern crate ark_bls12_381;
extern crate smallfield_sumcheck;

mod helper;
use criterion::Criterion;
use helper::*;
use smallfield_sumcheck::prover::AlgorithmType;

fn bench_baby_bear(c: &mut Criterion) {
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::Naive, 1);
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::WitnessChallengeSeparation, 1);
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::Precomputation, 1);
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::ToomCook, 1);

    sumcheck_prove_bench(c, 1, 8, AlgorithmType::Precomputation, 1);
    sumcheck_prove_bench(c, 1, 8, AlgorithmType::ToomCook, 1);

    sumcheck_prove_bench(c, 2, 3, AlgorithmType::Naive, 1);
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::WitnessChallengeSeparation, 1);
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::Precomputation, 1);
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::ToomCook, 1);

    sumcheck_prove_bench(c, 2, 8, AlgorithmType::Precomputation, 1);
    sumcheck_prove_bench(c, 2, 8, AlgorithmType::ToomCook, 1);

    sumcheck_prove_bench(c, 3, 3, AlgorithmType::Naive, 1);
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::WitnessChallengeSeparation, 1);
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::Precomputation, 1);
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::ToomCook, 1);

    sumcheck_prove_bench(c, 3, 8, AlgorithmType::Precomputation, 1);
    sumcheck_prove_bench(c, 3, 8, AlgorithmType::ToomCook, 1);

    sumcheck_prove_bench(c, 4, 3, AlgorithmType::Naive, 1);
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::WitnessChallengeSeparation, 1);
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::Precomputation, 1);
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::ToomCook, 1);

    sumcheck_prove_bench(c, 4, 8, AlgorithmType::Precomputation, 1);
    sumcheck_prove_bench(c, 4, 8, AlgorithmType::ToomCook, 1);
}

criterion_group!(benches, bench_baby_bear);
criterion_main!(benches);
