#[macro_use]
extern crate criterion;
extern crate ark_bls12_381;
extern crate smallfield_sumcheck;

use std::ops::Range;

use ark_std::iterable::Iterable;
use ark_std::vec::Vec;
use criterion::black_box;
use criterion::BatchSize;
use criterion::BenchmarkId;
use criterion::Criterion;
use merlin::Transcript;
use num::One;
use smallfield_sumcheck::prover::AlgorithmType;
use smallfield_sumcheck::prover::ProverState;
use smallfield_sumcheck::tests::test_helpers::common_setup_for_toom_cook;
use smallfield_sumcheck::tests::test_helpers::create_sumcheck_test_data;
use smallfield_sumcheck::tower_fields::binius::BiniusTowerField;
use smallfield_sumcheck::tower_fields::TowerField;
use smallfield_sumcheck::IPForMLSumcheck;

type BF = BiniusTowerField;
type EF = BiniusTowerField;

pub fn create_primitive_functions() -> (
    Box<dyn Fn(&BF) -> EF + Sync>,
    Box<dyn Fn(&Vec<EF>) -> EF + Sync>,
    Box<dyn Fn(&Vec<BF>) -> EF + Sync>,
    Box<dyn Fn(&BF, &EF) -> EF + Sync>,
    Box<dyn Fn(&EF, &EF) -> EF + Sync>,
    Box<dyn Fn(&BF, &BF) -> BF + Sync>,
    Box<dyn Fn(&EF, &EF) -> EF + Sync>,
) {
    // Convert a base field element to an extension field element
    let to_ef: Box<dyn Fn(&BF) -> EF + Sync> =
        Box::new(|base_field_element: &BF| -> EF { EF::new(base_field_element.get_val(), None) });

    // Define the combine function over EF
    let combine_fn_ef: Box<dyn Fn(&Vec<EF>) -> EF + Sync> = Box::new(|data: &Vec<EF>| -> EF {
        let product = data.iter().fold(EF::one(), |prod, d| prod * (*d));
        product
    });

    // Define the combine function over BF
    let combine_fn_bf: Box<dyn Fn(&Vec<BF>) -> EF + Sync> = Box::new(|data: &Vec<BF>| -> EF {
        let product = data.iter().fold(BF::one(), |prod, d| prod * (*d));
        EF::new(product.get_val(), None)
    });

    // Multiplies a base field element to an extension field element
    let mult_be: Box<dyn Fn(&BF, &EF) -> EF + Sync> = Box::new(
        |base_field_element: &BF, extension_field_element: &EF| -> EF {
            base_field_element * extension_field_element
        },
    );

    // Multiplies an extension field element to an extension field element
    let mult_ee: Box<dyn Fn(&EF, &EF) -> EF + Sync> =
        Box::new(|ee_element1: &EF, ee_element2: &EF| -> EF { ee_element1 * ee_element2 });

    // Multiplies a base field element to a base field element
    let mult_bb: Box<dyn Fn(&BF, &BF) -> BF + Sync> =
        Box::new(|bb_element1: &BF, bb_element2: &BF| -> BF { bb_element1 * bb_element2 });

    // Adds two extension field elements
    let add_ee: Box<dyn Fn(&EF, &EF) -> EF + Sync> =
        Box::new(|ee_element1: &EF, ee_element2: &EF| -> EF { ee_element1 + ee_element2 });

    (
        to_ef,
        combine_fn_ef,
        combine_fn_bf,
        mult_be,
        mult_ee,
        mult_bb,
        add_ee,
    )
}

pub struct ProverInputs {
    prover_state: ProverState<EF, BF>,
    combine_ef: Box<dyn Fn(&Vec<EF>) -> EF + Sync>,
    combine_bf: Box<dyn Fn(&Vec<BF>) -> EF + Sync>,
    prover_transcript: Transcript,
    to_ef: Box<dyn Fn(&BF) -> EF + Sync>,
    mult_be: Box<dyn Fn(&BF, &EF) -> EF + Sync>,
    add_ee: Box<dyn Fn(&EF, &EF) -> EF + Sync>,
    mult_ee: Box<dyn Fn(&EF, &EF) -> EF + Sync>,
    mult_bb: Box<dyn Fn(&BF, &BF) -> BF + Sync>,
    round_t: usize,
    mappings: Vec<Box<dyn Fn(&BF, &BF) -> BF + Send + Sync>>,
    projection_mapping_indices: Vec<usize>,
    interpolation_maps_bf: Vec<Box<dyn Fn(&Vec<BF>) -> BF>>,
    interpolation_maps_ef: Vec<Box<dyn Fn(&Vec<EF>) -> EF>>,
}

const NUM_VARIABLES_RANGE: Range<usize> = 10..21;

pub fn sumcheck_prove_bench(
    c: &mut Criterion,
    degree: usize,
    round_t: usize,
    algorithm: AlgorithmType,
) {
    let mut group = c.benchmark_group("Prove");
    for nv in NUM_VARIABLES_RANGE {
        group.significance_level(0.05).sample_size(10);
        let function_name: String = format!(
            "BabyBear/Algorithm/{:?}/Degree/{}/round_t: {}",
            algorithm, degree, round_t
        );
        group.bench_function(BenchmarkId::new(function_name, nv), |b| {
            b.iter_batched_ref(
                || -> ProverInputs {
                    {
                        let (to_ef, combine_ef, combine_bf, mult_be, mult_ee, mult_bb, add_ee) =
                            create_primitive_functions();
                        let (prover_state, _): (ProverState<EF, BF>, BF) =
                            create_sumcheck_test_data(nv, degree, algorithm.clone());
                        let (emaps_base, projection_mapping_indices, imaps_base, imaps_ext, _) =
                            common_setup_for_toom_cook::<BF, EF>(degree);

                        let prover_transcript = Transcript::new(b"bench_sumcheck");

                        ProverInputs {
                            prover_state,
                            combine_ef,
                            combine_bf,
                            prover_transcript,
                            to_ef,
                            mult_be,
                            add_ee,
                            mult_ee,
                            mult_bb,
                            round_t,
                            mappings: emaps_base,
                            projection_mapping_indices,
                            interpolation_maps_bf: imaps_base,
                            interpolation_maps_ef: imaps_ext,
                        }
                    }
                },
                |prover_input| {
                    IPForMLSumcheck::<EF, BF>::prove::<_, _, _, _, _, _, _>(
                        black_box(&mut prover_input.prover_state),
                        &prover_input.combine_ef,
                        &prover_input.combine_bf,
                        black_box(&mut prover_input.prover_transcript),
                        &prover_input.to_ef,
                        &prover_input.mult_be,
                        &prover_input.add_ee,
                        &prover_input.mult_ee,
                        &prover_input.mult_bb,
                        Some(prover_input.round_t),
                        Some(&prover_input.mappings),
                        Some(&prover_input.projection_mapping_indices),
                        Some(&prover_input.interpolation_maps_bf),
                        Some(&prover_input.interpolation_maps_ef),
                    );
                },
                BatchSize::SmallInput,
            )
        });
    }
    group.finish();
}

fn bench_baby_bear(c: &mut Criterion) {
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::Naive);
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::WitnessChallengeSeparation);
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::Precomputation);
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::ToomCook);

    sumcheck_prove_bench(c, 1, 8, AlgorithmType::Precomputation);
    sumcheck_prove_bench(c, 1, 8, AlgorithmType::ToomCook);

    sumcheck_prove_bench(c, 2, 3, AlgorithmType::Naive);
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::WitnessChallengeSeparation);
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::Precomputation);
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::ToomCook);

    sumcheck_prove_bench(c, 2, 8, AlgorithmType::Precomputation);
    sumcheck_prove_bench(c, 2, 8, AlgorithmType::ToomCook);

    sumcheck_prove_bench(c, 3, 3, AlgorithmType::Naive);
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::WitnessChallengeSeparation);
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::Precomputation);
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::ToomCook);

    sumcheck_prove_bench(c, 3, 8, AlgorithmType::Precomputation);
    sumcheck_prove_bench(c, 3, 8, AlgorithmType::ToomCook);

    sumcheck_prove_bench(c, 4, 3, AlgorithmType::Naive);
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::WitnessChallengeSeparation);
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::Precomputation);
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::ToomCook);

    sumcheck_prove_bench(c, 4, 8, AlgorithmType::Precomputation);
    sumcheck_prove_bench(c, 4, 8, AlgorithmType::ToomCook);
}

criterion_group!(benches, bench_baby_bear);
criterion_main!(benches);
