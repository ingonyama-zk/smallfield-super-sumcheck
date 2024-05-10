#[macro_use]
extern crate criterion;
extern crate ark_bls12_381;
extern crate smallfield_sumcheck;

use std::ops::Range;

use ark_ff::Field;
use ark_ff::Zero;
use ark_std::iterable::Iterable;
use ark_std::vec::Vec;
use criterion::black_box;
use criterion::BatchSize;
use criterion::BenchmarkId;
use criterion::Criterion;
use merlin::Transcript;
use smallfield_sumcheck::error::SumcheckError;
use smallfield_sumcheck::prover::AlgorithmType;
use smallfield_sumcheck::prover::ProverState;
use smallfield_sumcheck::prover::SumcheckProof;
use smallfield_sumcheck::tests::test_helpers::create_sumcheck_test_data;
use smallfield_sumcheck::tests::test_helpers::generate_binomial_interpolation_mult_matrix_transpose;
use smallfield_sumcheck::tests::test_helpers::get_maps_from_matrix;
use smallfield_sumcheck::IPForMLSumcheck;

type BF = ark_bls12_381::Fq;
type EF = ark_bls12_381::Fq2;

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
        Box::new(|base_field_element: &BF| -> EF { EF::new(*base_field_element, BF::zero()) });

    // Define the combine function over EF
    let combine_fn_ef: Box<dyn Fn(&Vec<EF>) -> EF + Sync> = Box::new(|data: &Vec<EF>| -> EF {
        let product = data.iter().fold(EF::ONE, |prod, d| prod * d);
        product
    });

    // Define the combine function over BF
    let combine_fn_bf: Box<dyn Fn(&Vec<BF>) -> EF + Sync> = Box::new(|data: &Vec<BF>| -> EF {
        let product = data.iter().fold(BF::ONE, |prod, d| prod * d);
        EF::new(product, BF::zero())
    });

    // Multiplies a base field element to an extension field element
    let mult_be: Box<dyn Fn(&BF, &EF) -> EF + Sync> = Box::new(
        |base_field_element: &BF, extension_field_element: &EF| -> EF {
            let mut result: EF = EF::from(*extension_field_element);
            result.mul_assign_by_basefield(base_field_element);
            result
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

pub fn sumcheck_test_helper(
    nv: usize,
    degree: usize,
    round_t: usize,
    algorithm: AlgorithmType,
    with_inversions: bool,
) -> (SumcheckProof<EF>, Result<bool, SumcheckError>) {
    let (to_ef, combine_ef, combine_bf, mult_be, mult_ee, mult_bb, add_ee) =
        create_primitive_functions();
    let (mut prover_state, claimed_sum): (ProverState<EF, BF>, BF) =
        create_sumcheck_test_data(nv, degree, algorithm.clone());

    let (emaps_base, projective_map_indices, imaps_base, imaps_ext, mut scaled_det) =
        setup_for_toom_cook(degree, with_inversions);

    // create a proof
    let mut prover_transcript = Transcript::new(b"test_sumcheck");
    let proof: SumcheckProof<EF> = IPForMLSumcheck::<EF, BF>::prove::<_, _, _, _, _, _, _>(
        &mut prover_state,
        &combine_ef,
        &combine_bf,
        &mut prover_transcript,
        &to_ef,
        &mult_be,
        &add_ee,
        &mult_ee,
        &mult_bb,
        Some(round_t),
        Some(&emaps_base),
        Some(&projective_map_indices),
        Some(&imaps_base),
        Some(&imaps_ext),
    );

    let mut round_t_v = round_t;
    if (algorithm != AlgorithmType::ToomCook) || (with_inversions == true) {
        scaled_det = 1;
        round_t_v = 0;
    }

    let mut verifier_transcript = Transcript::new(b"test_sumcheck");
    let result = IPForMLSumcheck::<EF, BF>::verify(
        to_ef(&claimed_sum),
        &proof,
        &mut verifier_transcript,
        algorithm,
        Some(EF::from(scaled_det)),
        Some(round_t_v),
    );
    (proof, result)
}

/// Setup all mappings etc for the toom-cook algorithm.
pub fn setup_for_toom_cook(
    degree: usize,
    with_inversions: bool,
) -> (
    Vec<Box<dyn Fn(&BF, &BF) -> BF>>,
    Vec<usize>,
    Vec<Box<dyn Fn(&Vec<BF>) -> BF>>,
    Vec<Box<dyn Fn(&Vec<EF>) -> EF>>,
    i64,
) {
    // Define evaluation mappings
    // p(x) = p0 + p1.x
    let num_evals = degree + 1;
    let mut emaps_base: Vec<Box<dyn Fn(&BF, &BF) -> BF>> = Vec::with_capacity(num_evals);
    emaps_base.push(Box::new(move |x: &BF, _y: &BF| -> BF { *x }));
    emaps_base.push(Box::new(move |_x: &BF, y: &BF| -> BF { *y }));
    for i in 1..=(num_evals / 2) {
        if emaps_base.len() < num_evals {
            let mapi = Box::new(move |x: &BF, y: &BF| -> BF { *x + (*y * BF::from(i as u32)) });
            emaps_base.push(mapi);
        }
        if emaps_base.len() < num_evals {
            let mapi = Box::new(move |x: &BF, y: &BF| -> BF { *x - (*y * BF::from(i as u32)) });
            emaps_base.push(mapi);
        }
    }
    let projective_map_indices = vec![0 as usize, 1 as usize];

    // Define interpolation mappings
    let (interpolation_matrix, scaled_det) = generate_binomial_interpolation_mult_matrix_transpose(degree);

    // If inversions are allowed (makes the protocol less efficient), modify the divisor accordingly.
    let mut divisor: i64 = 1;
    if with_inversions {
        divisor = scaled_det;
    }

    let imaps_base = get_maps_from_matrix::<BF>(&interpolation_matrix, divisor);
    let imaps_ext = get_maps_from_matrix::<EF>(&interpolation_matrix, divisor);

    (
        emaps_base,
        projective_map_indices,
        imaps_base,
        imaps_ext,
        scaled_det,
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
    mappings: Vec<Box<dyn Fn(&BF, &BF) -> BF>>,
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
    with_inversions: bool,
) {
    let mut group = c.benchmark_group("Prove");
    for nv in NUM_VARIABLES_RANGE {
        group.significance_level(0.05).sample_size(10);
        let function_name: String = format!(
            "Algorithm/{:?}/Degree/{}/round_t: {}",
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
                            setup_for_toom_cook(degree, with_inversions);
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

fn bench_bls_381(c: &mut Criterion) {
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::Naive, false);
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::WitnessChallengeSeparation, false);
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::Precomputation, false);
    sumcheck_prove_bench(c, 1, 3, AlgorithmType::ToomCook, false);

    sumcheck_prove_bench(c, 1, 8, AlgorithmType::Precomputation, false);
    sumcheck_prove_bench(c, 1, 8, AlgorithmType::ToomCook, false);

    sumcheck_prove_bench(c, 2, 3, AlgorithmType::Naive, false);
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::WitnessChallengeSeparation, false);
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::Precomputation, false);
    sumcheck_prove_bench(c, 2, 3, AlgorithmType::ToomCook, false);

    sumcheck_prove_bench(c, 2, 8, AlgorithmType::Precomputation, false);
    sumcheck_prove_bench(c, 2, 8, AlgorithmType::ToomCook, false);

    sumcheck_prove_bench(c, 3, 3, AlgorithmType::Naive, false);
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::WitnessChallengeSeparation, false);
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::Precomputation, false);
    sumcheck_prove_bench(c, 3, 3, AlgorithmType::ToomCook, false);

    sumcheck_prove_bench(c, 3, 8, AlgorithmType::Precomputation, false);
    sumcheck_prove_bench(c, 3, 8, AlgorithmType::ToomCook, false);

    sumcheck_prove_bench(c, 4, 3, AlgorithmType::Naive, false);
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::WitnessChallengeSeparation, false);
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::Precomputation, false);
    sumcheck_prove_bench(c, 4, 3, AlgorithmType::ToomCook, false);

    sumcheck_prove_bench(c, 4, 8, AlgorithmType::Precomputation, false);
    sumcheck_prove_bench(c, 4, 8, AlgorithmType::ToomCook, false);
}

criterion_group!(benches, bench_bls_381);
criterion_main!(benches);
