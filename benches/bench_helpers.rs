use ark_ff::{Field, PrimeField};
use criterion::{black_box, BatchSize, BenchmarkId, Criterion};
use merlin::Transcript;
use smallfield_sumcheck::{
    prover::{AlgorithmType, ProverState},
    tests::test_helpers::{common_setup_for_toom_cook, create_sumcheck_test_data, WitnessType},
    IPForMLSumcheck,
};

pub struct PrimitiveFunctions<EF: Field, BF: PrimeField> {
    pub to_ef: Box<dyn Fn(&BF) -> EF + Sync>,
    pub combine_ef: Box<dyn Fn(&Vec<EF>) -> EF + Sync>,
    pub combine_bf: Box<dyn Fn(&Vec<BF>) -> EF + Sync>,
    pub mult_be: Box<dyn Fn(&BF, &EF) -> EF + Sync>,
    pub mult_ee: Box<dyn Fn(&EF, &EF) -> EF + Sync>,
    pub mult_bb: Box<dyn Fn(&BF, &BF) -> BF + Sync>,
    pub add_ee: Box<dyn Fn(&EF, &EF) -> EF + Sync>,
}

pub struct ProverInputs<'a, EF: Field, BF: PrimeField> {
    prover_state: ProverState<EF, BF>,
    primitive_functions: &'a PrimitiveFunctions<EF, BF>,
    prover_transcript: Transcript,
    round_t: usize,
    eq_challenges: Option<Vec<EF>>,
    mappings: Vec<Box<dyn Fn(&BF, &BF) -> BF>>,
    mappings_int: Vec<Box<dyn Fn(&i64, &i64) -> i64 + Send + Sync>>,
    projection_mapping_indices: Vec<usize>,
    interpolation_maps_bf: Vec<Box<dyn Fn(&Vec<BF>) -> BF>>,
    interpolation_maps_ef: Vec<Box<dyn Fn(&Vec<EF>) -> EF>>,
}

pub const NUM_VARIABLES_RANGE: [usize; 5] = [16, 18, 20, 22, 24];



pub fn sumcheck_prove_bench<EF: Field, BF: PrimeField>(
    c: &mut Criterion,
    degree: usize,
    round_t: usize,
    algorithm: AlgorithmType,
    with_inversions: bool,
    primitive_functions: &PrimitiveFunctions<EF, BF>,
) {
    let mut group = c.benchmark_group("Prove");
    for nv in NUM_VARIABLES_RANGE {
        group.significance_level(0.05).sample_size(10);
        let function_name = format!(
            "Algorithm/{:?}/Degree/{}/round_t: {}",
            algorithm, degree, round_t
        );
        group.bench_function(BenchmarkId::new(function_name, nv), |b| {
            b.iter_batched_ref(
                || -> ProverInputs<EF, BF> {
                    {
                        // let (to_ef, combine_ef, combine_bf, mult_be, mult_ee, mult_bb, add_ee) =
                        //     create_primitive_functions();
                        let (prover_state, _, eq_challenges): (ProverState<EF, BF>, EF, Option<_>) =
                            create_sumcheck_test_data(
                                nv,
                                degree,
                                algorithm.clone(),
                                WitnessType::U1,
                                &primitive_functions.to_ef,
                            );
                        let (
                            emaps_base,
                            emaps_base_int,
                            projection_mapping_indices,
                            imaps_base,
                            imaps_ext,
                            _,
                        ) = common_setup_for_toom_cook::<BF, EF>(degree, with_inversions);

                        if eq_challenges.is_some() {
                            assert!(
                                algorithm == AlgorithmType::PrecomputationWithEq
                                    || algorithm == AlgorithmType::ToomCookWithEq 
                                    || algorithm == AlgorithmType::NaiveWithEq 
                                    || algorithm == AlgorithmType::WitnessChallengeSeparationWithEq,
                                "Eq challenges are generated only for algorithm 3/4 with eq polynomial."
                            );
                        }

                        let prover_transcript = Transcript::new(b"bench_sumcheck");

                        ProverInputs {
                            prover_state,
                            primitive_functions,
                            prover_transcript,
                            round_t,
                            eq_challenges,
                            mappings: emaps_base,
                            mappings_int: emaps_base_int,
                            projection_mapping_indices,
                            interpolation_maps_bf: imaps_base,
                            interpolation_maps_ef: imaps_ext,
                        }
                    }
                },
                |prover_input| {
                    IPForMLSumcheck::<EF, BF>::prove::<_, _, _, _, _, _, _>(
                        black_box(&mut prover_input.prover_state),
                        &prover_input.primitive_functions.combine_ef,
                        &prover_input.primitive_functions.combine_bf,
                        black_box(&mut prover_input.prover_transcript),
                        &prover_input.primitive_functions.to_ef,
                        &prover_input.primitive_functions.mult_be,
                        &prover_input.primitive_functions.add_ee,
                        &prover_input.primitive_functions.mult_ee,
                        &prover_input.primitive_functions.mult_bb,
                        Some(prover_input.round_t),
                        prover_input.eq_challenges.as_ref(),
                        Some(&prover_input.mappings),
                        Some(&prover_input.mappings_int),
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
