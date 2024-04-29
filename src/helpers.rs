use crate::{
    data_structures::LinearLagrangeList,
    error::SumcheckError,
    prover::{AlgorithmType, ProverState, SumcheckProof},
    utils::{generate_interpolation_matrix_transpose, get_maps_from_matrix},
    IPForMLSumcheck,
};
use ark_ff::{Field, PrimeField};
use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
use ark_std::{test_rng, vec::Vec};
use merlin::Transcript;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub trait ExtensionField<BF: PrimeField>: Field {
    fn new(c0: BF, c1: BF) -> Self;
    fn mul_assign_by_basefield(&mut self, element: &BF);
}

pub fn create_primitive_functions<EF: ExtensionField<BF>, BF: PrimeField>() -> (
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
        Box::new(|ee_element1: &EF, ee_element2: &EF| -> EF { *ee_element1 * *ee_element2 });

    // Multiplies a base field element to a base field element
    let mult_bb: Box<dyn Fn(&BF, &BF) -> BF + Sync> =
        Box::new(|bb_element1: &BF, bb_element2: &BF| -> BF { *bb_element1 * *bb_element2 });

    // Adds two extension field elements
    let add_ee: Box<dyn Fn(&EF, &EF) -> EF + Sync> =
        Box::new(|ee_element1: &EF, ee_element2: &EF| -> EF { *ee_element1 + *ee_element2 });

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

/// Helper function to create sumcheck test multivariate polynomials of given degree.
pub fn create_sumcheck_test_data<EF: ExtensionField<BF>, BF: PrimeField>(
    nv: usize,
    degree: usize,
    algorithm: AlgorithmType,
) -> (ProverState<EF, BF>, BF) {
    // Declare a randomness generation engine
    let mut rng = test_rng();

    let num_evaluations: usize = (1 as usize) << nv;
    let mut polynomials: Vec<LinearLagrangeList<BF>> = Vec::with_capacity(degree);
    let mut polynomial_hadamard: Vec<BF> = vec![BF::ONE; num_evaluations];
    for _ in 0..degree {
        let poly_i: DenseMultilinearExtension<BF> = DenseMultilinearExtension::rand(nv, &mut rng);
        polynomials.push(LinearLagrangeList::<BF>::from(&poly_i));
        polynomial_hadamard
            .iter_mut()
            .zip(poly_i.iter())
            .for_each(|(p_acc, p_curr)| *p_acc *= *p_curr);
    }
    let claimed_sum: BF = polynomial_hadamard
        .iter()
        .fold(BF::zero(), |acc, ph| acc + ph);

    let prover_state: ProverState<EF, BF> =
        IPForMLSumcheck::<EF, BF>::prover_init(&polynomials, degree, algorithm);

    (prover_state, claimed_sum)
}

/// Setup all mappings etc for the toom-cook algorithm.
pub fn setup_for_toom_cook<EF: Field, BF: PrimeField>(
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
    let (interpolation_matrix, scaled_det) = generate_interpolation_matrix_transpose(degree);

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

pub fn sumcheck_test_helper<EF: ExtensionField<BF> + std::convert::From<i64>, BF: PrimeField>(
    nv: usize,
    degree: usize,
    round_t: usize,
    algorithm: AlgorithmType,
    with_inversions: bool,
) -> (SumcheckProof<EF>, Result<bool, SumcheckError>) {
    let (to_ef, combine_ef, combine_bf, mult_be, mult_ee, mult_bb, add_ee) =
        create_primitive_functions::<EF, BF>();
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
