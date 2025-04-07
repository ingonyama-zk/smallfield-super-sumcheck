#[macro_use]
extern crate criterion;
extern crate ark_bn254;
extern crate smallfield_sumcheck;

use ark_ff::Field;
use ark_std::iterable::Iterable;
use ark_std::vec::Vec;
use criterion::Criterion;
use smallfield_sumcheck::prover::AlgorithmType;

mod bench_helpers;
use bench_helpers::*;

type BF = ark_bn254::Fq;
type EF = ark_bn254::Fq;

pub fn create_primitive_functions() -> PrimitiveFunctions<EF, BF> {
    // Convert a base field element to an extension field element
    let to_ef: Box<dyn Fn(&BF) -> EF + Sync> =
        Box::new(|base_field_element: &BF| -> EF { *base_field_element });

    // Define the combine function over EF
    let combine_ef: Box<dyn Fn(&Vec<EF>) -> EF + Sync> = Box::new(|data: &Vec<EF>| -> EF {
        let product = data.iter().fold(EF::ONE, |prod, d| prod * d);
        product
    });

    // Define the combine function over BF
    let combine_bf: Box<dyn Fn(&Vec<BF>) -> EF + Sync> = Box::new(|data: &Vec<BF>| -> EF {
        let product = data.iter().fold(BF::ONE, |prod, d| prod * d);
        product
    });

    // Multiplies a base field element to an extension field element
    let mult_be: Box<dyn Fn(&BF, &EF) -> EF + Sync> = Box::new(
        |base_field_element: &BF, extension_field_element: &EF| -> EF {
            extension_field_element * base_field_element
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

    PrimitiveFunctions {
        to_ef,
        combine_ef,
        combine_bf,
        mult_be,
        mult_ee,
        mult_bb,
        add_ee,
    }
}

fn bench_bn254(c: &mut Criterion) {
    let primitive_functions = create_primitive_functions();

    sumcheck_prove_bench(
        c,
        4, // degree
        6, // round_t
        AlgorithmType::ToomCook,
        false, // with_inversions
        &primitive_functions,
    );
}

criterion_group!(benches, bench_bn254);
criterion_main!(benches);
