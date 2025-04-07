#[macro_use]
extern crate criterion;
extern crate ark_bls12_381;
extern crate smallfield_sumcheck;

use ark_ff::Field;
use ark_ff::Zero;
use ark_std::iterable::Iterable;
use ark_std::vec::Vec;
use criterion::Criterion;

mod bench_helpers;
use bench_helpers::*;

type BF = ark_bls12_381::Fq;
type EF = ark_bls12_381::Fq2;

pub fn create_primitive_functions() -> PrimitiveFunctions<EF, BF> {
    // Convert a base field element to an extension field element
    let to_ef: Box<dyn Fn(&BF) -> EF + Sync> =
        Box::new(|base_field_element: &BF| -> EF { EF::new(*base_field_element, BF::zero()) });

    // Define the combine function over EF
    let combine_ef: Box<dyn Fn(&Vec<EF>) -> EF + Sync> = Box::new(|data: &Vec<EF>| -> EF {
        let product = data.iter().fold(EF::ONE, |prod, d| prod * d);
        product
    });

    // Define the combine function over BF
    let combine_bf: Box<dyn Fn(&Vec<BF>) -> EF + Sync> = Box::new(|data: &Vec<BF>| -> EF {
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

fn bench_bls_381(c: &mut Criterion) {
    // Read environment variables for configuration
    let (algo, degree, round_t, nv_range) = read_env_variables();

    let primitive_functions = create_primitive_functions();

    sumcheck_prove_bench(
        c,
        degree,
        round_t,
        algo,
        false,
        &primitive_functions,
        nv_range,
    );
}

criterion_group!(benches, bench_bls_381);
criterion_main!(benches);
