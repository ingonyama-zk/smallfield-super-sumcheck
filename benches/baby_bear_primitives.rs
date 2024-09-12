extern crate ark_bls12_381;
extern crate criterion;
extern crate smallfield_sumcheck;

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use rand::Rng;
use smallfield_sumcheck::tests::fields::BabyBearFq;
use smallfield_sumcheck::tests::fields::BabyBearFq2;
use smallfield_sumcheck::tests::fields::BabyBearFq4;

type BF = BabyBearFq;
type MF = BabyBearFq2;
type EF = BabyBearFq4;

use std::sync::Arc;

pub fn random_u8() -> u32 {
    let mut rng = rand::thread_rng();
    let random_u8: u8 = rng.gen();
    random_u8 as u32
}

pub fn random_u32() -> u32 {
    let mut rng = rand::thread_rng();
    let random_u32: u32 = rng.gen();
    random_u32
}

fn bench_primitives(c: &mut Criterion) {
    let small_base_field_element = BF::from(random_u8());
    let base_field_element1 = BF::from(random_u32());
    let base_field_element2 = BF::from(random_u32());
    let extension_field_element1 = EF::new(
        MF::new(BF::from(random_u32()), BF::from(random_u32())),
        MF::new(BF::from(random_u32()), BF::from(random_u32())),
    );
    let extension_field_element2 = EF::new(
        MF::new(BF::from(random_u32()), BF::from(random_u32())),
        MF::new(BF::from(random_u32()), BF::from(random_u32())),
    );

    let mult_be: Arc<dyn Fn(&BF, &EF) -> EF + Sync + Send> = Arc::new(
        |base_field_element: &BF, extension_field_element: &EF| -> EF {
            let mut result: EF = EF::from(*extension_field_element);
            result.mul_by_fp(base_field_element);
            result
        },
    );

    let mult_ee: Arc<dyn Fn(&EF, &EF) -> EF + Sync + Send> =
        Arc::new(|ee_element1: &EF, ee_element2: &EF| -> EF { ee_element1 * ee_element2 });

    let mult_bb: Arc<dyn Fn(&BF, &BF) -> BF + Sync + Send> =
        Arc::new(|bb_element1: &BF, bb_element2: &BF| -> BF { bb_element1 * bb_element2 });

    let add_ee: Arc<dyn Fn(&EF, &EF) -> EF + Sync + Send> =
        Arc::new(|ee_element1: &EF, ee_element2: &EF| -> EF { ee_element1 + ee_element2 });

    let add_bb: Arc<dyn Fn(&BF, &BF) -> BF + Sync + Send> =
        Arc::new(|bb_element1: &BF, bb_element2: &BF| -> BF { bb_element1 + bb_element2 });

    let mut group = c.benchmark_group("babybear");
    group.measurement_time(std::time::Duration::new(5, 0));

    group.bench_function("mult_bb", |b| {
        b.iter(|| {
            mult_bb(
                black_box(&base_field_element1),
                black_box(&base_field_element2),
            )
        })
    });

    group.bench_function("mult_be_small", |b| {
        b.iter(|| {
            mult_be(
                black_box(&small_base_field_element),
                black_box(&extension_field_element1),
            )
        })
    });

    group.bench_function("mult_be", |b| {
        b.iter(|| {
            mult_be(
                black_box(&base_field_element1),
                black_box(&extension_field_element1),
            )
        })
    });

    group.bench_function("mult_ee", |b| {
        b.iter(|| {
            mult_ee(
                black_box(&extension_field_element1),
                black_box(&extension_field_element2),
            )
        })
    });

    group.bench_function("add_bb", |b| {
        b.iter(|| {
            add_bb(
                black_box(&base_field_element1),
                black_box(&base_field_element1),
            )
        })
    });

    group.bench_function("add_ee", |b| {
        b.iter(|| {
            add_ee(
                black_box(&extension_field_element1),
                black_box(&extension_field_element2),
            )
        })
    });
}

criterion_group!(benches, bench_primitives);
criterion_main!(benches);
