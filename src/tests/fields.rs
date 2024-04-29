use ark_ff::{
    fields::{MontBackend, MontConfig},
    Field, Fp2, Fp2Config, Fp4, Fp4Config, Fp64, MontFp,
};

///
/// The baby bear field is given by 𝔽ₚ where
/// p = 15 * 2²⁷ + 1
///   = 2013265921
///
/// Generator g = 31.
/// Generated with sage math script:
/// GF(2013265921).multiplicative_generator()
///
/// Quadratic residue: r = p - 1
///
#[derive(MontConfig)]
#[modulus = "2013265921"]
#[generator = "31"]
pub struct BabyBearFqConfig;
pub type BabyBearFq = Fp64<MontBackend<BabyBearFqConfig, 1>>;

///
/// Degree-2 extension of the baby bear field.
///
pub type BabyBearFq2 = Fp2<BabyBearFq2Config>;
pub struct BabyBearFq2Config;
impl Fp2Config for BabyBearFq2Config {
    type Fp = BabyBearFq;

    /// NONRESIDUE = -1
    const NONRESIDUE: BabyBearFq = MontFp!("-1");

    /// Coefficients for the Frobenius automorphism.
    const FROBENIUS_COEFF_FP2_C1: &'static [BabyBearFq] = &[
        // NONRESIDUE**(((q^0) - 1) / 2)
        BabyBearFq::ONE,
        // NONRESIDUE**(((q^1) - 1) / 2)
        MontFp!("-1"),
    ];
}

#[allow(dead_code)]
pub type BabyBearFq4 = Fp4<BabyBearFq4Config>;
pub struct BabyBearFq4Config;
impl Fp4Config for BabyBearFq4Config {
    type Fp2Config = BabyBearFq2Config;

    const NONRESIDUE: BabyBearFq2 = BabyBearFq2::new(BabyBearFq::ZERO, BabyBearFq::ONE);

    // Coefficients for the Frobenius automorphism.
    // c1[0] = 1,
    // c1[1] = 281474976710656,
    // c1[2] = 18446744069414584320, (= q - 1)
    // c1[3] = 18446462594437873665,
    //
    // (Calculated using sage math)
    //
    // These are calculated as
    // `FROBENIUS_COEFF_FP4_C1[i] = Fp2Config::NONRESIDUE^((q^i - 1) / 4)`.
    const FROBENIUS_COEFF_FP4_C1: &'static [BabyBearFq] = &[
        BabyBearFq::ONE,
        MontFp!("281474976710656"),
        MontFp!("-1"),
        MontFp!("18446462594437873665"),
    ];
}

#[derive(MontConfig)]
#[modulus = "18446744069414584321"]
#[generator = "7"]
pub struct GoldilocksFqConfig;
pub type GoldlocksFq = Fp64<MontBackend<GoldilocksFqConfig, 1>>;

pub type GoldlocksFq2 = Fp2<GoldilocksFq2Config>;
pub struct GoldilocksFq2Config;
impl Fp2Config for GoldilocksFq2Config {
    type Fp = GoldlocksFq;

    /// NONRESIDUE = 7
    const NONRESIDUE: GoldlocksFq = MontFp!("7");

    /// Coefficients for the Frobenius automorphism.
    const FROBENIUS_COEFF_FP2_C1: &'static [GoldlocksFq] = &[
        // NONRESIDUE**(((q^0) - 1) / 2)
        GoldlocksFq::ONE,
        // NONRESIDUE**(((q^1) - 1) / 2)
        MontFp!("-1"),
    ];
}

pub struct GoldilocksFq4Config;
impl Fp4Config for GoldilocksFq4Config {
    type Fp2Config = GoldilocksFq2Config;

    const NONRESIDUE: GoldlocksFq2 = GoldlocksFq2::new(GoldlocksFq::ZERO, GoldlocksFq::ONE);

    // Coefficients for the Frobenius automorphism.
    // c1[0] = 1,
    // c1[1] = 281474976710656,
    // c1[2] = 18446744069414584320, (= q - 1)
    // c1[3] = 18446462594437873665,
    //
    // (Calculated using sage math)
    //
    // These are calculated as
    // `FROBENIUS_COEFF_FP4_C1[i] = Fp2Config::NONRESIDUE^((q^i - 1) / 4)`.
    const FROBENIUS_COEFF_FP4_C1: &'static [GoldlocksFq] = &[
        GoldlocksFq::ONE,
        MontFp!("281474976710656"),
        MontFp!("-1"),
        MontFp!("18446462594437873665"),
    ];
}
