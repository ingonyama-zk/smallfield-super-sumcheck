#[cfg(test)]
mod fq2_tests {
    use crate::error::SumcheckError;
    use crate::prover::AlgorithmType;
    use crate::prover::ProverState;
    use crate::prover::SumcheckProof;
    use crate::tests::test_helpers::create_sumcheck_test_data;
    use crate::tests::test_helpers::generate_binomial_interpolation_mult_matrix_transpose;
    use crate::tests::test_helpers::get_maps_from_matrix;
    use crate::IPForMLSumcheck;
    use ark_ff::Field;
    use ark_ff::Zero;
    use ark_std::iterable::Iterable;
    use ark_std::vec::Vec;
    use merlin::Transcript;
    use rstest::rstest;
    // use std::sync::atomic::{AtomicUsize, Ordering};

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
        let (interpolation_matrix, scaled_det) =
            generate_binomial_interpolation_mult_matrix_transpose(degree);

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

    #[rstest]
    fn check_sumcheck_product(
        #[values(5, 8, 12)] nv: usize,
        #[values(1, 2, 3, 6)] degree: usize,
        #[values(
            AlgorithmType::Naive,
            AlgorithmType::WitnessChallengeSeparation,
            AlgorithmType::Precomputation,
            AlgorithmType::ToomCook
        )]
        algorithm: AlgorithmType,
    ) {
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(nv, degree, 3, algorithm, false)
                .1
                .unwrap(),
            true
        );
    }

    #[rstest]
    fn check_sumcheck_product_with_threshold(
        #[values(5, 8)] nv: usize,
        #[values(2, 3)] degree: usize,
        #[values(nv / 2, nv)] round_t: usize,
        #[values(
            AlgorithmType::Naive,
            AlgorithmType::WitnessChallengeSeparation,
            AlgorithmType::Precomputation,
            AlgorithmType::ToomCook
        )]
        algorithm: AlgorithmType,
    ) {
        assert_eq!(
            sumcheck_test_helper(nv, degree, round_t, algorithm, false)
                .1
                .unwrap(),
            true
        );
    }

    #[rstest]
    fn check_proof_consistency(
        #[values(5, 8)] nv: usize,
        #[values(1, 3, 4)] degree: usize,
        #[values(1, nv / 2)] round_t: usize,
    ) {
        let (proof_1, result_1) =
            sumcheck_test_helper(nv, degree, round_t, AlgorithmType::Naive, false);
        let (proof_2, result_2) = sumcheck_test_helper(
            nv,
            degree,
            round_t,
            AlgorithmType::WitnessChallengeSeparation,
            false,
        );
        let (proof_3, result_3) =
            sumcheck_test_helper(nv, degree, round_t, AlgorithmType::Precomputation, false);
        let (proof_4, result_4) =
            sumcheck_test_helper(nv, degree, round_t, AlgorithmType::ToomCook, true);

        assert_eq!(result_1.unwrap(), true);
        assert_eq!(result_2.unwrap(), true);
        assert_eq!(result_3.unwrap(), true);
        assert_eq!(result_4.unwrap(), true);
        assert_eq!(proof_1, proof_2);
        assert_eq!(proof_2, proof_3);
        assert_eq!(proof_3, proof_4);
    }
}

#[cfg(test)]
mod fq6_tests {
    use crate::error::SumcheckError;
    use crate::prover::AlgorithmType;
    use crate::prover::ProverState;
    use crate::prover::SumcheckProof;
    use crate::tests::test_helpers::create_sumcheck_test_data;
    use crate::tests::test_helpers::generate_binomial_interpolation_mult_matrix_transpose;
    use crate::tests::test_helpers::get_maps_from_matrix;
    use crate::IPForMLSumcheck;
    use ark_ff::Field;
    use ark_ff::Zero;
    use ark_std::iterable::Iterable;
    use ark_std::vec::Vec;
    use merlin::Transcript;
    use rstest::rstest;

    type BF = ark_bls12_381::Fq;
    type MF = ark_bls12_381::Fq2;
    type EF = ark_bls12_381::Fq6;

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
        let to_ef: Box<dyn Fn(&BF) -> EF + Sync> = Box::new(|base_field_element: &BF| -> EF {
            EF::new(
                MF::new(*base_field_element, BF::zero()),
                MF::zero(),
                MF::zero(),
            )
        });

        // Define the combine function over EF
        let combine_fn_ef: Box<dyn Fn(&Vec<EF>) -> EF + Sync> = Box::new(|data: &Vec<EF>| -> EF {
            let product = data.iter().fold(EF::ONE, |prod, d| prod * d);
            product
        });

        // Define the combine function over BF
        let combine_fn_bf: Box<dyn Fn(&Vec<BF>) -> EF + Sync> = Box::new(|data: &Vec<BF>| -> EF {
            let product = data.iter().fold(BF::ONE, |prod, d| prod * d);
            EF::new(MF::new(product, BF::zero()), MF::zero(), MF::zero())
        });

        // Multiplies a base field element to an extension field element
        let mult_be: Box<dyn Fn(&BF, &EF) -> EF + Sync> = Box::new(
            |base_field_element: &BF, extension_field_element: &EF| -> EF {
                let mut result: EF = EF::from(*extension_field_element);
                result.mul_assign_by_base_field(&MF::new(*base_field_element, BF::zero()));
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
        let (interpolation_matrix, scaled_det) =
            generate_binomial_interpolation_mult_matrix_transpose(degree);

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

    #[rstest]
    fn check_sumcheck_product(
        #[values(5, 10)] nv: usize,
        #[values(1, 3, 4)] degree: usize,
        #[values(
            AlgorithmType::Naive,
            AlgorithmType::WitnessChallengeSeparation,
            AlgorithmType::Precomputation,
            AlgorithmType::ToomCook
        )]
        algorithm: AlgorithmType,
    ) {
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(nv, degree, 3, algorithm, false)
                .1
                .unwrap(),
            true
        );
    }

    #[rstest]
    fn check_sumcheck_product_with_threshold(
        #[values(5, 8)] nv: usize,
        #[values(2)] degree: usize,
        #[values(nv / 2, nv)] round_t: usize,
        #[values(
            AlgorithmType::Naive,
            AlgorithmType::WitnessChallengeSeparation,
            AlgorithmType::Precomputation,
            AlgorithmType::ToomCook
        )]
        algorithm: AlgorithmType,
    ) {
        assert_eq!(
            sumcheck_test_helper(nv, degree, round_t, algorithm, false)
                .1
                .unwrap(),
            true
        );
    }

    #[rstest]
    fn check_proof_consistency(
        #[values(5, 8)] nv: usize,
        #[values(1, 4)] degree: usize,
        #[values(1, nv / 2)] round_t: usize,
    ) {
        let (proof_1, result_1) =
            sumcheck_test_helper(nv, degree, round_t, AlgorithmType::Naive, false);
        let (proof_2, result_2) = sumcheck_test_helper(
            nv,
            degree,
            round_t,
            AlgorithmType::WitnessChallengeSeparation,
            false,
        );
        let (proof_3, result_3) =
            sumcheck_test_helper(nv, degree, round_t, AlgorithmType::Precomputation, false);
        let (proof_4, result_4) =
            sumcheck_test_helper(nv, degree, round_t, AlgorithmType::ToomCook, true);

        assert_eq!(result_1.unwrap(), true);
        assert_eq!(result_2.unwrap(), true);
        assert_eq!(result_3.unwrap(), true);
        assert_eq!(result_4.unwrap(), true);
        assert_eq!(proof_1, proof_2);
        assert_eq!(proof_2, proof_3);
        assert_eq!(proof_3, proof_4);
    }
}

#[cfg(test)]
mod fq12_tests {
    use crate::error::SumcheckError;
    use crate::prover::AlgorithmType;
    use crate::prover::ProverState;
    use crate::prover::SumcheckProof;
    use crate::tests::test_helpers::create_sumcheck_test_data;
    use crate::tests::test_helpers::generate_binomial_interpolation_mult_matrix_transpose;
    use crate::tests::test_helpers::get_maps_from_matrix;
    use crate::IPForMLSumcheck;
    use ark_ff::Field;
    use ark_ff::Zero;
    use ark_std::iterable::Iterable;
    use ark_std::vec::Vec;
    use merlin::Transcript;
    use rstest::rstest;

    type BF = ark_bls12_381::Fq;
    type TWOF = ark_bls12_381::Fq2;
    type SIXF = ark_bls12_381::Fq6;
    type EF = ark_bls12_381::Fq12;

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
        let to_ef: Box<dyn Fn(&BF) -> EF + Sync> = Box::new(|base_field_element: &BF| -> EF {
            EF::new(
                SIXF::new(
                    TWOF::new(*base_field_element, BF::zero()),
                    TWOF::zero(),
                    TWOF::zero(),
                ),
                SIXF::zero(),
            )
        });

        // Define the combine function over EF
        let combine_fn_ef: Box<dyn Fn(&Vec<EF>) -> EF + Sync> = Box::new(|data: &Vec<EF>| -> EF {
            let product = data.iter().fold(EF::ONE, |prod, d| prod * d);
            product
        });

        // Define the combine function over BF
        let combine_fn_bf: Box<dyn Fn(&Vec<BF>) -> EF + Sync> = Box::new(|data: &Vec<BF>| -> EF {
            let product = data.iter().fold(BF::ONE, |prod, d| prod * d);
            EF::new(
                SIXF::new(TWOF::new(product, BF::zero()), TWOF::zero(), TWOF::zero()),
                SIXF::zero(),
            )
        });

        // Multiplies a base field element to an extension field element
        let mult_be: Box<dyn Fn(&BF, &EF) -> EF + Sync> = Box::new(
            |base_field_element: &BF, extension_field_element: &EF| -> EF {
                let mut result: EF = EF::from(*extension_field_element);
                result.mul_assign_by_basefield(&SIXF::new(
                    TWOF::new(*base_field_element, BF::zero()),
                    TWOF::zero(),
                    TWOF::zero(),
                ));
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
        let (interpolation_matrix, scaled_det) =
            generate_binomial_interpolation_mult_matrix_transpose(degree);

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

    #[rstest]
    fn check_sumcheck_product(
        #[values(5, 10)] nv: usize,
        #[values(1, 3, 4)] degree: usize,
        #[values(
            AlgorithmType::Naive,
            AlgorithmType::WitnessChallengeSeparation,
            AlgorithmType::Precomputation,
            AlgorithmType::ToomCook
        )]
        algorithm: AlgorithmType,
    ) {
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(nv, degree, 3, algorithm, false)
                .1
                .unwrap(),
            true
        );
    }

    #[rstest]
    fn check_sumcheck_product_with_threshold(
        #[values(5, 8)] nv: usize,
        #[values(2)] degree: usize,
        #[values(nv / 2, nv)] round_t: usize,
        #[values(
            AlgorithmType::Naive,
            AlgorithmType::WitnessChallengeSeparation,
            AlgorithmType::Precomputation,
            AlgorithmType::ToomCook
        )]
        algorithm: AlgorithmType,
    ) {
        assert_eq!(
            sumcheck_test_helper(nv, degree, round_t, algorithm, false)
                .1
                .unwrap(),
            true
        );
    }

    #[rstest]
    fn check_proof_consistency(
        #[values(5, 8)] nv: usize,
        #[values(1, 4)] degree: usize,
        #[values(1, nv / 2)] round_t: usize,
    ) {
        let (proof_1, result_1) =
            sumcheck_test_helper(nv, degree, round_t, AlgorithmType::Naive, false);
        let (proof_2, result_2) = sumcheck_test_helper(
            nv,
            degree,
            round_t,
            AlgorithmType::WitnessChallengeSeparation,
            false,
        );
        let (proof_3, result_3) =
            sumcheck_test_helper(nv, degree, round_t, AlgorithmType::Precomputation, false);
        let (proof_4, result_4) =
            sumcheck_test_helper(nv, degree, round_t, AlgorithmType::ToomCook, true);

        assert_eq!(result_1.unwrap(), true);
        assert_eq!(result_2.unwrap(), true);
        assert_eq!(result_3.unwrap(), true);
        assert_eq!(result_4.unwrap(), true);
        assert_eq!(proof_1, proof_2);
        assert_eq!(proof_2, proof_3);
        assert_eq!(proof_3, proof_4);
    }
}
