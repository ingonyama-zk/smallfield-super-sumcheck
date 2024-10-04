#[cfg(test)]
mod fq_tests {
    use std::time::Instant;

    use crate::error::SumcheckError;
    use crate::prover::AlgorithmType;
    use crate::prover::ProverState;
    use crate::prover::SumcheckProof;
    use crate::tests::test_helpers::common_setup_for_toom_cook;
    use crate::tests::test_helpers::create_sumcheck_test_data;
    use crate::tests::test_helpers::WitnessType;
    use crate::IPForMLSumcheck;
    use ark_ff::Field;
    use ark_std::iterable::Iterable;
    use ark_std::vec::Vec;
    use merlin::Transcript;
    use rstest::rstest;
    // use std::sync::atomic::{AtomicUsize, Ordering};

    type BF = ark_bn254::Fr;
    type EF = ark_bn254::Fr;

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
            Box::new(|base_field_element: &BF| -> EF { *base_field_element });

        // Define the combine function over EF
        let combine_fn_ef: Box<dyn Fn(&Vec<EF>) -> EF + Sync> = Box::new(|data: &Vec<EF>| -> EF {
            let product = data.iter().fold(EF::ONE, |prod, d| prod * d);
            product
        });

        // Define the combine function over BF
        let combine_fn_bf: Box<dyn Fn(&Vec<BF>) -> EF + Sync> = Box::new(|data: &Vec<BF>| -> EF {
            let product = data.iter().fold(BF::ONE, |prod, d| prod * d);
            product
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

    pub fn sumcheck_test_helper(
        nv: usize,
        degree: usize,
        round_t: usize,
        algorithm: AlgorithmType,
        with_inversions: bool,
        witness_type: WitnessType,
    ) -> (SumcheckProof<EF>, Result<bool, SumcheckError>, u128) {
        let (to_ef, combine_ef, combine_bf, mult_be, mult_ee, mult_bb, add_ee) =
            create_primitive_functions();
        let (mut prover_state, claimed_sum): (ProverState<EF, BF>, BF) =
            create_sumcheck_test_data(nv, degree, algorithm.clone(), witness_type);

        let (
            emaps_base,
            emaps_base_int,
            projective_map_indices,
            imaps_base,
            imaps_ext,
            mut scaled_det,
        ) = common_setup_for_toom_cook::<BF, EF>(degree, with_inversions);

        // create a proof
        let mut prover_transcript = Transcript::new(b"test_sumcheck");
        let start = Instant::now();
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
            Some(&emaps_base_int),
            Some(&projective_map_indices),
            Some(&imaps_base),
            Some(&imaps_ext),
        );
        let elapsed = start.elapsed().as_millis();

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
        (proof, result, elapsed)
    }

    #[rstest]
    fn check_sumcheck_product_with_threshold(
        #[values(16, 18, 20, 22, 24, 26)] nv: usize,
        #[values(2, 3)] degree: usize,
        #[values(1, 2, 3, 4)] round_t: usize,
        #[values(WitnessType::U8)] witness_type: WitnessType,
    ) {
        // Run with command:
        // cargo test bn254 --release -- --nocapture | grep -v "ok"
        let (_, result_1, elapsed_1) = sumcheck_test_helper(
            nv,
            degree,
            round_t,
            AlgorithmType::Naive,
            false,
            witness_type,
        );
        assert_eq!(result_1.unwrap(), true);

        let (_, result_3, elapsed_3) = sumcheck_test_helper(
            nv,
            degree,
            round_t,
            AlgorithmType::Precomputation,
            false,
            witness_type,
        );
        assert_eq!(result_3.unwrap(), true);

        let (_, result_4, elapsed_4) = sumcheck_test_helper(
            nv,
            degree,
            round_t,
            AlgorithmType::ToomCook,
            false,
            witness_type,
        );
        assert_eq!(result_4.unwrap(), true);

        println!(
            "{},{},{},{:.2?},{:.2?},{:.2?}",
            nv, degree, round_t, elapsed_1, elapsed_3, elapsed_4,
        );
    }
}
