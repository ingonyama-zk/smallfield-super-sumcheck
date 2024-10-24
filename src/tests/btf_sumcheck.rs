#[cfg(test)]
mod fq4_tests {

    use crate::error::SumcheckError;
    use crate::prover::AlgorithmType;
    use crate::prover::ProverState;
    use crate::prover::SumcheckProof;
    use crate::tests::test_helpers::common_setup_for_toom_cook;
    use crate::tests::test_helpers::create_sumcheck_test_data;
    use crate::tower_fields::binius::BiniusTowerField;
    use crate::tower_fields::TowerField;
    use crate::IPForMLSumcheck;

    use ark_std::iterable::Iterable;
    use ark_std::vec::Vec;
    use merlin::Transcript;
    use num::One;
    use rstest::rstest;

    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::Instant;

    // Define a global atomic counter
    static BB_COUNT: AtomicUsize = AtomicUsize::new(0);

    // Define a function to get the current call count
    pub fn get_bb_count() -> usize {
        BB_COUNT.load(Ordering::SeqCst)
    }

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
        let to_ef: Box<dyn Fn(&BF) -> EF + Sync> = Box::new(|base_field_element: &BF| -> EF {
            EF::new(base_field_element.get_val(), None)
        });

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
            Box::new(|bb_element1: &BF, bb_element2: &BF| -> BF {
                // Increment the counter
                BB_COUNT.fetch_add(1, Ordering::SeqCst);
                bb_element1 * bb_element2
            });

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
        num_levels: usize,
    ) -> (SumcheckProof<EF>, Result<bool, SumcheckError>) {
        let (to_ef, combine_ef, combine_bf, mult_be, mult_ee, mult_bb, add_ee) =
            create_primitive_functions();
        let (mut prover_state, claimed_sum): (ProverState<EF, BF>, BF) =
            create_sumcheck_test_data(nv, degree, algorithm.clone(), num_levels);

        let (emaps_base, projective_map_indices, imaps_base, imaps_ext, mut scaled_det) =
            common_setup_for_toom_cook::<BF, EF>(degree);

        println!(
            "n = {}, d = {}, t = {}, algo = {:?}",
            nv, degree, round_t, algorithm
        );

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
            Some(&projective_map_indices),
            Some(&imaps_base),
            Some(&imaps_ext),
        );
        let elapsed = start.elapsed();
        println!("prove_time: {:.2?}", elapsed);

        // println!("mult_bb was called {} times", get_bb_count());

        let mut round_t_v = round_t;
        if algorithm != AlgorithmType::ToomCook {
            scaled_det = BF::one();
            round_t_v = 0;
        }

        let mut verifier_transcript = Transcript::new(b"test_sumcheck");
        let result = IPForMLSumcheck::<EF, BF>::verify(
            to_ef(&claimed_sum),
            &proof,
            &mut verifier_transcript,
            algorithm,
            Some(scaled_det),
            Some(round_t_v),
        );
        (proof, result)
    }

    #[test]
    fn check_simple_sumcheck_product() {
        let deg = 3;
        let thresh = 2;
        //
        // NAIVE
        //
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(10, deg, thresh, AlgorithmType::Naive, 1)
                .1
                .unwrap(),
            true
        );
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(12, deg, thresh, AlgorithmType::Naive, 1)
                .1
                .unwrap(),
            true
        );
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(14, deg, thresh, AlgorithmType::Naive, 1)
                .1
                .unwrap(),
            true
        );
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(16, deg, thresh, AlgorithmType::Naive, 1)
                .1
                .unwrap(),
            true
        );

        //
        // Algorithm 3
        //
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(10, deg, thresh, AlgorithmType::Precomputation, 1)
                .1
                .unwrap(),
            true
        );
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(12, deg, thresh, AlgorithmType::Precomputation, 1)
                .1
                .unwrap(),
            true
        );
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(14, deg, thresh, AlgorithmType::Precomputation, 1)
                .1
                .unwrap(),
            true
        );
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(16, deg, thresh, AlgorithmType::Precomputation, 1)
                .1
                .unwrap(),
            true
        );

        //
        // Algorithm 4
        //
        assert_eq!(
            sumcheck_test_helper(10, deg, thresh, AlgorithmType::ToomCook, 1)
                .1
                .unwrap(),
            true
        );
        assert_eq!(
            sumcheck_test_helper(12, deg, thresh, AlgorithmType::ToomCook, 1)
                .1
                .unwrap(),
            true
        );
        assert_eq!(
            sumcheck_test_helper(14, deg, thresh, AlgorithmType::ToomCook, 1)
                .1
                .unwrap(),
            true
        );
        assert_eq!(
            sumcheck_test_helper(16, deg, thresh, AlgorithmType::ToomCook, 1)
                .1
                .unwrap(),
            true
        );
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
            sumcheck_test_helper(nv, degree, 3, algorithm, 1).1.unwrap(),
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
            sumcheck_test_helper(nv, degree, round_t, algorithm, 1)
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
            sumcheck_test_helper(nv, degree, round_t, AlgorithmType::Naive, 1);
        let (proof_2, result_2) = sumcheck_test_helper(
            nv,
            degree,
            round_t,
            AlgorithmType::WitnessChallengeSeparation,
            1,
        );
        let (proof_3, result_3) =
            sumcheck_test_helper(nv, degree, round_t, AlgorithmType::Precomputation, 1);
        let (proof_4, result_4) =
            sumcheck_test_helper(nv, degree, round_t, AlgorithmType::ToomCook, 1);

        assert_eq!(result_1.unwrap(), true);
        assert_eq!(result_2.unwrap(), true);
        assert_eq!(result_3.unwrap(), true);
        assert_eq!(result_4.unwrap(), true);
        assert_eq!(proof_1, proof_2);
        assert_eq!(proof_2, proof_3);
        assert_eq!(proof_3, proof_4);
    }
}
