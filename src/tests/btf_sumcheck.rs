#[cfg(test)]
mod fq4_tests {
    use std::time::Instant;

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
    use rand::Rng;
    use rstest::rstest;

    use std::sync::atomic::{AtomicUsize, Ordering};

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
    ) -> (SumcheckProof<EF>, Result<bool, SumcheckError>) {
        let (to_ef, combine_ef, combine_bf, mult_be, mult_ee, mult_bb, add_ee) =
            create_primitive_functions();
        let (mut prover_state, claimed_sum): (ProverState<EF, BF>, BF) =
            create_sumcheck_test_data(nv, degree, algorithm.clone());

        let (emaps_base, projective_map_indices, imaps_base, imaps_ext, mut scaled_det) =
            common_setup_for_toom_cook::<BF, EF>(degree);

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

        println!("mult_bb was called {} times", get_bb_count());

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
        // assert_eq!(
        //     // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
        //     sumcheck_test_helper(8, 3, 5, AlgorithmType::Precomputation)
        //         .1
        //         .unwrap(),
        //     true
        // );

        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(8, 3, 5, AlgorithmType::Naive)
                .1
                .unwrap(),
            true
        );

        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(8, 3, 5, AlgorithmType::ToomCook)
                .1
                .unwrap(),
            true
        );
    }

    #[test]
    fn check_simple_mult() {
        let mut input_1 = 68 as i16;
        let multiplicand = 3 as i16;
        let n = 10000;
        let start = Instant::now();
        for _ in 0..n {
            input_1 = ((input_1 as i32) * (multiplicand as i32)) as i16;
        }
        let elapsed = start.elapsed();
        println!("time: {:?}", elapsed);
        println!("input = {}", input_1);
        println!("time per mult = {:?}", elapsed / n);
    }

    #[test]
    fn check_simple_mult_float() {
        let mut rng = rand::thread_rng();
        let num_elements = 100000;
        let input_a: Vec<f64> = (0..num_elements).map(|_| rng.gen::<f64>()).collect();
        let input_b: Vec<f64> = (0..num_elements).map(|_| rng.gen::<f64>()).collect();

        let start = Instant::now();
        let _ip_ab: Vec<f64> = input_a
            .iter()
            .zip(input_b.iter())
            .map(|(a, b)| a * b)
            .collect();
        let elapsed = start.elapsed();
        println!("time: {:?}", elapsed);
        // println!("out = {}", ip_ab[10]);
        println!("time per mult = {:?}", elapsed / num_elements);
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
            sumcheck_test_helper(nv, degree, 3, algorithm).1.unwrap(),
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
            sumcheck_test_helper(nv, degree, round_t, algorithm)
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
        let (proof_1, result_1) = sumcheck_test_helper(nv, degree, round_t, AlgorithmType::Naive);
        let (proof_2, result_2) = sumcheck_test_helper(
            nv,
            degree,
            round_t,
            AlgorithmType::WitnessChallengeSeparation,
        );
        let (proof_3, result_3) =
            sumcheck_test_helper(nv, degree, round_t, AlgorithmType::Precomputation);
        let (proof_4, result_4) =
            sumcheck_test_helper(nv, degree, round_t, AlgorithmType::ToomCook);

        assert_eq!(result_1.unwrap(), true);
        assert_eq!(result_2.unwrap(), true);
        assert_eq!(result_3.unwrap(), true);
        assert_eq!(result_4.unwrap(), true);
        assert_eq!(proof_1, proof_2);
        assert_eq!(proof_2, proof_3);
        assert_eq!(proof_3, proof_4);
    }
}
