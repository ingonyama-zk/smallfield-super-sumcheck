#[cfg(test)]
mod fq4_tests {

    use crate::error::SumcheckError;
    use crate::prover::AlgorithmType;
    use crate::prover::ProverState;
    use crate::prover::SumcheckProof;
    use crate::tests::test_helpers::common_setup_for_toom_cook;
    use crate::tests::test_helpers::create_sumcheck_test_data;
    use crate::tower_fields::binius::BiniusTowerField;
    use crate::tower_fields::binius::OptimizedBiniusTowerField;
    use crate::tower_fields::TowerField;
    use crate::IPForMLSumcheck;

    use ark_std::iterable::Iterable;
    use ark_std::vec::Vec;
    use merlin::Transcript;
    use num::One;
    use rstest::rstest;

    use chrono::Local;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::Instant;

    // Define a global atomic counter
    static BB_COUNT: AtomicUsize = AtomicUsize::new(0);

    // Define a function to get the current call count
    pub fn get_bb_count() -> usize {
        BB_COUNT.load(Ordering::SeqCst)
    }

    type BF = OptimizedBiniusTowerField;
    type EF = OptimizedBiniusTowerField;

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
        let (mut prover_state, claimed_sum, eq_challenges): (
            ProverState<EF, BF>,
            BF,
            Option<Vec<EF>>,
        ) = create_sumcheck_test_data(nv, degree, algorithm.clone(), num_levels);

        let (emaps_base, projective_map_indices, imaps_base, imaps_ext, mut scaled_det) =
            common_setup_for_toom_cook::<BF, EF>(degree);

        if eq_challenges.is_some() {
            assert!(
                algorithm == AlgorithmType::PrecomputationWithEq
                    || algorithm == AlgorithmType::ToomCookWithEq
                    || algorithm == AlgorithmType::NaiveWithEq
                    || algorithm == AlgorithmType::WitnessChallengeSeparationWithEq,
                "Eq challenges are generated only for algorithm 3/4 with eq polynomial."
            );
        }

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
            Some(scaled_det),
            Some(claimed_sum),
        );

        // println!("mult_bb was called {} times", get_bb_count());

        let mut round_t_v = round_t;
        if !(algorithm == AlgorithmType::ToomCook || algorithm == AlgorithmType::ToomCookWithEq) {
            scaled_det = BF::one();
            round_t_v = 0;
        }

        let mut verifier_transcript = Transcript::new(b"test_sumcheck");
        let result = IPForMLSumcheck::<EF, BF>::verify(
            claimed_sum,
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
        // NAIVE with eq polynomial
        //
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(10, deg, thresh, AlgorithmType::NaiveWithEq, 1)
                .1
                .unwrap(),
            true
        );
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(12, deg, thresh, AlgorithmType::NaiveWithEq, 1)
                .1
                .unwrap(),
            true
        );
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(14, deg, thresh, AlgorithmType::NaiveWithEq, 1)
                .1
                .unwrap(),
            true
        );
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(16, deg, thresh, AlgorithmType::NaiveWithEq, 1)
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
        // Algorithm 3 with eq polynomial
        //
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(10, deg, thresh, AlgorithmType::PrecomputationWithEq, 1)
                .1
                .unwrap(),
            true
        );
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(12, deg, thresh, AlgorithmType::PrecomputationWithEq, 1)
                .1
                .unwrap(),
            true
        );
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(14, deg, thresh, AlgorithmType::PrecomputationWithEq, 1)
                .1
                .unwrap(),
            true
        );
        assert_eq!(
            // Runs memory-heavy algorithm 3 and 4 only for first three rounds.
            sumcheck_test_helper(16, deg, thresh, AlgorithmType::PrecomputationWithEq, 1)
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

        //
        // Algorithm 4 with equality polynomial
        //
        assert_eq!(
            sumcheck_test_helper(10, deg, thresh, AlgorithmType::ToomCookWithEq, 1)
                .1
                .unwrap(),
            true
        );
        assert_eq!(
            sumcheck_test_helper(12, deg, thresh, AlgorithmType::ToomCookWithEq, 1)
                .1
                .unwrap(),
            true
        );
        assert_eq!(
            sumcheck_test_helper(14, deg, thresh, AlgorithmType::ToomCookWithEq, 1)
                .1
                .unwrap(),
            true
        );
        assert_eq!(
            sumcheck_test_helper(16, deg, thresh, AlgorithmType::ToomCookWithEq, 1)
                .1
                .unwrap(),
            true
        );
    }

    #[test]
    fn check_algo4_eq() {
        let deg = 3;
        let thresh = 2;
        //
        // Algorithm 4 with equality polynomial
        //
        assert_eq!(
            sumcheck_test_helper(16, deg, thresh, AlgorithmType::ToomCookWithEq, 1)
                .1
                .unwrap(),
            true
        );
    }

    #[test]
    fn benchmark_prover_to_get_optimal_round_t() {
        for (nv, degree) in vec![(16, 2), (18, 2), (20, 2), (22, 2), (24, 2)] {
            let thresholds = vec![1, 2, 3, 4, 5];
            let algorithms = vec![
                AlgorithmType::Naive,          // algo1
                AlgorithmType::ToomCook,       // algo4
                AlgorithmType::NaiveWithEq,    // algo1eq
                AlgorithmType::ToomCookWithEq, // algo4eq
            ];

            println!(
                "\nTest started at: {}",
                Local::now().format("%Y-%m-%d %H:%M:%S")
            );

            // Table header with increased column width
            println!("╔══════════════════════════════════════════════════════════════╗");
            println!(
                "║ Fixed Configurations: n = {}, degree = {}                     ║",
                nv, degree
            );
            println!("╠═════════════════╦════════════════════════════════════════════╣");
            println!("║ Algorithm       ║ Runtime (s) by threshold t                 ║");
            println!("╠═════════════════╬════════╦════════╦════════╦════════╦════════╣");
            println!("║                 ║  t=1   ║  t=2   ║  t=3   ║  t=4   ║  t=5   ║");
            println!("╠═════════════════╬════════╬════════╬════════╬════════╬════════╣");

            // For each algorithm
            for algorithm in algorithms {
                let algo_name = match algorithm {
                    AlgorithmType::NaiveWithEq => "Algo1Eq",
                    AlgorithmType::ToomCookWithEq => "Algo4Eq",
                    AlgorithmType::Naive => "Algo1",
                    AlgorithmType::ToomCook => "Algo4",
                    _ => "Unknown",
                };

                print!("║ {:<15} ║", algo_name);

                // For each threshold
                for &t in &thresholds {
                    let skip_condition_1 = (algorithm == AlgorithmType::Naive
                        || algorithm == AlgorithmType::NaiveWithEq)
                        && t > 1;
                    if skip_condition_1 {
                        // Leave the cell empty for t > 1 for Algo1 and Algo1Eq
                        print!("        ║");
                        continue;
                    }

                    // Run the test and measure time
                    let start = Instant::now();
                    let result = sumcheck_test_helper(nv, degree, t, algorithm.clone(), 1);
                    let elapsed = start.elapsed();
                    let time_s = elapsed.as_secs_f64(); // Convert to seconds

                    // Verify the result is correct
                    assert_eq!(
                        result.1.unwrap(),
                        true,
                        "Verification failed for algorithm {:?} with t={}",
                        algorithm,
                        t
                    );

                    // Print runtime in seconds with 2 decimal places
                    print!(" {:>6.2} ║", time_s);
                }

                // End the row
                println!();
                println!("╠═════════════════╬════════╬════════╬════════╬════════╬════════╣");
            }
            println!("╚═════════════════╩════════╩════════╩════════╩════════╩════════╝");
        }
    }

    #[rstest]
    fn check_sumcheck_product(
        #[values(16, 18)] nv: usize,
        #[values(2)] degree: usize,
        #[values(
            AlgorithmType::Naive,
            // AlgorithmType::WitnessChallengeSeparation,
            // AlgorithmType::Precomputation,
            AlgorithmType::ToomCook,
            AlgorithmType::NaiveWithEq,
            // AlgorithmType::WitnessChallengeSeparationWithEq,
            // AlgorithmType::PrecomputationWithEq,
            AlgorithmType::ToomCookWithEq
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

    // TODO: proof consistency actually doesn't work because with binary tower fields,
    // the proof is not consistent across algorithms. This is because the algorithms
    // use different methods to compute the polynomial evaluations.
    #[ignore]
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
