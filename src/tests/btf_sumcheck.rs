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

    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::Instant;
    use sysinfo::System;

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

    /// Returns current resident set size in MB (macOS and Linux, but not peak)
    fn get_current_rss_mb() -> f64 {
        let mut sys = System::new();
        sys.refresh_process(sysinfo::get_current_pid().unwrap());
        let pid = sysinfo::get_current_pid().unwrap();
        if let Some(proc) = sys.process(pid) {
            // memory() returns bytes
            proc.memory() as f64 / 1024.0 / 1024.0
        } else {
            0.0
        }
    }

    pub fn sumcheck_test_helper(
        nv: usize,
        degree: usize,
        round_t: usize,
        algorithm: AlgorithmType,
        num_levels: usize,
    ) -> (SumcheckProof<EF>, Result<bool, SumcheckError>, f64, f64) {
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
        let _ = get_current_rss_mb();
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
            Some(scaled_det),
            Some(claimed_sum),
        );
        let elapsed = start.elapsed();
        let time_s = elapsed.as_secs_f64();
        let mem_mb = get_current_rss_mb();

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
        (proof, result, time_s, mem_mb)
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

    /// Prints a table of runtimes and memory for all four algorithms for given nv, degree, round_t
    pub fn helper_benchmark_prover(nv: usize, degree: usize) {
        let algorithms = vec![
            AlgorithmType::Naive,          // Algo1
            AlgorithmType::ToomCook,       // Algo4
            AlgorithmType::NaiveWithEq,    // Algo1Eq
            AlgorithmType::ToomCookWithEq, // Algo4Eq
        ];
        let algo_names = vec!["Algo1", "Algo4", "Algo1Eq", "Algo4Eq"];

        debug_assert!(degree == 2 || degree == 3);

        println!("╔═══════════════════════════════════════════════════════════╗");
        println!(
            "║ Fixed Configurations: n = {}, degree = {},                 ║",
            nv, degree
        );
        println!("╠═════════════════╦════════════════════╦════════════════════╣");
        println!("║ Algorithm       ║ Runtime (s)        ║ Mem (MB)           ║");
        println!("╠═════════════════╬════════════════════╬════════════════════╣");

        for (algo, name) in algorithms.iter().zip(algo_names.iter()) {
            // Choose round_t based on empirical results
            let mut _round_t = 1;
            if degree == 2 && *algo == AlgorithmType::ToomCook {
                _round_t = 4;
            } else if degree == 2 && *algo == AlgorithmType::ToomCookWithEq {
                _round_t = 3;
            } else if degree == 3 && *algo == AlgorithmType::ToomCook {
                _round_t = 3;
            } else if degree == 3 && *algo == AlgorithmType::ToomCookWithEq {
                _round_t = 2;
            }

            let (_, result, time_s, mem_mb) =
                sumcheck_test_helper(nv, degree, _round_t, algo.clone(), 1);

            // Verify the result is correct
            assert_eq!(
                result.unwrap(),
                true,
                "Verification failed for algorithm {:?} with t={}",
                algo,
                _round_t
            );

            let mut algo_print_name = name.to_string();
            if *algo == AlgorithmType::ToomCook || *algo == AlgorithmType::ToomCookWithEq {
                algo_print_name = format!("{} (t={})", name, _round_t);
            }

            println!(
                "║ {:<15} ║ {:>10.2} s       ║ {:>10.0} MB      ║",
                algo_print_name, time_s, mem_mb
            );
            println!("╠═════════════════╬════════════════════╬════════════════════╣");
        }
        println!("╚═════════════════╩════════════════════╩════════════════════╝");
    }

    pub fn helper_benchmark_prover_algo(nv: usize, degree: usize, algo: AlgorithmType, name: &str) {
        debug_assert!(degree == 2 || degree == 3);

        println!("╔═══════════════════════════════════════════════════════════╗");
        println!(
            "║ Fixed Configurations: n = {}, degree = {},                 ║",
            nv, degree
        );
        println!("╠═════════════════╦════════════════════╦════════════════════╣");
        println!("║ Algorithm       ║ Runtime (s)        ║ Mem (MB)           ║");
        println!("╠═════════════════╬════════════════════╬════════════════════╣");

        // Choose round_t based on empirical results
        let mut _round_t = 1;
        if degree == 2 && algo == AlgorithmType::ToomCook {
            _round_t = 4;
        } else if degree == 2 && algo == AlgorithmType::ToomCookWithEq {
            _round_t = 3;
        } else if degree == 3 && algo == AlgorithmType::ToomCook {
            _round_t = 3;
        } else if degree == 3 && algo == AlgorithmType::ToomCookWithEq {
            _round_t = 2;
        }

        let (_, result, time_s, mem_mb) =
            sumcheck_test_helper(nv, degree, _round_t, algo.clone(), 1);

        // Verify the result is correct
        assert_eq!(
            result.unwrap(),
            true,
            "Verification failed for algorithm {:?} with t={}",
            algo,
            _round_t
        );

        let mut algo_print_name = name.to_string();
        if algo == AlgorithmType::ToomCook || algo == AlgorithmType::ToomCookWithEq {
            algo_print_name = format!("{} (t={})", name, _round_t);
        }

        println!(
            "║ {:<15} ║ {:>10.2} s       ║ {:>10.0} MB      ║",
            algo_print_name, time_s, mem_mb
        );
        println!("╠═════════════════╬════════════════════╬════════════════════╣");

        println!("╚═════════════════╩════════════════════╩════════════════════╝");
    }

    // Degree 2 tests, algo1
    #[test]
    fn benchmark_prover_n16_d2_a1() {
        helper_benchmark_prover_algo(16, 2, AlgorithmType::Naive, "Algo1");
    }
    #[test]
    fn benchmark_prover_n18_d2_a1() {
        helper_benchmark_prover_algo(18, 2, AlgorithmType::Naive, "Algo1");
    }
    #[test]
    fn benchmark_prover_n20_d2_a1() {
        helper_benchmark_prover_algo(20, 2, AlgorithmType::Naive, "Algo1");
    }
    #[test]
    fn benchmark_prover_n22_d2_a1() {
        helper_benchmark_prover_algo(22, 2, AlgorithmType::Naive, "Algo1");
    }
    #[test]
    fn benchmark_prover_n24_d2_a1() {
        helper_benchmark_prover_algo(24, 2, AlgorithmType::Naive, "Algo1");
    }
    #[test]
    fn benchmark_prover_n26_d2_a1() {
        helper_benchmark_prover_algo(26, 2, AlgorithmType::Naive, "Algo1");
    }
    #[test]
    fn benchmark_prover_n28_d2_a1() {
        helper_benchmark_prover_algo(28, 2, AlgorithmType::Naive, "Algo1");
    }

    // Degree 2 tests, algo4
    #[test]
    fn benchmark_prover_n16_d2_a4() {
        helper_benchmark_prover_algo(16, 2, AlgorithmType::ToomCook, "Algo4");
    }
    #[test]
    fn benchmark_prover_n18_d2_a4() {
        helper_benchmark_prover_algo(18, 2, AlgorithmType::ToomCook, "Algo4");
    }
    #[test]
    fn benchmark_prover_n20_d2_a4() {
        helper_benchmark_prover_algo(20, 2, AlgorithmType::ToomCook, "Algo4");
    }
    #[test]
    fn benchmark_prover_n22_d2_a4() {
        helper_benchmark_prover_algo(22, 2, AlgorithmType::ToomCook, "Algo4");
    }
    #[test]
    fn benchmark_prover_n24_d2_a4() {
        helper_benchmark_prover_algo(24, 2, AlgorithmType::ToomCook, "Algo4");
    }
    #[test]
    fn benchmark_prover_n26_d2_a4() {
        helper_benchmark_prover_algo(26, 2, AlgorithmType::ToomCook, "Algo4");
    }
    #[test]
    fn benchmark_prover_n28_d2_a4() {
        helper_benchmark_prover_algo(28, 2, AlgorithmType::ToomCook, "Algo4");
    }

    // Degree 2 tests, algo1 with eq
    #[test]
    fn benchmark_prover_n16_d2_a1_eq() {
        helper_benchmark_prover_algo(16, 2, AlgorithmType::NaiveWithEq, "Algo1Eq");
    }
    #[test]
    fn benchmark_prover_n18_d2_a1_eq() {
        helper_benchmark_prover_algo(18, 2, AlgorithmType::NaiveWithEq, "Algo1Eq");
    }
    #[test]
    fn benchmark_prover_n20_d2_a1_eq() {
        helper_benchmark_prover_algo(20, 2, AlgorithmType::NaiveWithEq, "Algo1Eq");
    }
    #[test]
    fn benchmark_prover_n22_d2_a1_eq() {
        helper_benchmark_prover_algo(22, 2, AlgorithmType::NaiveWithEq, "Algo1Eq");
    }
    #[test]
    fn benchmark_prover_n24_d2_a1_eq() {
        helper_benchmark_prover_algo(24, 2, AlgorithmType::NaiveWithEq, "Algo1Eq");
    }
    #[test]
    fn benchmark_prover_n26_d2_a1_eq() {
        helper_benchmark_prover_algo(26, 2, AlgorithmType::NaiveWithEq, "Algo1Eq");
    }
    #[test]
    fn benchmark_prover_n28_d2_a1_eq() {
        helper_benchmark_prover_algo(28, 2, AlgorithmType::NaiveWithEq, "Algo1Eq");
    }

    // Degree 2 tests, algo4 with eq
    #[test]
    fn benchmark_prover_n16_d2_a4_eq() {
        helper_benchmark_prover_algo(16, 2, AlgorithmType::ToomCookWithEq, "Algo4Eq");
    }
    #[test]
    fn benchmark_prover_n18_d2_a4_eq() {
        helper_benchmark_prover_algo(18, 2, AlgorithmType::ToomCookWithEq, "Algo4Eq");
    }
    #[test]
    fn benchmark_prover_n20_d2_a4_eq() {
        helper_benchmark_prover_algo(20, 2, AlgorithmType::ToomCookWithEq, "Algo4Eq");
    }
    #[test]
    fn benchmark_prover_n22_d2_a4_eq() {
        helper_benchmark_prover_algo(22, 2, AlgorithmType::ToomCookWithEq, "Algo4Eq");
    }
    #[test]
    fn benchmark_prover_n24_d2_a4_eq() {
        helper_benchmark_prover_algo(24, 2, AlgorithmType::ToomCookWithEq, "Algo4Eq");
    }
    #[test]
    fn benchmark_prover_n26_d2_a4_eq() {
        helper_benchmark_prover_algo(26, 2, AlgorithmType::ToomCookWithEq, "Algo4Eq");
    }
    #[test]
    fn benchmark_prover_n28_d2_a4_eq() {
        helper_benchmark_prover_algo(28, 2, AlgorithmType::ToomCookWithEq, "Algo4Eq");
    }

    // Degree 3 tests, algo1
    #[test]
    fn benchmark_prover_n16_d3_a1() {
        helper_benchmark_prover_algo(16, 3, AlgorithmType::Naive, "Algo1");
    }
    #[test]
    fn benchmark_prover_n18_d3_a1() {
        helper_benchmark_prover_algo(18, 3, AlgorithmType::Naive, "Algo1");
    }
    #[test]
    fn benchmark_prover_n20_d3_a1() {
        helper_benchmark_prover_algo(20, 3, AlgorithmType::Naive, "Algo1");
    }
    #[test]
    fn benchmark_prover_n22_d3_a1() {
        helper_benchmark_prover_algo(22, 3, AlgorithmType::Naive, "Algo1");
    }
    #[test]
    fn benchmark_prover_n24_d3_a1() {
        helper_benchmark_prover_algo(24, 3, AlgorithmType::Naive, "Algo1");
    }
    #[test]
    fn benchmark_prover_n26_d3_a1() {
        helper_benchmark_prover_algo(26, 3, AlgorithmType::Naive, "Algo1");
    }
    #[test]
    fn benchmark_prover_n28_d3_a1() {
        helper_benchmark_prover_algo(28, 3, AlgorithmType::Naive, "Algo1");
    }

    // Degree 3 tests, algo4
    #[test]
    fn benchmark_prover_n16_d3_a4() {
        helper_benchmark_prover_algo(16, 3, AlgorithmType::ToomCook, "Algo4");
    }
    #[test]
    fn benchmark_prover_n18_d3_a4() {
        helper_benchmark_prover_algo(18, 3, AlgorithmType::ToomCook, "Algo4");
    }
    #[test]
    fn benchmark_prover_n20_d3_a4() {
        helper_benchmark_prover_algo(20, 3, AlgorithmType::ToomCook, "Algo4");
    }
    #[test]
    fn benchmark_prover_n22_d3_a4() {
        helper_benchmark_prover_algo(22, 3, AlgorithmType::ToomCook, "Algo4");
    }
    #[test]
    fn benchmark_prover_n24_d3_a4() {
        helper_benchmark_prover_algo(24, 3, AlgorithmType::ToomCook, "Algo4");
    }
    #[test]
    fn benchmark_prover_n26_d3_a4() {
        helper_benchmark_prover_algo(26, 3, AlgorithmType::ToomCook, "Algo4");
    }
    #[test]
    fn benchmark_prover_n28_d3_a4() {
        helper_benchmark_prover_algo(28, 3, AlgorithmType::ToomCook, "Algo4");
    }

    // Degree 3 tests, algo1 with eq
    #[test]
    fn benchmark_prover_n16_d3_a1_eq() {
        helper_benchmark_prover_algo(16, 3, AlgorithmType::NaiveWithEq, "Algo1Eq");
    }
    #[test]
    fn benchmark_prover_n18_d3_a1_eq() {
        helper_benchmark_prover_algo(18, 3, AlgorithmType::NaiveWithEq, "Algo1Eq");
    }
    #[test]
    fn benchmark_prover_n20_d3_a1_eq() {
        helper_benchmark_prover_algo(20, 3, AlgorithmType::NaiveWithEq, "Algo1Eq");
    }
    #[test]
    fn benchmark_prover_n22_d3_a1_eq() {
        helper_benchmark_prover_algo(22, 3, AlgorithmType::NaiveWithEq, "Algo1Eq");
    }
    #[test]
    fn benchmark_prover_n24_d3_a1_eq() {
        helper_benchmark_prover_algo(24, 3, AlgorithmType::NaiveWithEq, "Algo1Eq");
    }
    #[test]
    fn benchmark_prover_n26_d3_a1_eq() {
        helper_benchmark_prover_algo(26, 3, AlgorithmType::NaiveWithEq, "Algo1Eq");
    }
    #[test]
    fn benchmark_prover_n28_d3_a1_eq() {
        helper_benchmark_prover_algo(28, 3, AlgorithmType::NaiveWithEq, "Algo1Eq");
    }

    // Degree 3 tests, algo4 with eq
    #[test]
    fn benchmark_prover_n16_d3_a4_eq() {
        helper_benchmark_prover_algo(16, 3, AlgorithmType::ToomCookWithEq, "Algo4Eq");
    }
    #[test]
    fn benchmark_prover_n18_d3_a4_eq() {
        helper_benchmark_prover_algo(18, 3, AlgorithmType::ToomCookWithEq, "Algo4Eq");
    }
    #[test]
    fn benchmark_prover_n20_d3_a4_eq() {
        helper_benchmark_prover_algo(20, 3, AlgorithmType::ToomCookWithEq, "Algo4Eq");
    }
    #[test]
    fn benchmark_prover_n22_d3_a4_eq() {
        helper_benchmark_prover_algo(22, 3, AlgorithmType::ToomCookWithEq, "Algo4Eq");
    }
    #[test]
    fn benchmark_prover_n24_d3_a4_eq() {
        helper_benchmark_prover_algo(24, 3, AlgorithmType::ToomCookWithEq, "Algo4Eq");
    }
    #[test]
    fn benchmark_prover_n26_d3_a4_eq() {
        helper_benchmark_prover_algo(26, 3, AlgorithmType::ToomCookWithEq, "Algo4Eq");
    }
    #[test]
    fn benchmark_prover_n28_d3_a4_eq() {
        helper_benchmark_prover_algo(28, 3, AlgorithmType::ToomCookWithEq, "Algo4Eq");
    }

    fn helper_benchmark_optimal_round_t(nv: usize, degree: usize) {
        let thresholds = vec![1, 2, 3, 4, 5];
        let algorithms = vec![
            AlgorithmType::Naive,          // algo1
            AlgorithmType::ToomCook,       // algo4
            AlgorithmType::NaiveWithEq,    // algo1eq
            AlgorithmType::ToomCookWithEq, // algo4eq
        ];

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
                let (_, result, time_s, _) =
                    sumcheck_test_helper(nv, degree, t, algorithm.clone(), 1);

                // Verify the result is correct
                assert_eq!(
                    result.unwrap(),
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

    #[test]
    fn benchmark_optimal_round_t_n16_d2() {
        helper_benchmark_optimal_round_t(16, 2);
    }
    #[test]
    fn benchmark_optimal_round_t_n18_d2() {
        helper_benchmark_optimal_round_t(18, 2);
    }
    #[test]
    fn benchmark_optimal_round_t_n20_d2() {
        helper_benchmark_optimal_round_t(20, 2);
    }
    #[test]
    fn benchmark_optimal_round_t_n22_d2() {
        helper_benchmark_optimal_round_t(22, 2);
    }

    #[test]
    fn benchmark_optimal_round_t_n16_d3() {
        helper_benchmark_optimal_round_t(16, 3);
    }
    #[test]
    fn benchmark_optimal_round_t_n18_d3() {
        helper_benchmark_optimal_round_t(18, 3);
    }
    #[test]
    fn benchmark_optimal_round_t_n20_d3() {
        helper_benchmark_optimal_round_t(20, 3);
    }
    #[test]
    fn benchmark_optimal_round_t_n22_d3() {
        helper_benchmark_optimal_round_t(22, 3);
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
        let (proof_1, result_1, _, _) =
            sumcheck_test_helper(nv, degree, round_t, AlgorithmType::Naive, 1);
        let (proof_2, result_2, _, _) = sumcheck_test_helper(
            nv,
            degree,
            round_t,
            AlgorithmType::WitnessChallengeSeparation,
            1,
        );
        let (proof_3, result_3, _, _) =
            sumcheck_test_helper(nv, degree, round_t, AlgorithmType::Precomputation, 1);
        let (proof_4, result_4, _, _) =
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
