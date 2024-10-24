#[cfg(test)]
mod simple_extension_tests {
    use crate::data_structures::LinearLagrangeList;
    use crate::prover::AlgorithmType;
    use crate::prover::ProverState;
    use crate::prover::SumcheckProof;
    use crate::tests::test_helpers::generate_binomial_interpolation_mult_matrix_transpose;
    use crate::tests::test_helpers::get_maps_from_matrix;
    use crate::tower_fields::binius::BiniusTowerField;
    use crate::tower_fields::TowerField;
    use crate::IPForMLSumcheck;
    use ark_std::vec::Vec;
    use merlin::Transcript;
    use num::Zero;

    type BF = BiniusTowerField;
    type EF = BiniusTowerField;

    #[test]
    fn test_sumcheck() {
        // Convert a base field element to an extension field element
        fn to_ef(base_field_element: &BF) -> EF {
            EF::new(base_field_element.get_val(), None)
        }

        // Define the combine function
        fn combine_fn_bf(data: &Vec<BF>) -> EF {
            assert!(data.len() > 0);
            to_ef(&data[0])
        }

        fn combine_fn_ef(data: &Vec<EF>) -> EF {
            assert!(data.len() > 0);
            data[0]
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(base_field_element: &BF, extension_field_element: &EF) -> EF {
            extension_field_element * base_field_element
        }

        // Adds two extension field elements
        fn add_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 + ee_element2
        }

        // Multiplies an extension field element to an extension field element
        fn mult_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 * ee_element2
        }

        // Multiplies a base field element to a base field element
        fn mult_bb(bb_element1: &BF, bb_element2: &BF) -> BF {
            bb_element1 * bb_element2
        }

        // Take a simple polynomial
        let num_variables = 3;
        let num_evaluations = (1 as u32) << num_variables;
        let evaluations: Vec<BF> = (0..num_evaluations).map(|i| BF::from(2 * i)).collect();
        let claimed_sum = evaluations.iter().fold(BF::zero(), |acc, e| acc + *e);

        let polynomials: Vec<LinearLagrangeList<BF>> =
            vec![LinearLagrangeList::<BF>::from_vector(&evaluations)];
        let mut prover_state: ProverState<EF, BF> =
            IPForMLSumcheck::prover_init(&polynomials, 1, AlgorithmType::Naive);

        // create a proof
        let mut prover_transcript = Transcript::new(b"test_sumcheck");
        let proof: SumcheckProof<EF> = IPForMLSumcheck::<EF, BF>::prove::<_, _, _, _, _, _, _>(
            &mut prover_state,
            &combine_fn_ef,
            &combine_fn_bf,
            &mut prover_transcript,
            &to_ef,
            &mult_be,
            &add_ee,
            &mult_ee,
            &mult_bb,
            None,
            None,
            None,
            None,
            None,
        );

        let mut verifier_transcript = Transcript::new(b"test_sumcheck");
        let result = IPForMLSumcheck::<EF, BF>::verify(
            to_ef(&claimed_sum),
            &proof,
            &mut verifier_transcript,
            AlgorithmType::Naive,
            None,
            None,
        );
        assert_eq!(result.unwrap(), true);
    }

    #[test]
    fn test_product_sumcheck_with_algorithm_1() {
        // Define the combine function
        fn combine_fn_bf(data: &Vec<BF>) -> EF {
            assert!(data.len() == 2);
            to_ef(&(data[0] * data[1]))
        }

        fn combine_fn_ef(data: &Vec<EF>) -> EF {
            assert!(data.len() == 2);
            data[0] * data[1]
        }

        // Convert a base field element to an extension field element
        fn to_ef(base_field_element: &BF) -> EF {
            EF::new(base_field_element.get_val(), None)
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(base_field_element: &BF, extension_field_element: &EF) -> EF {
            extension_field_element * base_field_element
        }

        // Adds two extension field elements
        fn add_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 + ee_element2
        }

        // Multiplies an extension field element to an extension field element
        fn mult_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 * ee_element2
        }

        // Multiplies a base field element to a base field element
        fn mult_bb(bb_element1: &BF, bb_element2: &BF) -> BF {
            bb_element1 * bb_element2
        }

        // Take two simple polynomial
        let num_variables = 2;
        let num_evaluations = (1 as u32) << num_variables;
        let evaluations_a: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::new((2 * i) as u128, Some(1)))
            .collect();
        let evaluations_b: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::new((i + 1) as u128, Some(1)))
            .collect();
        let claimed_sum = evaluations_a
            .iter()
            .zip(evaluations_b.iter())
            .fold(BF::zero(), |acc, (a, b)| acc + a * b);

        let polynomials: Vec<LinearLagrangeList<BF>> = vec![
            LinearLagrangeList::<BF>::from_vector(&evaluations_a),
            LinearLagrangeList::<BF>::from_vector(&evaluations_b),
        ];

        let mut prover_state: ProverState<EF, BF> =
            IPForMLSumcheck::prover_init(&polynomials, 2, AlgorithmType::Naive);
        let mut prover_transcript = Transcript::new(b"test_product_sumcheck");
        let proof: SumcheckProof<EF> = IPForMLSumcheck::<EF, BF>::prove::<_, _, _, _, _, _, _>(
            &mut prover_state,
            &combine_fn_ef,
            &combine_fn_bf,
            &mut prover_transcript,
            &to_ef,
            &mult_be,
            &add_ee,
            &mult_ee,
            &mult_bb,
            None,
            None,
            None,
            None,
            None,
        );

        let mut verifier_transcript = Transcript::new(b"test_product_sumcheck");
        let result = IPForMLSumcheck::<EF, BF>::verify(
            to_ef(&claimed_sum),
            &proof,
            &mut verifier_transcript,
            AlgorithmType::WitnessChallengeSeparation,
            None,
            None,
        );
        assert_eq!(result.unwrap(), true);
    }

    #[test]
    fn test_product_sumcheck_with_algorithm_2() {
        // Define the combine function
        fn combine_fn_bf(data: &Vec<BF>) -> EF {
            assert!(data.len() == 2);
            to_ef(&(data[0] * data[1]))
        }

        fn combine_fn_ef(data: &Vec<EF>) -> EF {
            assert!(data.len() == 2);
            data[0] * data[1]
        }

        // Convert a base field element to an extension field element
        fn to_ef(base_field_element: &BF) -> EF {
            EF::new(base_field_element.get_val(), None)
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(base_field_element: &BF, extension_field_element: &EF) -> EF {
            extension_field_element * base_field_element
        }

        // Adds two extension field elements
        fn add_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 + ee_element2
        }

        // Multiplies an extension field element to an extension field element
        fn mult_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 * ee_element2
        }

        // Multiplies a base field element to a base field element
        fn mult_bb(bb_element1: &BF, bb_element2: &BF) -> BF {
            bb_element1 * bb_element2
        }

        // Take two simple polynomial
        let num_variables = 2;
        let num_evaluations = (1 as u32) << num_variables;
        let evaluations_a: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::new((2 * i) as u128, Some(1)))
            .collect();
        let evaluations_b: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::new((i + 1) as u128, Some(1)))
            .collect();
        let claimed_sum = evaluations_a
            .iter()
            .zip(evaluations_b.iter())
            .fold(BF::zero(), |acc, (a, b)| acc + a * b);

        let polynomials: Vec<LinearLagrangeList<BF>> = vec![
            LinearLagrangeList::<BF>::from_vector(&evaluations_a),
            LinearLagrangeList::<BF>::from_vector(&evaluations_b),
        ];

        let mut prover_state: ProverState<EF, BF> = IPForMLSumcheck::prover_init(
            &polynomials,
            2,
            AlgorithmType::WitnessChallengeSeparation,
        );
        let mut prover_transcript = Transcript::new(b"test_product_sumcheck");
        let proof: SumcheckProof<EF> = IPForMLSumcheck::<EF, BF>::prove::<_, _, _, _, _, _, _>(
            &mut prover_state,
            &combine_fn_ef,
            &combine_fn_bf,
            &mut prover_transcript,
            &to_ef,
            &mult_be,
            &add_ee,
            &mult_ee,
            &mult_bb,
            None,
            None,
            None,
            None,
            None,
        );

        let mut verifier_transcript = Transcript::new(b"test_product_sumcheck");
        let result = IPForMLSumcheck::<EF, BF>::verify(
            to_ef(&claimed_sum),
            &proof,
            &mut verifier_transcript,
            AlgorithmType::WitnessChallengeSeparation,
            None,
            None,
        );
        assert_eq!(result.unwrap(), true);
    }

    #[test]
    fn test_product_sumcheck_with_algorithm_3() {
        // Define the combine function
        fn combine_fn_bf(data: &Vec<BF>) -> EF {
            assert!(data.len() == 3);
            to_ef(&(data[0] * data[1] * data[2]))
        }

        fn combine_fn_ef(data: &Vec<EF>) -> EF {
            assert!(data.len() == 3);
            data[0] * data[1] * data[2]
        }

        // Convert a base field element to an extension field element
        fn to_ef(base_field_element: &BF) -> EF {
            EF::new(base_field_element.get_val(), None)
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(base_field_element: &BF, extension_field_element: &EF) -> EF {
            extension_field_element * base_field_element
        }

        // Adds two extension field elements
        fn add_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 + ee_element2
        }

        // Multiplies an extension field element to an extension field element
        fn mult_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 * ee_element2
        }

        // Multiplies a base field element to a base field element
        fn mult_bb(bb_element1: &BF, bb_element2: &BF) -> BF {
            bb_element1 * bb_element2
        }

        // Take two simple polynomial
        let num_variables = 3;
        let num_evaluations = (1 as u32) << num_variables;
        let evaluations_a: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::from((2 * i) % 7))
            .collect();
        let evaluations_b: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::from((i + 1) % 7))
            .collect();
        let evaluations_c: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::from((i + 2) % 7))
            .collect();
        let claimed_sum = (0..num_evaluations)
            .map(|i| BF::from((2 * i) % 7) * BF::from((i + 1) % 7) * BF::from((i + 2) % 7))
            .fold(BF::zero(), |acc, val| acc + val);

        let polynomials: Vec<LinearLagrangeList<BF>> = vec![
            LinearLagrangeList::<BF>::from_vector(&evaluations_a),
            LinearLagrangeList::<BF>::from_vector(&evaluations_b),
            LinearLagrangeList::<BF>::from_vector(&evaluations_c),
        ];
        let mut prover_state: ProverState<EF, BF> =
            IPForMLSumcheck::prover_init(&polynomials, 3, AlgorithmType::Precomputation);
        let mut prover_transcript = Transcript::new(b"test_product_sumcheck");
        let proof: SumcheckProof<EF> = IPForMLSumcheck::<EF, BF>::prove::<_, _, _, _, _, _, _>(
            &mut prover_state,
            &combine_fn_ef,
            &combine_fn_bf,
            &mut prover_transcript,
            &to_ef,
            &mult_be,
            &add_ee,
            &mult_ee,
            &mult_bb,
            None,
            None,
            None,
            None,
            None,
        );

        let mut prover_state_dup: ProverState<EF, BF> =
            IPForMLSumcheck::prover_init(&polynomials, 3, AlgorithmType::Naive);
        let mut prover_transcript_dup = Transcript::new(b"test_product_sumcheck");
        let proof_dup: SumcheckProof<EF> = IPForMLSumcheck::<EF, BF>::prove::<_, _, _, _, _, _, _>(
            &mut prover_state_dup,
            &combine_fn_ef,
            &combine_fn_bf,
            &mut prover_transcript_dup,
            &to_ef,
            &mult_be,
            &add_ee,
            &mult_ee,
            &mult_bb,
            None,
            None,
            None,
            None,
            None,
        );

        let mut verifier_transcript = Transcript::new(b"test_product_sumcheck");
        let result = IPForMLSumcheck::<EF, BF>::verify(
            to_ef(&claimed_sum),
            &proof,
            &mut verifier_transcript,
            AlgorithmType::Precomputation,
            None,
            None,
        );
        assert_eq!(result.unwrap(), true);

        let mut verifier_transcript_dup = Transcript::new(b"test_product_sumcheck");
        let result_dup = IPForMLSumcheck::<EF, BF>::verify(
            to_ef(&claimed_sum),
            &proof_dup,
            &mut verifier_transcript_dup,
            AlgorithmType::Naive,
            None,
            None,
        );
        assert_eq!(result_dup.unwrap(), true);
    }

    #[test]
    fn test_product_sumcheck_with_algorithm_4_degree_3() {
        // Define the combine function
        fn combine_fn_bf(data: &Vec<BF>) -> EF {
            assert!(data.len() == 3);
            to_ef(&(data[0] * data[1] * data[2]))
        }

        fn combine_fn_ef(data: &Vec<EF>) -> EF {
            assert!(data.len() == 3);
            data[0] * data[1] * data[2]
        }

        // Convert a base field element to an extension field element
        fn to_ef(base_field_element: &BF) -> EF {
            EF::new(base_field_element.get_val(), None)
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(base_field_element: &BF, extension_field_element: &EF) -> EF {
            extension_field_element * base_field_element
        }

        // Adds two extension field elements
        fn add_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 + ee_element2
        }

        // Multiplies an extension field element to an extension field element
        fn mult_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 * ee_element2
        }

        // Multiplies a base field element to a base field element
        fn mult_bb(bb_element1: &BF, bb_element2: &BF) -> BF {
            bb_element1 * bb_element2
        }

        // Take three simple polynomial
        let num_variables = 3;
        let num_evaluations = (1 as u32) << num_variables;
        let evaluations_a: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::from((2 * i) % 7))
            .collect();
        let evaluations_b: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::from((i + 1) % 7))
            .collect();
        let evaluations_c: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::from((i + 2) % 7))
            .collect();
        let claimed_sum = (0..num_evaluations)
            .map(|i| BF::from((2 * i) % 7) * BF::from((i + 1) % 7) * BF::from((i + 2) % 7))
            .fold(BF::zero(), |acc, val| acc + val);

        let polynomials: Vec<LinearLagrangeList<BF>> = vec![
            LinearLagrangeList::<BF>::from_vector(&evaluations_a),
            LinearLagrangeList::<BF>::from_vector(&evaluations_b),
            LinearLagrangeList::<BF>::from_vector(&evaluations_c),
        ];

        // Define mappings: p(Z) = y.Z + x
        let map1 = Box::new(|x: &BF, _y: &BF| -> BF { *x });
        let map2 = Box::new(|x: &BF, y: &BF| -> BF { *x + *y });
        let map3 = Box::new(|x: &BF, y: &BF| -> BF { *x + (*y * BF::new(2u128, None)) });
        let map4 = Box::new(|_x: &BF, y: &BF| -> BF { *y });
        let maps: Vec<Box<dyn Fn(&BF, &BF) -> BF + Send + Sync>> = vec![map1, map2, map3, map4];
        let projective_map_indices = vec![0 as usize, 3 as usize];

        // Define interpolation matrix related maps.
        /// We have B as the binary expansion matrix.
        ///     ┌         ┐
        ///     │ 1 0 0 0 │
        /// B = │ 1 1 0 0 │
        ///     │ 1 0 1 0 │
        ///     │ 1 1 1 1 │
        ///     └         ┘
        /// We have P as the interpolation matrix
        ///     ┌         ┐
        ///     │ 1 0 0 0 │
        /// P = │ 2 3 1 2 │
        ///     │ 3 2 1 3 │
        ///     │ 0 0 0 1 │
        ///     └         ┘
        /// The mapping is computed as: M = (B * P)ᵀ
        ///     ┌         ┐ᵀ  ┌         ┐
        ///     │ 1 0 0 0 │   │ 1 3 2 0 │
        ///     │ 3 3 1 2 │   │ 0 3 2 1 │
        /// M = │ 2 2 1 3 │ = │ 0 1 1 0 │
        ///     │ 0 1 0 0 │   │ 0 2 3 0 │
        ///     └         ┘   └         ┘
        ///
        fn get_interpolation_maps<FF: TowerField>() -> Vec<Box<dyn Fn(&Vec<FF>) -> FF>> {
            // Define interpolation matrix related maps
            let imap_1 = Box::new(|v: &Vec<FF>| -> FF {
                v[0] + FF::new(3u128, None) * v[1] + FF::new(2u128, None) * v[2]
            });
            let imap_2 = Box::new(|v: &Vec<FF>| -> FF {
                FF::new(3u128, None) * v[1] + FF::new(2u128, None) * v[2] + v[3]
            });
            let imap_3 = Box::new(|v: &Vec<FF>| -> FF { v[1] + v[2] });
            let imap_4 = Box::new(|v: &Vec<FF>| -> FF {
                FF::new(2u128, None) * v[1] + FF::new(3u128, None) * v[2]
            });
            let interpolation_maps: Vec<Box<dyn Fn(&Vec<FF>) -> FF>> =
                vec![imap_1, imap_2, imap_3, imap_4];
            interpolation_maps
        }

        let imaps_base = get_interpolation_maps::<BF>();
        let imaps_ext = get_interpolation_maps::<EF>();

        let mut prover_state: ProverState<EF, BF> =
            IPForMLSumcheck::prover_init(&polynomials, 3, AlgorithmType::ToomCook);
        let mut prover_transcript = Transcript::new(b"test_product_sumcheck");
        let proof: SumcheckProof<EF> = IPForMLSumcheck::<EF, BF>::prove::<_, _, _, _, _, _, _>(
            &mut prover_state,
            &combine_fn_ef,
            &combine_fn_bf,
            &mut prover_transcript,
            &to_ef,
            &mult_be,
            &add_ee,
            &mult_ee,
            &mult_bb,
            None,
            Some(&maps),
            Some(&projective_map_indices),
            Some(&imaps_base),
            Some(&imaps_ext),
        );

        let mut prover_state_dup: ProverState<EF, BF> =
            IPForMLSumcheck::prover_init(&polynomials, 3, AlgorithmType::Naive);
        let mut prover_transcript_dup = Transcript::new(b"test_product_sumcheck");
        let proof_dup: SumcheckProof<EF> = IPForMLSumcheck::<EF, BF>::prove::<_, _, _, _, _, _, _>(
            &mut prover_state_dup,
            &combine_fn_ef,
            &combine_fn_bf,
            &mut prover_transcript_dup,
            &to_ef,
            &mult_be,
            &add_ee,
            &mult_ee,
            &mult_bb,
            None,
            None,
            None,
            None,
            None,
        );

        // The proofs generated with the naive and the toom-cook methods must exactly match.
        // assert_eq!(proof.round_polynomials, proof_dup.round_polynomials);

        let mut verifier_transcript = Transcript::new(b"test_product_sumcheck");
        let result = IPForMLSumcheck::<EF, BF>::verify(
            to_ef(&claimed_sum),
            &proof,
            &mut verifier_transcript,
            AlgorithmType::ToomCook,
            None,
            None,
        );
        assert_eq!(result.unwrap(), true);

        let mut verifier_transcript_dup = Transcript::new(b"test_product_sumcheck");
        let result_dup = IPForMLSumcheck::<EF, BF>::verify(
            to_ef(&claimed_sum),
            &proof_dup,
            &mut verifier_transcript_dup,
            AlgorithmType::Naive,
            None,
            None,
        );
        assert_eq!(result_dup.unwrap(), true);
    }

    #[test]
    fn test_product_sumcheck_with_algorithm_4_degree_4() {
        // Define the combine function
        fn combine_fn_bf(data: &Vec<BF>) -> EF {
            assert!(data.len() == 4);
            to_ef(&(data[0] * data[1] * data[2] * data[3]))
        }

        fn combine_fn_ef(data: &Vec<EF>) -> EF {
            assert!(data.len() == 4);
            data[0] * data[1] * data[2] * data[3]
        }

        // Convert a base field element to an extension field element
        fn to_ef(base_field_element: &BF) -> EF {
            EF::new(base_field_element.get_val(), None)
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(base_field_element: &BF, extension_field_element: &EF) -> EF {
            extension_field_element * base_field_element
        }

        // Adds two extension field elements
        fn add_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 + ee_element2
        }

        // Multiplies an extension field element to an extension field element
        fn mult_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 * ee_element2
        }

        // Multiplies a base field element to a base field element
        fn mult_bb(bb_element1: &BF, bb_element2: &BF) -> BF {
            bb_element1 * bb_element2
        }

        // Take four simple polynomial
        let num_variables = 4;
        let num_evaluations = (1 as u32) << num_variables;
        let evaluations_a: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::from((2 * i) % 7))
            .collect();
        let evaluations_b: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::from((i + 1) % 7))
            .collect();
        let evaluations_c: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::from((i + 2) % 7))
            .collect();
        let evaluations_d: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::from((i + 5) % 7))
            .collect();
        let claimed_sum = (0..num_evaluations)
            .map(|i| {
                BF::from((2 * i) % 7)
                    * BF::from((i + 1) % 7)
                    * BF::from((i + 2) % 7)
                    * BF::from((i + 5) % 7)
            })
            .fold(BF::zero(), |acc, val| acc + val);

        let polynomials: Vec<LinearLagrangeList<BF>> = vec![
            LinearLagrangeList::<BF>::from_vector(&evaluations_a),
            LinearLagrangeList::<BF>::from_vector(&evaluations_b),
            LinearLagrangeList::<BF>::from_vector(&evaluations_c),
            LinearLagrangeList::<BF>::from_vector(&evaluations_d),
        ];

        // Define mappings
        let map1 = Box::new(|x: &BF, _y: &BF| -> BF { *x });
        let map2 = Box::new(|x: &BF, y: &BF| -> BF { *x + *y });
        let map3 = Box::new(|x: &BF, y: &BF| -> BF { *x + (*y * BF::new(2u128, None)) });
        let map4 = Box::new(|x: &BF, y: &BF| -> BF { *x + (*y * BF::new(3u128, None)) });
        let map5 = Box::new(|_x: &BF, y: &BF| -> BF { *y });
        let maps: Vec<Box<dyn Fn(&BF, &BF) -> BF + Send + Sync>> =
            vec![map1, map2, map3, map4, map5];
        let projective_map_indices = vec![0 as usize, 4 as usize];

        /// Define interpolation matrix related maps.
        /// Let B be the binary expansion matrix. For binary tower fields,
        /// we need to compute B mod 2 as the binomial coefficients must be binary.
        /// Thus, we compute B' from B. (See tests/mod.rs for an explanation of this.)
        ///      ┌           ┐
        ///      │ 1 0 0 0 0 │
        ///      │ 0 1 0 0 0 │
        /// B' = │ 0 1 1 0 0 │
        ///      │ 0 1 0 1 0 │
        ///      │ 1 1 1 1 1 │
        ///      └           ┘
        /// We have P as the interpolation matrix
        ///           ┌           ┐
        ///           │ 1 0 0 0 0 │
        ///           │ 0 1 3 2 1 │
        /// P = 1/1 * │ 0 1 2 3 0 │
        ///           │ 1 1 1 1 0 │
        ///           │ 0 0 0 0 1 │
        ///           └           ┘
        /// The mapping is computed as: M = (B' * P)ᵀ
        ///     ┌           ┐ᵀ  ┌             ┐
        ///     │ 1 0 0 0 0 │   │  1 0 0 1 0  │
        ///     │ 0 1 3 2 1 │   │  0 1 0 0 1  │
        /// M = │ 0 0 1 1 1 │ = │  0 3 1 2 0  │
        ///     │ 1 0 2 3 1 │   │  0 2 1 3 0  │
        ///     │ 0 1 0 0 0 │   │  0 1 1 1 0  │
        ///     └           ┘   └             ┘
        ///
        fn get_interpolation_maps<FF: TowerField>() -> Vec<Box<dyn Fn(&Vec<FF>) -> FF>> {
            // Define interpolation matrix related maps
            let imap_1 = Box::new(|v: &Vec<FF>| -> FF { v[0] + v[3] });
            let imap_2 = Box::new(|v: &Vec<FF>| -> FF { v[1] + v[4] });
            let imap_3 = Box::new(|v: &Vec<FF>| -> FF {
                v[1] * FF::new(3u128, None) + v[2] + v[3] * FF::new(2u128, None)
            });
            let imap_4 = Box::new(|v: &Vec<FF>| -> FF {
                v[1] * FF::new(2u128, None) + v[2] + v[3] * FF::new(3u128, None)
            });
            let imap_5 = Box::new(|v: &Vec<FF>| -> FF { v[1] + v[2] + v[3] });
            let interpolation_maps: Vec<Box<dyn Fn(&Vec<FF>) -> FF>> =
                vec![imap_1, imap_2, imap_3, imap_4, imap_5];
            interpolation_maps
        }

        let imaps_base = get_interpolation_maps::<BF>();
        let imaps_ext = get_interpolation_maps::<EF>();

        let mut prover_state: ProverState<EF, BF> =
            IPForMLSumcheck::prover_init(&polynomials, 4, AlgorithmType::ToomCook);
        let mut prover_transcript = Transcript::new(b"test_product_sumcheck");
        let proof: SumcheckProof<EF> = IPForMLSumcheck::<EF, BF>::prove::<_, _, _, _, _, _, _>(
            &mut prover_state,
            &combine_fn_ef,
            &combine_fn_bf,
            &mut prover_transcript,
            &to_ef,
            &mult_be,
            &add_ee,
            &mult_ee,
            &mult_bb,
            None,
            Some(&maps),
            Some(&projective_map_indices),
            Some(&imaps_base),
            Some(&imaps_ext),
        );

        let mut prover_state_dup: ProverState<EF, BF> =
            IPForMLSumcheck::prover_init(&polynomials, 4, AlgorithmType::Naive);
        let mut prover_transcript_dup = Transcript::new(b"test_product_sumcheck");
        let proof_dup: SumcheckProof<EF> = IPForMLSumcheck::<EF, BF>::prove::<_, _, _, _, _, _, _>(
            &mut prover_state_dup,
            &combine_fn_ef,
            &combine_fn_bf,
            &mut prover_transcript_dup,
            &to_ef,
            &mult_be,
            &add_ee,
            &mult_ee,
            &mult_bb,
            None,
            None,
            None,
            None,
            None,
        );

        // The proofs generated with the naive and the toom-cook methods must exactly match.
        // TODO: investigate why the proofs from different algos don't match.
        // assert_eq!(proof.round_polynomials, proof_dup.round_polynomials);

        let mut verifier_transcript = Transcript::new(b"test_product_sumcheck");
        let result = IPForMLSumcheck::<EF, BF>::verify(
            to_ef(&claimed_sum),
            &proof,
            &mut verifier_transcript,
            AlgorithmType::ToomCook,
            None,
            None,
        );
        assert_eq!(result.unwrap(), true);

        let mut verifier_transcript_dup = Transcript::new(b"test_product_sumcheck");
        let result_dup = IPForMLSumcheck::<EF, BF>::verify(
            to_ef(&claimed_sum),
            &proof_dup,
            &mut verifier_transcript_dup,
            AlgorithmType::Naive,
            None,
            None,
        );
        assert_eq!(result_dup.unwrap(), true);
    }

    #[test]
    fn test_product_sumcheck_with_algorithm_4_degree_5_without_inversions() {
        // Define the combine function
        fn combine_fn_bf(data: &Vec<BF>) -> EF {
            assert!(data.len() == 5);
            to_ef(&(data[0] * data[1] * data[2] * data[3] * data[4]))
        }

        fn combine_fn_ef(data: &Vec<EF>) -> EF {
            assert!(data.len() == 5);
            data[0] * data[1] * data[2] * data[3] * data[4]
        }

        // Convert a base field element to an extension field element
        fn to_ef(base_field_element: &BF) -> EF {
            EF::new(base_field_element.get_val(), None)
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(base_field_element: &BF, extension_field_element: &EF) -> EF {
            extension_field_element * base_field_element
        }

        // Adds two extension field elements
        fn add_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 + ee_element2
        }

        // Multiplies an extension field element to an extension field element
        fn mult_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 * ee_element2
        }

        // Multiplies a base field element to a base field element
        fn mult_bb(bb_element1: &BF, bb_element2: &BF) -> BF {
            bb_element1 * bb_element2
        }

        // Take five simple polynomial
        let num_variables = 3;
        let num_evaluations = (1 as u32) << num_variables;
        let evaluations_a: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::from((2 * i) % 7))
            .collect();
        let evaluations_b: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::from((i + 1) % 7))
            .collect();
        let evaluations_c: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::from((i + 2) % 7))
            .collect();
        let evaluations_d: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::from((3 * i + 2) % 7))
            .collect();
        let evaluations_e: Vec<BF> = (0..num_evaluations)
            .map(|i| BF::from((2 * i + 1) % 7))
            .collect();
        let claimed_sum = (0..num_evaluations)
            .map(|i| {
                BF::from((2 * i) % 7)
                    * BF::from((i + 1) % 7)
                    * BF::from((i + 2) % 7)
                    * BF::from((3 * i + 2) % 7)
                    * BF::from((2 * i + 1) % 7)
            })
            .fold(BF::zero(), |acc, val| acc + val);

        let polynomials: Vec<LinearLagrangeList<BF>> = vec![
            LinearLagrangeList::<BF>::from_vector(&evaluations_a),
            LinearLagrangeList::<BF>::from_vector(&evaluations_b),
            LinearLagrangeList::<BF>::from_vector(&evaluations_c),
            LinearLagrangeList::<BF>::from_vector(&evaluations_d),
            LinearLagrangeList::<BF>::from_vector(&evaluations_e),
        ];

        // Define mappings
        // x + y * W
        let map1 = Box::new(|x: &BF, _y: &BF| -> BF { *x });
        let map2 = Box::new(|x: &BF, y: &BF| -> BF { *x + *y });
        let map3 = Box::new(|x: &BF, y: &BF| -> BF { *x + (*y * BF::new(2u128, None)) });
        let map4 = Box::new(|x: &BF, y: &BF| -> BF { *x + (*y * BF::new(3u128, None)) });
        let map5 = Box::new(|x: &BF, y: &BF| -> BF { *x + (*y * BF::new(4u128, None)) });
        let map6 = Box::new(|_x: &BF, y: &BF| -> BF { *y });
        let maps: Vec<Box<dyn Fn(&BF, &BF) -> BF + Send + Sync>> =
            vec![map1, map2, map3, map4, map5, map6];
        let projective_map_indices = vec![0 as usize, 5 as usize];

        // Define interpolation matrix related maps.
        //
        // The actual interpolation matrix contains fractions (like 1/2, -1/2, etc).
        // To avoid fractions in the interpolation matrix, we multiply each term by the determinant
        // of the original function matrix. Let E be the original function matrix. In this case:
        //
        // E = [[1, 0, 0, 0],
        //      [1, 1, 1, 1],
        //      [1, -1, 1, -1],
        //      [0, 0, 0, 1]].
        // We have:
        // I = E⁻¹
        //   = △⁻¹ adj(E)
        // where △ = det(E) is the determinant (a scalar) and adj(E) denotes the adjugate of matrix E.
        // If all entries in E are integers, then all entries in adj(E) are also integers. We wish to
        // avoid any fractional term in the interpolation matrix "I" because in that case we would have
        // to deal with inverses of integers (large numbers in extension field, which also results in
        // more extension-field multiplications). Therefore, we can use adj(E) as the interpolation matrix
        // and adjust the △ term (multiplicand) in the verifier algorithm accordingly.
        //
        // A consequence of this is that the round polynomial would change slightly. If the round polynomial
        // (in round 0) from the naive method is rₙ(c) and the round polynomial from the toom-cook method is rₜ(c):
        //
        // rₜ(c) = △ * rₙ(c)
        //
        // Hence the challenges are now different, and hence the proof generated using naive and toom-cook methods
        // would be different. We can simply adjust the verifier algorithm to take into account the determinant △.
        //
        // △ * r_1(x)
        // △^2 * r_2(x)
        // ...
        //
        let (inter_matrix_bf, det_bf) =
            generate_binomial_interpolation_mult_matrix_transpose::<BF>(5);
        let (inter_matrix_ef, det_ef) =
            generate_binomial_interpolation_mult_matrix_transpose::<EF>(5);
        assert_eq!(det_bf, det_ef);

        let imaps_base = get_maps_from_matrix::<BF>(&inter_matrix_bf);
        let imaps_ext = get_maps_from_matrix::<EF>(&inter_matrix_ef);

        let mut prover_state: ProverState<EF, BF> =
            IPForMLSumcheck::prover_init(&polynomials, 5, AlgorithmType::ToomCook);
        let mut prover_transcript = Transcript::new(b"test_product_sumcheck");
        let proof: SumcheckProof<EF> = IPForMLSumcheck::<EF, BF>::prove::<_, _, _, _, _, _, _>(
            &mut prover_state,
            &combine_fn_ef,
            &combine_fn_bf,
            &mut prover_transcript,
            &to_ef,
            &mult_be,
            &add_ee,
            &mult_ee,
            &mult_bb,
            Some(3),
            Some(&maps),
            Some(&projective_map_indices),
            Some(&imaps_base),
            Some(&imaps_ext),
        );

        let mut prover_state_dup: ProverState<EF, BF> =
            IPForMLSumcheck::prover_init(&polynomials, 5, AlgorithmType::Naive);
        let mut prover_transcript_dup = Transcript::new(b"test_product_sumcheck");
        let proof_dup: SumcheckProof<EF> = IPForMLSumcheck::<EF, BF>::prove::<_, _, _, _, _, _, _>(
            &mut prover_state_dup,
            &combine_fn_ef,
            &combine_fn_bf,
            &mut prover_transcript_dup,
            &to_ef,
            &mult_be,
            &add_ee,
            &mult_ee,
            &mult_bb,
            None,
            None,
            None,
            None,
            None,
        );

        // Remember, we need to adjust for the △ term in the verifier. We only need to pass it as the
        // argument to the verifier. The verifier equation changes as:
        //
        // rᵢ₊₁(0) + rᵢ₊₁(1) == △ * rᵢ(αᵢ)
        //
        let mut verifier_transcript = Transcript::new(b"test_product_sumcheck");
        let result = IPForMLSumcheck::<EF, BF>::verify(
            to_ef(&claimed_sum),
            &proof,
            &mut verifier_transcript,
            AlgorithmType::ToomCook,
            Some(EF::new(2u128, None)),
            Some(3 as usize),
        );
        assert_eq!(result.unwrap(), true);

        let mut verifier_transcript_dup = Transcript::new(b"test_product_sumcheck");
        let result_dup = IPForMLSumcheck::<EF, BF>::verify(
            to_ef(&claimed_sum),
            &proof_dup,
            &mut verifier_transcript_dup,
            AlgorithmType::Naive,
            None,
            None,
        );
        assert_eq!(result_dup.unwrap(), true);
    }

    #[test]
    fn test_r1cs_sumcheck() {
        // Define the combine function for r1cs: (a * b * e) - (c * e) = 0
        fn combine_fn_bf(data: &Vec<BF>) -> EF {
            assert!(data.len() == 4);
            let result = data[0] * data[1] * data[3] - data[2] * data[3];
            to_ef(&result)
        }

        // Define the combine function for r1cs: (a * b * e) - (c * e) = 0
        fn combine_fn_ef(data: &Vec<EF>) -> EF {
            assert!(data.len() == 4);
            data[0] * data[1] * data[3] - data[2] * data[3]
        }

        // Convert a base field element to an extension field element
        fn to_ef(base_field_element: &BF) -> EF {
            EF::new(base_field_element.get_val(), None)
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(base_field_element: &BF, extension_field_element: &EF) -> EF {
            extension_field_element * base_field_element
        }

        // Adds two extension field elements
        fn add_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 + ee_element2
        }

        // Multiplies an extension field element to an extension field element
        fn mult_ee(ee_element1: &EF, ee_element2: &EF) -> EF {
            ee_element1 * ee_element2
        }

        // Multiplies a base field element to a base field element
        fn mult_bb(bb_element1: &BF, bb_element2: &BF) -> BF {
            bb_element1 * bb_element2
        }

        // Take four simple polynomial
        const NV: usize = 10;
        const NE: u32 = (1 as u32) << NV;
        let poly_a = BF::rand_vector(NE as usize, Some(3));
        let poly_b = BF::rand_vector(NE as usize, Some(3));
        let poly_c = poly_a
            .iter()
            .zip(poly_b.iter())
            .map(|(a, b)| a * b)
            .collect();
        let poly_e = BF::rand_vector(NE as usize, Some(3));
        let claimed_sum: BF = BF::zero();

        let polynomials: Vec<LinearLagrangeList<BF>> = vec![
            LinearLagrangeList::<BF>::from_vector(&poly_a),
            LinearLagrangeList::<BF>::from_vector(&poly_b),
            LinearLagrangeList::<BF>::from_vector(&poly_c),
            LinearLagrangeList::<BF>::from_vector(&poly_e),
        ];
        let mut prover_state: ProverState<EF, BF> =
            IPForMLSumcheck::<EF, BF>::prover_init(&polynomials, 3, AlgorithmType::Naive);
        let mut prover_transcript = Transcript::new(b"test_r1cs_sumcheck");
        let proof: SumcheckProof<EF> = IPForMLSumcheck::<EF, BF>::prove::<_, _, _, _, _, _, _>(
            &mut prover_state,
            &combine_fn_ef,
            &combine_fn_bf,
            &mut prover_transcript,
            &to_ef,
            &mult_be,
            &add_ee,
            &mult_ee,
            &mult_bb,
            None,
            None,
            None,
            None,
            None,
        );

        let mut verifier_transcript = Transcript::new(b"test_r1cs_sumcheck");
        let result = IPForMLSumcheck::<EF, BF>::verify(
            to_ef(&claimed_sum),
            &proof,
            &mut verifier_transcript,
            AlgorithmType::Naive,
            None,
            None,
        );
        assert_eq!(result.unwrap(), true);
    }
}
