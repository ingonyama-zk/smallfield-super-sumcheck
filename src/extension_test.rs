#[cfg(test)]
mod extension_tests {
    use crate::data_structures::LinearLagrangeList;
    use crate::prover::AlgorithmType;
    use crate::prover::ProverState;
    use crate::prover::SumcheckProof;
    use crate::IPForMLSumcheck;
    use ark_ff::Field;
    use ark_ff::Zero;
    use ark_poly::DenseMultilinearExtension;
    use ark_poly::MultilinearExtension;
    use ark_std::iterable::Iterable;
    use ark_std::test_rng;
    use ark_std::vec::Vec;
    use merlin::Transcript;

    type BF = ark_bls12_381::Fq;
    type EF = ark_bls12_381::Fq2;

    #[test]
    fn test_sumcheck() {
        // Convert a base field element to an extension field element
        fn to_ef(base_field_element: &BF) -> EF {
            EF::new(*base_field_element, BF::zero())
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
            let mut result: EF = EF::from(*extension_field_element);
            result.mul_assign_by_basefield(base_field_element);
            result
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
        let claimed_sum = evaluations.iter().fold(BF::zero(), |acc, e| acc + e);
        let poly =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations);

        let polynomials: Vec<LinearLagrangeList<BF>> = vec![LinearLagrangeList::<BF>::from(&poly)];
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
    fn test_product_sumcheck() {
        // Convert a base field element to an extension field element
        fn to_ef(base_field_element: &BF) -> EF {
            EF::new(*base_field_element, BF::zero())
        }

        // Define the combine function
        fn combine_fn_bf(data: &Vec<BF>) -> EF {
            assert!(data.len() == 2);
            to_ef(&(data[0] * data[1]))
        }

        fn combine_fn_ef(data: &Vec<EF>) -> EF {
            assert!(data.len() == 2);
            data[0] * data[1]
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(base_field_element: &BF, extension_field_element: &EF) -> EF {
            let mut result: EF = EF::from(*extension_field_element);
            result.mul_assign_by_basefield(base_field_element);
            result
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
        let evaluations_a: Vec<BF> = (0..num_evaluations).map(|i| BF::from(2 * i)).collect();
        let evaluations_b: Vec<BF> = (0..num_evaluations).map(|i| BF::from(i + 1)).collect();
        let claimed_sum = evaluations_a
            .iter()
            .zip(evaluations_b.iter())
            .fold(BF::zero(), |acc, (a, b)| acc + a * b);
        let poly_a =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_a);
        let poly_b =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_b);

        let polynomials: Vec<LinearLagrangeList<BF>> = vec![
            LinearLagrangeList::<BF>::from(&poly_a),
            LinearLagrangeList::<BF>::from(&poly_b),
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

        let mut prover_state_dup: ProverState<EF, BF> =
            IPForMLSumcheck::prover_init(&polynomials, 2, AlgorithmType::Naive);
        let mut prover_transcript_dup = Transcript::new(b"test_product_sumcheck_algo2");
        let proof_dup: SumcheckProof<EF> = IPForMLSumcheck::<EF, BF>::prove_product::<_, _, _>(
            &mut prover_state_dup,
            &mut prover_transcript_dup,
            &mult_be,
            &mult_ee,
            &mult_bb,
        );

        let mut verifier_transcript = Transcript::new(b"test_product_sumcheck");
        let result = IPForMLSumcheck::<EF, BF>::verify(
            to_ef(&claimed_sum),
            &proof,
            &mut verifier_transcript,
            AlgorithmType::Naive,
            None,
            None,
        );
        assert_eq!(result.unwrap(), true);

        let mut verifier_transcript_dup = Transcript::new(b"test_product_sumcheck_algo2");
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
            EF::new(*base_field_element, BF::zero())
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(base_field_element: &BF, extension_field_element: &EF) -> EF {
            let mut result: EF = EF::from(*extension_field_element);
            result.mul_assign_by_basefield(base_field_element);
            result
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
        let evaluations_a: Vec<BF> = (0..num_evaluations).map(|i| BF::from(2 * i)).collect();
        let evaluations_b: Vec<BF> = (0..num_evaluations).map(|i| BF::from(i + 1)).collect();
        let claimed_sum = evaluations_a
            .iter()
            .zip(evaluations_b.iter())
            .fold(BF::zero(), |acc, (a, b)| acc + a * b);
        let poly_a =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_a);
        let poly_b =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_b);

        let polynomials: Vec<LinearLagrangeList<BF>> = vec![
            LinearLagrangeList::<BF>::from(&poly_a),
            LinearLagrangeList::<BF>::from(&poly_b),
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

        let mut prover_state_dup: ProverState<EF, BF> =
            IPForMLSumcheck::prover_init(&polynomials, 2, AlgorithmType::Naive);
        let mut prover_transcript_dup = Transcript::new(b"test_product_sumcheck");
        let proof_dup: SumcheckProof<EF> = IPForMLSumcheck::<EF, BF>::prove_product::<_, _, _>(
            &mut prover_state_dup,
            &mut prover_transcript_dup,
            &mult_be,
            &mult_ee,
            &mult_bb,
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
            EF::new(*base_field_element, BF::zero())
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(base_field_element: &BF, extension_field_element: &EF) -> EF {
            let mut result: EF = EF::from(*extension_field_element);
            result.mul_assign_by_basefield(base_field_element);
            result
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

        let poly_a =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_a);
        let poly_b =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_b);
        let poly_c =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_c);

        let polynomials: Vec<LinearLagrangeList<BF>> = vec![
            LinearLagrangeList::<BF>::from(&poly_a),
            LinearLagrangeList::<BF>::from(&poly_b),
            LinearLagrangeList::<BF>::from(&poly_c),
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

    /// Converts an interpolation matrix into maps.
    fn get_imaps<FF: Field>(
        interpolation_matrix: &Vec<Vec<i32>>,
    ) -> Vec<Box<dyn Fn(&Vec<FF>) -> FF>> {
        // Ensure the interpolation matrix is a square matrix.
        let num_evals = interpolation_matrix.len();
        for i in 0..num_evals {
            assert_eq!(interpolation_matrix[i].len(), num_evals);
        }

        interpolation_matrix
            .iter()
            .map(|irow| {
                let irow_cloned = irow.clone();
                let imap: Box<dyn Fn(&Vec<FF>) -> FF> = Box::new(move |v: &Vec<FF>| -> FF {
                    v.iter()
                        .zip(irow_cloned.iter())
                        .fold(FF::zero(), |acc, (value, scalar)| {
                            if *scalar < 0 {
                                acc - FF::from((*scalar).abs() as u32) * value
                            } else {
                                acc + FF::from((*scalar).abs() as u32) * value
                            }
                        })
                });
                imap
            })
            .collect::<Vec<Box<dyn Fn(&Vec<FF>) -> FF>>>()
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
            EF::new(*base_field_element, BF::zero())
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(base_field_element: &BF, extension_field_element: &EF) -> EF {
            let mut result: EF = EF::from(*extension_field_element);
            result.mul_assign_by_basefield(base_field_element);
            result
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

        let poly_a =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_a);
        let poly_b =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_b);
        let poly_c =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_c);

        let polynomials: Vec<LinearLagrangeList<BF>> = vec![
            LinearLagrangeList::<BF>::from(&poly_a),
            LinearLagrangeList::<BF>::from(&poly_b),
            LinearLagrangeList::<BF>::from(&poly_c),
        ];

        // Define mappings
        let map1 = Box::new(|x: &BF, _y: &BF| -> BF { *x });
        let map2 = Box::new(|x: &BF, y: &BF| -> BF { *x + *y });
        let map3 = Box::new(|x: &BF, y: &BF| -> BF { *x - *y });
        let map4 = Box::new(|_x: &BF, y: &BF| -> BF { *y });
        let maps: Vec<Box<dyn Fn(&BF, &BF) -> BF>> = vec![map1, map2, map3, map4];
        let projective_map_indices = vec![0 as usize, 3 as usize];

        // Define interpolation matrix related maps.
        fn get_interpolation_maps<FF: Field>() -> Vec<Box<dyn Fn(&Vec<FF>) -> FF>> {
            // Define interpolation matrix related maps
            let imap_1 = Box::new(|v: &Vec<FF>| -> FF { v[0] - v[2] });
            let imap_2 = Box::new(|v: &Vec<FF>| -> FF {
                let two_inv = FF::from(2 as u32).inverse().unwrap();
                two_inv * (v[2] + v[1])
            });
            let imap_3 = Box::new(|v: &Vec<FF>| -> FF {
                let two_inv = FF::from(2 as u32).inverse().unwrap();
                two_inv * (v[2] - v[1])
            });
            let imap_4 = Box::new(|v: &Vec<FF>| -> FF { v[3] - v[1] });
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
        assert_eq!(proof.round_polynomials, proof_dup.round_polynomials);

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
            EF::new(*base_field_element, BF::zero())
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(base_field_element: &BF, extension_field_element: &EF) -> EF {
            let mut result: EF = EF::from(*extension_field_element);
            result.mul_assign_by_basefield(base_field_element);
            result
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

        let poly_a =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_a);
        let poly_b =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_b);
        let poly_c =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_c);
        let poly_d =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_d);

        let polynomials: Vec<LinearLagrangeList<BF>> = vec![
            LinearLagrangeList::<BF>::from(&poly_a),
            LinearLagrangeList::<BF>::from(&poly_b),
            LinearLagrangeList::<BF>::from(&poly_c),
            LinearLagrangeList::<BF>::from(&poly_d),
        ];

        // Define mappings
        let map1 = Box::new(|x: &BF, _y: &BF| -> BF { *x });
        let map2 = Box::new(|x: &BF, y: &BF| -> BF { *x + *y });
        let map3 = Box::new(|x: &BF, y: &BF| -> BF { *x - *y });
        let map4 = Box::new(|x: &BF, y: &BF| -> BF { *x + (*y * BF::from(2)) });
        let map5 = Box::new(|_x: &BF, y: &BF| -> BF { *y });
        let maps: Vec<Box<dyn Fn(&BF, &BF) -> BF>> = vec![map1, map2, map3, map4, map5];
        let projective_map_indices = vec![0 as usize, 4 as usize];

        // Define interpolation matrix related maps.
        fn get_interpolation_maps<FF: Field>() -> Vec<Box<dyn Fn(&Vec<FF>) -> FF>> {
            // Define interpolation matrix related maps
            let imap_1 = Box::new(|v: &Vec<FF>| -> FF {
                let two_inv = FF::from(2 as u32).inverse().unwrap();
                v[0] - v[2] + two_inv * (v[3] - v[1])
            });
            let imap_2 = Box::new(|v: &Vec<FF>| -> FF {
                let two_inv = FF::from(2 as u32).inverse().unwrap();
                v[1] + two_inv * (v[2] - v[3])
            });
            let imap_3 = Box::new(|v: &Vec<FF>| -> FF {
                let two_inv = FF::from(2 as u32).inverse().unwrap();
                let three_inv = FF::from(3 as u32).inverse().unwrap();
                two_inv * v[2] - three_inv * v[1] - (two_inv * three_inv) * v[3]
            });
            let imap_4 = Box::new(|v: &Vec<FF>| -> FF {
                let six_inv = FF::from(6 as u32).inverse().unwrap();
                six_inv * (v[3] - v[1])
            });
            let imap_5 =
                Box::new(|v: &Vec<FF>| -> FF { FF::from(2 as u32) * (v[1] - v[3]) + v[4] - v[2] });
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
        assert_eq!(proof.round_polynomials, proof_dup.round_polynomials);

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
    fn test_product_sumcheck_with_algorithm_4_degree_3_without_inversions() {
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
            EF::new(*base_field_element, BF::zero())
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(base_field_element: &BF, extension_field_element: &EF) -> EF {
            let mut result: EF = EF::from(*extension_field_element);
            result.mul_assign_by_basefield(base_field_element);
            result
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

        let poly_a =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_a);
        let poly_b =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_b);
        let poly_c =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_c);

        let polynomials: Vec<LinearLagrangeList<BF>> = vec![
            LinearLagrangeList::<BF>::from(&poly_a),
            LinearLagrangeList::<BF>::from(&poly_b),
            LinearLagrangeList::<BF>::from(&poly_c),
        ];

        // Define mappings
        // x + y * W
        let map1 = Box::new(|x: &BF, _y: &BF| -> BF { *x }); // 0
        let map2 = Box::new(|x: &BF, y: &BF| -> BF { *x + *y }); // 1
        let map3 = Box::new(|x: &BF, y: &BF| -> BF { *x - *y }); // -1
        let map4 = Box::new(|_x: &BF, y: &BF| -> BF { *y }); // infty
        let maps: Vec<Box<dyn Fn(&BF, &BF) -> BF>> = vec![map1, map2, map3, map4];
        let projective_map_indices = vec![0 as usize, 3 as usize];

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
        let interpolation_matrix = vec![
            vec![2, 0, -2, 0],
            vec![0, 1, 1, 0],
            vec![0, -1, 1, 0],
            vec![0, -2, 0, 2],
        ];
        let imaps_base = get_imaps::<BF>(&interpolation_matrix);
        let imaps_ext = get_imaps::<EF>(&interpolation_matrix);

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
            Some(3),
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
            Some(EF::from(2 as u32)),
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
    fn test_product_sumcheck_with_algorithm_4_degree_4_without_inversions() {
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
            EF::new(*base_field_element, BF::zero())
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(base_field_element: &BF, extension_field_element: &EF) -> EF {
            let mut result: EF = EF::from(*extension_field_element);
            result.mul_assign_by_basefield(base_field_element);
            result
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

        let poly_a =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_a);
        let poly_b =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_b);
        let poly_c =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_c);
        let poly_d =
            DenseMultilinearExtension::<BF>::from_evaluations_vec(num_variables, evaluations_d);

        let polynomials: Vec<LinearLagrangeList<BF>> = vec![
            LinearLagrangeList::<BF>::from(&poly_a),
            LinearLagrangeList::<BF>::from(&poly_b),
            LinearLagrangeList::<BF>::from(&poly_c),
            LinearLagrangeList::<BF>::from(&poly_d),
        ];

        // Define mappings
        // p(x) = p0 + p1.x
        let map1 = Box::new(|x: &BF, _y: &BF| -> BF { *x }); // 0
        let map2 = Box::new(|x: &BF, y: &BF| -> BF { *x + *y }); // 1
        let map3 = Box::new(|x: &BF, y: &BF| -> BF { *x - *y }); // -1
        let map4 = Box::new(|x: &BF, y: &BF| -> BF { *x + (*y * BF::from(2)) }); // 2
        let map5 = Box::new(|_x: &BF, y: &BF| -> BF { *y }); // inf
        let maps: Vec<Box<dyn Fn(&BF, &BF) -> BF>> = vec![map1, map2, map3, map4, map5];
        let projective_map_indices = vec![0 as usize, 4 as usize];

        // Define interpolation matrix related maps.
        //
        // The actual interpolation matrix contains fractions (like 1/2, -1/2, etc).
        // To avoid fractions in the interpolation matrix, we multiply each term by the determinant
        // of the original function matrix. Let E be the original function matrix. In this case:
        //
        // E = [[1, 0, 0, 0, 0],
        //      [1, 1, 1, 1, 1],
        //      [1, -1, 1, -1, 1],
        //      [1, 2, 4, 8, 16],
        //      [0, 0, 0, 0, 1]].
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
        let interpolation_matrix = vec![
            vec![6, -3, -6, 3, 0],
            vec![0, 6, 3, -3, 0],
            vec![0, -2, 3, -1, 0],
            vec![0, -1, 0, 1, 0],
            vec![0, 12, -6, -12, 6],
        ];
        let imaps_base = get_imaps::<BF>(&interpolation_matrix);
        let imaps_ext = get_imaps::<EF>(&interpolation_matrix);

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
            Some(3),
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

        // Remember, we need to adjust for the △ term in the verifier. We only need to pass it as the
        // argument to the verifier. The verifier equation changes as:
        //
        // rᵢ₊₁(0) + rᵢ₊₁(1) == △ * rᵢ(αᵢ)
        //
        let round_t = Some(3 as usize);
        let mut verifier_transcript = Transcript::new(b"test_product_sumcheck");
        let result = IPForMLSumcheck::<EF, BF>::verify(
            to_ef(&claimed_sum),
            &proof,
            &mut verifier_transcript,
            AlgorithmType::ToomCook,
            Some(EF::from(6 as u32)),
            round_t,
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
            EF::new(*base_field_element, BF::zero())
        }

        // Multiplies a base field element to an extension field element
        fn mult_be(base_field_element: &BF, extension_field_element: &EF) -> EF {
            let mut result: EF = EF::from(*extension_field_element);
            result.mul_assign_by_basefield(base_field_element);
            result
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
        let mut rng = test_rng();
        const NV: usize = 10;
        let poly_a: DenseMultilinearExtension<BF> = DenseMultilinearExtension::rand(NV, &mut rng);
        let poly_b: DenseMultilinearExtension<BF> = DenseMultilinearExtension::rand(NV, &mut rng);
        let poly_c: DenseMultilinearExtension<BF> = DenseMultilinearExtension::from_evaluations_vec(
            NV,
            poly_a
                .evaluations
                .iter()
                .zip(poly_b.evaluations.iter())
                .map(|(a, b)| a * b)
                .collect(),
        );
        let poly_e: DenseMultilinearExtension<BF> = DenseMultilinearExtension::rand(NV, &mut rng);
        let claimed_sum: BF = BF::zero();

        let polynomials: Vec<LinearLagrangeList<BF>> = vec![
            LinearLagrangeList::<BF>::from(&poly_a),
            LinearLagrangeList::<BF>::from(&poly_b),
            LinearLagrangeList::<BF>::from(&poly_c),
            LinearLagrangeList::<BF>::from(&poly_e),
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
