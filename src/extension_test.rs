#[cfg(test)]
mod extension_tests {
    use crate::data_structures::LinearLagrangeList;
    use crate::prover::AlgorithmType;
    use crate::prover::ProverState;
    use crate::prover::SumcheckProof;
    use crate::IPForMLSumcheck;
    use ark_ff::PrimeField;
    use ark_ff::Zero;
    use ark_poly::DenseMultilinearExtension;
    use ark_poly::MultilinearExtension;
    use ark_std::test_rng;
    use ark_std::vec::Vec;
    use merlin::Transcript;

    type BF = ark_bls12_381::Fq;
    type EF = ark_bls12_381::Fq2;

    // #[ignore]
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
        );

        let mut verifier_transcript = Transcript::new(b"test_sumcheck");
        let result = IPForMLSumcheck::<EF, BF>::verify(
            to_ef(&claimed_sum),
            &proof,
            &mut verifier_transcript,
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
            None,
            None,
        );
        assert_eq!(result.unwrap(), true);

        let mut verifier_transcript_dup = Transcript::new(b"test_product_sumcheck_algo2");
        let result_dup = IPForMLSumcheck::<EF, BF>::verify(
            to_ef(&claimed_sum),
            &proof_dup,
            &mut verifier_transcript_dup,
            None,
            None,
        );
        assert_eq!(result_dup.unwrap(), true);
    }
}
