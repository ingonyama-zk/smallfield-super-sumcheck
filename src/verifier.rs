use merlin::Transcript;

use crate::{
    btf_transcript::TFTranscriptProtocol,
    utils::error::SumcheckError,
    prover::{AlgorithmType, SumcheckProof},
    tower_fields::TowerField,
    utils::polynomial_interpolation::barycentric_interpolation_with_infinity,
    IPForMLSumcheck,
};

impl<EF: TowerField, BF: TowerField> IPForMLSumcheck<EF, BF> {
    ///
    /// Verify a sumcheck proof by checking for correctness of each round polynomial.
    /// Additionally, checks the evaluation of the original MLE polynomial (via oracle access)
    /// at the challenge vector is correct.
    ///
    /// TODO: Add final evaluation check for verifier using an opening proof (of a commitment scheme).
    /// The verifier does not perform the final check: f(alpha_1, alpha_2, ..., alpha_n) == r_n(alpha_n).
    /// This is because we have not implemented a commitment scheme that can allow a prover to "open" an MLE polynomial.
    /// We could give the verifier an oracle access to the MLE polynomial `f` but we defer this to the commitment
    /// scheme implementation in a future release.
    ///
    pub fn verify(
        claimed_sum: EF,
        proof: &SumcheckProof<EF>,
        transcript: &mut Transcript,
        algorithm: AlgorithmType,
        multiplicand: Option<EF>,
        round_t: Option<usize>,
    ) -> Result<bool, SumcheckError> {
        if proof.num_vars == 0 {
            return Err(SumcheckError::InvalidProof);
        }

        // Initiate the transcript with the protocol name
        <Transcript as TFTranscriptProtocol<EF, BF>>::sumcheck_proof_domain_sep(
            transcript,
            proof.num_vars as u64,
            proof.degree as u64,
        );

        let multiplicand_inv = match multiplicand {
            Some(m) => {
                if algorithm == AlgorithmType::ToomCook
                    || algorithm == AlgorithmType::ToomCookWithEq
                {
                    // TODO: Handle potential error instead of unwrap
                    m.inverse().expect("Multiplicand should be invertible")
                } else {
                    EF::one()
                }
            }
            None => EF::one(),
        };

        let mut multiplicand_inv_pow_t = EF::one();
        let unwrapped_round_t = match round_t {
            Some(t) => {
                if algorithm == AlgorithmType::ToomCook
                    || algorithm == AlgorithmType::ToomCookWithEq
                {
                    t
                } else {
                    0
                }
            }
            None => 0,
        };
        for _ in 0..unwrapped_round_t {
            multiplicand_inv_pow_t *= multiplicand_inv;
        }

        let mut expected_sum = claimed_sum;
        for round_index in 0..proof.num_vars {
            let s_degree = proof.degree; // Degree of the round polynomial s_i(X)
            // Received evaluations are in format: [s(0), s(∞), s(2), ..., s(degree-1)]
            let received_evaluations: &Vec<EF> = &proof.round_polynomials[round_index];

            // Expect message length to match degree
            if received_evaluations.len() != s_degree {
                return Err(SumcheckError::InvalidRoundPolynomial);
            }

            // Check rᵢ(αᵢ) == rᵢ₊₁(0) + rᵢ₊₁(1)
            //
            // (The below is DEPRECATED, we no longer need to worry about scaling factors)
            // In case of toom-cook based sumcheck, we would instead check the following:
            // For i ∈ [1, t):
            //              rᵢ(αᵢ) == rᵢ₊₁(0) + rᵢ₊₁(1)
            //   ⇒   △ᶦ⁺¹ * rᵢ(αᵢ) == △ᶦ⁺¹ * (rᵢ₊₁(0) + rᵢ₊₁(1))
            //   ⇒     △ * r'ᵢ(αᵢ) == r'ᵢ₊₁(0) + r'ᵢ₊₁(1)
            //
            // where r'ᵢ(.) and r'ᵢ₊₁(.) are the round polynomials sent by the prover.
            // For i = t:
            //               rₜ(αₜ) == rₜ₊₁(0) + rₜ₊₁(1)
            //
            // But since round t polynomial actually sent is r'ₜ(.) = △ᵗ * rₜ(.), we only have access
            // to r'ₜ(αₜ) = △ᵗ * rₜ(αₜ). Also, the round polynomials after round t are sent as simply:
            // rₜ₊₁(.), rₜ₊₂(.), ..., rₙ(.). Thus, we need to modify the verification equality as:
            //        △⁻ᵗ * r'ₜ(αₜ) == rₜ₊₁(0) + rₜ₊₁(1)
            //
            // For i > t, we don't need to change anything to the verification equation.
            //
            let modified_expected_sum = match multiplicand {
                Some(m) => {
                    assert!(round_t.is_some());
                    if (round_index + 1) <= unwrapped_round_t {
                        // Rounds [1, t]
                        m * expected_sum
                    } else if (round_index + 1) == (unwrapped_round_t + 1) {
                        // Round (t + 1)
                        multiplicand_inv_pow_t * expected_sum
                    } else {
                        // Rounds (t + 1, n]
                        expected_sum
                    }
                }
                None => expected_sum,
            };

            // Extract s_i(0) and s_i(∞)
            let round_poly_evaluation_at_0 = received_evaluations[0];
            let round_poly_evaluation_at_inf = if s_degree > 1 {
                received_evaluations[1]
            } else {
                // If degree is 1, s(inf) is implicitly 0 (or doesn't matter for interpolation)
                EF::zero()
            };

            // Derive s_i(1) using the expected sum: s_i(1) = modified_expected_sum - s_i(0)
            let derived_round_poly_evaluation_at_1 =
                modified_expected_sum - round_poly_evaluation_at_0;

            // Prepare evaluations for interpolation: [s(0), s(1), s(2), ..., s(degree-1)]
            let mut evaluations_for_interpolation = Vec::with_capacity(s_degree);
            evaluations_for_interpolation.push(round_poly_evaluation_at_0); // s(0)
            evaluations_for_interpolation.push(derived_round_poly_evaluation_at_1); // s(1)
            if s_degree > 2 {
                // Add s(2)...s(degree-1) from indices 2.. onwards
                evaluations_for_interpolation.extend_from_slice(&received_evaluations[2..]);
            }

            debug_assert_eq!(
                evaluations_for_interpolation.len(),
                s_degree,
                "Evaluations for interpolation should be of length s_degree"
            );

            // append the *prover's actual message* to the transcript
            // Format: [s(0), s(∞), s(2), ..., s(degree-1)]
            <Transcript as TFTranscriptProtocol<EF, BF>>::append_scalars(
                transcript,
                b"r_poly",
                received_evaluations,
            );

            // derive the verifier's challenge for the next round
            let alpha = <Transcript as TFTranscriptProtocol<EF, BF>>::challenge_scalar(
                transcript,
                b"challenge_nextround",
            );

            // Compute r_{i}(α_i) using the interpolation formula with infinity
            // Input evaluations: [s(0), s(1), ..., s(degree-1)]
            expected_sum = barycentric_interpolation_with_infinity(
                &evaluations_for_interpolation,
                round_poly_evaluation_at_inf,   // s(∞)
                alpha,
            );
        }
        // TODO: Add final evaluation check here
        // This would involve checking expected_sum against the claimed evaluation of the original MLE at the challenge point (alpha_1, ..., alpha_n)
        Ok(true)
    }
}

// All interpolation helper functions and tests have been moved to src/utils/polynomial_interpolation.rs
