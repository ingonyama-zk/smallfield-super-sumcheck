use ark_ec::CurveGroup;
use ark_ff::{batch_inversion_and_mul, PrimeField};
use merlin::Transcript;

use crate::{prover::SumcheckProof, transcript::TranscriptProtocol, IPForMLSumcheck};

impl<EF: PrimeField, BF: PrimeField> IPForMLSumcheck<EF, BF> {
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
    pub fn verify<G>(
        claimed_sum: EF,
        proof: &SumcheckProof<EF>,
        transcript: &mut Transcript,
        multiplicand: Option<EF>,
        round_t: Option<usize>,
    ) -> Result<bool, &'static str>
    where
        G: CurveGroup<ScalarField = EF>,
    {
        if proof.num_vars == 0 {
            return Err("Invalid proof.");
        }

        // Initiate the transcript with the protocol name
        <Transcript as TranscriptProtocol<G>>::sumcheck_proof_domain_sep(
            transcript,
            proof.num_vars as u64,
            proof.degree as u64,
        );

        let multiplicand_inv = match multiplicand {
            Some(m) => m.inverse().unwrap(),
            None => EF::ONE,
        };
        let mut multiplicand_inv_pow_t = EF::ONE;
        let unwrapped_round_t = match round_t {
            Some(t) => t,
            None => 0,
        };
        for _ in 0..unwrapped_round_t {
            multiplicand_inv_pow_t *= multiplicand_inv;
        }

        let mut expected_sum = claimed_sum;
        for round_index in 0..proof.num_vars {
            let round_poly_evaluations: &Vec<EF> = &proof.round_polynomials[round_index];
            if round_poly_evaluations.len() != (proof.degree + 1) {
                panic!(
                    "incorrect number of evaluations of the {}-th round polynomial",
                    round_index + 1
                );
            }

            let round_poly_evaluation_at_0 = round_poly_evaluations[0];
            let round_poly_evaluation_at_1 = round_poly_evaluations[1];
            let computed_sum = round_poly_evaluation_at_0 + round_poly_evaluation_at_1;

            // Check rᵢ(αᵢ) == rᵢ₊₁(0) + rᵢ₊₁(1)
            //
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
            if computed_sum != modified_expected_sum {
                return Err("Prover message is not consistent with the claim.".into());
            }

            // append the prover's message to the transcript
            <Transcript as TranscriptProtocol<G>>::append_scalars(
                transcript,
                b"r_poly",
                &proof.round_polynomials[round_index],
            );

            // derive the verifier's challenge for the next round
            let alpha = <Transcript as TranscriptProtocol<G>>::challenge_scalar(
                transcript,
                b"challenge_nextround",
            );

            // Compute r_{i}(α_i) using barycentric interpolation
            expected_sum = barycentric_interpolation(round_poly_evaluations, alpha);
        }
        Ok(true)
    }
}

///
/// Evaluates an MLE polynomial at `x` given its evaluations on a set of integers.
/// This works only for `num_points` ≤ 20 because we assume the integers are 64-bit numbers.
/// We know that 2^61 < factorial(20) < 2^62, hence factorial(20) can fit in a 64-bit number.
/// We can trivially extend this for `num_points` > 20 but in practical use cases, `num_points` would not exceed 8 or 10.
/// Reference: Equation (3.3) from https://people.maths.ox.ac.uk/trefethen/barycentric.pdf
///
pub(crate) fn barycentric_interpolation<F: PrimeField>(evaluations: &[F], x: F) -> F {
    let num_points = evaluations.len();
    let mut lagrange_coefficients: Vec<F> =
        (0..num_points).map(|j| x - F::from(j as u64)).collect();
    let lagrange_evaluation = lagrange_coefficients
        .iter()
        .fold(F::one(), |mult, lc| mult * lc);

    for i in 0..num_points {
        let negative_factorial = u64_factorial(num_points - 1 - i);
        let positive_factorial = u64_factorial(i);

        let barycentric_weight = negative_factorial * positive_factorial;
        if (num_points - 1 - i) % 2 == 1 {
            lagrange_coefficients[i] *= -F::from(barycentric_weight);
        } else {
            lagrange_coefficients[i] *= F::from(barycentric_weight);
        }
    }

    batch_inversion_and_mul(&mut lagrange_coefficients, &F::one());

    return lagrange_evaluation
        * evaluations
            .iter()
            .zip(lagrange_coefficients.iter())
            .fold(F::zero(), |acc, (&e, &lc)| acc + e * lc);
}

/// compute the factorial(a) = 1 * 2 * ... * a
#[inline]
fn u64_factorial(a: usize) -> u64 {
    let mut res = 1u64;
    for i in 1..=a {
        res *= i as u64;
    }
    res
}

#[cfg(test)]
mod test {
    use super::u64_factorial;
    use crate::verifier::barycentric_interpolation;
    use ark_poly::univariate::DensePolynomial;
    use ark_poly::DenseUVPolynomial;
    use ark_poly::Polynomial;
    use ark_std::vec::Vec;
    use ark_std::UniformRand;

    type F = ark_bls12_381::Fr;

    #[test]
    fn test_u64_factorial() {
        let input = 10 as usize;
        let result = u64_factorial(input);
        let result_prev = u64_factorial(input - 1);
        assert_eq!((input as u64) * result_prev, result);
    }

    #[test]
    fn test_interpolation() {
        let mut prng = ark_std::test_rng();

        // test a polynomial with 20 known points, i.e., with degree 19
        let poly = DensePolynomial::<F>::rand(20 - 1, &mut prng);
        let evals = (0..20)
            .map(|i| poly.evaluate(&F::from(i)))
            .collect::<Vec<F>>();
        let query = F::rand(&mut prng);

        assert_eq!(
            poly.evaluate(&query),
            barycentric_interpolation(&evals, query)
        );
    }
}
