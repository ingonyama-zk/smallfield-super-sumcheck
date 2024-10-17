use merlin::Transcript;

use crate::{
    btf_transcript::TFTranscriptProtocol,
    error::SumcheckError,
    prover::{AlgorithmType, SumcheckProof},
    tower_fields::TowerField,
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
                if algorithm == AlgorithmType::ToomCook {
                    m.inverse().unwrap()
                } else {
                    EF::one()
                }
            }
            None => EF::one(),
        };
        println!("mult_inv = {}", multiplicand_inv);
        let mut multiplicand_inv_pow_t = EF::one();
        let unwrapped_round_t = match round_t {
            Some(t) => {
                if algorithm == AlgorithmType::ToomCook {
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

        println!("mult_inv_pow_t = {}", multiplicand_inv_pow_t);

        let mut expected_sum = claimed_sum;
        for round_index in 0..proof.num_vars {
            let round_poly_evaluations: &Vec<EF> = &proof.round_polynomials[round_index];
            if round_poly_evaluations.len() != (proof.degree + 1) {
                return Err(SumcheckError::InvalidRoundPolynomial);
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
                return Err(SumcheckError::ProofVerificationFailure);
            }

            // append the prover's message to the transcript
            <Transcript as TFTranscriptProtocol<EF, BF>>::append_scalars(
                transcript,
                b"r_poly",
                &proof.round_polynomials[round_index],
            );

            // derive the verifier's challenge for the next round
            let alpha = <Transcript as TFTranscriptProtocol<EF, BF>>::challenge_scalar(
                transcript,
                b"challenge_nextround",
            );
            println!("v_challenge = {:?}", alpha);

            // Compute r_{i}(α_i) using barycentric interpolation
            expected_sum = barycentric_interpolation(round_poly_evaluations, alpha);
        }
        Ok(true)
    }
}

/// Given a vector of field elements {v_i}, compute the vector {coeff * v_i^(-1)}.
/// This method is explicitly single-threaded.
/// Based on arkwork's function (but modified for binary tower fields):
/// https://github.com/arkworks-rs/algebra/blob/b33df5cce2d54cf4c9248e4b229c7d6708fa9375/ff/src/fields/mod.rs#L381
fn batch_inversion_and_multiply<F: TowerField>(v: &mut [F], coeff: &F) {
    // Montgomery’s Trick and Fast Implementation of Masked AES
    // Genelle, Prouff and Quisquater
    // Section 3.2
    // but with an optimization to multiply every element in the returned vector by
    // coeff

    // First pass: compute [a, ab, abc, abcd]
    let mut prod = Vec::with_capacity(v.len());
    let mut tmp = F::one();
    for f in v.iter().filter(|f| !f.is_zero()) {
        tmp.mul_assign(f.clone());
        prod.push(tmp);
    }

    // Invert `tmp` ==> tmp = (1 / abcd)
    tmp = tmp.inverse().unwrap(); // Guaranteed to be nonzero.

    // Multiply product by coeff, so all inverses will be scaled by coeff
    // tmp = q / abcd
    tmp *= coeff.clone();

    // Second pass: iterate backwards to compute inverses
    // f: [d  c  a  b]
    // s: [abc  ab  a  1]
    // tmp: q / abcd
    //
    // 0:  abc * tmp = abc * (q / abcd) = q / d
    // 1:  ab  * tmp = ab  * (q / abc)  = q / c
    // 2:  a   * tmp = a   * (q / ab)   = q / b
    // 3:  1   * tmp = 1   * (q / a)    = q / a
    //
    for (f, s) in v
        .iter_mut()
        // Backwards
        .rev()
        // Ignore normalized elements
        .filter(|f| !f.is_zero())
        // Backwards, skip last element, fill in one for last term.
        .zip(prod.into_iter().rev().skip(1).chain(Some(F::one())))
    {
        // tmp := tmp * f; f := tmp * s = 1/f
        let new_tmp = tmp * *f;
        *f = tmp * s;
        tmp = new_tmp;
    }
}

fn compute_barycentric_weight<F: TowerField>(i: usize, n: usize) -> F {
    let mut weight = F::one();
    let f_i = F::new(i as u128, None);
    for j in 0..n {
        if j == i {
            continue;
        } else {
            let difference = f_i - F::new(j as u128, None);
            weight *= difference;
        }
    }
    weight
}

///
/// Evaluates an MLE polynomial at `x` given its evaluations on a set of integers.
/// This works only for `num_points` ≤ 20 because we assume the integers are 64-bit numbers.
/// We know that 2^61 < factorial(20) < 2^62, hence factorial(20) can fit in a 64-bit number.
/// We can trivially extend this for `num_points` > 20 but in practical use cases, `num_points` would not exceed 8 or 10.
/// Reference: Equation (3.3) from https://people.maths.ox.ac.uk/trefethen/barycentric.pdf
///
/// We assume the integers are: I := {0, 1, 2, ..., n - 1}
///
pub(crate) fn barycentric_interpolation<F: TowerField>(evaluations: &[F], x: F) -> F {
    // If the evaluation point x is in I, just return the corresponding evaluation.
    let num_points = evaluations.len();
    if x.get_val() < (num_points as u128) {
        return evaluations[x.get_val() as usize];
    }

    // Calculate Lagrange coefficients: (x - 0), (x - 1), ..., (x - (n - 1))
    let mut lagrange_coefficients: Vec<F> = (0..num_points)
        .map(|j| x - F::new(j as u128, None))
        .collect();

    // Compute the product of all lagrange coefficients: (x - 0) * (x - 1) * ... * (x - (n - 1))
    let lagrange_evaluation = lagrange_coefficients
        .iter()
        .fold(F::one(), |mult, lc| mult * lc.clone());

    for i in 0..num_points {
        // The i-th barycentric weight is: (i - 0) * (i - 1) * ... * (i - (n - 1))
        // except the (i - i) term (ofcourse).
        let barycentric_weight = compute_barycentric_weight::<F>(i, num_points);

        // Modify the coefficients with the barycentric weights
        lagrange_coefficients[i] *= barycentric_weight;
    }

    // Perform batch inversion and multiply by the coefficient
    // Here, we assume you want to multiply by the identity (F::one())
    batch_inversion_and_multiply(&mut lagrange_coefficients, &F::one());

    // Evaluate the final polynomial at point x
    let interpolation_result = evaluations
        .iter()
        .zip(lagrange_coefficients.iter())
        .fold(F::zero(), |acc, (&e, &lc)| acc + (e * lc));

    return lagrange_evaluation * interpolation_result;
}

#[cfg(test)]
mod test {
    use num::Zero;

    use crate::tower_fields::binius::BiniusTowerField;
    use crate::tower_fields::TowerField;
    use crate::verifier::{barycentric_interpolation, batch_inversion_and_multiply};

    type BF = BiniusTowerField;

    fn evaluate<F: TowerField>(v: &[F], x: &F) -> F {
        let mut result = F::zero();
        let mut x_pow = F::one();

        // Iterate through the coefficients from highest degree to lowest
        for coeff in v.iter() {
            // Add the current term (coeff * x^i) to the result
            result += coeff.clone() * x_pow.clone();
            x_pow *= x.clone();
        }
        result
    }

    #[test]
    fn test_batch_inversion_and_multiply() {
        // Define constants
        const NV: usize = 16;
        const NE: u32 = (1 as u32) << NV;

        // Generate a random vector of elements in the binary field (BF)
        let mut v = BF::rand_vector(NE as usize, Some(4));

        // Create a random coefficient to multiply every element in the vector after inversion
        let coeff = BF::rand(Some(2));

        // Store the original vector for verification after batch inversion
        let original_v = v.clone();

        // Perform the batch inversion and multiplication
        batch_inversion_and_multiply(&mut v, &coeff);

        // Check that each non-zero element in the original vector was correctly inverted
        for (i, elem) in original_v.iter().enumerate() {
            // Ignore zero elements as they are not inverted
            if !elem.is_zero() {
                // The product of the original element and its batch inverse (multiplied by the coefficient)
                // should be equal to the coefficient
                let inverted_elem = &v[i];

                // Check that elem * inverted_elem * coeff = coeff
                let product = *elem * *inverted_elem;

                // Since we're in a binary field, this product should equal coeff
                assert_eq!(product, coeff, "Batch inversion failed at index {}", i);
            }
        }
    }

    #[test]
    fn test_barycentric_interpolation_random() {
        const NE: u32 = 100; // Number of elements

        // Step 1: Sample a random coefficient vector
        let coeffs: Vec<BF> = (0..NE).map(|_| BF::rand(Some(3))).collect();

        // Step 2: Compute its evaluation on [0, 1, ..., N-1]
        let points: Vec<BF> = (0..NE).map(|j| BF::new(j as u128, Some(3))).collect();
        let values: Vec<BF> = points.iter().map(|x| evaluate(&coeffs, x)).collect();

        // Step 3: Choose a random point in a large range
        let x_rand = BF::rand(Some(5));

        // Step 4: Perform barycentric interpolation at the random point
        let barycentric_eval = barycentric_interpolation(&values, x_rand);

        // Step 5: Evaluate the original coefficient form at the random point
        let original_eval = evaluate(&coeffs, &x_rand);

        // Step 6: Assert that the barycentric evaluation matches the original evaluation
        assert_eq!(
            barycentric_eval, original_eval,
            "Barycentric evaluation does not match original evaluation!"
        );
    }
}
