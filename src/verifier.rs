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
                if algorithm == AlgorithmType::ToomCook
                    || algorithm == AlgorithmType::ToomCookWithEq
                {
                    m.inverse().unwrap()
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
            // Received evaluations are s_i(0), s_i(2), ..., s_i(d-1), s_i(inf)
            let received_evaluations: &Vec<EF> = &proof.round_polynomials[round_index];

            // Expect d = proof.degree evaluations
            if received_evaluations.len() != proof.degree {
                return Err(SumcheckError::InvalidRoundPolynomial);
            }

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

            // Derive s_i(1) using the expected sum: s_i(1) = modified_expected_sum - s_i(0)
            let derived_round_poly_evaluation_at_1 =
                modified_expected_sum - received_evaluations[0];

            // Extract s_i(inf)
            let mut round_poly_evaluation_at_inf = EF::zero();
            if proof.degree > 1 {
                round_poly_evaluation_at_inf = received_evaluations[proof.degree - 1];
            }

            // Reconstruct the evaluations vector [s_i(0), s_i(1), ..., s_i(d-1)] needed for interpolation
            let mut evaluations_for_interpolation = received_evaluations.clone();
            evaluations_for_interpolation.insert(1, derived_round_poly_evaluation_at_1); // Insert s_i(1)
            evaluations_for_interpolation.remove(proof.degree - 1); // Remove s_i(inf)
            debug_assert_eq!(
                evaluations_for_interpolation.len(),
                proof.degree,
                "Evaluations for interpolation should be of length d"
            );

            // append the *prover's actual message* to the transcript
            <Transcript as TFTranscriptProtocol<EF, BF>>::append_scalars(
                transcript,
                b"r_poly",
                received_evaluations, // Use the received evaluations [s(0), s_i(2), ..., s(d-1), s(inf)]
            );

            // derive the verifier's challenge for the next round
            let alpha = <Transcript as TFTranscriptProtocol<EF, BF>>::challenge_scalar(
                transcript,
                b"challenge_nextround",
            );

            // Compute r_{i}(α_i) using the interpolation formula with infinity
            expected_sum = barycentric_interpolation_with_infinity(
                &evaluations_for_interpolation, // s(0)...s(d-1)
                round_poly_evaluation_at_inf,   // s(inf)
                alpha,
            );
        }
        Ok(true)
    }
}

/// Given a vector of field elements {v_i}, compute the vector {coeff * v_i^(-1)}.
/// This method is explicitly single-threaded.
/// Based on arkwork's function (but modified for binary tower fields):
/// https://github.com/arkworks-rs/algebra/blob/b33df5cce2d54cf4c9248e4b229c7d6708fa9375/ff/src/fields/mod.rs#L381
fn batch_inversion_and_multiply<F: TowerField>(v: &mut [F], coeff: &F) {
    // Montgomery's Trick and Fast Implementation of Masked AES
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
    if (x.get_val() as usize) < num_points {
        return evaluations[x.get_val() as usize];
    }

    // Calculate L(x) = product_{k=0}^{n-1} (x - k)
    let lagrange_evaluation = (0..num_points)
        .map(|j| x - F::new(j as u128, None))
        .fold(F::one(), |mult, val| mult * val);

    // Calculate terms to be inverted: (x - j) * product_{k != j}(j - k)
    let mut terms_to_invert: Vec<F> = Vec::with_capacity(num_points);
    for j in 0..num_points {
        let x_minus_j = x - F::new(j as u128, None);
        let weight_j = compute_barycentric_weight::<F>(j, num_points); // weight_j = product_{k != j}(j-k)
        terms_to_invert.push(x_minus_j * weight_j);
    }

    // Batch invert the terms: terms_to_invert[j] now holds 1 / ((x-j)*w_j)
    batch_inversion_and_multiply(&mut terms_to_invert, &F::one());

    // Evaluate the final polynomial at point x using the formula:
    // P(x) = L(x) * sum_{j=0}^{n-1} ( y_j / ((x-j)*w_j) )
    let interpolation_result = evaluations
        .iter()
        .zip(terms_to_invert.iter())
        .fold(F::zero(), |acc, (&y_j, &inv_term_j)| {
            acc + (y_j * inv_term_j)
        });

    return lagrange_evaluation * interpolation_result;
}

///
/// Evaluates a polynomial s(x) of degree `d` given its evaluations at points {0, 1, ..., d-1}
/// and its evaluation at infinity s(inf), which is the leading coefficient.
/// Uses the formula from Lemma 2.2 (Eq 10) adapted for points {inf, 0, ..., d-1}:
/// s(x) = s(inf) * product_{k=0}^{d-1}(x - k) + P_{0..d-1}(x)
/// where P_{0..d-1}(x) is the unique polynomial of degree d-1 passing through (k, s(k)) for k=0..d-1.
///
pub(crate) fn barycentric_interpolation_with_infinity<F: TowerField>(
    evaluations_at_0_to_d_minus_1: &[F],
    evaluation_at_infinity: F,
    x: F,
) -> F {
    let d = evaluations_at_0_to_d_minus_1.len(); // This is the degree

    // Check if x is one of the finite evaluation points {0, ..., d-1}
    if (x.get_val() as usize) < d {
        return evaluations_at_0_to_d_minus_1[x.get_val() as usize];
    }

    // Calculate L(x) = product_{k=0}^{d-1} (x - k)
    let mut l_at_x = F::one();
    for k in 0..d {
        l_at_x *= x - F::new(k as u128, None);
    }

    // Calculate P_{0..d-1}(x) using standard barycentric interpolation for points {0..d-1}
    // Note: The polynomial P has degree d-1, uses d points {0..d-1}
    // Input evaluations should be s(0)...s(d-1)
    let interp_poly_degree_d_minus_1 = barycentric_interpolation(evaluations_at_0_to_d_minus_1, x);

    // Combine results: s(x) = s(inf) * L(x) + P_{0..d-1}(x)
    evaluation_at_infinity * l_at_x + interp_poly_degree_d_minus_1
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
        let x_rand = BF::rand(Some(6));

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
