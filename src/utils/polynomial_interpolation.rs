use crate::{tower_fields::TowerField, utils::error::SumcheckError};
use num::{One, Zero};

/// Given a vector of field elements {v_i}, compute the vector {coeff * v_i^(-1)}.
/// This method is explicitly single-threaded.
/// Based on arkwork's function (but modified for binary tower fields):
/// https://github.com/arkworks-rs/algebra/blob/b33df5cce2d54cf4c9248e4b229c7d6708fa9375/ff/src/fields/mod.rs#L381
pub(crate) fn batch_inversion_and_multiply<F: TowerField>(v: &mut [F], coeff: &F) {
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
    // TODO: Handle potential error instead of unwrap
    tmp = tmp.inverse().expect("Inverse should exist for non-zero product");

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
/// Evaluates an MLE polynomial at `x` given its evaluations on a set of integers {0, 1, ..., n-1}.
/// Uses the standard barycentric formula (Form 2).
/// Reference: Equation (3.3) from https://people.maths.ox.ac.uk/trefethen/barycentric.pdf
///
/// We assume the integers are: I := {0, 1, 2, ..., n - 1} where n = evaluations.len().
///
pub fn barycentric_interpolation<F: TowerField>(evaluations: &[F], x: F) -> F {
    let num_points = evaluations.len();
    if num_points == 0 {
        return F::zero();
    }
    if num_points == 1 {
        return evaluations[0];
    }

    // If the evaluation point x is one of the interpolation points {0, ..., n-1}, return the corresponding evaluation.
    // Check if x represents a small integer within the range [0, num_points-1]
    if x.get_val() < num_points as u128 {
        // Check if the field element actually corresponds to this integer value
        if x == F::new(x.get_val(), None) {
            return evaluations[x.get_val() as usize];
        }
    }

    // Check if x is one of the interpolation points explicitly to avoid division by zero later
    for j in 0..num_points {
        if x == F::new(j as u128, None) {
            return evaluations[j];
        }
    }

    // Calculate L(x) = product_{k=0}^{n-1} (x - k)
    let lagrange_evaluation = (0..num_points)
        .map(|j| x - F::new(j as u128, None))
        .fold(F::one(), |mult, val| mult * val);

    // Calculate terms to be inverted: (x - j) * product_{k != j}(j - k)
    let mut terms_to_invert: Vec<F> = Vec::with_capacity(num_points);
    for j in 0..num_points {
        let x_minus_j = x - F::new(j as u128, None);
        // weight_j = product_{k != j}(j-k)
        let weight_j = compute_barycentric_weight::<F>(j, num_points);
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

    lagrange_evaluation * interpolation_result
}


///
/// Evaluates a polynomial s(x) of degree `d` given its evaluations at points {0, 1, ..., d-1}
/// and its evaluation at infinity s(inf), which is the leading coefficient.
/// Uses the formula from Lemma 2.2 (Eq 10) adapted for points {inf, 0, ..., d-1}:
/// s(x) = s(inf) * product_{k=0}^{d-1}(x - k) + P_{0..d-1}(x)
/// where P_{0..d-1}(x) is the unique polynomial of degree d-1 passing through (k, s(k)) for k=0..d-1.
///
pub fn barycentric_interpolation_with_infinity<F: TowerField>(
    evaluations_at_0_to_d_minus_1: &[F],
    evaluation_at_infinity: F,
    x: F,
) -> F {
    let d = evaluations_at_0_to_d_minus_1.len(); // This is the degree

    // Handle degree 0 case (polynomial is constant s(inf))
    if d == 0 {
        return evaluation_at_infinity;
    }

    // Handle degree 1 case: s(x) = s(inf)*x + s(0)
    if d == 1 {
        let s_0 = evaluations_at_0_to_d_minus_1[0];
        return evaluation_at_infinity * x + s_0;
    }

    // Check if x is one of the finite evaluation points {0, ..., d-1}
    // Check if x represents a small integer within the range [0, d-1]
    if x.get_val() < d as u128 {
        // Check if the field element actually corresponds to this integer value
        if x == F::new(x.get_val(), None) {
            return evaluations_at_0_to_d_minus_1[x.get_val() as usize];
        }
    }

    // Check if x is one of the interpolation points explicitly to avoid division by zero in underlying call
    for k in 0..d {
        if x == F::new(k as u128, None) {
             return evaluations_at_0_to_d_minus_1[k];
        }
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

/// Interpolates the evaluations of a product polynomial `s(X) = l(X) * t(X)`.
///
/// Given evaluations of a linear polynomial `l(X)` at 0 and infinity (`linear_evals = [l(0), l(inf)]`),
/// and evaluations of a degree `d` polynomial `t(X)` at points `{0, inf, 2, ..., d-1}`
/// (`t_evals = [t(0), t(inf), t(2), ..., t(d-1)]`), and a hint `C = s(0) + s(1)`,
/// this function computes the required prover message for the sumcheck round, which consists
/// of evaluations of `s(X)` (degree `d+1`) at points `{0, inf, 2, ..., d+1}`.
///
/// The logic follows Gruen's optimization:
/// 1. Compute `s(0) = l(0) * t(0)`.
/// 2. Compute `s(1) = C - s(0)`.
/// 3. Compute `l(1) = l(0) + l(inf)`.
/// 4. If `l(1) == 0`, check consistency (`s(1)` must be 0). Return error if inconsistent or if l(1)=0 (as t(1) is needed).
/// 5. Compute `t(1) = s(1) / l(1)`.
/// 6. Compute `s(inf) = l(inf) * t(inf)`.
/// 7. Compute `s(u) = l(u) * t(u)` for `u = 2, ..., d+1`:
///    - `l(u)` is derived from `l(0)` and `l(inf)`.
///    - `t(u)` is derived by interpolating `t(X)` using evaluations at `{0, 1, ..., d-1, inf}`.
/// 8. Return `([s(0), s(inf), s(2), ..., s(d+1)], s(1))`.
///
/// # Arguments
/// * `linear_evals`: `[l(0), l(inf)]`.
/// * `t_evals`: `[t(0), t(inf), t(2), ..., t(d-1)]`. Length `d`.
/// * `hint`: The claimed sum `C = s(0) + s(1)`.
///
/// # Returns
/// A `Result` containing `(prover_message, s(1))` on success, or `SumcheckError` on failure.
/// `prover_message` is `[s(0), s(inf), s(2), ..., s(d+1)]`.
pub fn interpolate_product_poly_evals<F: TowerField>(
    linear_evals: &[F; 2],
    t_evals: &[F], // Expecting [t(0), t(inf), t(2), ..., t(d-1)] (length d)
    hint: F,
) -> Result<(Vec<F>, F), SumcheckError> {
    let d = t_evals.len(); // Degree of t(X) is d
    if d < 1 { // Need at least degree 1 for t(X) -> s(X) degree 2
         // Handle t(X) constant case (d=0)? If combine fn is constant, t is zero poly?
         // Assume d >= 1 for now, based on compute_ti_evaluations logic
         // TODO: Clarify and handle d=0 case if necessary.
        return Err(SumcheckError::InvalidRoundPolynomial);
    }
    let s_degree = d + 1;

    if linear_evals.len() != 2 {
        return Err(SumcheckError::InvalidRoundPolynomial); // Input length mismatch
    }
    if t_evals.len() != d {
        // This check seems redundant given how d is derived, but keep for clarity
        return Err(SumcheckError::InvalidRoundPolynomial); // Input length mismatch
    }


    let l_0 = linear_evals[0];
    let l_inf = linear_evals[1];
    let t_0 = t_evals[0];
    let t_inf = t_evals[1]; // t(inf) is the second element

    // 1. Calculate s(0) = l(0) * t(0)
    let s_0 = l_0 * t_0;

    // 2. Calculate s(1) using the hint: s(1) = hint - s(0)
    let s_1 = hint - s_0;

    // 3. Calculate l(1) = l(0) + l(inf)
    let l_1 = l_0 + l_inf;

    // 4. & 5. Calculate t(1)
    let t_1 = if l_1.is_zero() {
        // If l(1) is 0, then s(1) must also be 0 for consistency.
        if !s_1.is_zero() {
             return Err(SumcheckError::InvalidRoundPolynomial); // Hint inconsistent with l(1)=0
        }
        // If s(1)=0 and l(1)=0, t(1) is undetermined by hint s(1) = l(1)t(1).
        // The interpolation step requires t(1).
        // Returning error as we cannot proceed without a defined t(1).
        return Err(SumcheckError::InvalidRoundPolynomial); // Cannot determine t(1) when l(1) is zero
    } else {
        // Calculate t(1) = s(1) / l(1)
        s_1 * l_1.inverse().ok_or(SumcheckError::InvalidRoundPolynomial)? // Indicate inverse failure
    };

    // Assemble the d+1 evaluations of t needed for interpolation over points {0, 1, ..., d-1, inf}.
    // Order for barycentric_interpolation_with_infinity: evals at 0..d-1, then eval at infinity.
    let mut t_interp_evals_0_to_d_minus_1 = Vec::with_capacity(d);
    t_interp_evals_0_to_d_minus_1.push(t_0); // t(0)
    t_interp_evals_0_to_d_minus_1.push(t_1); // t(1)
    if d > 2 { // t_evals = [t(0), t(inf), t(2), ..., t(d-1)]
        t_interp_evals_0_to_d_minus_1.extend_from_slice(&t_evals[2..]); // t(2) ... t(d-1)
    }
    // t_interp_evals_0_to_d_minus_1 now contains [t(0), t(1), t(2), ..., t(d-1)]

    // --- Calculate required s evaluations ---
    // Need [s(0), s(inf), s(2), ..., s(d+1)] (length d+2 for degree d+1 poly)
    let mut prover_message = Vec::with_capacity(s_degree + 1);

    // s(0) - already computed
    prover_message.push(s_0);

    // s(inf) = l(inf) * t(inf) (leading coefficient of s)
    let s_inf = l_inf * t_inf;
    prover_message.push(s_inf);

    // Compute s(u) = l(u) * t(u) for u = 2..d
    // l(u) = l(0) + u * l(inf)
    // t(u) is taken from t_evals for u=2..d-1, and interpolated for u=d
    let mut current_l_eval = l_1; // Start from l(1)
    for u_val in 2..=d {
        current_l_eval += l_inf; // l(u) = l(u-1) + l(inf)

        // Get t(u)
        let point_u = F::new(u_val as u128, None);
        let t_u = if u_val < d {
            // For u = 2..d-1, t(u) is directly available in t_evals at index u.
            // t_evals = [t(0), t(inf), t(2), ..., t(d-1)]
            t_evals[u_val]
        } else {
            // For u = d, interpolate t(u).
            barycentric_interpolation_with_infinity(
                &t_interp_evals_0_to_d_minus_1, // Evals at 0..d-1
                t_inf,                          // Eval at infinity
                point_u,                        // Point to evaluate at
            )
        };

        prover_message.push(current_l_eval * t_u); // s(u) = l(u) * t(u)
    }

    // Final prover message structure: [s(0), s(inf), s(2), ..., s(d)], and s(1)
    Ok((prover_message, s_1))
}

// Helper for evaluating a polynomial given its coefficients.
// Moved to module scope for test visibility
#[cfg(test)]
fn evaluate_poly<F: TowerField>(coeffs: &[F], x: F) -> F {
    let mut res = F::zero();
    // Evaluate using Horner's method
    for &c in coeffs.iter().rev() {
        res = res * x + c;
    }
    res
}

#[cfg(test)]
mod test {
    use super::*;
    // Explicitly bring evaluate_poly into test module scope
    use super::evaluate_poly;
    use crate::tower_fields::binius::BiniusTowerField;
    use crate::utils::error::SumcheckError;
    use num::{One, Zero};

    type BF = BiniusTowerField;

    // Helper function to evaluate a polynomial given its coefficients
    fn evaluate<F: TowerField>(coeffs: &[F], x: &F) -> F {
        let mut result = F::zero();
        let mut x_pow = F::one();

        // Evaluate using Horner's method or similar
        for coeff in coeffs.iter() {
            result += *coeff * x_pow;
            x_pow *= *x;
        }
        result
    }


    #[test]
    fn test_batch_inversion_and_multiply() {
        // Define constants
        const NE: usize = 16; // Number of elements to test

        // Generate a random vector of elements in the binary field (BF)
        let mut v: Vec<BF> = (0..NE).map(|_| BF::rand(Some(4))).collect();

        // Ensure some elements are zero for testing filtering
        if NE > 2 {
            v[1] = BF::zero();
        }

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
                // The product of the original element and its batch inverse should be equal to the coefficient
                let inverted_elem = &v[i];
                let product = *elem * *inverted_elem;
                assert_eq!(product, coeff, "Batch inversion failed at index {}", i);
            } else {
                // Zero elements should remain zero
                 assert!(v[i].is_zero(), "Zero element changed at index {}", i);
            }
        }
    }


    #[test]
    fn test_barycentric_interpolation_random() {
        const NE: usize = 10; // Number of evaluation points (degree = NE - 1)

        // Step 1: Sample a random coefficient vector for a polynomial of degree NE-1
        let coeffs: Vec<BF> = (0..NE).map(|_| BF::rand(Some(3))).collect();

        // Step 2: Compute its evaluation on [0, 1, ..., NE-1]
        let points: Vec<BF> = (0..NE).map(|j| BF::new(j as u128, None)).collect();
        let values: Vec<BF> = points.iter().map(|x| evaluate(&coeffs, x)).collect();

        // Step 3: Choose a random point outside the interpolation set
        let x_rand = BF::rand(Some(6)); // Choose a random point

        // Step 4: Perform barycentric interpolation at the random point
        let barycentric_eval = barycentric_interpolation(&values, x_rand);

        // Step 5: Evaluate the original coefficient form at the random point
        let original_eval = evaluate(&coeffs, &x_rand);

        // Step 6: Assert that the barycentric evaluation matches the original evaluation
        assert_eq!(
            barycentric_eval, original_eval,
            "Barycentric evaluation does not match original evaluation!"
        );

        // Step 7: Test evaluation at one of the known points
         let x_known = BF::new(2, None);
         if NE > 2 {
            let barycentric_eval_known = barycentric_interpolation(&values, x_known);
            assert_eq!(barycentric_eval_known, values[2], "Barycentric evaluation failed at known point 2");
         }
    }

     #[test]
    fn test_barycentric_interpolation_degree_0() {
        let coeffs = vec![BF::new(5, None)]; // Constant polynomial 5
        let values = vec![BF::new(5, None)]; // Evaluation at 0 is 5
        let x_eval = BF::rand(Some(3));
        let interp_eval = barycentric_interpolation(&values, x_eval);
        assert_eq!(interp_eval, coeffs[0]);
    }


    #[test]
    fn test_barycentric_interpolation_with_infinity() {
        // Define a polynomial s(x) = c_d * x^d + ... + c_1 * x + c_0
        let degree = 5; // Polynomial degree
        let num_coeffs = degree + 1;
        let coeffs: Vec<BF> = (0..num_coeffs).map(|_| BF::rand(Some(3))).collect();
        let s_inf = coeffs[degree]; // Leading coefficient is s(inf)

        // Calculate evaluations at {0, 1, ..., d-1}
        let points_0_to_d_minus_1: Vec<BF> = (0..degree).map(|j| BF::new(j as u128, None)).collect();
        let evals_0_to_d_minus_1: Vec<BF> = points_0_to_d_minus_1.iter().map(|x| evaluate(&coeffs, x)).collect();

        // Choose a random evaluation point x
        let x_eval = BF::rand(Some(5));

        // Evaluate using the interpolation function
        let interp_eval = barycentric_interpolation_with_infinity(
            &evals_0_to_d_minus_1,
            s_inf,
            x_eval,
        );

        // Evaluate directly using coefficients
        let direct_eval = evaluate(&coeffs, &x_eval);

        // Assert they match
        assert_eq!(interp_eval, direct_eval, "Interpolation with infinity failed");

        // Test edge case: evaluate at one of the known points (e.g., 2)
        let x_known = BF::new(2, None);
         if degree > 2 {
            let interp_eval_known = barycentric_interpolation_with_infinity(
                &evals_0_to_d_minus_1,
                s_inf,
                x_known,
            );
            assert_eq!(interp_eval_known, evals_0_to_d_minus_1[2], "Interpolation with infinity failed at known point 2");
         }
    }

     #[test]
    fn test_barycentric_interpolation_with_infinity_degree_0() {
        // s(x) = c_0 (constant)
        let s_inf = BF::zero(); // Leading coeff is 0 for degree 0
        let evals_0_to_d_minus_1 = &[]; // No points for d=0
        let x_eval = BF::rand(Some(3));
        let interp_eval = barycentric_interpolation_with_infinity(evals_0_to_d_minus_1, s_inf, x_eval);
        assert_eq!(interp_eval, BF::zero(), "Interpolation deg 0 failed"); // Should maybe return s(0) if interpreted differently? The current logic returns s_inf=0.
        // Let's test the degree 1 case with this function too, as it's handled specifically
        // s(x) = 3x + 5
         let coeffs_deg1 = vec![BF::new(5, None), BF::new(3, None)];
         let s_inf_deg1 = BF::new(3, None);
         let evals_deg1 = vec![evaluate(&coeffs_deg1, &BF::zero())]; // s(0) = 5
         let interp_eval_deg1 = barycentric_interpolation_with_infinity(&evals_deg1, s_inf_deg1, x_eval);
         assert_eq!(interp_eval_deg1, evaluate(&coeffs_deg1, &x_eval), "Interpolation deg 1 failed");
    }

    // Add tests for interpolate_product_poly_evals
    #[test]
    fn test_interpolate_product_poly_evals_quadratic() {
        // s(X) = l(X) * t(X), where l is linear, t is linear (t_degree=1, d=1)
        // s(X) is quadratic (s_degree=2)
        type F = BiniusTowerField;
        let l_0 = F::new(3, None);
        let l_inf = F::new(2, None); // l(X) = 3 + 2X
        let l_evals = [l_0, l_inf];
        // t(X) is linear (degree=1). Input t_evals = [t(0), t(inf)], length d=1.
        let t_0 = F::new(5, None);
        let t_inf = F::new(4, None); // t(X) = 5 + 4X
        let t_evals = &[t_0, t_inf]; // [t(0), t(inf)]

        // Calculate expected s(X) = (3+2X)(5+4X) = 15 + 22X + 8X^2
        let s_coeffs_exp = vec![F::new(15, None), F::new(22, None), F::new(8, None)];
        let s_0_exp = evaluate_poly(&s_coeffs_exp, F::zero()); // 15
        let s_1_exp = evaluate_poly(&s_coeffs_exp, F::one()); // 15 + 22 + 8 = 45
        let s_2_exp = evaluate_poly(&s_coeffs_exp, F::new(2, None)); // 15 + 44 + 32 = 91
        let s_inf_exp = F::new(8, None); // Leading coefficient

        let hint = s_0_exp + s_1_exp; // 15 + 45 = 60

        let result = interpolate_product_poly_evals(&l_evals, t_evals, hint);
        assert!(result.is_ok(), "interpolate_product_poly_evals failed: {:?}", result.err());
        let (s_evals_prover, s_1_res) = result.unwrap();

        // Expected prover message for quadratic s(X) (degree 2): [s(0), s(inf), s(2)], length s_degree+1 = 3
        assert_eq!(s_evals_prover.len(), 3, "Prover message length incorrect");
        assert_eq!(s_evals_prover[0], s_0_exp, "s(0)");
        assert_eq!(s_evals_prover[1], s_inf_exp, "s(inf)");
        assert_eq!(s_evals_prover[2], s_2_exp, "s(2)");
        assert_eq!(s_1_res, s_1_exp, "s(1)");
    }

    #[test]
    fn test_interpolate_product_poly_evals_cubic_t() {
        // t is cubic (degree=3, d=3)
        // s is quartic (s_degree=4)
        type F = BiniusTowerField;
        let l_0 = F::new(2, None);
        let l_inf = F::new(1, None); // l(X) = 2 + X
        let l_evals = [l_0, l_inf];

        // t(X) = 1 + 2X + 3X^2 + 4X^3 (degree=3)
        let t_coeffs = vec![F::new(1, None), F::new(2, None), F::new(3, None), F::new(4, None)];
        let t_0 = evaluate_poly(&t_coeffs, F::zero()); // t(0)=1
        let t_1 = evaluate_poly(&t_coeffs, F::one()); // t(1)=10
        let t_2 = evaluate_poly(&t_coeffs, F::new(2, None)); // t(2)=49
        let t_inf = F::new(4, None); // Leading coeff

        // Input t_evals: [t(0), t(inf), t(2...d-1)] = [t(0), t(inf), t(2)], length d=3
        let t_evals = &[t_0, t_inf, t_2];

        // Expected s(X) = (2+X)(1 + 2X + 3X^2 + 4X^3) = 2 + 5X + 8X^2 + 11X^3 + 4X^4 (degree s_degree=4)
        let s_coeffs = vec![F::new(2, None), F::new(5, None), F::new(8, None), F::new(11, None), F::new(4, None)];
        let s_0_exp = evaluate_poly(&s_coeffs, F::zero()); // 2
        let s_1_exp = evaluate_poly(&s_coeffs, F::one()); // 30
        let s_2_exp = evaluate_poly(&s_coeffs, F::new(2, None)); // 196
        let s_3_exp = evaluate_poly(&s_coeffs, F::new(3, None)); // 710
        let s_4_exp = evaluate_poly(&s_coeffs, F::new(4, None)); // 1962
        let s_inf_exp = F::new(4, None); // Leading coeff

        let hint = s_0_exp + s_1_exp; // 2 + 30 = 32

        let result = interpolate_product_poly_evals(&l_evals, t_evals, hint);
         assert!(result.is_ok(), "Result was {:?}", result.err());
        let (s_evals_prover, s_1_res) = result.unwrap();

        // Expected prover message for quartic s(X) (degree 4): [s(0), s(inf), s(2), s(3), s(4)], length s_degree+1 = 5
        assert_eq!(s_evals_prover.len(), 5, "Prover message length incorrect");
        assert_eq!(s_evals_prover[0], s_0_exp, "s(0)");
        assert_eq!(s_evals_prover[1], s_inf_exp, "s(inf)");
        assert_eq!(s_evals_prover[2], s_2_exp, "s(2)");
        assert_eq!(s_evals_prover[3], s_3_exp, "s(3)");
        assert_eq!(s_evals_prover[4], s_4_exp, "s(4)");
        assert_eq!(s_1_res, s_1_exp, "s(1)");
    }

    #[test]
    fn test_interpolate_product_poly_evals_constant_t() {
        // t is constant (degree=0, d=0). Should error.
        // s is linear (s_degree=1)
        type F = BiniusTowerField;
        let l_0 = F::new(7, None);
        let l_inf = F::new(6, None); // l(X) = 7 + 6X
        let l_evals = [l_0, l_inf];

        // t(X) is constant (degree=0). Input t_evals should be [], length d=0.
        let t_0 = F::new(5, None); // t(X) = 5
        let t_evals:&[F] = &[]; // Empty slice for d=0

        // Calculate expected s(X) = (7+6X)(5) = 35 + 30X
        let s_coeffs_exp = vec![F::new(35, None), F::new(30, None)];
        let hint = F::new(100, None); // Doesn't matter, should error before use

        let result = interpolate_product_poly_evals(&l_evals, t_evals, hint);
        assert!(result.is_err(), "Expected error for d=0, but got Ok");
        match result {
            Err(SumcheckError::InvalidRoundPolynomial) => { /* Correct error */ }
            _ => panic!("Expected InvalidRoundPolynomial error for d=0, got {:?}", result),
        }
    }

    // Test case where l(1) = 0
    #[test]
    fn test_interpolate_product_poly_evals_l1_zero() {
         // t is linear (degree=1, d=1)
          // s is quadratic (s_degree=2)
        type F = BiniusTowerField;
        // l(X) = 1 - X -> l(0)=1, l(1)=0. l(inf) = l(1)-l(0) = -1
        let l_0 = F::one();
        let l_inf = F::new(u128::MAX, None);
        let l_evals = [l_0, l_inf];

        // t(X) = 5 + 4X (degree=1). Input [t(0), t(inf)], length d=1.
        let t_0 = F::new(5, None);
        let t_inf = F::new(4, None);
        let t_evals = &[t_0, t_inf];

        // s(X) = (1-X)(5+4X) = 5 - X - 4X^2
        let s_coeffs_exp = vec![F::new(5, None), F::new(u128::MAX, None), F::new(u128::MAX - 3, None)]; // 5, -1, -4
        let s_0_exp = evaluate_poly(&s_coeffs_exp, F::zero()); // 5
        let s_1_exp = evaluate_poly(&s_coeffs_exp, F::one()); // 5 - 1 - 4 = 0
        let s_2_exp = evaluate_poly(&s_coeffs_exp, F::new(2, None)); // 5 - 2 - 16 = -13
        let s_inf_exp = F::new(u128::MAX - 3, None); // -4

        let hint = s_0_exp + s_1_exp; // 5 + 0 = 5

        // Since l(1)=0, and the hint is consistent (s(1)=0), the function should return an error
        // because it cannot determine t(1) from the hint.
        let result = interpolate_product_poly_evals(&l_evals, t_evals, hint);
        assert!(result.is_err(), "Expected error for l(1)=0, but got Ok");
        match result {
            Err(SumcheckError::InvalidRoundPolynomial) => { /* Correct error */ }
            _ => panic!("Expected InvalidRoundPolynomial error for l(1)=0, got {:?}", result),
        }
    }

    // Test case where l(1) = 0 and hint is inconsistent
    #[test]
    fn test_interpolate_product_poly_evals_l1_zero_inconsistent() {
        type F = BiniusTowerField;
        let l_0 = F::one();
        let l_inf = F::new(u128::MAX, None);
        let l_evals = [l_0, l_inf];
        let t_0 = F::new(5, None);
        let t_inf = F::new(4, None);
        let t_evals = &[t_0, t_inf];
        let s_0_exp = F::new(5, None);
        let inconsistent_hint = s_0_exp + F::one();

        let result = interpolate_product_poly_evals(&l_evals, t_evals, inconsistent_hint);
        assert!(result.is_err());
        // Compare the error variant correctly
        match result {
            Err(SumcheckError::InvalidRoundPolynomial) => { /* Correct error */ }
            _ => panic!("Expected InvalidRoundPolynomial error, got {:?}", result),
        }
        // assert_eq!(result.err().unwrap(), SumcheckError::InvalidRoundPolynomial);
    }

} 