use crate::{tower_fields::TowerField, utils::error::SumcheckError};

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

/// Computes the evaluations of a product polynomial s(X) = l(X) * t(X) at specific points.
///
/// Given:
/// - l(X): A linear polynomial, provided as evaluations `[l(0), l(∞)]`.
/// - t(X): A polynomial of degree `d`, provided as evaluations `[t(0), t(∞), t(2), ..., t(d-1)]`.
/// - hint: The value `T = s(0) + s(1)`.
///
/// Computes and returns the evaluations of s(X) in the format `[s(0), s(∞), s(2), ..., s(d)]`.
/// The degree of s(X) is `d + 1`.
///
pub fn interpolate_product_poly_evals<F: TowerField>(
    linear_evals: &[F; 2],
    t_evals: &[F],
    hint: F,
) -> Result<Vec<F>, SumcheckError> {
    let d = t_evals.len(); // Length of input evals, indicates degree d

    // Handle t(X) degree 0 case (constant)
    if d == 0 {
        // If t is constant (degree 0), t_evals should be [t(0)=t(inf)]. s(X) is linear.
        if t_evals.len() != 1 {
            return Err(SumcheckError::InvalidRoundPolynomial);
        }
        let l_0 = linear_evals[0];
        let l_inf = linear_evals[1];
        let t_0 = t_evals[0];

        let s_0 = l_0 * t_0;
        // s(inf) is leading coeff of (l0+l_inf*X)*t0 = l_inf*t0*X + l0*t0
        let s_inf = l_inf * t_0;

        // Check hint: s(0) + s(1) = s(0) + (l(1)*t(1)) = s(0) + (l0+l_inf)*t0 = hint
        // s(0) + (l0+l_inf)*t0 = l0*t0 + l0*t0 + l_inf*t0 = l_inf*t0
        let l_1 = l_0 + l_inf;
        let s_1 = l_1 * t_0; // Since t(1) = t(0)
        if s_0 + s_1 != hint {
            return Err(SumcheckError::InvalidRoundPolynomial);
        }

        // Output for degree 1: [s(0), s(inf)]
        return Ok(vec![s_0, s_inf]);
    }

    // Handle t(X) degree 1 case (linear)
    if d == 1 {
        if linear_evals.len() != 2 {
            return Err(SumcheckError::InvalidRoundPolynomial);
        }
        let l_0 = linear_evals[0];
        let l_inf = linear_evals[1];
        let t_0 = t_evals[0]; // Input is [t(0)]

        // Calculate l(1)
        let l_1 = l_0 + l_inf;

        // Calculate t(1) using hint: l(0)t(0) + l(1)t(1) = hint
        let s_0 = l_0 * t_0;
        let term_l1_t1 = hint - s_0;

        let t_1 = if l_1.is_zero() {
            // If l(1) is 0, hint must equal s(0).
            if !term_l1_t1.is_zero() {
                return Err(SumcheckError::InvalidRoundPolynomial);
            }
            // If l(1)=0 and hint=s(0), t(1) could be anything based on this equation alone.
            // However, for a linear t(X)=t0 + t_inf*X, t(1) must be t0+t_inf.
            // We cannot determine t_inf without t(1). This seems ill-defined for linear t.
            // Let's assume the caller ensures l(1) is non-zero for d=1 case or the hint is consistent.
            // If l(1) is zero, then l(X) = l0 - l0*X. It evaluates to 0 at X=1.
            // If the hint requires s(0)+s(1)=s(0), it means s(1)=0. s(1)=l(1)*t(1)=0*t(1)=0.
            // This holds for any t(1). We can't determine t(1) uniquely.
            // For now, return error if l(1) is zero in d=1 case, needs clarification.
            return Err(SumcheckError::InvalidRoundPolynomial); // Cannot determine t(1) uniquely
        } else {
            // Calculate t(1) = (hint - s(0)) / l(1)
            term_l1_t1 * l_1.inverse().expect("l(1) should be invertible")
        };

        // Calculate t(inf) = t(1) - t(0)
        let t_inf = t_1 - t_0;

        // Calculate s(inf) = l(inf) * t(inf)
        let s_inf = l_inf * t_inf;

        // Output for d=1 is [s(0), s(inf)], length d+1=2
        return Ok(vec![s_0, s_inf]);
    }

    // Check input lengths
    if linear_evals.len() != 2 {
        return Err(SumcheckError::InvalidRoundPolynomial);
    }
    // t_evals = [t(0), t(inf), t(2), ..., t(d-1)], length is d
    if t_evals.len() != d {
        // This case should ideally not happen if d is derived from t_evals.len()
         return Err(SumcheckError::InvalidRoundPolynomial);
    }

    let l_0 = linear_evals[0];
    let l_inf = linear_evals[1];
    let t_0 = t_evals[0];
    let t_inf = t_evals[1]; // Leading coefficient of t(X)

    // Calculate l(1)
    let l_1 = l_0 + l_inf;

    // Calculate t(1) using the hint: s(0) + s(1) = hint => l(0)t(0) + l(1)t(1) = hint
    let s_0 = l_0 * t_0;
    let term_l1_t1 = hint - s_0;

    let t_1 = if l_1.is_zero() {
        // If l(1) is 0, then hint must equal s(0) for a solution to exist.
        if !term_l1_t1.is_zero() {
            return Err(SumcheckError::InvalidRoundPolynomial);
        }
        // If l(1)=0 and hint=s(0), t(1) can be anything. We need to interpolate t(X)
        // using points {0, 2, ..., d-1} and t(inf) to find t(1).
        // Let's construct the points for standard interpolation excluding t(1).
        let mut t_evals_for_t1_interp = vec![t_0];
        if d > 2 {
             t_evals_for_t1_interp.extend_from_slice(&t_evals[2..]);
        }
        let point_1 = F::new(1, None);
        barycentric_interpolation_with_infinity(&t_evals_for_t1_interp, t_inf, point_1)
    } else {
        // Calculate t(1) = (hint - s(0)) / l(1)
        // TODO: Handle potential error instead of unwrap
        term_l1_t1 * l_1.inverse().expect("l(1) should be invertible")
    };

    // Prepare evaluations for interpolating t(X): [t(0), t(1), t(2), ..., t(d-1)]
    let mut t_evals_0_to_d_minus_1 = Vec::with_capacity(d);
    t_evals_0_to_d_minus_1.push(t_0); // t(0)
    t_evals_0_to_d_minus_1.push(t_1); // t(1)
    if d > 2 {
        // Add t(2)...t(d-1) from indices 2.. onwards in the input t_evals
        t_evals_0_to_d_minus_1.extend_from_slice(&t_evals[2..]);
    }

    // Calculate t(d) using interpolation with infinity
    let point_d = F::new(d as u128, None);
    let t_d = barycentric_interpolation_with_infinity(&t_evals_0_to_d_minus_1, t_inf, point_d);

    // We now have t(0), t(1), ..., t(d), and t(inf).
    // We also have l(0) and l(inf).

    // Calculate required evaluations of l(X): l(0), l(2), ..., l(d), l(inf)
    let mut l_evals_needed = Vec::with_capacity(d + 1);
    l_evals_needed.push(l_0); // l(0)
    l_evals_needed.push(l_inf); // l(inf)
    let mut current_l_eval = l_1; // Start from l(1) to compute l(2)
    for _ in 2..=d {
        current_l_eval += l_inf; // l(u) = l(u-1) + l(inf)
        l_evals_needed.push(current_l_eval);
    }
    // l_evals_needed now contains [l(0), l(inf), l(2), l(3), ..., l(d)]

    // Calculate required evaluations of t(X): t(0), t(2), ..., t(d), t(inf)
    let mut t_evals_needed = Vec::with_capacity(d + 1);
    t_evals_needed.push(t_0); // t(0)
    t_evals_needed.push(t_inf); // t(inf)
    if d > 2 {
         t_evals_needed.extend_from_slice(&t_evals[2..]); // t(2)...t(d-1)
    }
     if d >= 2 { // Need t(d) if d>=2
         t_evals_needed.push(t_d);
     }
    // t_evals_needed now contains [t(0), t(inf), t(2), ..., t(d)] (potentially missing t(2)..t(d-1) if d<3)
    // Let's re-structure t_evals_needed properly
    let mut t_evals_for_product = Vec::with_capacity(d + 1);
    t_evals_for_product.push(t_0); // t(0)
    t_evals_for_product.push(t_inf); // t(inf)
    if d > 2 {
        t_evals_for_product.extend_from_slice(&t_evals[2..]); // t(2..d-1)
    }
    if d >= 2 {
        t_evals_for_product.push(t_d); // t(d)
    }
    // Correct order: [t(0), t(inf), t(2), ..., t(d)]

    // Calculate the output evaluations s(X): [s(0), s(inf), s(2), ..., s(d)]
    // Degree of s is d+1
    let mut s_evals = Vec::with_capacity(d + 1);

    // s(0) = l(0) * t(0)
    s_evals.push(s_0);

    // s(inf) = l(inf) * t(inf) (leading coefficient of s)
    let s_inf = l_inf * t_inf;
    s_evals.push(s_inf);

    // s(u) = l(u) * t(u) for u = 2..d
    let mut current_l_val = l_1; // l(1)
    for u_idx in 2..=d {
        current_l_val += l_inf; // l(u) = l(u-1) + l_inf
        let t_u = if u_idx == d {
            t_d
        } else {
            // u_idx corresponds to index u_idx in t_evals (which starts [t(0), t(inf), t(2)...]
            t_evals[u_idx]
        };
        s_evals.push(current_l_val * t_u);
    }

    // s_evals should now be [s(0), s(inf), s(2), ..., s(d)]
    Ok(s_evals)
}

#[cfg(test)]
mod test {
    use num::Zero;

    use crate::tower_fields::{binius::BiniusTowerField, TowerField};
    use crate::utils::polynomial_interpolation::{
        barycentric_interpolation, batch_inversion_and_multiply, barycentric_interpolation_with_infinity, interpolate_product_poly_evals
    };

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
        // Test case from the original user-provided code (d=2)
        // s(X) = l(X) * t(X), l is linear, t is quadratic (d=2)
        // s(X) = (a + bX) * (c + dX + eX^2) = ac + (ad + bc)X + (ae + bd)X^2 + beX^3
        type F = BiniusTowerField;

        let a = F::new(3, None); // l(0)
        let b = F::new(2, None); // l(inf)
        let c = F::new(5, None); // t(0)
        let d = F::new(7, None); // t(1) coeff (missing from input)
        let e = F::new(4, None); // t(inf)

        let l_evals = [a, b];
        let t_evals_input = vec![c, e]; // Input: [t(0), t(inf)] (d=2)
        let degree_t = t_evals_input.len();

        // Calculate hint: s(0) + s(1)
        let s_0 = a * c;
        let l_1 = a + b;
        let t_1 = c + d + e; // t(1) = t(0) + t_lin_coeff + t(inf)
        let s_1 = l_1 * t_1;
        let hint = s_0 + s_1;

        // Call the function
        let result = interpolate_product_poly_evals(&l_evals, &t_evals_input, hint);
        assert!(result.is_ok());
        let s_evals_output = result.unwrap();

        // Expected output: [s(0), s(inf), s(2)] (degree d+1 = 3)
        let expected_s_0 = a * c;
        let expected_s_inf = b * e;
        let l_2 = l_1 + b; // l(2) = l(1) + l(inf)
        let t_2 = evaluate(&[c, d, e], &F::new(2, None)); // t(2)
        let expected_s_2 = l_2 * t_2;

        assert_eq!(s_evals_output.len(), degree_t + 1);
        assert_eq!(s_evals_output[0], expected_s_0, "s(0) mismatch");
        assert_eq!(s_evals_output[1], expected_s_inf, "s(inf) mismatch");
        assert_eq!(s_evals_output[2], expected_s_2, "s(2) mismatch");
    }

     #[test]
    fn test_interpolate_product_poly_evals_cubic_t() {
        // t is cubic (d=3), s is quartic (d+1=4)
        type F = BiniusTowerField;

        let l_coeffs = [F::rand(Some(2)), F::rand(Some(2))]; // [l(0), l(inf)]
        let t_coeffs = [F::rand(Some(2)), F::rand(Some(2)), F::rand(Some(2)), F::rand(Some(2))]; // [t0, t1, t2, t3=tinf]
        let degree_t = 3;

        let t_0 = t_coeffs[0];
        let t_inf = t_coeffs[degree_t]; // Coeff of X^3
        let t_2 = evaluate(&t_coeffs, &F::new(2, None));
        // Input format [t(0), t(inf), t(2)] for d=3
        let t_evals_input = vec![t_0, t_inf, t_2];

        // Calculate hint s(0) + s(1)
        let l_0 = l_coeffs[0];
        let l_inf = l_coeffs[1];
        let s_0 = l_0 * t_0;
        let l_1 = l_0 + l_inf;
        let t_1 = evaluate(&t_coeffs, &F::new(1, None));
        let s_1 = l_1 * t_1;
        let hint = s_0 + s_1;

        let result = interpolate_product_poly_evals(&l_coeffs, &t_evals_input, hint);
        assert!(result.is_ok());
        let s_evals_output = result.unwrap();

        // Expected output: [s(0), s(inf), s(2), s(3)] (degree 4)
        // Calculate expected values directly using polynomial definitions
        let l0 = l_coeffs[0];
        let li = l_coeffs[1];
        let l1 = l0 + li;
        let l2 = l1 + li;
        let l3 = l2 + li;

        let t0 = t_coeffs[0];
        // Need t(1), t(2), t(3) evaluated correctly
        let point1 = F::new(1, None);
        let point2 = F::new(2, None);
        let point3 = F::new(3, None);
        let _ = evaluate(&t_coeffs, &point1);
        let t2_calc = evaluate(&t_coeffs, &point2); // t(2) used in input was calculated this way
        let t3 = evaluate(&t_coeffs, &point3);
        let t_inf_calc = t_coeffs[degree_t]; // Leading coefficient t3

        // Double check input t(2) matches calculated t(2)
        assert_eq!(t_evals_input[2], t2_calc, "Input t(2) calculation mismatch in test");

        let expected_s_0 = l0 * t0;
        let expected_s_inf = li * t_inf_calc; // s(inf) = l(inf) * t(inf)
        let expected_s_2 = l2 * t2_calc; // s(2) = l(2) * t(2)
        let expected_s_3 = l3 * t3;     // s(3) = l(3) * t(3)

        assert_eq!(s_evals_output.len(), degree_t + 1, "Output length mismatch");
        assert_eq!(s_evals_output[0], expected_s_0, "s(0) mismatch");
        assert_eq!(s_evals_output[1], expected_s_inf, "s(inf) mismatch");
        assert_eq!(s_evals_output[2], expected_s_2, "s(2) mismatch");
        assert_eq!(s_evals_output[3], expected_s_3, "s(3) mismatch");
    }

     #[test]
    fn test_interpolate_product_poly_evals_linear_t() {
        // t is linear (d=1), s is quadratic (d+1=2)
        type F = BiniusTowerField;

        let l_coeffs = [F::rand(Some(2)), F::rand(Some(2))]; // [l(0), l(inf)]
        // Define t(X) = t0 + t1*X
        let t_coeffs = [F::rand(Some(2)), F::rand(Some(2))]; // [t0, t1]
        let degree_t = 1;

        let t_0 = t_coeffs[0];
        let t_1_coeff = t_coeffs[1]; // Coefficient of X is t(inf) for linear
        // Input format [t(0)] for d=1
        let t_evals_input = vec![t_0];

        // Calculate hint s(0) + s(1)
        let l_0 = l_coeffs[0];
        let l_inf = l_coeffs[1];
        let s_0 = l_0 * t_0;
        let l_1 = l_0 + l_inf;
        // Calculate t(1) directly: t(1) = t0 + t1
        let t_1_eval = t_coeffs[0] + t_coeffs[1];
        let s_1 = l_1 * t_1_eval;
        let hint = s_0 + s_1;

        // Ensure l(1) is not zero for this test case, otherwise hint logic is ambiguous
        if l_1.is_zero() {
            println!("Skipping test_interpolate_product_poly_evals_linear_t because l(1) is zero");
            return;
        }

        let result = interpolate_product_poly_evals(&l_coeffs, &t_evals_input, hint);
        assert!(result.is_ok(), "Function returned error: {:?}", result.err());
        let s_evals_output = result.unwrap();

        // Expected output: [s(0), s(inf)] (degree d+1 = 2)
        let expected_s_0 = l_0 * t_0;
        let t_inf_calc = t_1_coeff; // t(inf) is the coefficient of X for linear
        let expected_s_inf = l_inf * t_inf_calc;

        assert_eq!(s_evals_output.len(), degree_t + 1, "Output length mismatch"); // Expect length 2
        assert_eq!(s_evals_output[0], expected_s_0, "s(0) mismatch");
        assert_eq!(s_evals_output[1], expected_s_inf, "s(inf) mismatch");
    }


} 