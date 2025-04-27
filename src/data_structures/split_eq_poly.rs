use crate::{data_structures::eq_poly::EqPoly, tower_fields::TowerField};


/// A struct holding the equality polynomial evaluations for use in sum-check,
/// incorporating Gruen's optimization via cached evaluations.
///
/// For the `i = 0..n`-th round of sum-check (where rounds proceed from n-1 down to 0),
/// this struct maintains the evaluation `eq(w[i..], r[..i])` as `current_scalar`
/// and uses precomputed staged evaluations `E1` and `E2` corresponding to halves
/// of the initial `w` vector (excluding the last element).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SplitEqPoly<F: TowerField> {
    /// The index of the variable currently being bound (decrements from w.len() down to 0).
    pub(crate) current_index: usize,
    /// The evaluation of the EQ polynomial for the variables already bound.
    /// Starts at 1 and accumulates eq(w[i], r_i) for i from n-1 down to current_index.
    pub(crate) current_scalar: F,
    /// The original challenge vector `w`. Stored for calculating `eq(w[i], r_i)` during binding.
    pub(crate) w: Vec<F>,
    /// Cached evaluations for the second half of `w` (excluding the last element).
    /// `E1[k]` contains evaluations of `eq(w1[..=k], x)`
    pub(crate) e1: Vec<Vec<F>>,
    /// Cached evaluations for the first half of `w`.
    /// `E2[k]` contains evaluations of `eq(w2[..=k], x)`
    pub(crate) e2: Vec<Vec<F>>,
}

impl<F: TowerField> SplitEqPoly<F> {
    /// Creates a new `SplitEqPoly` instance from the challenge vector `w`.
    ///
    /// Precomputes the cached EQ evaluations for the two halves of `w`
    /// (excluding the last element) in parallel.
    pub fn new(w: Vec<F>) -> Self {
        let n = w.len();
        assert!(n > 0, "Input vector w cannot be empty");

        let e1;
        let e2;

        if n == 1 {
            // Base case: w has only one element. E1 and E2 correspond to empty inputs.
            // compute_staged_evals should ideally handle empty vec and return vec![vec![F::one()]].
            // Assuming EqPoly::new(vec![]) is valid and compute_staged_evals works.
            // If not, EqPoly needs adjustment. For now, we assume it returns the base case [[1]].
             let eq_poly_empty = EqPoly::new(vec![]);
             // We need two separate base cases as rayon::join expects two closures.
             e1 = eq_poly_empty.compute_staged_evals(false);
             e2 = eq_poly_empty.compute_staged_evals(false);

             // Check if the base case is as expected. If EqPoly returns empty vec for empty input, use this:
             // e1 = vec![vec![F::one()]];
             // e2 = vec![vec![F::one()]];

        } else {
            // Split w into w2 (first m elements), w1 (next elements), and w_last (last element)
            let (_, wprime) = w.split_last().unwrap(); // wprime = w[0..n-1]
            let m = n / 2; // Split point used in the original code
            let (w2_slice, w1_slice) = wprime.split_at(m);

            let eq_poly_w2 = EqPoly::new(w2_slice.to_vec());
            let eq_poly_w1 = EqPoly::new(w1_slice.to_vec());

            // Compute staged evaluations in parallel. Use big-endian (false).
             (e2, e1) = rayon::join(
                 || eq_poly_w2.compute_staged_evals(false),
                 || eq_poly_w1.compute_staged_evals(false),
             );
        }

         Self {
            current_index: n,
            current_scalar: F::one(),
            w: w.to_vec(),
            e1,
            e2,
        }
    }

    /// Returns the total number of variables (length of the original `w`).
    pub fn get_num_vars(&self) -> usize {
        self.w.len()
    }

    /// Returns the number of evaluations in the current (last) vector of E1.
    pub fn e1_len(&self) -> usize {
        self.e1.last().map_or(0, |v| v.len())
    }

    /// Returns the number of evaluations in the current (last) vector of E2.
    pub fn e2_len(&self) -> usize {
        self.e2.last().map_or(0, |v| v.len())
    }

    /// Returns a slice to the current (last) evaluation vector of E1.
    pub fn e1_current(&self) -> &[F] {
        self.e1.last().map_or(&[], |v| v.as_slice())
    }

    /// Returns a slice to the current (last) evaluation vector of E2.
    pub fn e2_current(&self) -> &[F] {
         self.e2.last().map_or(&[], |v| v.as_slice())
    }

    /// Binds the next variable (at `current_index - 1`) to the challenge `r`.
    ///
    /// Updates `current_scalar` and pops the corresponding cached evaluation vector
    /// from `E1` or `E2`.
    pub fn bind(&mut self, r: F) {
        assert!(self.current_index > 0, "Cannot bind further");

        let current_w_index = self.current_index - 1;
        let wi = self.w[current_w_index];

        // Update scalar: current_scalar *= eq(wi, r) = wi * r + (1-wi)*(1-r)
        let eq_val = wi * r + (F::one() - wi) * (F::one() - r);
        self.current_scalar *= eq_val;

        // Determine which cache (E1 or E2) corresponds to the bound variable
        // and pop the last evaluation vector from it.
        let n = self.w.len();
        let m = n / 2; // Integer division, split point for wprime

        // Indices n-1 down to m correspond to w_last and w1 (handled by E1)
        // Indices m-1 down to 0 correspond to w2 (handled by E2)
        if current_w_index >= m {
            // Corresponds to w_last or w1. Pop from E1's cache if it's not the base case.
            // The base case E1 = [[1]] should not be popped.
            if self.e1.len() > 1 {
                 self.e1.pop();
            }
        } else {
            // Corresponds to w2. Pop from E2's cache if it's not the base case.
            if self.e2.len() > 1 {
                 self.e2.pop();
            }
        }

        // Decrement index for the next round
        self.current_index -= 1;
    }

     // TODO: Add tests similar to the original file if possible.
     // This might require a `DensePolynomial` equivalent or an `evaluate` method.
     // For now, skipping the `merge` and `test` functions.
}


#[cfg(test)]
mod tests {
     use super::*;
     use crate::tower_fields::binius::BiniusTowerField;
     use num::One;

     // Define a field for testing, e.g., BiniusTowerField
     type F = BiniusTowerField;

     // Basic test to check creation and binding sanity
     #[test]
     fn test_split_eq_poly_creation_and_bind() {
         // Test case 1: n = 1
         let w1 = vec![F::new(2, Some(2))];
         let mut split_eq1 = SplitEqPoly::new(w1.clone());
         assert_eq!(split_eq1.get_num_vars(), 1);
         assert_eq!(split_eq1.current_index, 1);
         assert_eq!(split_eq1.e1.len(), 1); // Should be [[1]]
         assert_eq!(split_eq1.e2.len(), 1); // Should be [[1]]
         assert_eq!(split_eq1.e1_current(), &[F::one()]);
         assert_eq!(split_eq1.e2_current(), &[F::one()]);

         let r1 = F::new(5, Some(2));
         split_eq1.bind(r1);
         assert_eq!(split_eq1.current_index, 0);
         let expected_scalar1 = w1[0] * r1 + (F::one() - w1[0]) * (F::one() - r1);
         assert_eq!(split_eq1.current_scalar, expected_scalar1);
         // Caches should remain [[1]] after binding the only variable
         assert_eq!(split_eq1.e1.len(), 1);
         assert_eq!(split_eq1.e2.len(), 1);


         // Test case 2: n = 4. w = [w0, w1, w2, w3]. m=2.
         // wprime = [w0, w1, w2]. w2_slice = [w0, w1], w1_slice = [w2].
         let w4 = vec![F::new(2,Some(2)), F::new(3,Some(2)), F::new(4,Some(2)), F::new(5,Some(2))];
         let mut split_eq4 = SplitEqPoly::new(w4.clone());
         assert_eq!(split_eq4.get_num_vars(), 4);
         assert_eq!(split_eq4.current_index, 4);

         // E2 = evals_cached([w0, w1]) -> len 3. [[1], [1-w0, w0], [ (1-w0)(1-w1), w0(1-w1), (1-w0)w1, w0w1 ]]
         // E1 = evals_cached([w2]) -> len 2. [[1], [1-w2, w2]]
         assert_eq!(split_eq4.e2.len(), 3); // Length of w2_slice + 1
         assert_eq!(split_eq4.e1.len(), 2); // Length of w1_slice + 1

         assert_eq!(split_eq4.e2_len(), 4); // 2^(len(w2_slice))
         assert_eq!(split_eq4.e1_len(), 2); // 2^(len(w1_slice))

         // Bind w[3] = w_last
         let r3 = F::new(6, Some(2));
         split_eq4.bind(r3); // current_index = 3. w_index = 3 >= m=2. Pop E1.
         assert_eq!(split_eq4.current_index, 3);
         assert_eq!(split_eq4.e1.len(), 1); // Popped [1-w2, w2]
         assert_eq!(split_eq4.e1_current(), &[F::one()]); // Remaining base case
         assert_eq!(split_eq4.e2.len(), 3); // E2 unchanged

         let scalar3 = w4[3] * r3 + (F::one() - w4[3]) * (F::one() - r3);
         assert_eq!(split_eq4.current_scalar, scalar3);

         // Bind w[2] = w1_slice[0]
         let r2 = F::new(7, Some(2));
         split_eq4.bind(r2); // current_index = 2. w_index = 2 >= m=2. Try Pop E1.
         assert_eq!(split_eq4.current_index, 2);
         assert_eq!(split_eq4.e1.len(), 1); // Already at base case [[1]], no pop.
         assert_eq!(split_eq4.e2.len(), 3); // E2 unchanged

         let scalar2 = scalar3 * (w4[2] * r2 + (F::one() - w4[2]) * (F::one() - r2));
         assert_eq!(split_eq4.current_scalar, scalar2);

         // Bind w[1] = w2_slice[1]
         let r1 = F::new(8, Some(2));
         split_eq4.bind(r1); // current_index = 1. w_index = 1 < m=2. Pop E2.
         assert_eq!(split_eq4.current_index, 1);
         assert_eq!(split_eq4.e1.len(), 1); // E1 unchanged
         assert_eq!(split_eq4.e2.len(), 2); // Popped E2's last vec

         let scalar1 = scalar2 * (w4[1] * r1 + (F::one() - w4[1]) * (F::one() - r1));
         assert_eq!(split_eq4.current_scalar, scalar1);

         // Bind w[0] = w2_slice[0]
         let r0 = F::new(9, Some(2));
         split_eq4.bind(r0); // current_index = 0. w_index = 0 < m=2. Pop E2.
         assert_eq!(split_eq4.current_index, 0);
         assert_eq!(split_eq4.e1.len(), 1); // E1 unchanged
         assert_eq!(split_eq4.e2.len(), 1); // Popped E2's last vec

         let scalar0 = scalar1 * (w4[0] * r0 + (F::one() - w4[0]) * (F::one() - r0));
         assert_eq!(split_eq4.current_scalar, scalar0);

         // Optional: Compare final scalar with direct EQ evaluation if needed
         // let final_eval = EqPoly::new(w4).evaluate(&[r0, r1, r2, r3]); // Need evaluate method on EqPoly
         // assert_eq!(split_eq4.current_scalar, final_eval);
     }

     // Test to ensure E1/E2 base cases are handled.
      #[test]
     fn test_split_eq_poly_edge_cases() {
          // n=2. w=[w0, w1]. m=1. wprime=[w0]. w2_slice=[w0], w1_slice=[].
          let w2 = vec![F::new(2,Some(2)), F::new(3,Some(2))];
          let mut split_eq2 = SplitEqPoly::new(w2.clone());
          assert_eq!(split_eq2.get_num_vars(), 2);
          // E2 = evals_cached([w0]) -> [[1], [1-w0, w0]] -> len 2
          // E1 = evals_cached([]) -> [[1]] -> len 1
          assert_eq!(split_eq2.e2.len(), 2);
          assert_eq!(split_eq2.e1.len(), 1);

          // Bind w[1] (w_last)
          let r1 = F::new(5, Some(2));
          split_eq2.bind(r1); // index=1. w_idx=1 >= m=1. Try Pop E1.
          assert_eq!(split_eq2.current_index, 1);
          assert_eq!(split_eq2.e1.len(), 1); // No pop, was base case.
          assert_eq!(split_eq2.e2.len(), 2);

           // Bind w[0] (w2_slice[0])
          let r0 = F::new(6, Some(2));
          split_eq2.bind(r0); // index=0. w_idx=0 < m=1. Pop E2.
          assert_eq!(split_eq2.current_index, 0);
          assert_eq!(split_eq2.e1.len(), 1);
          assert_eq!(split_eq2.e2.len(), 1); // Popped.
     }
} 