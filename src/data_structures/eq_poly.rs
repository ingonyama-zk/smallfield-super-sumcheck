use crate::{data_structures::LinearLagrangeList, tower_fields::TowerField};

#[derive(Clone, PartialEq, Eq)]
pub struct EqPoly<F: TowerField> {
    pub basis: Vec<F>,
    pub log_size: usize,
}

impl<F: TowerField> EqPoly<F> {
    pub fn new(basis: Vec<F>) -> Self {
        let log_size = basis.len();
        Self { basis, log_size }
    }

    /// Compute the evaluations of the polynomial at the powers of the basis
    /// Suppose the basis is [a, b, c], then the evaluations are:
    /// Stage 1    Stage 2                Stage 3
    /// [1 - a]    [1 - a] * [1 - b]      [1 - a] * [1 - b] * [1 - c]
    /// [a]        [1 - a] * [b]          [1 - a] * [1 - b] * [c]
    ///            [a] * [1 - b]          [1 - a] * [b] * [1 - c]
    ///            [a] * [b]              [1 - a] * [b] * [c]
    ///                                   [a] * [1 - b] * [1 - c]
    ///                                   [a] * [1 - b] * [c]
    ///                                   [a] * [b] * [1 - c]
    ///                                   [a] * [b] * [c]
    ///
    /// If the variable is_little_endian true, then the evaluations are:
    /// Stage 1    Stage 2                Stage 3
    /// [1 - a]    [1 - b] * [1 - a]      [1 - c] * [1 - b] * [1 - a]
    /// [a]        [1 - b] * [a]          [1 - c] * [1 - b] * [a]
    ///            [b] * [1 - a]          [1 - c] * [b] * [1 - a]
    ///            [b] * [a]              [1 - c] * [b] * [a]
    ///                                   [c] * [1 - b] * [1 - a]
    ///                                   [c] * [1 - b] * [a]
    ///                                   [c] * [b] * [1 - a]
    ///                                   [c] * [b] * [a]
    ///
    pub fn compute_staged_evals(&self, is_little_endian: bool) -> Vec<Vec<F>> {
        assert!(self.basis.len() == self.log_size);
        assert!(self.basis.len() > 0);
        let mut staged_evals = Vec::with_capacity(self.log_size);
        staged_evals.push(vec![F::one() - self.basis[0], self.basis[0]]);

        for i in 1..self.log_size {
            let current_basis_value = self.basis[i];

            assert_eq!(staged_evals.len(), i);
            assert_eq!(staged_evals[i - 1].len(), 1 << i);
            let current_evals_at_1: Vec<F> = staged_evals[i - 1]
                .iter()
                .map(|&x| x * current_basis_value)
                .collect();

            let current_evals_at_0: Vec<F> = staged_evals[i - 1]
                .iter()
                .zip(&current_evals_at_1)
                .map(|(&x, &y)| x - y)
                .collect();

            // Initialize the next inner vector in staged_evals
            staged_evals.push(Vec::with_capacity(2 * staged_evals[i - 1].len()));

            if is_little_endian {
                for l in current_evals_at_0.iter() {
                    staged_evals[i].push(*l);
                }
                for r in current_evals_at_1.iter() {
                    staged_evals[i].push(*r);
                }
            } else {
                for (l, r) in current_evals_at_0.iter().zip(current_evals_at_1.iter()) {
                    staged_evals[i].push(*l);
                    staged_evals[i].push(*r);
                }
            }
        }
        staged_evals
    }

    /// Compute the evaluations of the polynomial at the powers of the basis
    /// Lemma 1 from the paper: https://eprint.iacr.org/2025/105.pdf
    /// This function requires 2m multiplications
    ///
    pub fn compute_evals(&self, is_little_endian: bool) -> Vec<F> {
        self.compute_staged_evals(is_little_endian)
            .last()
            .unwrap()
            .to_vec()
    }

    pub fn evaluate_at_variable(&self, variable_index: usize, value: F) -> Self {
        let mut new_basis = self.basis.clone();
        new_basis[variable_index] = value;
        Self::new(new_basis)
    }

    pub fn to_linear_lagrange_list(&self) -> LinearLagrangeList<F> {
        LinearLagrangeList::from_vector(&self.compute_evals(false))
    }
}

// Write tests for equality polynomial
#[cfg(test)]
mod tests {
    use super::*;
    use crate::tower_fields::binius::BiniusTowerField as F;
    use num::One;

    #[test]
    fn test_eq_poly() {
        let basis = vec![F::new(2, Some(2)), F::new(3, Some(2)), F::new(4, Some(2))];
        let eq_poly = EqPoly::new(basis.clone());
        let evals = eq_poly.compute_evals(false);
        let evals_big_endian = eq_poly.compute_evals(true);

        let big_endian_pairs = basis
            .iter()
            .rev()
            .map(|&x| vec![F::one() - x, x])
            .collect::<Vec<Vec<F>>>();

        let little_endian_pairs = basis
            .iter()
            .map(|&x| vec![F::one() - x, x])
            .collect::<Vec<Vec<F>>>();

        assert_eq!(evals.len(), 1 << basis.len());
        assert_eq!(evals_big_endian.len(), 1 << basis.len());
        for index in 0..evals.len() {
            let mut res_index = F::one();
            let mut res_index_big_endian = F::one();
            for i in 0..basis.len() {
                res_index *= big_endian_pairs[i][(index >> i) & 1];
                res_index_big_endian *= little_endian_pairs[i][(index >> i) & 1];
            }
            assert_eq!(res_index, evals[index]);
            assert_eq!(res_index_big_endian, evals_big_endian[index]);
        }
    }
}
