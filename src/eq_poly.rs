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
    /// Lemma 1 from the paper: https://eprint.iacr.org/2025/105.pdf
    /// This function requires 2m multiplications
    ///
    pub fn compute_evals(&self) -> Vec<F> {
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

            staged_evals.push(
                // concatenate the two vectors
                current_evals_at_0
                    .into_iter()
                    .chain(current_evals_at_1)
                    .collect(),
            );
        }

        staged_evals.last().unwrap().to_vec()
    }

    pub fn to_linear_lagrange_list(&self) -> LinearLagrangeList<F> {
        LinearLagrangeList::from_vector(&self.compute_evals())
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
        let evals = eq_poly.compute_evals();

        let pairs = basis
            .iter()
            .map(|&x| vec![F::one() - x, x])
            .collect::<Vec<Vec<F>>>();

        assert_eq!(evals.len(), 1 << basis.len());
        for index in 0..evals.len() {
            let mut res_index = F::one();
            for i in 0..basis.len() {
                res_index *= pairs[i][(index >> i) & 1];
            }
            assert_eq!(res_index, evals[index]);
        }
    }
}
