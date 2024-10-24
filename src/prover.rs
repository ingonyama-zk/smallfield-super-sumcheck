use crate::{
    btf_transcript::TFTranscriptProtocol, data_structures::LinearLagrangeList,
    tower_fields::TowerField, IPForMLSumcheck,
};
use ark_std::{log2, vec::Vec};
use merlin::Transcript;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

// A sumcheck proof contains all round polynomials
#[derive(PartialEq, Debug)]
pub struct SumcheckProof<EF: TowerField> {
    pub(crate) num_vars: usize,
    pub(crate) degree: usize,
    pub(crate) round_polynomials: Vec<Vec<EF>>,
}

#[derive(PartialEq, Clone, Debug)]
pub enum AlgorithmType {
    Naive,
    WitnessChallengeSeparation,
    Precomputation,
    ToomCook,
}

/// Prover State
/// EF stands for extension field and BF stands for base field
/// bb = base-field element multiplied to a base-field element
/// be = base-field element multiplied to an extension-field element
/// ee = extension-field element multiplied to an extension-field element
pub struct ProverState<EF: TowerField, BF: TowerField> {
    /// sampled randomness (for each round) given by the verifier
    pub randomness: Vec<EF>,
    /// Stores a list of multilinear extensions
    pub state_polynomials: Vec<LinearLagrangeList<BF>>,
    /// Number of variables
    pub num_vars: usize,
    /// Max number of multiplicands in a product
    pub max_multiplicands: usize,
    /// The current round number
    pub round: usize,
    /// Algorithm type for small field sumcheck
    pub algo: AlgorithmType,
}

impl<EF: TowerField, BF: TowerField> IPForMLSumcheck<EF, BF> {
    /// Initialise prover state from a given set of polynomials (in their evaluation form).
    /// The degree of the sumcheck round polynomial also needs to be input.
    pub fn prover_init(
        polynomials: &Vec<LinearLagrangeList<BF>>,
        sumcheck_poly_degree: usize,
        algorithm: AlgorithmType,
    ) -> ProverState<EF, BF> {
        // sanity check 1: no polynomials case must not be allowed.
        if polynomials.len() == 0 {
            panic!("Cannot prove empty input polynomials.")
        }

        // sanity check 2: all polynomial evaluations must be of the same size.
        let problem_size = polynomials[0].size;
        let _ = polynomials.iter().enumerate().map(|(i, poly)| {
            if poly.size != problem_size {
                panic!("Polynomial size mismatch at {}", i)
            }
        });

        // sanity check 3: size must be a power of two.
        if !problem_size.is_power_of_two() {
            panic!("Number of polynomial evaluations must be a power of two.")
        }

        let num_variables: usize = log2(2 * problem_size).try_into().unwrap();
        ProverState {
            randomness: Vec::with_capacity(num_variables),
            state_polynomials: polynomials.to_vec(),
            num_vars: num_variables,
            max_multiplicands: sumcheck_poly_degree,
            round: 0,
            algo: algorithm,
        }
    }

    ///
    /// Creates a sumcheck proof consisting of `n` round polynomials each of degree `d` using Algorithm 1.
    /// We allow for any function `combine_function` on a set of MLE polynomials.
    ///
    /// We implement four algorithms to compute the sumcheck proof according to the algorithms in the small-field
    /// sumcheck paper by Justin Thaler: https://people.cs.georgetown.edu/jthaler/small-sumcheck.pdf
    ///
    pub fn prove<EC, BC, T, BE, AEE, EE, BB>(
        prover_state: &mut ProverState<EF, BF>,
        ef_combine_function: &EC, // TODO: Using two combines is bad, templatize it?
        bf_combine_function: &BC,
        transcript: &mut Transcript,
        to_ef: &T,
        mult_be: &BE,
        add_ee: &AEE,
        mult_ee: &EE,
        mult_bb: &BB,
        round_t: Option<usize>,
        mappings: Option<&Vec<Box<dyn Fn(&BF, &BF) -> BF + Send + Sync>>>,
        projection_mapping_indices: Option<&Vec<usize>>,
        interpolation_maps_bf: Option<&Vec<Box<dyn Fn(&Vec<BF>) -> BF>>>,
        interpolation_maps_ef: Option<&Vec<Box<dyn Fn(&Vec<EF>) -> EF>>>,
    ) -> SumcheckProof<EF>
    where
        BC: Fn(&Vec<BF>) -> EF + Sync,
        EC: Fn(&Vec<EF>) -> EF + Sync,
        T: Fn(&BF) -> EF + Sync,
        BE: Fn(&BF, &EF) -> EF + Sync,
        AEE: Fn(&EF, &EF) -> EF + Sync,
        EE: Fn(&EF, &EF) -> EF + Sync,
        BB: Fn(&BF, &BF) -> BF + Sync,
    {
        // Initiate the transcript with the protocol name
        <Transcript as TFTranscriptProtocol<EF, BF>>::sumcheck_proof_domain_sep(
            transcript,
            prover_state.num_vars as u64,
            prover_state.max_multiplicands as u64,
        );

        // Declare r_polys and initialise it with 0s
        let r_degree = prover_state.max_multiplicands;
        let mut r_polys: Vec<Vec<EF>> = (0..prover_state.num_vars)
            .map(|_| vec![EF::zero(); r_degree + 1])
            .collect();

        // Extract threshold round
        let round_threshold = match round_t {
            Some(t_value) => {
                if (prover_state.algo == AlgorithmType::Precomputation)
                    || (prover_state.algo == AlgorithmType::ToomCook)
                {
                    assert!(t_value <= prover_state.num_vars);
                    t_value
                } else {
                    prover_state.num_vars
                }
            }
            None => prover_state.num_vars,
        };

        match prover_state.algo {
            AlgorithmType::Naive => Self::prove_with_naive_algorithm::<EC, BC, T>(
                prover_state,
                &ef_combine_function,
                &bf_combine_function,
                transcript,
                &mut r_polys,
                to_ef,
            ),
            AlgorithmType::WitnessChallengeSeparation => {
                Self::prove_with_witness_challenge_sep_agorithm::<BC, BE, AEE, EE>(
                    prover_state,
                    &bf_combine_function,
                    transcript,
                    &mut r_polys,
                    &mult_be,
                    &add_ee,
                    &mult_ee,
                )
            }
            AlgorithmType::Precomputation => {
                Self::prove_with_precomputation_agorithm::<BE, EE, BB, EC>(
                    prover_state,
                    transcript,
                    &mut r_polys,
                    round_threshold,
                    mult_be,
                    mult_ee,
                    mult_bb,
                    ef_combine_function,
                )
            }
            AlgorithmType::ToomCook => Self::prove_with_toom_cook_agorithm::<BE, EE, BB, EC>(
                prover_state,
                transcript,
                &mut r_polys,
                round_threshold,
                mult_be,
                mult_ee,
                mult_bb,
                mappings.unwrap(),
                projection_mapping_indices.unwrap(),
                interpolation_maps_bf.unwrap(),
                interpolation_maps_ef.unwrap(),
                ef_combine_function,
            ),
        }

        SumcheckProof {
            num_vars: prover_state.num_vars,
            degree: r_degree,
            round_polynomials: r_polys,
        }
    }
}
