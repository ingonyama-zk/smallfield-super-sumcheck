use ark_std::fmt;

/// This is an error that could occur during serialization
#[derive(Debug)]
pub enum SumcheckError {
    /// Sumcheck proof is invalid, this could be because of invalid inputs/constants.
    InvalidProof,
    /// Round polynomial contains incorrect number of evaluations.
    InvalidRoundPolynomial,
    /// Sumcheck proof verification failure.
    ProofVerificationFailure,
}

impl ark_std::error::Error for SumcheckError {}

impl fmt::Display for SumcheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            SumcheckError::InvalidProof => write!(f, "the proof data is invalid, check the inputs"),
            SumcheckError::InvalidRoundPolynomial => {
                write!(f, "one of the round polynomial is invalid")
            }
            SumcheckError::ProofVerificationFailure => write!(f, "the proof verification failed,"),
        }
    }
}
