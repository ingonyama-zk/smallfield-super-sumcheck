//! TFTranscript for the MLE sumcheck

use merlin::Transcript;

use crate::tower_fields::TowerField;

pub trait TFTranscriptProtocol<EF: TowerField, BF: TowerField> {
    /// Append a domain separator for sumcheck proof of with `num_vars` variables and degree `m` of combine function.
    fn sumcheck_proof_domain_sep(&mut self, num_vars: u64, m: u64);

    /// Append a `scalar` with the given `label`.
    fn append_scalar(&mut self, label: &'static [u8], scalar: &EF);

    /// Append multiple `scalars` with the given `label`.
    fn append_scalars(&mut self, label: &'static [u8], scalars: &[EF]);

    /// Compute a `label`ed challenge variable.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> EF;

    /// Compute a `label`ed vector of challenges.
    fn challenge_vector(&mut self, label: &'static [u8], len: usize) -> Vec<EF>;
}

impl<EF: TowerField, BF: TowerField> TFTranscriptProtocol<EF, BF> for Transcript {
    fn sumcheck_proof_domain_sep(&mut self, num_vars: u64, m: u64) {
        self.append_message(b"domain-separator", b"sumcheck v1");
        self.append_u64(b"n", num_vars);
        self.append_u64(b"m", m);
    }

    fn append_scalar(&mut self, label: &'static [u8], scalar: &EF) {
        let binding = scalar.bin();
        let buf = binding.as_bytes();
        self.append_message(label, &buf);
    }

    fn append_scalars(&mut self, label: &'static [u8], scalars: &[EF]) {
        self.append_message(label, b"begin_append_vector");
        for item in scalars.iter() {
            <Self as TFTranscriptProtocol<EF, BF>>::append_scalar(self, label, item);
        }
        self.append_message(label, b"end_append_vector");
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> EF {
        let mut buffer = vec![0u8; 16];
        self.challenge_bytes(label, &mut buffer);
        EF::new(
            u128::from_le_bytes(
                buffer
                    .try_into()
                    .expect("Expects a vector of length 16 to compute challenge."),
            ),
            Some(7),
        )
    }

    fn challenge_vector(&mut self, label: &'static [u8], len: usize) -> Vec<EF> {
        (0..len)
            .map(|_i| <Self as TFTranscriptProtocol<EF, BF>>::challenge_scalar(self, label))
            .collect::<Vec<EF>>()
    }
}
