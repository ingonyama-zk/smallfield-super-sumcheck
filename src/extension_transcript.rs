//! ExtensionTranscript for the MLE sumcheck

use ark_ff::{Field, PrimeField};
use merlin::Transcript;

pub trait ExtensionTranscriptProtocol<EF: Field, BF: PrimeField> {
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

impl<EF: Field, BF: PrimeField> ExtensionTranscriptProtocol<EF, BF> for Transcript {
    fn sumcheck_proof_domain_sep(&mut self, num_vars: u64, m: u64) {
        self.append_message(b"domain-separator", b"sumcheck v1");
        self.append_u64(b"n", num_vars);
        self.append_u64(b"m", m);
    }

    fn append_scalar(&mut self, label: &'static [u8], scalar: &EF) {
        let mut buf = vec![];
        scalar.serialize_compressed(&mut buf).unwrap();
        self.append_message(label, &buf);
    }

    fn append_scalars(&mut self, label: &'static [u8], scalars: &[EF]) {
        self.append_message(label, b"begin_append_vector");
        for item in scalars.iter() {
            <Self as ExtensionTranscriptProtocol<EF, BF>>::append_scalar(self, label, item);
        }
        self.append_message(label, b"end_append_vector");
    }

    fn challenge_scalar(&mut self, label: &'static [u8]) -> EF {
        let ext_degree = EF::extension_degree() as usize;
        let mut buffer = vec![0u8; 64 * ext_degree];
        self.challenge_bytes(label, &mut buffer);
        let mut new_buffer = Vec::with_capacity(64 * ext_degree);
        for i in 0..ext_degree {
            let base_field_element = BF::from_le_bytes_mod_order(&buffer[(i * 64)..(i * 64 + 64)]);
            let _ = base_field_element.serialize_compressed(&mut new_buffer);
        }
        EF::deserialize_compressed(&new_buffer[..]).unwrap()
    }

    fn challenge_vector(&mut self, label: &'static [u8], len: usize) -> Vec<EF> {
        (0..len)
            .map(|_i| <Self as ExtensionTranscriptProtocol<EF, BF>>::challenge_scalar(self, label))
            .collect::<Vec<EF>>()
    }
}
