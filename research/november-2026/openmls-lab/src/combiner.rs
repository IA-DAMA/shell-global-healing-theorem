//! Experimental combiner used only by the Classical + PQ research lab.
use hkdf::Hkdf;
use sha2::Sha256;

const DOMAIN: &[u8] = b"shell.classical-pq.kz/1";

/// Derive an ephemeral 32-byte research K_Z from independent Classical and PQ inputs.
/// This is an experiment, not a production protocol construction.
pub fn combine_exported_secrets(classical: &[u8; 32], pq: &[u8; 32], context: &[u8]) -> [u8; 32] {
    let mut ikm = [0u8; 64];
    ikm[..32].copy_from_slice(classical);
    ikm[32..].copy_from_slice(pq);
    let hk = Hkdf::<Sha256>::new(Some(DOMAIN), &ikm);
    let mut info = Vec::with_capacity(DOMAIN.len() + 8 + context.len());
    info.extend_from_slice(DOMAIN);
    info.extend_from_slice(&(context.len() as u64).to_be_bytes());
    info.extend_from_slice(context);
    let mut out = [0u8; 32];
    hk.expand(&info, &mut out).expect("32-byte HKDF output");
    out
}
