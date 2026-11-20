//! INST-COMPOSITION: injective public nonce encoding for the theorem boundary.
//!
//! This is NOT an MSS26 split-key combiner and never evaluates a secret. It
//! only makes the full accepted public ChallengeBinding unambiguous at the
//! boundary where a future, reviewed concrete instantiation may use it.
use crate::ChallengeBinding;

const NONCE_DOMAIN: &[u8] = b"shell.kz-formal.nonce/1";

fn append_field(out: &mut Vec<u8>, field: &[u8]) {
    let size = u64::try_from(field.len()).expect("field length fits u64");
    out.extend_from_slice(&size.to_be_bytes());
    out.extend_from_slice(field);
}

/// Injective, versioned encoding of the public challenge selector.
///
/// It uses a fixed field order and length-delimited byte strings. Epoch and
/// output length use fixed-width big-endian integers. Equality of encoded
/// values implies equality of every public selector in this profile, but does
/// not certify provider authenticity, state acceptance, or nonce uniqueness
/// across independently running/replayed clones.
///
/// This deliberately excludes the accepted observation flag from the nonce:
/// a caller must run the separate accepted-state challenge gate before use.
#[must_use]
pub fn encode_challenge_nonce(b: &ChallengeBinding) -> Vec<u8> {
    let epoch = b.provider_epoch.to_be_bytes();
    let length = u64::try_from(b.output_length)
        .expect("output length fits u64")
        .to_be_bytes();
    let fields: [&[u8]; 15] = [
        b.shell_domain_version.as_bytes(),
        b.provider_id.as_bytes(),
        b.provider_version.as_bytes(),
        b.suite.as_bytes(),
        &b.opaque_group_id,
        &b.accepted_shell_head,
        &b.parent,
        &epoch,
        &b.accepted_membership_digest,
        &b.challenge_generator,
        &b.provider_state_authenticator,
        b.exporter_label.as_bytes(),
        &b.exporter_context,
        b.challenge_purpose.as_bytes(),
        &length,
    ];
    let mut out = Vec::with_capacity(
        NONCE_DOMAIN.len() + fields.iter().map(|f| 8 + f.len()).sum::<usize>(),
    );
    out.extend_from_slice(NONCE_DOMAIN);
    for field in fields {
        append_field(&mut out, field);
    }
    out
}
