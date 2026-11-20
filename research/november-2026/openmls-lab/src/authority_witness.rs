//! INST-CHALLENGE: independently signed authority selection at the lab boundary.
//!
//! This adapter is experimental. The verifying public key, current generation
//! and currently selected head come from a trusted caller, never this SQLite DB.
//! The secret signer is not stored by the crate. A signed witness authenticates
//! what a trusted authority selected, but not the authority's own correctness.
//! It is NOT a formal refinement of OpenMLS internals or a production API.
use super::*;
use openmls::prelude::SignatureScheme;
use openmls_traits::crypto::OpenMlsCrypto;
use serde::{Deserialize, Serialize};

const WITNESS_DOMAIN: &str = "shell.f4.external-authority-selection/1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuthorityStatement {
    pub domain: String,
    pub generation: u64,
    pub leg: String,
    pub binding: ChallengeBinding,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SignedAuthorityStatement {
    pub statement: AuthorityStatement,
    pub signature: Vec<u8>,
}

pub(crate) fn witness_message(statement: &AuthorityStatement) -> Result<Vec<u8>> {
    // The type has a fixed field order. Prefix separates the signed message
    // from other Ed25519 uses even when the encoded structure is identical.
    encode(&(WITNESS_DOMAIN, statement))
}

/// Constructs the public statement. Signing requires an OUT-OF-PROCESS issuer.
/// There is deliberately no secret signing key in this library.
/// # Errors
/// A malformed generation or an unaccepted local state fails closed.
pub fn unsigned_authority_statement(
    path: &Path,
    leg: ChallengeLeg,
    generation: u64,
) -> Result<AuthorityStatement> {
    if generation == 0 {
        return Err("invalid_generation".into());
    }
    Ok(AuthorityStatement {
        domain: WITNESS_DOMAIN.into(),
        generation,
        leg: format!("{leg:?}"),
        binding: accepted_challenge(path, leg)?,
    })
}

/// Verify the current external selection, its independent Ed25519 signature,
/// and an accepted two-sided OpenMLS challenge.
/// # Errors
/// A forged, stale, unselected, or provider-divergent challenge fails closed.
/// This read-only diagnostic is NOT a token that authorizes a later transition:
/// a real action must recheck selection under its own atomic authority fence.
pub fn verify_external_authority_selection(
    path: &Path,
    leg: ChallengeLeg,
    statement: &SignedAuthorityStatement,
    trusted_public_key: &[u8],
    current_generation: u64,
    current_selected_head: &[u8; 32],
) -> Result<ChallengeBinding> {
    let claim = &statement.statement;
    if claim.domain != WITNESS_DOMAIN
        || claim.leg != format!("{leg:?}")
        || current_generation == 0
        || claim.generation != current_generation
        || !claim.binding.accepted
        || &claim.binding.accepted_shell_head != current_selected_head
    {
        return Err("authority_selection_mismatch".into());
    }
    let crypto = OpenMlsRustCrypto::default();
    checked(
        crypto.crypto().verify_signature(
            SignatureScheme::ED25519,
            &witness_message(claim)?,
            trusted_public_key,
            &statement.signature,
        ),
        "authority_signature_invalid",
    )?;
    // Re-reads durable Shell and the real accepted OpenMLS group and peers.
    // The selected head and generation are rechecked inside that transaction,
    // not only in an earlier, potentially stale read.
    challenge::verify_challenge_guarded(path, leg, &claim.binding, |actual| {
        if actual.accepted_shell_head != *current_selected_head
            || claim.generation != current_generation
            || actual != &claim.binding
        {
            return Err("authority_selection_mismatch".into());
        }
        Ok(())
    })?;
    Ok(claim.binding.clone())
}
