//! INST-CHALLENGE research-only correspondence gate for ACCEPTED OpenMLS states.
//! No production integration, account credentials, network, or exported keys.
//! Equality of typed public fields is an executable correspondence check,
//! not a computational PCS/QPT proof or signed attestation.
use super::*;

const DOMAIN: &str = "shell.challenge/1";
const PROVIDER: &str = "openmls";
const VERSION: &str = "0.9.0";
const LABEL: &str = "shell.f4.accepted/1";
const PURPOSE: &str = "accepted-epoch-correspondence";
const OUTPUT_LEN: usize = 32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChallengeLeg {
    Classical,
    PostQuantum,
}
impl ChallengeLeg {
    const fn index(self) -> usize {
        match self {
            Self::Classical => 0,
            Self::PostQuantum => 1,
        }
    }
}

/// Public, typed challenge identity. No exporter or epoch secret is serialized.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChallengeBinding {
    pub shell_domain_version: String,
    pub provider_id: String,
    pub provider_version: String,
    pub suite: String,
    pub opaque_group_id: Vec<u8>,
    pub accepted_shell_head: [u8; 32],
    pub parent: [u8; 32],
    pub provider_epoch: u64,
    pub accepted_membership_digest: [u8; 32],
    pub challenge_generator: Vec<u8>,
    pub provider_state_authenticator: [u8; 32],
    pub exporter_label: String,
    pub exporter_context: Vec<u8>,
    pub challenge_purpose: String,
    pub output_length: usize,
    pub accepted: bool,
}

fn binding(
    state: &State,
    index: usize,
    group_id: &[u8],
    epoch: u64,
    members: &[Vec<u8>],
    state_auth: [u8; 32],
    generator: &[u8],
) -> Result<ChallengeBinding> {
    let mut result = ChallengeBinding {
        shell_domain_version: DOMAIN.into(),
        provider_id: PROVIDER.into(),
        provider_version: VERSION.into(),
        suite: format!("{:?}", [CLASSICAL, PQ][index]),
        opaque_group_id: group_id.to_vec(),
        accepted_shell_head: state.checkpoint,
        parent: state.parent,
        provider_epoch: epoch,
        accepted_membership_digest: hash(&encode(&members)?),
        challenge_generator: generator.to_vec(),
        provider_state_authenticator: state_auth,
        exporter_label: LABEL.into(),
        exporter_context: Vec::new(),
        challenge_purpose: PURPOSE.into(),
        output_length: OUTPUT_LEN,
        accepted: true,
    };
    // Context binds all public challenge selectors; never raw secret material.
    result.exporter_context = encode(&(
        "shell.f4.exporter-context/1",
        &result.shell_domain_version,
        &result.provider_id,
        &result.provider_version,
        &result.suite,
        &result.opaque_group_id,
        result.accepted_shell_head,
        result.parent,
        result.provider_epoch,
        result.accepted_membership_digest,
        &result.challenge_generator,
        result.provider_state_authenticator,
        &result.exporter_label,
        &result.challenge_purpose,
        result.output_length,
    ))?;
    Ok(result)
}

fn shell_binding(state: &State, index: usize) -> Result<ChallengeBinding> {
    let leg = &state.legs[index];
    binding(
        state,
        index,
        &leg.group_id,
        state.epoch,
        &leg.members,
        leg.authenticator_hash,
        &leg.signer_public,
    )
}

fn provider_binding(state: &State, index: usize, group: &MlsGroup) -> Result<ChallengeBinding> {
    // This must be read from the accepted MLS roster, NOT copied from the
    // Shell state; otherwise comparison would be tautological for generator.
    let generator = group
        .members()
        .find(|member| member.credential.serialized_content() == b"synthetic-A")
        .ok_or("bad_challenge")?;
    binding(
        state,
        index,
        group.group_id().as_slice(),
        group.epoch().as_u64(),
        &identities(group),
        hash(group.epoch_authenticator().as_slice()),
        &generator.signature_key,
    )
}

fn accepted_pair(
    connection: &Connection,
    leg: ChallengeLeg,
) -> Result<(ChallengeBinding, ChallengeBinding)> {
    // Existing inspect checks both OpenMLS legs, peers, receipt and accepted
    // durable checkpoint together under the same BEGIN IMMEDIATE transaction.
    inspect_connection(connection)?;
    let state = read_state(connection)?;
    let index = leg.index();
    let provider = Provider::new(connection);
    let group = load_group(&provider, &state.legs[index].group_id)?;
    if !group.is_active() || group.pending_commit().is_some() {
        return Err("bad_challenge".into());
    }
    let signer = &state.legs[index].signer_public;
    if SignatureKeyPair::read(
        provider.storage(),
        signer,
        [CLASSICAL, PQ][index].signature_algorithm(),
    )
    .is_none()
    {
        return Err("bad_challenge".into());
    }
    Ok((
        shell_binding(&state, index)?,
        provider_binding(&state, index, &group)?,
    ))
}

/// Obtain an accepted, PUBLIC challenge selector from the current local state.
/// This is a lab observation, not an attestation or an authority to act.
/// # Errors
/// Any provider/receipt divergence or prepared-but-unaccepted state fails closed.
pub fn accepted_challenge(path: &Path, leg: ChallengeLeg) -> Result<ChallengeBinding> {
    let connection = store::open(path)?;
    store::transaction(&connection, || {
        let (shell, provider) = accepted_pair(&connection, leg)?;
        if shell != provider {
            return Err("bad_challenge".into());
        }
        Ok(shell)
    })
}

/// Check a supplied challenge against both durable Shell state and the real
/// accepted OpenMLS group, then perform exporter equality with the peer.
/// No secret is returned, persisted in a report or printed.
/// # Errors
/// Every mutated, stale, tentative or mismatched selector fails closed.
pub fn verify_challenge(
    path: &Path,
    leg: ChallengeLeg,
    candidate: &ChallengeBinding,
) -> Result<()> {
    verify_challenge_guarded(path, leg, candidate, |_| Ok(()))
}

/// Research-only guarded verifier. The additional public authority selection
/// is checked under the SAME durable read transaction as both OpenMLS views,
/// preventing a read-only TOCTOU between selector verification and peer export.
/// The caller must separately implement a live issuer/monotone authority.
pub(crate) fn verify_challenge_guarded(
    path: &Path,
    leg: ChallengeLeg,
    candidate: &ChallengeBinding,
    guard: impl FnOnce(&ChallengeBinding) -> Result<()>,
) -> Result<()> {
    let connection = store::open(path)?;
    store::transaction(&connection, || {
        let (shell, actual) = accepted_pair(&connection, leg)?;
        if !candidate.accepted || *candidate != shell || *candidate != actual {
            return Err("bad_challenge".into());
        }
        guard(&actual)?;
        let state = read_state(&connection)?;
        let index = leg.index();
        let provider = Provider::new(&connection);
        let group = load_group(&provider, &state.legs[index].group_id)?;
        let peer = load_peer(&connection, index, &state)?;
        if !peer.group.is_active()
            || peer.group.pending_commit().is_some()
            || peer.group.group_id() != group.group_id()
            || peer.group.epoch() != group.epoch()
        {
            return Err("bad_challenge".into());
        }
        let a = checked(
            group.export_secret(
                provider.crypto(),
                &actual.exporter_label,
                &actual.exporter_context,
                actual.output_length,
            ),
            "exporter",
        )?;
        let b = checked(
            peer.group.export_secret(
                peer.provider.crypto(),
                &actual.exporter_label,
                &actual.exporter_context,
                actual.output_length,
            ),
            "exporter",
        )?;
        if a.as_slice() != b.as_slice() || a.as_slice().len() != OUTPUT_LEN {
            return Err("exporter_mismatch".into());
        }
        Ok(())
    })
}
