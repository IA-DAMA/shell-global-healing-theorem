//! Independent classical and PQ MLS sessions: one local durable Shell fact.
//! No secret binding, exported PSK, custom KDF, or product integration.
use openmls::prelude::{
    tls_codec::{Deserialize as _, Serialize as _},
    *,
};
use openmls_basic_credential::SignatureKeyPair;
use openmls_rust_crypto::OpenMlsRustCrypto;
use openmls_traits::{OpenMlsProvider, crypto::OpenMlsCrypto};
use rusqlite::{Connection, OptionalExtension};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::path::Path;
mod combiner;
mod challenge;
#[cfg(test)]
mod exporter_trace_tests;
mod authority_witness;
mod instantiation;
mod store;
use store::{Provider, Result, checked};
pub use combiner::combine_exported_secrets;
pub use challenge::{ChallengeBinding, ChallengeLeg, accepted_challenge, verify_challenge};
pub use authority_witness::{AuthorityStatement, SignedAuthorityStatement, unsigned_authority_statement, verify_external_authority_selection};
pub use instantiation::encode_challenge_nonce;

/// Published classical control suite.
pub const CLASSICAL: Ciphersuite = Ciphersuite::MLS_128_DHKEMX25519_AES128GCM_SHA256_Ed25519;
/// Published experimental `OpenMLS` suite reproduced in the preceding milestone.
pub const PQ: Ciphersuite = Ciphersuite::MLS_128_MLKEM768X25519_CHACHA20POLY1305_SHA384_MLDSA44;
const ZERO: [u8; 32] = [0; 32];

/// Fixed experimental schedules, not a new cryptographic protocol.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Schedule {
    /// The PQ peer updates; the exposed canonical device retains its leaf key.
    PeerUpdate,
    /// Canonical PQ device renews its leaf, and the other member commits it.
    ExposedLeafRenewal,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct Leg {
    group_id: Vec<u8>,
    signer_public: Vec<u8>,
    authenticator_hash: [u8; 32],
    members: Vec<Vec<u8>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct State {
    epoch: u64,
    parent: [u8; 32],
    checkpoint: [u8; 32],
    legs: [Leg; 2],
    artifacts_hash: [u8; 32],
}

// Private peer state stays only in the laboratory database. Not Debug, not logs.
#[derive(Serialize, Deserialize)]
struct PeerState {
    signer_public: Vec<u8>,
    entries: Vec<(Vec<u8>, Vec<u8>)>,
}
struct Peer {
    provider: OpenMlsRustCrypto,
    signer: SignatureKeyPair,
    group: MlsGroup,
}

/// Public handshake artifacts only. No secret material is combined or exported.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Artifacts {
    pub classical_commit: Vec<u8>,
    pub pq_proposal: Option<Vec<u8>>,
    pub pq_commit: Vec<u8>,
}

/// Canonical receipt returned byte-identically on committed retry.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Receipt {
    pub operation_id: String,
    pub request: [u8; 32],
    pub parent: [u8; 32],
    pub checkpoint: [u8; 32],
    pub epoch: u64,
    pub schedule: Schedule,
    pub artifacts: Artifacts,
    // Public checkpoint inputs allow validation of historical retry artifacts.
    successor: State,
}

/// Observation after reopening durable state. Inspect fails closed on mismatch.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Inspection {
    pub classical_epoch: u64,
    pub pq_epoch: u64,
    pub shell_epoch: u64,
    pub checkpoint: [u8; 32],
    pub classical_peer_epoch: u64,
    pub pq_peer_epoch: u64,
    pub identities: Vec<Vec<u8>>,
    pub receipts: u64,
    pub outbox: u64,
}

fn encode<T: Serialize>(value: &T) -> Result<Vec<u8>> {
    checked(serde_json::to_vec(value), "encode")
}
fn decode<T: serde::de::DeserializeOwned>(bytes: &[u8]) -> Result<T> {
    checked(serde_json::from_slice(bytes), "decode")
}
fn hash(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}
fn checkpoint(state: &State) -> Result<[u8; 32]> {
    // Public local-integrity digest. It is NOT a cryptographic combiner or a
    // signed checkpoint and cannot stop a malicious writer recomputing hashes.
    Ok(hash(&encode(&(
        "shell.classical-pq.local-checkpoint/1",
        state.epoch,
        state.parent,
        &state.legs,
        state.artifacts_hash,
    ))?))
}
fn identities(group: &MlsGroup) -> Vec<Vec<u8>> {
    let mut identities: Vec<_> = group
        .members()
        .map(|m| m.credential.serialized_content().to_vec())
        .collect();
    identities.sort();
    identities
}
fn metadata(group: &MlsGroup, public: &[u8]) -> Leg {
    Leg {
        group_id: group.group_id().as_slice().to_vec(),
        signer_public: public.to_vec(),
        authenticator_hash: hash(group.epoch_authenticator().as_slice()),
        members: identities(group),
    }
}
fn capabilities(suite: Ciphersuite) -> Capabilities {
    Capabilities::new(None, Some(&[suite]), None, None, None)
}
fn credential(name: &[u8], signer: &SignatureKeyPair) -> CredentialWithKey {
    CredentialWithKey {
        credential: BasicCredential::new(name.to_vec()).into(),
        signature_key: signer.public().into(),
    }
}
fn protocol(bytes: &[u8]) -> Result<ProtocolMessage> {
    checked(
        checked(MlsMessageIn::tls_deserialize_exact(bytes), "wire_decode")?
            .try_into_protocol_message(),
        "protocol_message",
    )
}
fn wire(message: &MlsMessageOut) -> Result<Vec<u8>> {
    checked(message.tls_serialize_detached(), "wire_encode")
}
fn accept<P: OpenMlsProvider>(group: &mut MlsGroup, provider: &P, bytes: &[u8]) -> Result<()> {
    let processed = checked(
        group.process_message(provider, protocol(bytes)?),
        "process_commit",
    )?;
    let ProcessedMessageContent::StagedCommitMessage(staged) = processed.into_content() else {
        return Err("not_commit".into());
    };
    checked(group.merge_staged_commit(provider, *staged), "merge_commit")
}
fn proposal<P: OpenMlsProvider>(group: &mut MlsGroup, provider: &P, bytes: &[u8]) -> Result<()> {
    let processed = checked(
        group.process_message(provider, protocol(bytes)?),
        "process_proposal",
    )?;
    let ProcessedMessageContent::ProposalMessage(staged) = processed.into_content() else {
        return Err("not_proposal".into());
    };
    checked(
        group.store_pending_proposal(provider.storage(), *staged),
        "store_proposal",
    )
}
fn update<P: OpenMlsProvider>(
    group: &mut MlsGroup,
    provider: &P,
    signer: &SignatureKeyPair,
) -> Result<Vec<u8>> {
    let update = checked(
        group.self_update(provider, signer, LeafNodeParameters::default()),
        "self_update",
    )?;
    let bytes = wire(&update.into_commit())?;
    checked(group.merge_pending_commit(provider), "merge_pending")?;
    Ok(bytes)
}
fn load_group<P: OpenMlsProvider>(provider: &P, id: &[u8]) -> Result<MlsGroup> {
    checked(
        MlsGroup::load(provider.storage(), &GroupId::from_slice(id)),
        "load_group",
    )?
    .ok_or_else(|| "group_absent".into())
}
fn peer_bytes(peer: &Peer) -> Result<Vec<u8>> {
    let values = peer
        .provider
        .storage()
        .values
        .read()
        .map_err(|_| "peer_lock")?;
    let mut entries: Vec<_> = values.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    encode(&PeerState {
        signer_public: peer.signer.public().to_vec(),
        entries,
    })
}
fn load_peer(connection: &Connection, index: usize, state: &State) -> Result<Peer> {
    let bytes: Vec<u8> = checked(
        connection.query_row("SELECT state FROM shell_peer WHERE leg=?1", [index], |r| {
            r.get(0)
        }),
        "peer_row",
    )?;
    let stored: PeerState = decode(&bytes)?;
    let provider = OpenMlsRustCrypto::default();
    provider
        .storage()
        .values
        .write()
        .map_err(|_| "peer_lock")?
        .extend(stored.entries);
    let signer = SignatureKeyPair::read(
        provider.storage(),
        &stored.signer_public,
        [CLASSICAL, PQ][index].signature_algorithm(),
    )
    .ok_or("peer_signer_absent")?;
    let group = load_group(&provider, &state.legs[index].group_id)?;
    Ok(Peer {
        provider,
        signer,
        group,
    })
}
fn save_peer(connection: &Connection, index: usize, peer: &Peer) -> Result<()> {
    checked(connection.execute("INSERT INTO shell_peer(leg,state) VALUES(?1,?2) ON CONFLICT(leg) DO UPDATE SET state=excluded.state", (index, peer_bytes(peer)?)), "save_peer").map(|_| ())
}

fn initialize_leg(provider: &Provider<'_>, suite: Ciphersuite) -> Result<(Leg, Peer)> {
    checked(provider.crypto().supports(suite), "unsupported_suite")?;
    let signer = checked(SignatureKeyPair::new(suite.signature_algorithm()), "signer")?;
    checked(signer.store(provider.storage()), "store_signer")?;
    let config = MlsGroupCreateConfig::builder()
        .ciphersuite(suite)
        .capabilities(capabilities(suite))
        .wire_format_policy(PURE_PLAINTEXT_WIRE_FORMAT_POLICY)
        .use_ratchet_tree_extension(true)
        .build();
    let mut group = checked(
        MlsGroup::new(
            provider,
            &signer,
            &config,
            credential(b"synthetic-A", &signer),
        ),
        "create_group",
    )?;
    let peer_provider = OpenMlsRustCrypto::default();
    let peer_signer = checked(
        SignatureKeyPair::new(suite.signature_algorithm()),
        "peer_signer",
    )?;
    checked(
        peer_signer.store(peer_provider.storage()),
        "store_peer_signer",
    )?;
    let package = checked(
        KeyPackage::builder()
            .leaf_node_capabilities(capabilities(suite))
            .build(
                suite,
                &peer_provider,
                &peer_signer,
                credential(b"synthetic-B", &peer_signer),
            ),
        "key_package",
    )?;
    let (_, welcome, _) = checked(
        group.add_members(provider, &signer, &[package.key_package().clone()]),
        "add_peer",
    )?;
    checked(group.merge_pending_commit(provider), "merge_add")?;
    let parsed = checked(
        MlsMessageIn::tls_deserialize_exact(wire(&welcome)?),
        "welcome_decode",
    )?;
    let MlsMessageBodyIn::Welcome(welcome) = parsed.extract() else {
        return Err("not_welcome".into());
    };
    let config = MlsGroupJoinConfig::builder()
        .wire_format_policy(PURE_PLAINTEXT_WIRE_FORMAT_POLICY)
        .build();
    let peer_group = checked(
        checked(
            StagedWelcome::new_from_welcome(&peer_provider, &config, welcome, None),
            "stage_welcome",
        )?
        .into_group(&peer_provider),
        "join",
    )?;
    Ok((
        metadata(&group, signer.public()),
        Peer {
            provider: peer_provider,
            signer: peer_signer,
            group: peer_group,
        },
    ))
}

/// Initialize two independent two-member sessions at epoch 1 (after Add).
/// # Errors
/// Returns a sanitized stage on provider/storage error or existing schema.
pub fn initialize(path: &Path) -> Result<Inspection> {
    let mut connection = store::open(path)?;
    store::initialize(&mut connection)?;
    store::transaction(&connection, || {
        let provider = Provider::new(&connection);
        let (classical, cp) = initialize_leg(&provider, CLASSICAL)?;
        let (pq, qp) = initialize_leg(&provider, PQ)?;
        if classical.group_id == pq.group_id || classical.signer_public == pq.signer_public {
            return Err("independence_failed".into());
        }
        let mut state = State {
            epoch: 1,
            parent: ZERO,
            checkpoint: ZERO,
            legs: [classical, pq],
            artifacts_hash: ZERO,
        };
        state.checkpoint = checkpoint(&state)?;
        save_peer(&connection, 0, &cp)?;
        save_peer(&connection, 1, &qp)?;
        checked(
            connection.execute(
                "INSERT INTO shell_state VALUES(1,?1,?2)",
                (state.checkpoint.as_slice(), encode(&state)?),
            ),
            "genesis",
        )?;
        Ok(())
    })?;
    inspect(path)
}

fn read_state(connection: &Connection) -> Result<State> {
    let (stored_hash, bytes): (Vec<u8>, Vec<u8>) = checked(
        connection.query_row(
            "SELECT checkpoint,state FROM shell_state WHERE singleton=1",
            [],
            |r| Ok((r.get(0)?, r.get(1)?)),
        ),
        "state_row",
    )?;
    let state: State = decode(&bytes)?;
    if stored_hash != state.checkpoint || checkpoint(&state)? != state.checkpoint {
        return Err("checkpoint_mismatch".into());
    }
    Ok(state)
}

fn read_receipt(connection: &Connection, id: &str) -> Result<Option<Receipt>> {
    let row = checked(
        connection
            .query_row(
                "SELECT parent,checkpoint,request,receipt FROM shell_receipt WHERE operation_id=?1",
                [id],
                |r| {
                    Ok((
                        r.get::<_, Vec<u8>>(0)?,
                        r.get::<_, Vec<u8>>(1)?,
                        r.get::<_, Vec<u8>>(2)?,
                        r.get::<_, Vec<u8>>(3)?,
                    ))
                },
            )
            .optional(),
        "receipt_row",
    )?;
    let Some((parent, checkpoint, request, bytes)) = row else {
        return Ok(None);
    };
    let receipt: Receipt = decode(&bytes)?;
    let outbox: Vec<u8> = checked(
        connection.query_row(
            "SELECT receipt FROM shell_outbox WHERE operation_id=?1",
            [id],
            |r| r.get(0),
        ),
        "outbox_row",
    )?;
    let expected_request = hash(&encode(&(
        "shell.classical-pq.request/1",
        id,
        receipt.parent,
        receipt.schedule,
    ))?);
    if receipt.operation_id != id
        || receipt.parent != parent.as_slice()
        || receipt.checkpoint != checkpoint.as_slice()
        || receipt.request != request.as_slice()
        || receipt.request != expected_request
        || outbox != bytes
        || encode(&receipt)? != bytes
    {
        return Err("receipt_mismatch".into());
    }
    if receipt.successor.checkpoint != receipt.checkpoint
        || receipt.successor.epoch != receipt.epoch
        || receipt.successor.parent != receipt.parent
        || crate::checkpoint(&receipt.successor)? != receipt.checkpoint
        || hash(&encode(&receipt.artifacts)?) != receipt.successor.artifacts_hash
    {
        return Err("artifact_mismatch".into());
    }
    Ok(Some(receipt))
}

/// Load an existing canonical receipt, without executing MLS again.
/// # Errors
/// Missing or inconsistent receipts fail closed.
pub fn committed_receipt(path: &Path, id: &str) -> Result<Receipt> {
    read_receipt(&store::open(path)?, id)?.ok_or_else(|| "receipt_absent".into())
}

/// Reopen all four member states and check epochs, suite, identity and receipt.
/// # Errors
/// Any divergence returns a sanitized stage, never secret state.
pub fn inspect(path: &Path) -> Result<Inspection> {
    let connection = store::open(path)?;
    store::transaction(&connection, || inspect_connection(&connection))
}

fn inspect_connection(connection: &Connection) -> Result<Inspection> {
    let state = read_state(connection)?;
    let provider = Provider::new(connection);
    let expected_members = vec![b"synthetic-A".to_vec(), b"synthetic-B".to_vec()];
    for (index, suite) in [CLASSICAL, PQ].iter().enumerate() {
        let leg = &state.legs[index];
        let group = load_group(&provider, &leg.group_id)?;
        let peer = load_peer(connection, index, &state)?;
        if group.epoch().as_u64() != state.epoch
            || peer.group.epoch() != group.epoch()
            || group.ciphersuite() != *suite
            || peer.group.ciphersuite() != *suite
            || metadata(&group, &leg.signer_public) != *leg
            || identities(&group) != expected_members
            || identities(&peer.group) != expected_members
            || group.epoch_authenticator().as_slice() != peer.group.epoch_authenticator().as_slice()
        {
            return Err("provider_state_mismatch".into());
        }
    }
    if state.epoch > 1 {
        let id: String = checked(
            connection.query_row(
                "SELECT operation_id FROM shell_receipt WHERE checkpoint=?1",
                [state.checkpoint.as_slice()],
                |r| r.get(0),
            ),
            "current_receipt",
        )?;
        let receipt = read_receipt(connection, &id)?.ok_or("receipt_absent")?;
        if receipt.epoch != state.epoch
            || receipt.parent != state.parent
            || hash(&encode(&receipt.artifacts)?) != state.artifacts_hash
        {
            return Err("artifact_mismatch".into());
        }
    }
    let receipts: u64 = checked(
        connection.query_row("SELECT COUNT(*) FROM shell_receipt", [], |r| r.get(0)),
        "receipt_count",
    )?;
    let outbox: u64 = checked(
        connection.query_row("SELECT COUNT(*) FROM shell_outbox", [], |r| r.get(0)),
        "outbox_count",
    )?;
    if receipts != state.epoch - 1 || receipts != outbox {
        return Err("history_count_mismatch".into());
    }
    Ok(Inspection {
        classical_epoch: state.epoch,
        pq_epoch: state.epoch,
        shell_epoch: state.epoch,
        classical_peer_epoch: state.epoch,
        pq_peer_epoch: state.epoch,
        checkpoint: state.checkpoint,
        identities: expected_members,
        receipts,
        outbox,
    })
}

/// Run one Shell transition. Failpoints abort a child process, never host/apps.
/// # Errors
/// Fails closed on stale predecessor, conflicting id, state or provider errors.
pub fn transition(
    path: &Path,
    id: &str,
    parent: [u8; 32],
    schedule: Schedule,
    abort_at: Option<usize>,
    after_commit: bool,
) -> Result<(Receipt, Vec<String>)> {
    run_transition(path, id, parent, schedule, abort_at, after_commit, |_| {})
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn run_transition(
    path: &Path,
    id: &str,
    parent: [u8; 32],
    schedule: Schedule,
    abort_at: Option<usize>,
    after_commit: bool,
    mut after_fresh_key: impl FnMut(&Connection),
) -> Result<(Receipt, Vec<String>)> {
    let connection = store::open(path)?;
    let boundaries = store::install_failpoints(&connection, abort_at)?;
    let request = hash(&encode(&(
        "shell.classical-pq.request/1",
        id,
        parent,
        schedule,
    ))?);
    let receipt = store::transaction(&connection, || {
        // Verify current canonical state even for a historical retry.
        inspect_connection(&connection)?;
        if let Some(receipt) = read_receipt(&connection, id)? {
            if receipt.request != request {
                return Err("operation_id_equivocation".into());
            }
            return Ok(receipt);
        }
        let mut state = read_state(&connection)?;
        if state.checkpoint != parent {
            return Err("stale_predecessor".into());
        }
        let provider = Provider::new(&connection);
        let mut classical = load_group(&provider, &state.legs[0].group_id)?;
        let mut pq = load_group(&provider, &state.legs[1].group_id)?;
        let mut cp = load_peer(&connection, 0, &state)?;
        let mut qp = load_peer(&connection, 1, &state)?;
        let cs = SignatureKeyPair::read(
            provider.storage(),
            &state.legs[0].signer_public,
            CLASSICAL.signature_algorithm(),
        )
        .ok_or("classical_signer_absent")?;
        let qs = SignatureKeyPair::read(
            provider.storage(),
            &state.legs[1].signer_public,
            PQ.signature_algorithm(),
        )
        .ok_or("pq_signer_absent")?;
        let classical_commit = update(&mut classical, &provider, &cs)?;
        accept(&mut cp.group, &cp.provider, &classical_commit)?;
        let (pq_proposal, pq_commit) = match schedule {
            Schedule::PeerUpdate => (None, update(&mut qp.group, &qp.provider, &qp.signer)?),
            Schedule::ExposedLeafRenewal => {
                let (message, _) = checked(
                    pq.propose_self_update(&provider, &qs, LeafNodeParameters::default()),
                    "renew_leaf",
                )?;
                let bytes = wire(&message)?;
                proposal(&mut qp.group, &qp.provider, &bytes)?;
                after_fresh_key(&connection);
                let (commit, _, _) = checked(
                    qp.group
                        .commit_to_pending_proposals(&qp.provider, &qp.signer),
                    "commit_proposal",
                )?;
                checked(
                    qp.group.merge_pending_commit(&qp.provider),
                    "merge_peer_proposal",
                )?;
                (Some(bytes), wire(&commit)?)
            }
        };
        accept(&mut pq, &provider, &pq_commit)?;
        let artifacts = Artifacts {
            classical_commit,
            pq_proposal,
            pq_commit,
        };
        let next = state.epoch.checked_add(1).ok_or("epoch_overflow")?;
        for (index, group) in [&classical, &pq].iter().enumerate() {
            if group.epoch().as_u64() != next || identities(group) != state.legs[index].members {
                return Err("transition_epoch_or_membership".into());
            }
            state.legs[index] = metadata(group, &state.legs[index].signer_public);
        }
        state.epoch = next;
        state.parent = parent;
        state.artifacts_hash = hash(&encode(&artifacts)?);
        state.checkpoint = checkpoint(&state)?;
        // All remote-role storage here is LAB co-location, not distributed commit.
        save_peer(&connection, 0, &cp)?;
        save_peer(&connection, 1, &qp)?;
        let changed = checked(
            connection.execute(
                "UPDATE shell_state SET checkpoint=?1,state=?2 WHERE singleton=1 AND checkpoint=?3",
                (
                    state.checkpoint.as_slice(),
                    encode(&state)?,
                    parent.as_slice(),
                ),
            ),
            "checkpoint_cas",
        )?;
        if changed != 1 {
            return Err("checkpoint_cas_lost".into());
        }
        let receipt = Receipt {
            operation_id: id.into(),
            request,
            parent,
            checkpoint: state.checkpoint,
            epoch: next,
            schedule,
            artifacts,
            successor: state,
        };
        let bytes = encode(&receipt)?;
        checked(
            connection.execute("INSERT INTO shell_outbox VALUES(?1,?2)", (id, &bytes)),
            "outbox_write",
        )?;
        checked(
            connection.execute(
                "INSERT INTO shell_receipt VALUES(?1,?2,?3,?4,?5)",
                (
                    id,
                    parent.as_slice(),
                    receipt.checkpoint.as_slice(),
                    request.as_slice(),
                    &bytes,
                ),
            ),
            "receipt_write",
        )?;
        inspect_connection(&connection)?;
        store::before_commit(&connection)?;
        Ok(receipt)
    })?;
    if after_commit {
        use std::io::Write as _;
        println!("CRASH_AT=COMMIT/AFTER");
        let _ = std::io::stdout().flush();
        std::process::abort();
    }
    Ok((receipt, boundaries.labels()))
}

#[cfg(test)]
mod exposure;
#[cfg(test)]
mod authentication_probe;
