//! Counterexample: a local, unsigned genesis checkpoint can be recomputed.
//!
//! The experiment is deliberately adversarial and synthetic. It demonstrates
//! that equal selectors plus real OpenMLS exporter equality do not authenticate
//! a Shell history anchor independently of a writable SQLite file.
//! It does NOT allege that production Linka uses this unauthenticated design.
use openmls::prelude::SignatureScheme;
use openmls_rust_crypto::OpenMlsRustCrypto;
use openmls_traits::{OpenMlsProvider, crypto::OpenMlsCrypto};
use rusqlite::{Connection, params};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use shell_classical_pq_composition::{
    ChallengeLeg, SignedAuthorityStatement, accepted_challenge, initialize, inspect,
    verify_challenge, unsigned_authority_statement, verify_external_authority_selection,
};
use std::{
    fs,
    path::PathBuf,
    time::{SystemTime, UNIX_EPOCH},
};

#[derive(Serialize, Deserialize)]
struct Leg {
    group_id: Vec<u8>,
    signer_public: Vec<u8>,
    authenticator_hash: [u8; 32],
    members: Vec<Vec<u8>>,
}

#[derive(Serialize, Deserialize)]
struct State {
    epoch: u64,
    parent: [u8; 32],
    checkpoint: [u8; 32],
    legs: [Leg; 2],
    artifacts_hash: [u8; 32],
}

fn checksum(state: &State) -> [u8; 32] {
    let bytes = serde_json::to_vec(&(
        "shell.classical-pq.local-checkpoint/1",
        state.epoch,
        state.parent,
        &state.legs,
        state.artifacts_hash,
    ))
    .expect("encode public checkpoint inputs");
    Sha256::digest(bytes).into()
}

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock")
            .as_nanos();
        Self(std::env::temp_dir().join(format!(
            "shell-f4-forged-genesis-{}-{nonce}.sqlite",
            std::process::id()
        )))
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
        let _ = fs::remove_file(format!("{}-journal", self.0.display()));
    }
}

#[test]
fn writable_local_genesis_can_reanchor_shell_without_changing_accepted_mls() {
    let db = Fixture::new();
    initialize(&db.0).expect("initialized real OpenMLS lab");
    let old_classical = accepted_challenge(&db.0, ChallengeLeg::Classical).unwrap();
    let old_pq = accepted_challenge(&db.0, ChallengeLeg::PostQuantum).unwrap();

    // Independent trusted Ed25519 authority selects the original accepted head.
    // Its private key never enters the mutable SQLite database.
    let issuer = OpenMlsRustCrypto::default();
    let (signer_private, signer_public) =
        issuer.crypto().signature_key_gen(SignatureScheme::ED25519).unwrap();
    let original_statement = unsigned_authority_statement(
        &db.0, ChallengeLeg::Classical, 5,
    ).unwrap();
    let signed_bytes = serde_json::to_vec(&(
        "shell.f4.external-authority-selection/1",
        &original_statement,
    )).unwrap();
    let signed_original = SignedAuthorityStatement {
        statement: original_statement,
        signature: issuer.crypto().sign(
            SignatureScheme::ED25519, &signed_bytes, &signer_private,
        ).unwrap(),
    };
    verify_external_authority_selection(
        &db.0, ChallengeLeg::Classical, &signed_original,
        &signer_public, 5, &old_classical.accepted_shell_head,
    ).unwrap();

    let connection = Connection::open(&db.0).unwrap();
    let (stored, encoded): (Vec<u8>, Vec<u8>) = connection
        .query_row(
            "SELECT checkpoint,state FROM shell_state WHERE singleton=1",
            [],
            |r| Ok((r.get(0)?, r.get(1)?)),
        )
        .unwrap();
    let mut state: State = serde_json::from_slice(&encoded).unwrap();
    assert_eq!(state.epoch, 1, "genesis is receipt-free");
    assert_eq!(state.parent, [0; 32]);
    assert_eq!(checksum(&state).as_slice(), stored.as_slice());

    // Attacker only modifies public local Shell metadata. The MLS provider
    // groups, credential keys, and remote synthetic peer states are untouched.
    state.parent[0] ^= 0x80;
    state.checkpoint = checksum(&state);
    assert_ne!(state.checkpoint, old_classical.accepted_shell_head);

    connection
        .execute(
            "UPDATE shell_state SET checkpoint=?1,state=?2 WHERE singleton=1",
            params![
                state.checkpoint.as_slice(),
                serde_json::to_vec(&state).unwrap()
            ],
        )
        .unwrap();
    drop(connection);

    // THIS IS THE COUNTEREXAMPLE: inspection, two-sided challenge equality
    // and real OpenMLS peer exporter comparisons still all accept.
    inspect(&db.0).expect("local inspection cannot authenticate chosen parent");
    for (leg, before) in [
        (ChallengeLeg::Classical, old_classical.clone()),
        (ChallengeLeg::PostQuantum, old_pq),
    ] {
        let forged = accepted_challenge(&db.0, leg).unwrap();
        assert_eq!(forged.provider_epoch, before.provider_epoch);
        assert_eq!(forged.opaque_group_id, before.opaque_group_id);
        assert_eq!(forged.accepted_membership_digest, before.accepted_membership_digest);
        assert_eq!(forged.challenge_generator, before.challenge_generator);
        assert_eq!(forged.provider_state_authenticator, before.provider_state_authenticator);
        assert_eq!(forged.parent, state.parent);
        assert_eq!(forged.accepted_shell_head, state.checkpoint);
        assert_ne!(forged.parent, before.parent);
        assert_ne!(forged.accepted_shell_head, before.accepted_shell_head);
        verify_challenge(&db.0, leg, &forged)
            .expect("forged public history anchor is accepted as local canonical");
        assert_eq!(
            verify_challenge(&db.0, leg, &before),
            Err("bad_challenge".into()),
            "previous authentic history anchor no longer matches local copy",
        );
    }

    // Positive boundary: the *same forged lab state* is rejected once the
    // independent signed current selection is required.
    assert!(
        verify_external_authority_selection(
            &db.0, ChallengeLeg::Classical, &signed_original,
            &signer_public, 5, &old_classical.accepted_shell_head,
        ).is_err(),
        "old signed selection must not authenticate forged current local state",
    );
    assert!(
        verify_external_authority_selection(
            &db.0, ChallengeLeg::Classical, &signed_original,
            &signer_public, 5, &state.checkpoint,
        ).is_err(),
        "attacker-selected local head must not replace signed authority head",
    );
    let mut fake_new_witness = signed_original;
    fake_new_witness.statement.binding.parent = state.parent;
    fake_new_witness.statement.binding.accepted_shell_head = state.checkpoint;
    assert!(
        verify_external_authority_selection(
            &db.0, ChallengeLeg::Classical, &fake_new_witness,
            &signer_public, 5, &state.checkpoint,
        ).is_err(),
        "editing witness without resigning must not authenticate forged head",
    );
}
