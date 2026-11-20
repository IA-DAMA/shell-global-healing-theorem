//! Executed threat controls for independently signed current authority witness.
//!
//! The synthetic service key is held by the test, NOT in the SQLite database.
//! This is a conditional trusted-issuer experiment, not a production guarantee.
use openmls::prelude::SignatureScheme;
use openmls_rust_crypto::OpenMlsRustCrypto;
use openmls_traits::{OpenMlsProvider, crypto::OpenMlsCrypto};
use shell_classical_pq_composition::{
    AuthorityStatement, ChallengeLeg, Schedule, SignedAuthorityStatement,
    accepted_challenge, initialize, transition, unsigned_authority_statement,
    verify_external_authority_selection,
};
use std::{
    fs,
    path::PathBuf,
    time::{SystemTime, UNIX_EPOCH},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let stamp = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        Self(std::env::temp_dir().join(format!(
            "shell-f4-authority-witness-{}-{stamp}.sqlite", std::process::id()
        )))
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
        let _ = fs::remove_file(format!("{}-journal", self.0.display()));
    }
}

fn signed(
    crypto: &OpenMlsRustCrypto,
    private_key: &[u8],
    statement: AuthorityStatement,
) -> SignedAuthorityStatement {
    let message = serde_json::to_vec(&(
        "shell.f4.external-authority-selection/1",
        &statement,
    ))
    .expect("canonical test message");
    SignedAuthorityStatement {
        statement,
        signature: crypto.crypto().sign(SignatureScheme::ED25519, &message, private_key).unwrap(),
    }
}

#[test]
fn independent_signed_authority_accepts_each_real_openmls_leg() {
    let db = Fixture::new();
    initialize(&db.0).unwrap();
    let issuer = OpenMlsRustCrypto::default();
    let (private_key, public_key) =
        issuer.crypto().signature_key_gen(SignatureScheme::ED25519).unwrap();
    for leg in [ChallengeLeg::Classical, ChallengeLeg::PostQuantum] {
        let expected = accepted_challenge(&db.0, leg).unwrap();
        let claim = signed(
            &issuer,
            &private_key,
            unsigned_authority_statement(&db.0, leg, 7).unwrap(),
        );
        assert_eq!(
            verify_external_authority_selection(
                &db.0, leg, &claim, &public_key, 7, &expected.accepted_shell_head
            ).unwrap(),
            expected,
        );
    }
}

#[test]
fn unsigned_forged_or_stale_selection_cannot_pass_signed_current_witness() {
    let db = Fixture::new();
    let state = initialize(&db.0).unwrap();
    let issuer = OpenMlsRustCrypto::default();
    let (private_key, public_key) =
        issuer.crypto().signature_key_gen(SignatureScheme::ED25519).unwrap();
    let (other_private_key, wrong_public_key) =
        issuer.crypto().signature_key_gen(SignatureScheme::ED25519).unwrap();
    let leg = ChallengeLeg::PostQuantum;
    let before = accepted_challenge(&db.0, leg).unwrap();
    let valid = signed(
        &issuer,
        &private_key,
        unsigned_authority_statement(&db.0, leg, 3).unwrap(),
    );
    assert!(
        verify_external_authority_selection(&db.0, leg, &valid, &wrong_public_key, 3, &before.accepted_shell_head).is_err(),
        "wrong issuer key was accepted",
    );
    assert!(
        verify_external_authority_selection(&db.0, leg, &valid, &public_key, 4, &before.accepted_shell_head).is_err(),
        "stale selected generation was accepted",
    );
    let mut forged = valid.clone();
    forged.statement.binding.parent[0] ^= 1;
    assert!(
        verify_external_authority_selection(&db.0, leg, &forged, &public_key, 3, &before.accepted_shell_head).is_err(),
        "mutated but unresigned statement was accepted",
    );
    let forged_signature = signed(&issuer, &other_private_key, forged.statement);
    assert!(
        verify_external_authority_selection(&db.0, leg, &forged_signature, &public_key, 3, &before.accepted_shell_head).is_err(),
        "attacker-created signature was accepted",
    );

    transition(&db.0, "signed-witness-epoch", state.checkpoint, Schedule::PeerUpdate, None, false).unwrap();
    let after = accepted_challenge(&db.0, leg).unwrap();
    assert_ne!(before.accepted_shell_head, after.accepted_shell_head);
    assert!(
        verify_external_authority_selection(&db.0, leg, &valid, &public_key, 3, &after.accepted_shell_head).is_err(),
        "stale signed anchor was accepted for new current head",
    );
    let current = signed(
        &issuer,
        &private_key,
        unsigned_authority_statement(&db.0, leg, 4).unwrap(),
    );
    verify_external_authority_selection(
        &db.0, leg, &current, &public_key, 4, &after.accepted_shell_head
    ).expect("fresh signed head accepted");
}

#[test]
fn cross_leg_reuse_and_absent_generation_fail_even_with_valid_signature() {
    let db = Fixture::new();
    initialize(&db.0).unwrap();
    let issuer = OpenMlsRustCrypto::default();
    let (private_key, public_key) =
        issuer.crypto().signature_key_gen(SignatureScheme::ED25519).unwrap();
    let binding = accepted_challenge(&db.0, ChallengeLeg::Classical).unwrap();
    let claim = signed(
        &issuer,
        &private_key,
        unsigned_authority_statement(&db.0, ChallengeLeg::Classical, 1).unwrap(),
    );
    assert!(verify_external_authority_selection(
        &db.0, ChallengeLeg::PostQuantum, &claim, &public_key, 1, &binding.accepted_shell_head
    ).is_err());
    assert!(verify_external_authority_selection(
        &db.0, ChallengeLeg::Classical, &claim, &public_key, 0, &binding.accepted_shell_head
    ).is_err());
    assert!(unsigned_authority_statement(&db.0, ChallengeLeg::Classical, 0).is_err());
}
