//! INST-AUTH: in-process adversarial acceptance controls using REAL OpenMLS.
//! These are lab protocol-message integrity controls. They cannot prove Shell
//! device authority, revocation or selected-session correctness.
use super::*;

struct SyntheticDb(std::path::PathBuf);
impl Drop for SyntheticDb {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
        let _ = std::fs::remove_file(format!("{}-journal", self.0.display()));
    }
}

#[test]
fn inst_auth_real_openmls_rejects_modified_commit_before_acceptance() {
    use std::time::{SystemTime, UNIX_EPOCH};
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock")
        .as_nanos();
    let db = SyntheticDb(std::env::temp_dir().join(format!(
        "shell-inst-auth-{}-{nonce}.sqlite",
        std::process::id()
    )));
    initialize(&db.0).expect("real synthetic MLS initialization");
    let connection = store::open(&db.0).unwrap();
    let state = read_state(&connection).unwrap();
    let provider = Provider::new(&connection);
    let leg = &state.legs[0];
    let mut origin = load_group(&provider, &leg.group_id).unwrap();
    let mut recipient = load_peer(&connection, 0, &state).unwrap();
    let signer = SignatureKeyPair::read(
        provider.storage(), &leg.signer_public, CLASSICAL.signature_algorithm(),
    ).expect("registered signer");

    let signed_commit = update(&mut origin, &provider, &signer).unwrap();
    assert!(signed_commit.len() > 2);
    let mut modified = signed_commit.clone();
    let last = modified.len() - 1;
    modified[last] ^= 0x01;

    assert!(
        accept(&mut recipient.group, &recipient.provider, &modified).is_err(),
        "modified MLS wire commit was accepted"
    );
    accept(&mut recipient.group, &recipient.provider, &signed_commit).unwrap();
    assert_eq!(recipient.group.epoch(), origin.epoch());
}
