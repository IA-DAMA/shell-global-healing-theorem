//! INST-AUTH, INST-CLONE and INST-COMPOSITION research diagnostic controls.
//! These are real persisted OpenMLS lab invocations, NOT proof that the product
//! authority controller or a formal MSS26 split-key instance is implemented.
use shell_classical_pq_composition::{
    ChallengeBinding, ChallengeLeg, Schedule, accepted_challenge, encode_challenge_nonce,
    initialize, inspect, transition, verify_challenge,
};
use std::{
    fs,
    path::PathBuf,
    time::{SystemTime, UNIX_EPOCH},
};

struct Fixture(PathBuf);
impl Fixture {
    fn new(label: &str) -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time")
            .as_nanos();
        Self(std::env::temp_dir().join(format!(
            "shell-inst-{label}-{}-{nonce}.sqlite",
            std::process::id()
        )))
    }
    fn clone_file(&self) -> Self {
        let clone = Self::new("clone");
        fs::copy(&self.0, &clone.0).expect("copy synthetic database");
        clone
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
        let _ = fs::remove_file(format!("{}-journal", self.0.display()));
    }
}

#[test]
fn inst_auth_research_transition_lacks_independent_caller_authority() {
    // Diagnostic counterexample, not a security pass. The lab API takes only
    // operation ID, predecessor and schedule; no actor/device authorization
    // proof is supplied. Product-level INST-AUTH cannot be marked closed.
    let db = Fixture::new("auth-diagnostic");
    let before = initialize(&db.0).expect("synthetic init");
    let (receipt, _) = transition(
        &db.0, "anonymous-lab-call", before.checkpoint, Schedule::PeerUpdate,
        None, false,
    ).expect("the synthetic lab has no caller-identity gate");
    assert_eq!(receipt.epoch, 2);
}

#[test]
fn inst_clone_copies_can_each_advance_without_external_authority_election() {
    // Diagnostic counterexample to GLOBAL single-history uniqueness:
    // each independent copied database may be internally consistent.
    // This is not a production attack assertion; the lab lacks a witness.
    let source = Fixture::new("clone-source");
    let before = initialize(&source.0).expect("synthetic init");
    let clone = source.clone_file();

    let (left, _) = transition(
        &source.0, "left-successor", before.checkpoint, Schedule::PeerUpdate,
        None, false,
    ).expect("left local successor");
    let (right, _) = transition(
        &clone.0, "right-successor", before.checkpoint, Schedule::PeerUpdate,
        None, false,
    ).expect("right local successor");
    assert_eq!(inspect(&source.0).unwrap().shell_epoch, 2);
    assert_eq!(inspect(&clone.0).unwrap().shell_epoch, 2);
    assert_eq!(left.parent, right.parent);
    assert_ne!(left.operation_id, right.operation_id);
    assert_ne!(left.checkpoint, right.checkpoint);
}

fn mutate_nonce<F: FnOnce(&mut ChallengeBinding)>(
    accepted: &ChallengeBinding,
    change: F,
) -> Vec<u8> {
    let mut mutated = accepted.clone();
    change(&mut mutated);
    encode_challenge_nonce(&mutated)
}

#[test]
fn inst_composition_injective_nonce_binds_all_public_selectors() {
    let db = Fixture::new("nonce");
    initialize(&db.0).unwrap();
    let a = accepted_challenge(&db.0, ChallengeLeg::Classical).unwrap();
    let q = accepted_challenge(&db.0, ChallengeLeg::PostQuantum).unwrap();
    verify_challenge(&db.0, ChallengeLeg::Classical, &a).unwrap();
    verify_challenge(&db.0, ChallengeLeg::PostQuantum, &q).unwrap();

    let canonical = encode_challenge_nonce(&a);
    assert_ne!(canonical, encode_challenge_nonce(&q));
    let mutants: Vec<(&str, fn(&mut ChallengeBinding))> = vec![
        ("domain", |b| b.shell_domain_version.push('x')),
        ("provider", |b| b.provider_id.push('x')),
        ("version", |b| b.provider_version.push('x')),
        ("suite", |b| b.suite.push('x')),
        ("group", |b| b.opaque_group_id.push(1)),
        ("head", |b| b.accepted_shell_head[0] ^= 1),
        ("parent", |b| b.parent[0] ^= 1),
        ("epoch", |b| b.provider_epoch += 1),
        ("membership", |b| b.accepted_membership_digest[0] ^= 1),
        ("generator", |b| b.challenge_generator.push(1)),
        ("authenticator", |b| b.provider_state_authenticator[0] ^= 1),
        ("label", |b| b.exporter_label.push('x')),
        ("context", |b| b.exporter_context.push(1)),
        ("purpose", |b| b.challenge_purpose.push('x')),
        ("length", |b| b.output_length += 1),
    ];
    for (field, change) in mutants {
        assert_ne!(canonical, mutate_nonce(&a, change), "nonce omits {field}");
    }
}

#[test]
fn inst_composition_clone_replays_same_nonce_without_global_cache() {
    // Exact retry uses the same label/nonce. MSS26 allows this only as a
    // single cached evaluation, NOT as another adversarial oracle query.
    // No global cache/authority election is implemented in this lab.
    let source = Fixture::new("nonce-clone");
    initialize(&source.0).unwrap();
    let clone = source.clone_file();
    let a = accepted_challenge(&source.0, ChallengeLeg::Classical).unwrap();
    let b = accepted_challenge(&clone.0, ChallengeLeg::Classical).unwrap();
    assert_eq!(encode_challenge_nonce(&a), encode_challenge_nonce(&b));
}
