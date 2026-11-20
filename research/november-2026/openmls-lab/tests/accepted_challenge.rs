//! INST-CHALLENGE adversarial checks against persisted OpenMLS laboratory state.
//! All identities are synthetic. No private key or exporter is printed.
use shell_classical_pq_composition::{
    ChallengeBinding, ChallengeLeg, Schedule, accepted_challenge, initialize,
    transition, verify_challenge,
};
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        Self(std::env::temp_dir().join(format!(
            "shell-f4-{}-{nonce}.sqlite",
            std::process::id()
        )))
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
        let _ = std::fs::remove_file(format!("{}-journal", self.0.display()));
    }
}

fn mutated<F: FnOnce(&mut ChallengeBinding)>(
    seed: &ChallengeBinding,
    change: F,
) -> ChallengeBinding {
    let mut value = seed.clone();
    change(&mut value);
    value
}

#[test]
fn real_accepted_openmls_views_agree_and_f4_mutations_fail_closed() {
    let db = Fixture::new();
    initialize(&db.0).unwrap();
    for leg in [ChallengeLeg::Classical, ChallengeLeg::PostQuantum] {
        let canonical = accepted_challenge(&db.0, leg).unwrap();
        assert!(canonical.accepted);
        assert_eq!(canonical.output_length, 32);
        verify_challenge(&db.0, leg, &canonical).unwrap();

        let mutants = vec![
            ("C1 epoch", mutated(&canonical, |b| b.provider_epoch += 1)),
            ("C2 membership", mutated(&canonical, |b| b.accepted_membership_digest[0] ^= 1)),
            ("C3 generator", mutated(&canonical, |b| b.challenge_generator[0] ^= 1)),
            ("C4 group", mutated(&canonical, |b| b.opaque_group_id[0] ^= 1)),
            ("C5 provider", mutated(&canonical, |b| b.provider_version.push_str("-wrong"))),
            ("C6 exporter label", mutated(&canonical, |b| b.exporter_label.push_str("-wrong"))),
            ("C7 exporter context", mutated(&canonical, |b| b.exporter_context.push(0))),
            ("C8 head", mutated(&canonical, |b| b.accepted_shell_head[0] ^= 1)),
            ("C8 parent", mutated(&canonical, |b| b.parent[0] ^= 1)),
            ("C9 length", mutated(&canonical, |b| b.output_length = 64)),
            ("C9 purpose", mutated(&canonical, |b| b.challenge_purpose.push_str("-wrong"))),
            ("C10 unaccepted", mutated(&canonical, |b| b.accepted = false)),
            ("domain", mutated(&canonical, |b| b.shell_domain_version.push_str("-wrong"))),
            ("suite", mutated(&canonical, |b| b.suite.push_str("-wrong"))),
            ("state authenticator", mutated(&canonical, |b| b.provider_state_authenticator[0] ^= 1)),
        ];
        for (label, bad) in mutants {
            assert_eq!(
                verify_challenge(&db.0, leg, &bad),
                Err("bad_challenge".into()),
                "failed to reject {label} on {leg:?}"
            );
        }
        verify_challenge(&db.0, leg, &canonical).unwrap();
    }
}

#[test]
fn accepted_epoch_advancement_invalidates_old_challenge() {
    let db = Fixture::new();
    let baseline = initialize(&db.0).unwrap();
    let before_c = accepted_challenge(&db.0, ChallengeLeg::Classical).unwrap();
    let before_pq = accepted_challenge(&db.0, ChallengeLeg::PostQuantum).unwrap();
    transition(
        &db.0,
        "f4-advance",
        baseline.checkpoint,
        Schedule::PeerUpdate,
        None,
        false,
    )
    .unwrap();

    for (leg, old) in [
        (ChallengeLeg::Classical, before_c),
        (ChallengeLeg::PostQuantum, before_pq),
    ] {
        assert_eq!(
            verify_challenge(&db.0, leg, &old),
            Err("bad_challenge".into())
        );
        let current = accepted_challenge(&db.0, leg).unwrap();
        assert_ne!(old, current);
        verify_challenge(&db.0, leg, &current).unwrap();
    }
}

#[test]
fn two_distinct_legs_cannot_reuse_the_same_challenge() {
    let db = Fixture::new();
    initialize(&db.0).unwrap();
    let pq = accepted_challenge(&db.0, ChallengeLeg::PostQuantum).unwrap();
    assert_eq!(
        verify_challenge(&db.0, ChallengeLeg::Classical, &pq),
        Err("bad_challenge".into())
    );
}
