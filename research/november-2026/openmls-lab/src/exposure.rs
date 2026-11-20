//! Snapshot controls inside the *same composed database and transition path*.
use super::*;
use std::time::{SystemTime, UNIX_EPOCH};

struct SyntheticDatabase(std::path::PathBuf);
impl Drop for SyntheticDatabase {
    fn drop(&mut self) {
        // Remove only the exact synthetic database owned by this test.
        let _ = std::fs::remove_file(&self.0);
        let _ = std::fs::remove_file(format!("{}-journal", self.0.display()));
    }
}

fn exported32<P: OpenMlsProvider>(group: &MlsGroup, provider: &P, label: &str, context: &[u8]) -> [u8; 32] {
    group.export_secret(provider.crypto(), label, context, 32).unwrap().as_slice().try_into().unwrap()
}
fn kz<P: OpenMlsProvider, Q: OpenMlsProvider>(classical: &MlsGroup, cp: &P, pq: &MlsGroup, qp: &Q, context: &[u8]) -> [u8; 32] {
    let cs = exported32(classical, cp, "shell.classical-pq.classical/1", context);
    let qs = exported32(pq, qp, "shell.classical-pq.pq/1", context);
    combine_exported_secrets(&cs, &qs, context)
}
fn same_secret<P: OpenMlsProvider, Q: OpenMlsProvider>(a: &MlsGroup, ap: &P, b: &MlsGroup, bp: &Q) {
    let left = a
        .export_secret(
            ap.crypto(),
            "shell-observation-only",
            b"never-a-combiner",
            32,
        )
        .unwrap();
    let right = b
        .export_secret(
            bp.crypto(),
            "shell-observation-only",
            b"never-a-combiner",
            32,
        )
        .unwrap();
    // Compare only a boolean: do not print secret bytes on assertion failure.
    #[allow(clippy::manual_assert_eq)]
    {
        assert!(left == right);
    }
}
fn opens<P: OpenMlsProvider>(group: &mut MlsGroup, provider: &P, bytes: &[u8]) {
    let result = group
        .process_message(provider, protocol(bytes).unwrap())
        .unwrap();
    let ProcessedMessageContent::ApplicationMessage(message) = result.into_content() else {
        panic!("not application");
    };
    #[allow(clippy::manual_assert_eq)]
    {
        assert!(message.into_bytes() == b"synthetic-exposure-control");
    }
}

#[test]
#[allow(clippy::too_many_lines)]
fn composed_exposure_controls_include_continuing_and_renewed_compromise() {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "shell-pq-exposure-{}-{nonce}.sqlite",
        std::process::id()
    ));
    let _fixture = SyntheticDatabase(path.clone());
    let initial = initialize(&path).unwrap();
    let connection = store::open(&path).unwrap();
    let initial_state = read_state(&connection).unwrap();
    let pq_id = initial_state.legs[1].group_id.clone();
    let classical_id = initial_state.legs[0].group_id.clone();
    let stolen = store::snapshot(&connection);
    // Check snapshot scope explicitly: no collaborator private state included.
    let peer_tables: u64 = stolen
        .query_row(
            "SELECT COUNT(*) FROM sqlite_master WHERE name='shell_peer'",
            [],
            |r| r.get(0),
        )
        .unwrap();
    assert_eq!(peer_tables, 0);
    let stolen_provider = Provider::new(&stolen);
    let mut old = load_group(&stolen_provider, &pq_id).unwrap();
    let old_classical = load_group(&stolen_provider, &classical_id).unwrap();
    let canonical_provider = Provider::new(&connection);
    let canonical = load_group(&canonical_provider, &pq_id).unwrap();
    same_secret(&canonical, &canonical_provider, &old, &stolen_provider);
    drop(canonical);
    drop(connection);

    let (first, _) = transition(
        &path,
        "exposure-other",
        initial.checkpoint,
        Schedule::PeerUpdate,
        None,
        false,
    )
    .unwrap();
    accept(&mut old, &stolen_provider, &first.artifacts.pq_commit).unwrap();
    let connection = store::open(&path).unwrap();
    let state = read_state(&connection).unwrap();
    let mut peer = load_peer(&connection, 1, &state).unwrap();
    same_secret(&peer.group, &peer.provider, &old, &stolen_provider);
    let message = wire(
        &peer
            .group
            .create_message(&peer.provider, &peer.signer, b"synthetic-exposure-control")
            .unwrap(),
    )
    .unwrap();
    opens(&mut old, &stolen_provider, &message);

    // Negative healing control: after a normal PeerUpdate (no renewal of the
    // exposed canonical PQ leaf), the compromised snapshot still follows the
    // public Commit, converges on the same PQ exporter, and opens application
    // data. This is the A arm for the later ExposedLeafRenewal B arm.
    let peer_update_context = b"shell.exposure.peer-update.epoch2/1";
    let peer_after_first = load_peer(&store::open(&path).unwrap(), 1, &state).unwrap();
    let old_q_after_peer = exported32(&old, &stolen_provider, "shell.classical-pq.pq/1", peer_update_context);
    let peer_q_after_peer = exported32(&peer_after_first.group, &peer_after_first.provider, "shell.classical-pq.pq/1", peer_update_context);
    assert_eq!(old_q_after_peer, peer_q_after_peer);
    drop(connection);

    // Continuing compromise captures the new private leaf before Commit.
    // This uses a distinct Commit author and avoids OwnCommitMismatch.
    let mut continued = None;
    let (second, _) = run_transition(
        &path,
        "exposure-renew",
        first.checkpoint,
        Schedule::ExposedLeafRenewal,
        None,
        false,
        |connection| {
            let captured = store::snapshot(connection);
            let provider = Provider::new(&captured);
            let pending = load_group(&provider, &pq_id).unwrap();
            // A fresh uncommitted proposal is not a healed canonical epoch.
            same_secret(&pending, &provider, &old, &stolen_provider);
            continued = Some(captured);
        },
    )
    .unwrap();
    let continued = continued.unwrap();
    let continued_provider = Provider::new(&continued);
    let mut live_snapshot = load_group(&continued_provider, &pq_id).unwrap();
    let live_classical = load_group(&continued_provider, &classical_id).unwrap();
    proposal(
        &mut old,
        &stolen_provider,
        second.artifacts.pq_proposal.as_ref().unwrap(),
    )
    .unwrap();
    accept(
        &mut live_snapshot,
        &continued_provider,
        &second.artifacts.pq_commit,
    )
    .unwrap();
    let error = old
        .process_message(
            &stolen_provider,
            protocol(&second.artifacts.pq_commit).unwrap(),
        )
        .expect_err("old snapshot excluded");
    assert_eq!(
        format!("{error:?}"),
        "InvalidCommit(UpdatePathError(MissingSender))"
    );
    assert_eq!(old.epoch().as_u64(), 2);
    assert_eq!(live_snapshot.epoch().as_u64(), 3);
    let durable = inspect(&path).unwrap();
    assert_eq!(durable.classical_epoch, 3);
    assert_eq!(durable.pq_epoch, 3);
    let connection = store::open(&path).unwrap();
    let state = read_state(&connection).unwrap();
    let mut peer = load_peer(&connection, 1, &state).unwrap();
    let provider = Provider::new(&connection);
    let mut honest = load_group(&provider, &pq_id).unwrap();
    let honest_classical = load_group(&provider, &classical_id).unwrap();
    same_secret(&honest, &provider, &peer.group, &peer.provider);
    same_secret(&honest, &provider, &live_snapshot, &continued_provider);
    // Compose K_Z from real MLS exporters; secret bytes are never printed.
    let kz_context = b"shell.exposure.epoch3/1";
    let kz_honest = kz(&honest_classical, &provider, &honest, &provider, kz_context);
    let kz_continued = kz(&live_classical, &continued_provider, &live_snapshot, &continued_provider, kz_context);
    assert_eq!(kz_honest, kz_continued);
    let kz_old = kz(&old_classical, &stolen_provider, &old, &stolen_provider, kz_context);
    assert_ne!(kz_honest, kz_old);

    // Factor the composed result to isolate which real MLS leg changed.
    // Use the SAME context for every counterfactual and never print secrets.
    let c_honest = exported32(&honest_classical, &provider, "shell.classical-pq.classical/1", kz_context);
    let c_old = exported32(&old_classical, &stolen_provider, "shell.classical-pq.classical/1", kz_context);
    let q_honest = exported32(&honest, &provider, "shell.classical-pq.pq/1", kz_context);
    let q_old = exported32(&old, &stolen_provider, "shell.classical-pq.pq/1", kz_context);
    assert_ne!(c_honest, c_old);
    assert_ne!(q_honest, q_old);

    // Counterfactual A: freeze Classical at the honest epoch-3 exporter and
    // vary only PQ old->honest. Any K_Z difference is therefore PQ-causal.
    let kz_cf_pq_old = combine_exported_secrets(&c_honest, &q_old, kz_context);
    let kz_cf_pq_fresh = combine_exported_secrets(&c_honest, &q_honest, kz_context);
    assert_ne!(kz_cf_pq_old, kz_cf_pq_fresh);
    assert_eq!(kz_cf_pq_fresh, kz_honest);

    // Counterfactual B: freeze PQ at honest epoch 3 and vary only Classical.
    // This records the symmetric confound rather than hiding it.
    let kz_cf_classical_old = combine_exported_secrets(&c_old, &q_honest, kz_context);
    let kz_cf_classical_fresh = combine_exported_secrets(&c_honest, &q_honest, kz_context);
    assert_ne!(kz_cf_classical_old, kz_cf_classical_fresh);
    assert_eq!(kz_cf_classical_fresh, kz_honest);

    // Transcript-only reconstruction control.  The attacker is given the old
    // snapshot plus the exact public renewal proposal/commit bytes.  Derive a
    // public transcript digest and verify that treating public transcript data
    // as a substitute PQ input does not reproduce the honest K_Z.  This does
    // NOT prove computational infeasibility; it rules out the direct/public
    // transcript-as-secret reconstruction route in this executable model.
    let mut transcript_hasher = Sha256::new();
    transcript_hasher.update(second.artifacts.pq_proposal.as_ref().unwrap());
    transcript_hasher.update(&second.artifacts.pq_commit);
    let transcript_digest: [u8; 32] = transcript_hasher.finalize().into();
    let kz_public_transcript_candidate = combine_exported_secrets(&c_honest, &transcript_digest, kz_context);
    assert_ne!(kz_public_transcript_candidate, kz_honest);

    // The old snapshot's actual PQ exporter plus the full public transcript
    // still does not equal the fresh PQ exporter.  Bind both into a diagnostic
    // hash only; no secret bytes leave the test.
    let mut old_plus_public = Sha256::new();
    old_plus_public.update(q_old);
    old_plus_public.update(transcript_digest);
    let old_plus_public_digest: [u8; 32] = old_plus_public.finalize().into();
    assert_ne!(old_plus_public_digest, q_honest);

    // Temporal causality control: a snapshot taken after proposal creation but
    // before Commit has the same epoch exporter as the old snapshot. Fresh
    // key generation alone is therefore not healing; the committed transition
    // is required before the fresh contribution reaches the epoch exporter.
    let pending_snapshot = Provider::new(&continued);
    let pending_group = load_group(&pending_snapshot, &pq_id).unwrap();
    // `continued` has subsequently processed the Commit in this test, so use
    // the already-recorded pre-Commit invariant above (`same_secret(pending, old)`)
    // as the authoritative pre-Commit control; here assert the committed state
    // is now different from the old epoch exporter.
    let q_continued_committed = exported32(&pending_group, &pending_snapshot, "shell.classical-pq.pq/1", kz_context);
    assert_eq!(q_continued_committed, q_honest);
    assert_ne!(q_continued_committed, q_old);
    let future = wire(
        &peer
            .group
            .create_message(&peer.provider, &peer.signer, b"synthetic-exposure-control")
            .unwrap(),
    )
    .unwrap();
    assert!(matches!(
        protocol(&future).unwrap(),
        ProtocolMessage::PrivateMessage(_)
    ));
    opens(&mut honest, &provider, &future);
    opens(&mut live_snapshot, &continued_provider, &future);
    assert!(
        old.process_message(&stolen_provider, protocol(&future).unwrap())
            .is_err()
    );
    // Persistence control: advance honest state one more epoch without any
    // recapture of the pre-renewal attacker. The old snapshot must remain
    // unable to process future application traffic.
    drop(peer);
    drop(honest);
    drop(provider);
    drop(connection);
    let (third, _) = transition(
        &path,
        "exposure-post-heal-followup",
        second.checkpoint,
        Schedule::PeerUpdate,
        None,
        false,
    ).unwrap();
    let connection = store::open(&path).unwrap();
    let state = read_state(&connection).unwrap();
    assert_eq!(state.epoch, 4);
    let provider = Provider::new(&connection);
    let honest_epoch4 = load_group(&provider, &pq_id).unwrap();
    let honest_classical_epoch4 = load_group(&provider, &classical_id).unwrap();
    let mut peer_epoch4 = load_peer(&connection, 1, &state).unwrap();
    let epoch4_context = b"shell.exposure.epoch4/1";
    let kz_honest_epoch4 = kz(&honest_classical_epoch4, &provider, &honest_epoch4, &provider, epoch4_context);
    let old_q_epoch2 = exported32(&old, &stolen_provider, "shell.classical-pq.pq/1", epoch4_context);
    let honest_q_epoch4 = exported32(&honest_epoch4, &provider, "shell.classical-pq.pq/1", epoch4_context);
    assert_ne!(old_q_epoch2, honest_q_epoch4);
    let future_epoch4 = wire(&peer_epoch4.group.create_message(&peer_epoch4.provider, &peer_epoch4.signer, b"synthetic-exposure-control").unwrap()).unwrap();
    assert!(old.process_message(&stolen_provider, protocol(&future_epoch4).unwrap()).is_err());
    assert_eq!(third.epoch, 4);

    // Multi-epoch persistence: continue two additional honest peer updates.
    // The original pre-renewal snapshot is never recaptured or refreshed.
    drop(peer_epoch4);
    drop(honest_epoch4);
    drop(honest_classical_epoch4);
    drop(provider);
    drop(connection);
    let (fourth, _) = transition(&path, "exposure-post-heal-followup-2", third.checkpoint, Schedule::PeerUpdate, None, false).unwrap();
    assert_eq!(fourth.epoch, 5);
    let (fifth, _) = transition(&path, "exposure-post-heal-followup-3", fourth.checkpoint, Schedule::PeerUpdate, None, false).unwrap();
    assert_eq!(fifth.epoch, 6);
    let connection = store::open(&path).unwrap();
    let state = read_state(&connection).unwrap();
    assert_eq!(state.epoch, 6);
    let provider = Provider::new(&connection);
    let honest_epoch6 = load_group(&provider, &pq_id).unwrap();
    let epoch6_context = b"shell.exposure.epoch6/1";
    let old_q_epoch2_at6 = exported32(&old, &stolen_provider, "shell.classical-pq.pq/1", epoch6_context);
    let honest_q_epoch6 = exported32(&honest_epoch6, &provider, "shell.classical-pq.pq/1", epoch6_context);
    assert_ne!(old_q_epoch2_at6, honest_q_epoch6);
    let mut peer_epoch6 = load_peer(&connection, 1, &state).unwrap();
    let future_epoch6 = wire(&peer_epoch6.group.create_message(&peer_epoch6.provider, &peer_epoch6.signer, b"synthetic-exposure-control").unwrap()).unwrap();
    assert!(old.process_message(&stolen_provider, protocol(&future_epoch6).unwrap()).is_err());
    let _ = kz_honest_epoch4;

    let reexposed = store::snapshot(&connection);
    let rp = Provider::new(&reexposed);
    let rg = load_group(&rp, &pq_id).unwrap();
    same_secret(&honest_epoch6, &provider, &rg, &rp);
    let reexposed_q = exported32(&rg, &rp, "shell.classical-pq.pq/1", epoch6_context);
    assert_eq!(reexposed_q, honest_q_epoch6);
    let reexposed_classical = load_group(&rp, &classical_id).unwrap();
    let honest_classical_epoch6 = load_group(&provider, &classical_id).unwrap();
    let kz_reexposed = kz(&reexposed_classical, &rp, &rg, &rp, epoch6_context);
    let kz_honest_epoch6 = kz(&honest_classical_epoch6, &provider, &honest_epoch6, &provider, epoch6_context);
    assert_eq!(kz_reexposed, kz_honest_epoch6);
    println!(
        "EXPOSURE: old_snapshot_follows_other_update=true; no_exposed_leaf_renewal_compromise_persists=true; old_snapshot_rejected_after_own_renewal=MissingSender; continuing_compromise_follows=true; recapture_knows_current=true; kz_real_exporters_honest_eq_continued=true; kz_old_ne_honest=true; real_exporter_factorization=true; pq_only_counterfactual_changes_kz=true; classical_only_counterfactual_changes_kz=true; public_transcript_direct_reconstruction=false; old_plus_public_diagnostic_ne_fresh_pq=true; fresh_generation_precommit_not_healed=true; committed_fresh_contribution_reaches_exporter=true; reexposure_restores_current_kz_knowledge=true; healing_is_not_permanent_after_recapture=true; old_compromise_excluded_through_followup_epoch=true; old_compromise_excluded_through_epoch6=true; pq_pcs_qpt=NOT_PROVEN"
    );
}
