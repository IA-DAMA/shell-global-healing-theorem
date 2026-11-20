use rusqlite::{Connection, types::Value};
use shell_classical_pq_composition::{
    Inspection, Receipt, Schedule, committed_receipt, initialize, inspect, transition,
};
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::{Arc, Barrier},
    thread,
    time::{SystemTime, UNIX_EPOCH},
};

struct Database(PathBuf);
impl Database {
    fn new(label: &str) -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        Self(std::env::temp_dir().join(format!(
            "shell-cpq-{label}-{}-{nonce}.sqlite",
            std::process::id()
        )))
    }
    fn copy(source: &Self, label: &str) -> Self {
        let db = Self::new(label);
        fs::copy(&source.0, &db.0).unwrap();
        db
    }
}
impl Drop for Database {
    fn drop(&mut self) {
        // Exact synthetic file owned by this fixture only, never directories.
        let _ = fs::remove_file(&self.0);
        let _ = fs::remove_file(format!("{}-journal", self.0.display()));
    }
}
fn complete(state: &Inspection, epoch: u64) {
    assert_eq!(state.classical_epoch, epoch);
    assert_eq!(state.pq_epoch, epoch);
    assert_eq!(state.shell_epoch, epoch);
    assert_eq!(state.classical_peer_epoch, epoch);
    assert_eq!(state.pq_peer_epoch, epoch);
    assert_eq!(state.receipts, epoch - 1);
    assert_eq!(state.outbox, epoch - 1);
    assert_eq!(
        state.identities,
        vec![b"synthetic-A".to_vec(), b"synthetic-B".to_vec()]
    );
}
// Compare every persistent table row, including secret provider/peer state,
// entirely in memory. Never print or save the values/digests to a report.
fn rows(path: &Path) -> Vec<Vec<Vec<Value>>> {
    let conn = Connection::open(path).unwrap();
    let mut statement = conn
        .prepare("SELECT name FROM sqlite_master WHERE type='table' ORDER BY name")
        .unwrap();
    let tables: Vec<String> = statement
        .query_map([], |r| r.get(0))
        .unwrap()
        .map(Result::unwrap)
        .collect();
    tables
        .into_iter()
        .map(|name| {
            let name = name.replace('"', "\"\"");
            let count = conn
                .prepare(&format!("SELECT * FROM \"{name}\""))
                .unwrap()
                .column_count();
            let order = (1..=count)
                .map(|n| n.to_string())
                .collect::<Vec<_>>()
                .join(",");
            let mut query = conn
                .prepare(&format!("SELECT * FROM \"{name}\" ORDER BY {order}"))
                .unwrap();
            query
                .query_map([], |r| (0..count).map(|i| r.get(i)).collect())
                .unwrap()
                .map(Result::unwrap)
                .collect()
        })
        .collect()
}
fn raw_receipt(path: &Path) -> Vec<u8> {
    Connection::open(path)
        .unwrap()
        .query_row(
            "SELECT receipt FROM shell_receipt WHERE operation_id='matrix-operation'",
            [],
            |r| r.get(0),
        )
        .unwrap()
}

#[test]
#[allow(clippy::too_many_lines)]
fn all_observed_write_boundaries_and_lost_responses_recover() {
    let baseline = Database::new("baseline");
    let initial = initialize(&baseline.0).unwrap();
    complete(&initial, 1);
    let advanced = Database::copy(&baseline, "advanced");
    transition(
        &advanced.0,
        "prelude",
        initial.checkpoint,
        Schedule::PeerUpdate,
        None,
        false,
    )
    .unwrap();
    let mut evidence = Vec::new();
    for (base, schedule, name) in [
        (&baseline, Schedule::PeerUpdate, "peer"),
        (&advanced, Schedule::ExposedLeafRenewal, "renew"),
    ] {
        let before = inspect(&base.0).unwrap();
        let before_rows = rows(&base.0);
        let count_db = Database::copy(base, "count");
        let (_, labels) = transition(
            &count_db.0,
            "matrix-operation",
            before.checkpoint,
            schedule,
            None,
            false,
        )
        .unwrap();
        assert!(labels.len() > 30);
        assert_eq!(labels.last().unwrap(), "COMMIT/BEFORE");
        for required in [
            "openmls_group_data",
            "shell_peer",
            "shell_state",
            "shell_outbox",
            "shell_receipt",
        ] {
            assert!(
                labels.iter().any(|label| label.starts_with(required)),
                "missing boundary {required}"
            );
        }
        for (index, label) in labels.iter().enumerate() {
            let crashed = Database::copy(base, "crashed");
            let output = Command::new(env!("CARGO_BIN_EXE_crash_worker"))
                .arg(&crashed.0)
                .arg(name)
                .arg((index + 1).to_string())
                .arg("pre")
                .output()
                .unwrap();
            assert!(!output.status.success());
            assert!(
                output.stderr.is_empty(),
                "worker stage error, not intended abort"
            );
            assert!(
                String::from_utf8_lossy(&output.stdout)
                    .contains(&format!("CRASH_AT={}:{label}", index + 1)),
                "crash marker mismatch"
            );
            let reopened = inspect(&crashed.0).unwrap();
            assert_eq!(reopened, before);
            #[allow(clippy::manual_assert_eq)]
            {
                assert!(
                    rows(&crashed.0) == before_rows,
                    "durable provider state differs after rollback"
                );
            }
            let (receipt, retry_labels) = transition(
                &crashed.0,
                "matrix-operation",
                before.checkpoint,
                schedule,
                None,
                false,
            )
            .unwrap();
            assert_eq!(retry_labels, labels);
            complete(&inspect(&crashed.0).unwrap(), before.shell_epoch + 1);
            let raw = raw_receipt(&crashed.0);
            let (retry, no_writes) = transition(
                &crashed.0,
                "matrix-operation",
                before.checkpoint,
                schedule,
                None,
                false,
            )
            .unwrap();
            assert_eq!(receipt, retry);
            assert!(no_writes.is_empty());
            assert_eq!(raw, serde_json::to_vec(&retry).unwrap());
        }
        let committed = Database::copy(base, "lost-response");
        let output = Command::new(env!("CARGO_BIN_EXE_crash_worker"))
            .arg(&committed.0)
            .arg(name)
            .arg("0")
            .arg("post")
            .output()
            .unwrap();
        assert!(!output.status.success());
        assert!(output.stderr.is_empty());
        assert!(String::from_utf8_lossy(&output.stdout).contains("CRASH_AT=COMMIT/AFTER"));
        complete(&inspect(&committed.0).unwrap(), before.shell_epoch + 1);
        let receipt = committed_receipt(&committed.0, "matrix-operation").unwrap();
        let raw = raw_receipt(&committed.0);
        let after_rows = rows(&committed.0);
        let (retry, no_writes) = transition(
            &committed.0,
            "matrix-operation",
            before.checkpoint,
            schedule,
            None,
            false,
        )
        .unwrap();
        assert!(no_writes.is_empty());
        assert_eq!(receipt, retry);
        assert_eq!(raw, serde_json::to_vec(&retry).unwrap());
        #[allow(clippy::manual_assert_eq)]
        {
            assert!(after_rows == rows(&committed.0));
        }
        println!(
            "MATRIX schedule={name} predecessor={} precommit_boundaries={} rollback_and_retry=PASS postcommit=PASS",
            before.shell_epoch,
            labels.len()
        );
        evidence.push(serde_json::json!({"schedule":name,"predecessor_epoch":before.shell_epoch,"precommit_boundaries":labels.len(),"labels":labels,"each_precommit_crash_rollback_all_rows_and_retry":"PASS","postcommit_exact_bytes_retry":"PASS"}));
    }
    // Generated observations only: fixed path inside ignored target directory.
    let target = Path::new(env!("CARGO_MANIFEST_DIR")).join("target");
    fs::create_dir_all(&target).unwrap();
    fs::write(
        target.join("crash-observations.json"),
        serde_json::to_vec_pretty(&evidence).unwrap(),
    )
    .unwrap();
}

#[test]
fn competing_successors_have_one_winner_and_explicit_conflict() {
    let db = Database::new("concurrent");
    let initial = initialize(&db.0).unwrap();
    let barrier = Arc::new(Barrier::new(2));
    let jobs: Vec<_> = ["operation-A", "operation-B"]
        .iter()
        .map(|id| {
            let barrier = Arc::clone(&barrier);
            let path = db.0.clone();
            thread::spawn(move || {
                barrier.wait();
                transition(
                    &path,
                    id,
                    initial.checkpoint,
                    Schedule::PeerUpdate,
                    None,
                    false,
                )
            })
        })
        .collect();
    let results: Vec<_> = jobs.into_iter().map(|j| j.join().unwrap()).collect();
    assert_eq!(results.iter().filter(|r| r.is_ok()).count(), 1);
    assert!(
        results
            .iter()
            .any(|r| matches!(r,Err(error) if error=="stale_predecessor"))
    );
    complete(&inspect(&db.0).unwrap(), 2);
}

#[test]
fn two_epochs_and_historical_retry_and_operation_id_equivocation() {
    let db = Database::new("two-epochs");
    let initial = initialize(&db.0).unwrap();
    let (first, _) = transition(
        &db.0,
        "first",
        initial.checkpoint,
        Schedule::PeerUpdate,
        None,
        false,
    )
    .unwrap();
    let (second, _) = transition(
        &db.0,
        "second",
        first.checkpoint,
        Schedule::ExposedLeafRenewal,
        None,
        false,
    )
    .unwrap();
    complete(&inspect(&db.0).unwrap(), 3);
    let (retry, writes) = transition(
        &db.0,
        "first",
        initial.checkpoint,
        Schedule::PeerUpdate,
        None,
        false,
    )
    .unwrap();
    assert_eq!(retry, first);
    assert!(writes.is_empty());
    assert_eq!(
        transition(
            &db.0,
            "first",
            initial.checkpoint,
            Schedule::ExposedLeafRenewal,
            None,
            false
        )
        .unwrap_err(),
        "operation_id_equivocation"
    );
    assert_eq!(
        transition(
            &db.0,
            "third",
            first.checkpoint,
            Schedule::PeerUpdate,
            None,
            false
        )
        .unwrap_err(),
        "stale_predecessor"
    );
    assert_eq!(inspect(&db.0).unwrap().checkpoint, second.checkpoint);
}

#[test]
fn tampered_receipt_and_matching_outbox_do_not_bypass_checkpoint() {
    let db = Database::new("tamper");
    let initial = initialize(&db.0).unwrap();
    let (mut receipt, _) = transition(
        &db.0,
        "tamper",
        initial.checkpoint,
        Schedule::PeerUpdate,
        None,
        false,
    )
    .unwrap();
    receipt.artifacts.pq_commit[0] ^= 1;
    let bytes = serde_json::to_vec(&receipt).unwrap();
    let conn = Connection::open(&db.0).unwrap();
    conn.execute("UPDATE shell_receipt SET receipt=?1", [&bytes])
        .unwrap();
    conn.execute("UPDATE shell_outbox SET receipt=?1", [&bytes])
        .unwrap();
    assert_eq!(inspect(&db.0).unwrap_err(), "artifact_mismatch");
    assert_eq!(
        transition(
            &db.0,
            "tamper",
            initial.checkpoint,
            Schedule::PeerUpdate,
            None,
            false
        )
        .unwrap_err(),
        "artifact_mismatch"
    );
}

#[test]
fn receipt_rebind_to_different_request_fails_closed() {
    let db = Database::new("receipt");
    let initial = initialize(&db.0).unwrap();
    transition(
        &db.0,
        "matrix-operation",
        initial.checkpoint,
        Schedule::PeerUpdate,
        None,
        false,
    )
    .unwrap();
    let mut receipt: Receipt = serde_json::from_slice(&raw_receipt(&db.0)).unwrap();
    receipt.schedule = Schedule::ExposedLeafRenewal;
    let bytes = serde_json::to_vec(&receipt).unwrap();
    let conn = Connection::open(&db.0).unwrap();
    conn.execute("UPDATE shell_receipt SET receipt=?1", [&bytes])
        .unwrap();
    conn.execute("UPDATE shell_outbox SET receipt=?1", [&bytes])
        .unwrap();
    assert_eq!(inspect(&db.0).unwrap_err(), "receipt_mismatch");
}

#[test]
fn historical_receipt_artifact_tampering_fails_closed() {
    let db = Database::new("historical-tamper");
    let initial = initialize(&db.0).unwrap();
    let (mut first, _) = transition(
        &db.0,
        "first",
        initial.checkpoint,
        Schedule::PeerUpdate,
        None,
        false,
    )
    .unwrap();
    transition(
        &db.0,
        "second",
        first.checkpoint,
        Schedule::ExposedLeafRenewal,
        None,
        false,
    )
    .unwrap();
    first.artifacts.classical_commit[0] ^= 1;
    let bytes = serde_json::to_vec(&first).unwrap();
    let connection = Connection::open(&db.0).unwrap();
    connection
        .execute(
            "UPDATE shell_receipt SET receipt=?1 WHERE operation_id='first'",
            [&bytes],
        )
        .unwrap();
    connection
        .execute(
            "UPDATE shell_outbox SET receipt=?1 WHERE operation_id='first'",
            [&bytes],
        )
        .unwrap();
    assert_eq!(
        committed_receipt(&db.0, "first").unwrap_err(),
        "artifact_mismatch"
    );
    assert_eq!(
        transition(
            &db.0,
            "first",
            initial.checkpoint,
            Schedule::PeerUpdate,
            None,
            false
        )
        .unwrap_err(),
        "artifact_mismatch"
    );
}

#[test]
fn concurrent_duplicate_id_returns_one_identical_canonical_receipt() {
    let db = Database::new("duplicate-concurrent");
    let initial = initialize(&db.0).unwrap();
    let barrier = Arc::new(Barrier::new(2));
    let jobs: Vec<_> = (0..2)
        .map(|_| {
            let barrier = Arc::clone(&barrier);
            let path = db.0.clone();
            thread::spawn(move || {
                barrier.wait();
                transition(
                    &path,
                    "same-operation",
                    initial.checkpoint,
                    Schedule::PeerUpdate,
                    None,
                    false,
                )
                .unwrap()
            })
        })
        .collect();
    let results: Vec<_> = jobs.into_iter().map(|job| job.join().unwrap()).collect();
    assert_eq!(results[0].0, results[1].0);
    assert_eq!(
        results.iter().filter(|result| result.1.is_empty()).count(),
        1
    );
    complete(&inspect(&db.0).unwrap(), 2);
}
