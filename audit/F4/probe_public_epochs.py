"""Check two *public epoch numbers* in a synthetic test after SQL rollback.
Only accepts the disposable source directory made by replay_global_v1.sh.
Always restores those source bytes on exit. No MLS bytes are serialized.
"""
from pathlib import Path
import subprocess
import sys

from retained_observation_fixture import MARKERS, extend_native

CRATE = Path("research/protocol_shell/pq_group_chat_lab")
ANCHOR = "        b.successor_group_info = Binary(probe?);"
PREMERGE = "        let probe = (|| {"
BEFORE_PROBE = r"""        #[cfg(test)]
        let durable_cut = if b.kind == "REMOVE" {
            let restored = MlsGroup::load(provider.storage(), group.group_id())
                .expect("synthetic read failed").expect("synthetic group missing");
            assert!(restored.pending_commit().is_some());
            assert!(group.pending_commit().is_some());
            assert_eq!(restored.epoch(), group.epoch());
            assert!(matches!(match_native_snapshot(c, &current), Err(ref e)
                if e == "product_current_private_member_epoch"));
            Some(restored.epoch().as_u64())
        } else { None };
"""
INSERT = r'''        #[cfg(test)]
        if probe.is_ok() && b.kind == "REMOVE" {
            let restored = MlsGroup::load(provider.storage(), group.group_id())
                .expect("synthetic read failed").expect("synthetic group missing");
            let durable_epoch = restored.epoch().as_u64();
            let memory_epoch = group.epoch().as_u64();
            assert_eq!(durable_cut, Some(durable_epoch));
            assert_eq!(durable_epoch.checked_add(1), Some(memory_epoch));
            assert!(restored.pending_commit().is_some());
            assert!(group.pending_commit().is_none());
            assert!(matches!(match_native_snapshot(c, &current), Err(ref e)
                if e == "product_current_private_member_epoch"));
            println!("F4_CC_PUBLIC_EPOCHS=disk_predecessor,memory_successor");
        }
'''


BEFORE = '    let op = "47474747-4747-4747-4747-474747474747";'
AFTER = """    let removal: lifecycle::ProductLifecycleRequest =
        serde_json::from_value(prepared["prepared"].clone()).unwrap();
    let (removal_facts, _) = lifecycle::public_checked(&removal).unwrap();"""
SETUP = r"""    let inspected = ProductRequest::ExportGroupInfo {};
    let selector = lab.context_wire(0, &inspected, lab.current(0, &third_receipt,
        third.request.successor_group_info.clone(), third.request.successor_context.clone(),
        third_facts.successor_roster.clone()));
    let observe_selected = || {
        crate::offline_activation::with_product_fixture_clock(&clock(1000), || {
            crate::android_storage::with_custody(&lab.group[0], &MATERIAL, || {
                let connection = store::open(&lab.group[0])?;
                f4_exposure::capture_verified_full_state(&connection, &selector,
                    &lab.contexts[0], &clock(1000), &inspected, 1).map(|_| ())
            })
        })
    };
    observe_selected().expect("admitted before prepare");
"""
CHECK = r"""    assert!(matches!(observe_selected(), Err(ref e)
        if e == "product_current_private_member_epoch"));
    println!("F4_CC_SELECTED_CAPTURE=accepted_before,refused_pending");
"""


def main(out):
    if not (out / "native.log").is_file() or not (out / ".synthetic-cc").is_file():
        raise ValueError("requires a private reproduction directory")
    crate = out / "native" / CRATE
    source = crate / "src/offline_product_lifecycle.rs"
    original = source.read_bytes()
    text = original.decode("utf-8")
    if text.count(ANCHOR) != 1 or text.count(PREMERGE) != 1:
        raise ValueError("source anchor differs")
    fixture = crate / "src/offline_product_reentry_tests.rs"
    raw_fixture = fixture.read_bytes()
    fixture_text = raw_fixture.decode("utf-8")
    if fixture_text.count(BEFORE) != 1 or fixture_text.count(AFTER) != 1:
        raise ValueError("fixture differs")
    log = out / "epochs.log"
    try:
        lifecycle, test = extend_native(
            text.replace(PREMERGE, BEFORE_PROBE + PREMERGE).replace(ANCHOR, INSERT + ANCHOR),
            fixture_text.replace(BEFORE, SETUP + BEFORE).replace(AFTER, CHECK + AFTER),
        )
        source.write_text(lifecycle, encoding="utf-8")
        fixture.write_text(test, encoding="utf-8")
        with log.open("wb") as sink:
            result = subprocess.run(["cargo", "test", "--offline", "--locked", "--lib", "--features",
                                     "android-keystore-storage,direct-policy-lab",
                                     "staged_remove_and_fresh_join_primitives_preserve_survivors_without_publishing_partial_chain",
                                     "--", "--test-threads=1", "--show-output"], cwd=crate,
                                    stderr=subprocess.STDOUT, stdout=sink)
    finally:
        source.write_bytes(original)
        fixture.write_bytes(raw_fixture)
    output = log.read_text()
    if result.returncode or "test result: ok. 1 passed; 0 failed; 0 ignored;" not in output:
        raise ValueError(output[-2500:])
    marker = "F4_CC_PUBLIC_EPOCHS=disk_predecessor,memory_successor"
    count = output.splitlines().count(marker)
    if count == 0 or "F4_REPLACEMENT_EXPORT_EQUAL=[false,true,true]" not in output.splitlines():
        raise ValueError("expected the epoch measurement and baseline comparison")
    capture = "F4_CC_SELECTED_CAPTURE=accepted_before,refused_pending"
    if output.splitlines().count(capture) != 1:
        raise ValueError("missing matched observations")
    seen = [line for line in output.splitlines() if line in MARKERS]
    if seen != list(MARKERS):
        raise ValueError("missing or out-of-order capability checks")
    for line in seen:
        print(line)
    print(capture)
    print(f"{marker} observations={count}")


if __name__ == "__main__":
    main(Path(sys.argv[1]).resolve())
