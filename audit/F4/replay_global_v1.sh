#!/usr/bin/env bash
set -euo pipefail
proof=$(cd "$(dirname "$0")/../.." && pwd)
native=$(cd "${1:?use a checkout containing the pinned native commit}" && pwd)
gitcmd=${F4_GIT:-git}
pin=476bd8f1f4755ae2f6a689d23a937ba2573434a4
out=$(mktemp -d)
printf 'Artifacts %s\n' "$out"
mkdir -p "$out/native" "$out/ec" "$out/liveness"
(cd "$native"; "$gitcmd" -c core.autocrlf=false archive --format=tar "$pin" research/protocol_shell/pq_group_chat_lab research/ghost_manifest_protocol/payload_schemas third_party/openmls-0.9.0 </dev/null) | tar -xf - -C "$out/native"
cd "$out/native/research/protocol_shell/pq_group_chat_lab"
export CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_DEV_INCREMENTAL=false
cargo test --locked --offline --lib --features android-keystore-storage,direct-policy-lab staged_remove_and_fresh_join_primitives_preserve_survivors_without_publishing_partial_chain -- --test-threads=1 --show-output >"$out/native.log" 2>&1 || { tail -30 "$out/native.log"; exit 1; }
grep -F 'test result: ok. 1 passed; 0 failed; 0 ignored;' "$out/native.log"
grep -Fx 'F4_REPLACEMENT_PARTIAL=3' "$out/native.log"
grep -Fx 'F4_REPLACEMENT_RETRIED=4' "$out/native.log"
grep -Fx 'F4_REPLACEMENT_EXPORT_EQUAL=[false,true,true]' "$out/native.log"
touch "$out/.synthetic-cc"
cargo rustc --locked --offline --profile dev --lib \
  --features android-keystore-storage,direct-policy-lab -- \
  --emit=mir="$out/ordinary.mir" \
  >"$out/mir.log" 2>&1 || { tail -20 "$out/mir.log"; exit 1; }
RUSTC_BOOTSTRAP=1 cargo rustc --locked --offline --profile dev --lib \
  --features android-keystore-storage,direct-policy-lab -- \
  -Zdump-mir=offline_product::lifecycle::prepare \
  -Zdump-mir-dir="$out/liveness" -Zmir-include-spans=yes \
  >"$out/liveness.log" 2>&1 || { tail -20 "$out/liveness.log"; exit 1; }
python3 -B "$proof/audit/F4/verify_remove_gate.py" "$out/ordinary.mir" "$out"
python3 -B "$proof/audit/F4/verify_snapshot_selector.py" "$out/ordinary.mir" "$out"
python3 -B "$proof/audit/F4/probe_public_epochs.py" "$out"
python3 -B "$proof/audit/F4/verify_selected_possession.py" "$out"
python3 -B "$proof/audit/F4/verify_l1_window.py" "$out/native" "$out/liveness"
python3 -B "$proof/audit/F4/verify_l2_source_scope.py" "$out/native"
python3 -B "$proof/audit/F4/verify_l4_refinement_scope.py" "$out/native"
cd "$proof"
python3 -B -m unittest discover -s formal/tools -p 'test_f4*contract*.py'
python3 -B research/november-2026/compare_singleton_schedule.py "$native" --git "$gitcmd"
python3 -B audit/F4/check_cc_prefix.py
cp formal/easycrypt/*.ec "$out/ec/"
F4_EC_DIR="$out/ec" bash research/november-2026/verify_easycrypt.sh >"$out/easycrypt.log" 2>&1 || { tail -c 2500 "$out/easycrypt.log"; exit 1; }
grep -Fx 'EASYCRYPT_ALL_83_ACCEPTED=true' "$out/easycrypt.log"
python3 -B audit/F4/check_cc_prefix.py --negative "$out/ec"
sed 's/if p = AfterRollback then 1 else 0/if p = AfterRollback then 0 else 0/' "$out/ec/F4_CC_Selected_Snapshot.ec" > "$out/ec/WrongSnapshotPhase.ec"
if (cd "$out/ec" && easycrypt WrongSnapshotPhase.ec) > "$out/phase-negative.log" 2>&1; then
  echo 'phase-insensitive reconstruction unexpectedly passed' >&2
  exit 1
fi
proof_line=$(grep -n '^proof. by case: p;' "$out/ec/WrongSnapshotPhase.ec" | cut -d: -f1)
grep -F "[critical] [WrongSnapshotPhase.ec: line $proof_line " "$out/phase-negative.log" | grep -Fq 'cannot prove goal'
printf 'REJECTED=omit merge phase at phase_recovers_live_epoch\n'
sed 's/with t=T2Merged => \[OldState;SuccessorState;SuccessorExporter;/with t=T2Merged => [OldState;SuccessorExporter;/' \
  "$out/ec/F4_L1_Process_Window.ec" > "$out/ec/WrongL1Successor.ec"
if (cd "$out/ec" && easycrypt WrongL1Successor.ec) >"$out/l1-negative.log" 2>&1; then
  echo 'omitting the merged successor unexpectedly passed' >&2
  exit 1
fi
proof_line=$(grep -n '^proof. by case: t. qed.' "$out/ec/WrongL1Successor.ec" | head -1 | cut -d: -f1)
grep -F "[critical] [WrongL1Successor.ec: line $proof_line " "$out/l1-negative.log" | grep -Fq 'cannot close goals'
printf 'REJECTED=omit T2 successor at successor_is_accounted\n'
sed 's/(state.`1 \/\\ f4_sa_source_public_step state.`2 event,/(true \/\\ f4_sa_source_public_step state.`2 event,/' \
  "$out/ec/F4_Native_Source_Semantic_Coverage.ec" > "$out/ec/WrongCoverageMemory.ec"
if (cd "$out/ec" && easycrypt WrongCoverageMemory.ec) >"$out/l2-negative.log" 2>&1; then
  echo 'allowing a later step to erase a coverage gap unexpectedly passed' >&2
  exit 1
fi
proof_line=$(grep -n -m1 -F '  rewrite /f4_sa_fold_step.' "$out/ec/WrongCoverageMemory.ec" | cut -d: -f1)
grep -F "[critical] [WrongCoverageMemory.ec: line $proof_line " "$out/l2-negative.log" | grep -Eq 'cannot (close goals|prove goal|save an incomplete proof)'
printf 'REJECTED=forget source coverage gap at f4_sa_gap_never_disappears_under_any_finite_suffix\n'
sed 's/\[OldCapture; Welcome; Grant; CopyDevice; Retry\]/[OldCapture; Welcome; CopyDevice; Retry]/' \
  "$out/ec/F4_L3_Joint_Copy_Closure.ec" > "$out/ec/WrongL3OutputLedger.ec"
if (cd "$out/ec" && easycrypt WrongL3OutputLedger.ec) >"$out/l3-negative.log" 2>&1; then
  echo 'omitting the peer grant unexpectedly passed' >&2
  exit 1
fi
proof_line=$(grep -n '^lemma l3_cross_install_combination_reaches_output' "$out/ec/WrongL3OutputLedger.ec" | cut -d: -f1)
failure_line=$((proof_line + 4))
grep -F "[critical] [WrongL3OutputLedger.ec: line $failure_line " "$out/l3-negative.log" | grep -Eq 'cannot (close goals|prove goal|save an incomplete proof)'
printf 'REJECTED=omit peer grant at l3_cross_install_combination_reaches_output\n'
sed '/^op l4_keep_coverage /c\op l4_keep_coverage (old good : bool) = good.' \
  "$out/ec/F4_L4_Product_Game_Refinement.ec" > "$out/ec/WrongL4CoverageMemory.ec"
if (cd "$out/ec" && easycrypt WrongL4CoverageMemory.ec) >"$out/l4-negative.log" 2>&1; then
  echo 'allowing a later step to erase an L4 divergence unexpectedly passed' >&2
  exit 1
fi
proof_line=$(grep -n '^  move=> h; apply ih;' "$out/ec/WrongL4CoverageMemory.ec" | cut -d: -f1)
grep -F "[critical] [WrongL4CoverageMemory.ec: line $proof_line " "$out/l4-negative.log" | grep -Eq 'cannot (close goals|prove goal|save an incomplete proof)'
printf 'REJECTED=forget L4 divergence at l4_gap_never_disappears\n'
sed '/^module L5G1(/,/^}.$/ s/H.real(g.`1,g.`2)/H.real(g.`1,aux)/' \
  "$out/ec/F4_L5_QPT_Blackbox_Bridge.ec" > "$out/ec/WrongL5AuxThread.ec"
if (cd "$out/ec" && easycrypt WrongL5AuxThread.ec) >"$out/l5-negative.log" 2>&1; then
  echo 'discarding the generator residual qaux unexpectedly passed' >&2
  exit 1
fi
proof_line=$(grep -n '^proof. by sim. qed.' "$out/ec/WrongL5AuxThread.ec" | sed -n '2p' | cut -d: -f1)
grep -F "[critical] [WrongL5AuxThread.ec: line $proof_line " "$out/l5-negative.log" | grep -Eq 'cannot (close goals|prove goal|save an incomplete proof)|not able to process'
printf 'REJECTED=discard generator residual qaux at l5_g1_generator_ideal_exact\n'
sed 's/eps_pq + eps_ref + bad_cc + eps_svc + eps_env/eps_pq + eps_ref + bad_cc + eps_env/' \
  "$out/ec/F4_L6_Global_Conditional_Bound.ec" > "$out/ec/WrongL6MissingService.ec"
if (cd "$out/ec" && easycrypt WrongL6MissingService.ec) >"$out/l6-negative.log" 2>&1; then
  echo 'omitting eps_svc from the global bound unexpectedly passed' >&2
  exit 1
fi
proof_line=$(grep -n '^  by rewrite -order.' "$out/ec/WrongL6MissingService.ec" | cut -d: -f1)
grep -F "[critical] [WrongL6MissingService.ec: line $proof_line " "$out/l6-negative.log" | grep -Eq 'cannot (close goals|prove goal|save an incomplete proof)|nothing to rewrite'
printf 'REJECTED=omit eps_svc at f4_global_conditional_qpt_bound\n'
