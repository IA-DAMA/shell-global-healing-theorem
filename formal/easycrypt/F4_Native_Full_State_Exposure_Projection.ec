require import AllCore Int List.
require import F4_Native_Accepted_Trace_Refinement.
require import F4_Adversarial_Query_Ledger.

(* F4 M2 source-shaped SUCCESSFUL native corruption projection.
   Rust Product: offline_product_f4_exposure.rs issues an opaque, test-only
   F4NativeCapturedFullState only after signed CURRENT validation, protected
   SQLite MlsGroup::load, exporter consistency and a second acceptance
   validation. This module maps the metadata of SUCH A SUCCESSFUL RESULT
   into the adversarial query ledger. It neither models a synthetic success
   Boolean nor assumes PCS or a FreshQ backend predicate.

   IMPORTANT: the universal Rust-source -> EasyCrypt simulation for ALL
   successful/failed calls and all erased/retained secrets remains OPEN.
   This file proves the shape of the emitted exposure, not code extraction.
*)

type f4_native_capture_projection = {
  f4_cp_state : f4_native_trace_point;
  f4_cp_index : int;
  f4_cp_member : f4_member_id;
  f4_cp_device : f4_device_id;
  f4_cp_secret_kind : f4_secret_kind_id;
}.

(* Source projection: capture is a successful Corrupt of the native epoch,
   never a caller-supplied claimed epoch. No success flag is introduced. *)
op f4_captured_native_corrupt_query
    (cp : f4_native_capture_projection) : f4_query_record =
 {| f4_q_index = cp.`f4_cp_index;
    f4_q_epoch = cp.`f4_cp_state.`f4_nt_epoch;
    f4_q_member = cp.`f4_cp_member;
    f4_q_device = cp.`f4_cp_device;
    f4_q_secret_kind = cp.`f4_cp_secret_kind;
    f4_q_corrupt = true;
    f4_q_reveal = false |}.

op f4_challenge_at_native_state
    (point : f4_native_trace_point)
    (cp : f4_native_capture_projection)
    (index : int) : f4_query_record =
 {| f4_q_index = index;
    f4_q_epoch = point.`f4_nt_epoch;
    f4_q_member = cp.`f4_cp_member;
    f4_q_device = cp.`f4_cp_device;
    f4_q_secret_kind = cp.`f4_cp_secret_kind;
    f4_q_corrupt = false;
    f4_q_reveal = false |}.

op f4_capture_matches_native_prestate
    (point : f4_native_trace_point)
    (cp : f4_native_capture_projection) : bool =
  point.`f4_nt_verified /\
  cp.`f4_cp_state = point.

lemma f4_source_corrupt_has_native_epoch_and_identity
    (cp : f4_native_capture_projection) :
  (f4_captured_native_corrupt_query cp).`f4_q_epoch =
    cp.`f4_cp_state.`f4_nt_epoch /\
  (f4_captured_native_corrupt_query cp).`f4_q_member =
    cp.`f4_cp_member /\
  (f4_captured_native_corrupt_query cp).`f4_q_device =
    cp.`f4_cp_device /\
  (f4_captured_native_corrupt_query cp).`f4_q_corrupt.
proof.
  by rewrite /f4_captured_native_corrupt_query.
qed.

lemma f4_successful_native_capture_blocks_same_epoch_direct_challenge
    (point : f4_native_trace_point)
    (cp : f4_native_capture_projection) (index : int) :
  f4_capture_matches_native_prestate point cp =>
  cp.`f4_cp_index < index =>
  f4_exposed_before_challenge
    [f4_captured_native_corrupt_query cp]
    (f4_challenge_at_native_state point cp index).
proof.
  rewrite /f4_capture_matches_native_prestate
          /f4_exposed_before_challenge /= /f4_prior_exposure_for
          /f4_captured_native_corrupt_query
          /f4_challenge_at_native_state.
  by smt().
qed.

(* This is the important cross-epoch obligation: exact-epoch direct exposure
   checks alone are INSUFFICIENT to classify native PCS recovery. It is
   structurally possible for the real old MlsGroup to be captured, followed
   by an accepted external transition. The source-level Rust test checks
   that the stolen old Group keeps its old exporter after that transition.
   This does not assert that the NEW epoch is known to the attacker. *)
lemma f4_successful_native_capture_not_detected_by_direct_new_epoch_guard
    (before after : f4_native_trace_point)
    (cp : f4_native_capture_projection) (index : int) :
  f4_capture_matches_native_prestate before cp =>
  f4_nt_local_successor before after =>
  cp.`f4_cp_index < index =>
  ! f4_exposed_before_challenge
    [f4_captured_native_corrupt_query cp]
    (f4_challenge_at_native_state after cp index).
proof.
  rewrite /f4_capture_matches_native_prestate
          /f4_nt_local_successor
          /f4_exposed_before_challenge /= /f4_prior_exposure_for
          /f4_captured_native_corrupt_query
          /f4_challenge_at_native_state.
  by smt().
qed.

(* The exposure QUERY itself remains present when a native epoch advances;
   only its classification relative to the challenge changes. *)
lemma f4_native_step_does_not_relabel_captured_exposure
    (before after : f4_native_trace_point)
    (cp : f4_native_capture_projection) :
  f4_capture_matches_native_prestate before cp =>
  f4_nt_local_successor before after =>
  (f4_captured_native_corrupt_query cp).`f4_q_epoch =
    before.`f4_nt_epoch /\
  (f4_captured_native_corrupt_query cp).`f4_q_epoch <>
    after.`f4_nt_epoch.
proof.
  rewrite /f4_capture_matches_native_prestate
          /f4_nt_local_successor /f4_captured_native_corrupt_query.
  by smt().
qed.

(* No claim of quantum indistinguishability, erasure, or complete exposure
   inventory; the native Rust test establishes this one concrete case. *)
