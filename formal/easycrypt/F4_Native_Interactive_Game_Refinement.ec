require import AllCore Int List.
require import F4_Native_Accepted_Trace_Refinement F4_Interactive_PCS_Game.

(* The accepted Parent is captured from the concrete challenger AFTER the
   backend call and BEFORE eligibility evaluation. This prevents the Hoare
   argument from assuming the opaque backend preserves local globals. The
   accepted path then has no further backend calls before it commits the
   canonical state. This proves actual interactive game control flow, not
   source-level OpenMLS Rust secrecy or complete native exposure semantics. *)

lemma f4_interactive_internal_accept_uses_native_link
    (B <: F4ProductPCSBackend{-F4Challenger}) :
  hoare [F4Challenger(B).accepted_commit :
     true
     ==>
     (res <> None =>
       f4_nt_local_successor
         F4Challenger.accepted_parent (oget res) /\
       ((oget res).`f4_nt_op = f4_nt_op_internal_own_update \/
        (oget res).`f4_nt_op = f4_nt_op_remove) /\
       F4Challenger.last_native_state = oget res /\
       F4Challenger.global_epoch = (oget res).`f4_nt_epoch)].
proof.
  proc.
  wp.
  call (_: true).
  auto; smt().
qed.

lemma f4_interactive_external_accept_uses_native_link
    (B <: F4ProductPCSBackend{-F4Challenger}) :
  hoare [F4Challenger(B).accepted_external_commit :
     true
     ==>
     (res <> None =>
       f4_nt_local_successor
         F4Challenger.accepted_parent (oget res) /\
       (oget res).`f4_nt_op = f4_nt_op_external_commit /\
       F4Challenger.last_native_state = oget res /\
       F4Challenger.global_epoch = (oget res).`f4_nt_epoch)].
proof.
  proc.
  wp.
  call (_: true).
  auto; smt().
qed.

lemma f4_interactive_unproved_welcome_poison_challenge
    (B <: F4ProductPCSBackend{-F4Challenger}) :
  hoare [F4Challenger(B).welcome_install :
     true
     ==> F4Challenger.bad_challenge].
proof.
  proc.
  wp.
  call (_: true).
  auto; smt().
qed.

lemma f4_interactive_unproved_resync_poison_challenge
    (B <: F4ProductPCSBackend{-F4Challenger}) :
  hoare [F4Challenger(B).resync_install :
     true
     ==> F4Challenger.bad_challenge].
proof.
  proc.
  wp.
  call (_: true).
  auto; smt().
qed.

(* Still OPEN, and not a new axiom: link the verified opaque Rust Product
   state/exposure source to the algorithm and show exhaustive causal
   retention/erasure and QPT real/ideal correspondence. *)
