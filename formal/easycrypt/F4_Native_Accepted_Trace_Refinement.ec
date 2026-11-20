require import AllCore Int List.
require import F4_Typed_Challenge_Model.

(* Exact public transition SHAPE used by the native Rust research boundary
   offline_product_f4_trace.rs, with the same accepted group/head/parent/epoch
   checks. This is NOT a Rust extraction theorem and does NOT assert an
   unproved property about hidden provider secrets, erasure or PCS.

   Rust evidence is sourced by observe_signed_accepted_product() from an
   authenticated, persisted Product state. The f4_nt_verified bit here is
   an abstract description of that verified boundary, not a new axiom:
   completion of source-level simulation remains an explicit obligation.
*)

type f4_native_trace_point = {
  f4_nt_group : f4_group_id;
  f4_nt_suite : f4_suite;
  f4_nt_service : int;
  f4_nt_epoch : int;
  f4_nt_head : f4_head;
  f4_nt_parent : f4_head option;
  f4_nt_parent_epoch : int option;
  f4_nt_op : int;
  f4_nt_verified : bool;
  f4_nt_own_path_verified : bool;
}.

op f4_nt_op_genesis : int = 0.
op f4_nt_op_external_commit : int = 1.
op f4_nt_op_internal_own_update : int = 2.
op f4_nt_op_remove : int = 3.
op f4_nt_op_close : int = 4.

op f4_nt_local_successor (before after : f4_native_trace_point) : bool =
  before.`f4_nt_verified /\ after.`f4_nt_verified /\
  before.`f4_nt_group = after.`f4_nt_group /\
  before.`f4_nt_suite = after.`f4_nt_suite /\
  before.`f4_nt_service = after.`f4_nt_service /\
  after.`f4_nt_parent = Some before.`f4_nt_head /\
  after.`f4_nt_parent_epoch = Some before.`f4_nt_epoch /\
  after.`f4_nt_epoch = before.`f4_nt_epoch + 1 /\
  after.`f4_nt_head <> before.`f4_nt_head /\
  (after.`f4_nt_op = f4_nt_op_external_commit \/
   after.`f4_nt_op = f4_nt_op_internal_own_update \/
   after.`f4_nt_op = f4_nt_op_remove) /\
  (after.`f4_nt_own_path_verified =>
   after.`f4_nt_op = f4_nt_op_internal_own_update).

op f4_nt_fold_step
    (state : bool * f4_native_trace_point)
    (after : f4_native_trace_point) : bool * f4_native_trace_point =
  (state.`1 /\ f4_nt_local_successor state.`2 after, after).

op f4_nt_trace
    (initial : f4_native_trace_point)
    (successors : f4_native_trace_point list) :
      bool * f4_native_trace_point =
  foldl f4_nt_fold_step (true, initial) successors.

lemma f4_nt_step_preserves_exact_parent_and_epoch
    (before after : f4_native_trace_point) :
  f4_nt_local_successor before after =>
  after.`f4_nt_parent = Some before.`f4_nt_head /\
  after.`f4_nt_parent_epoch = Some before.`f4_nt_epoch /\
  after.`f4_nt_epoch = before.`f4_nt_epoch + 1 /\
  after.`f4_nt_group = before.`f4_nt_group.
proof.
  rewrite /f4_nt_local_successor.
  by smt().
qed.

lemma f4_nt_replay_cannot_advance_epoch
    (before after : f4_native_trace_point) :
  after.`f4_nt_head = before.`f4_nt_head =>
  ! f4_nt_local_successor before after.
proof.
  rewrite /f4_nt_local_successor.
  by smt().
qed.

lemma f4_nt_epoch_skip_is_rejected
    (before after : f4_native_trace_point) :
  after.`f4_nt_epoch <> before.`f4_nt_epoch + 1 =>
  ! f4_nt_local_successor before after.
proof.
  rewrite /f4_nt_local_successor.
  by smt().
qed.

lemma f4_nt_cross_group_cannot_form_step
    (before after : f4_native_trace_point) :
  before.`f4_nt_group <> after.`f4_nt_group =>
  ! f4_nt_local_successor before after.
proof.
  rewrite /f4_nt_local_successor.
  by smt().
qed.

lemma f4_nt_external_commit_cannot_claim_own_path
    (before after : f4_native_trace_point) :
  after.`f4_nt_op = f4_nt_op_external_commit =>
  f4_nt_local_successor before after =>
  ! after.`f4_nt_own_path_verified.
proof.
  rewrite /f4_nt_local_successor /f4_nt_op_external_commit
          /f4_nt_op_internal_own_update.
  by smt().
qed.

lemma f4_nt_two_real_successor_shapes_compose
    (genesis external own : f4_native_trace_point) :
  f4_nt_local_successor genesis external =>
  f4_nt_local_successor external own =>
  (f4_nt_trace genesis [external; own]).`1 /\
  (f4_nt_trace genesis [external; own]).`2 = own /\
  own.`f4_nt_parent = Some external.`f4_nt_head /\
  own.`f4_nt_epoch = genesis.`f4_nt_epoch + 2.
proof.
  move=> h01 h12.
  have hparent : own.`f4_nt_parent = Some external.`f4_nt_head
    by rewrite /f4_nt_local_successor in h12; smt().
  have hepoch : own.`f4_nt_epoch = genesis.`f4_nt_epoch + 2
    by rewrite /f4_nt_local_successor in h01;
       rewrite /f4_nt_local_successor in h12; smt().
  rewrite /f4_nt_trace /f4_nt_fold_step /= h01 h12 /=.
  by smt().
qed.

(* Source-backed adversarial boundary: Product replacement::complete()
   durably merges REMOVE in store::transaction and calls catch_up(JOIN)
   only AFTER that transaction returned. It is therefore a pair of accepted
   successor links, NOT an atomic synthetic "resync epoch+2" transition.
   The intermediate state must be allowed to survive a failed second phase.
   The following is a shape theorem about verified endpoints; the universal
   SQLite crash/durability simulation remains open. *)
lemma f4_native_replacement_requires_two_steps_not_epoch_skip
    (pre removed joined : f4_native_trace_point) :
  f4_nt_local_successor pre removed =>
  removed.`f4_nt_op = f4_nt_op_remove =>
  f4_nt_local_successor removed joined =>
  joined.`f4_nt_op = f4_nt_op_external_commit =>
  removed.`f4_nt_epoch = pre.`f4_nt_epoch + 1 /\
  joined.`f4_nt_epoch = pre.`f4_nt_epoch + 2 /\
  !f4_nt_local_successor pre joined.
proof.
  rewrite /f4_nt_local_successor.
  by smt().
qed.

lemma f4_native_replacement_can_stop_at_authenticated_remove
    (pre removed : f4_native_trace_point) :
  f4_nt_local_successor pre removed =>
  removed.`f4_nt_op = f4_nt_op_remove =>
  (f4_nt_trace pre [removed]).`1 /\
  (f4_nt_trace pre [removed]).`2 = removed.
proof.
  move=> hstep _.
  by rewrite /f4_nt_trace /f4_nt_fold_step /= hstep.
qed.

(* This formal chain does NOT define FreshQ from accepted epochs. A signed
   successor only carries PUBLIC state; native exposure and cryptographic
   indistinguishability must be discharged separately. *)
