require import AllCore Int List.
require import F4_Native_Accepted_Trace_Refinement.
require import F4_Native_Reveal_Installation_Chronology.

(* Source-shaped F4 M2 semantic COVERAGE BARRIER.
   Rust source: offline_product_f4_semantic_audit.rs calls execute_android
   exactly once between two opaque, independently authenticated native
   Product observations. The result is classified as one of six exhaustive
   F4SemanticStepClass variants, not a claimed 'accepted' bit.
   Only VerifiedPublicRead, VerifiedSingleAcceptedCommit and independently signed\n   same-epoch native installation can be verified
   as ordinary public-state steps by this boundary. Rejected native calls,
   partial multi-epoch replacements, staging, Welcome and resync are NOT
   silently identified with a stutter or an accepted +1 Commit.

   This algebraic proof covers arbitrarily long finite source-typed event
   streams, NOT an extraction/adequacy proof for *all* Rust/OpenMLS internal
   secret mutations, crash histories or QPT security. All unsupported steps
   leave an irreversible coverage failure; the game cannot claim universal
   semantic refinement from them. *)

op f4_sa_kind_read : int = 0.
op f4_sa_kind_commit : int = 1.
op f4_sa_kind_rejected_public_view : int = 2.
op f4_sa_kind_rejected_mutation : int = 3.
op f4_sa_kind_unproved_effect : int = 4.
op f4_sa_kind_unproved_transition : int = 5.
op f4_sa_kind_same_epoch_install : int = 6.
(* Exact Product Android dispatcher rejects this declared wire-command class
   before an OpenMLS/Product operation runs.  It is represented explicitly
   rather than folded into an unspecified source failure, so a Rust-side
   dispatcher extension cannot be silently certified as a game stutter. *)
op f4_sa_kind_dispatcher_rejected : int = 7.

type f4_source_audited_event = {
  f4_sa_kind : int;
  f4_sa_before : f4_native_trace_point;
  f4_sa_after : f4_native_trace_point;
}.

(* This predicate is deliberately STRICTER than recognizing a returned
   Product JSON 'Success': it requires exact verified endpoints. *)
op f4_sa_source_public_step
    (current : f4_native_trace_point)
    (event : f4_source_audited_event) : bool =
  if event.`f4_sa_kind = f4_sa_kind_read then
    current.`f4_nt_verified /\
    event.`f4_sa_before = current /\
    event.`f4_sa_after = current
  else if event.`f4_sa_kind = f4_sa_kind_commit then
    event.`f4_sa_before = current /\
    f4_nt_local_successor current event.`f4_sa_after
  else if event.`f4_sa_kind = f4_sa_kind_same_epoch_install then
    event.`f4_sa_before = current /\
    f4_native_source_installation current event.`f4_sa_after
  else false.

(* Track both the accepted view and whether ANY semantic coverage hole
   has occurred. A later correct Commit may advance the accepted view but
   must NOT erase the earlier coverage failure. *)
op f4_sa_fold_step
    (state : bool * f4_native_trace_point)
    (event : f4_source_audited_event) :
      bool * f4_native_trace_point =
  (state.`1 /\ f4_sa_source_public_step state.`2 event,
   if f4_sa_source_public_step state.`2 event
   then event.`f4_sa_after else state.`2).

op f4_sa_fold
    (initial : bool * f4_native_trace_point)
    (events : f4_source_audited_event list) :
      bool * f4_native_trace_point =
  foldl f4_sa_fold_step initial events.

lemma f4_sa_audited_read_stutters
    (current : f4_native_trace_point)
    (e : f4_source_audited_event) :
  e.`f4_sa_kind = f4_sa_kind_read =>
  f4_sa_source_public_step current e =>
  e.`f4_sa_after = current.
proof.
  rewrite /f4_sa_source_public_step /f4_sa_kind_read.
  by smt().
qed.

lemma f4_sa_audited_commit_has_exact_signed_parent_and_epoch
    (current : f4_native_trace_point)
    (e : f4_source_audited_event) :
  e.`f4_sa_kind = f4_sa_kind_commit =>
  f4_sa_source_public_step current e =>
  e.`f4_sa_after.`f4_nt_parent = Some current.`f4_nt_head /\
  e.`f4_sa_after.`f4_nt_parent_epoch = Some current.`f4_nt_epoch /\
  e.`f4_sa_after.`f4_nt_epoch = current.`f4_nt_epoch + 1.
proof.
  rewrite /f4_sa_source_public_step
          /f4_sa_kind_read /f4_sa_kind_commit
          /f4_nt_local_successor.
  by smt().
qed.

lemma f4_sa_same_epoch_install_does_not_advance_global_head
    (current : f4_native_trace_point)
    (e : f4_source_audited_event) :
  e.`f4_sa_kind = f4_sa_kind_same_epoch_install =>
  f4_sa_source_public_step current e =>
  e.`f4_sa_after.`f4_nt_epoch = current.`f4_nt_epoch /\
  e.`f4_sa_after.`f4_nt_head = current.`f4_nt_head.
proof.
  rewrite /f4_sa_source_public_step
          /f4_sa_kind_read /f4_sa_kind_commit
          /f4_sa_kind_same_epoch_install
          /f4_native_source_installation.
  by smt().
qed.

lemma f4_sa_unproved_operation_never_receives_public_certificate
    (current : f4_native_trace_point)
    (e : f4_source_audited_event) :
  e.`f4_sa_kind <> f4_sa_kind_read =>
  e.`f4_sa_kind <> f4_sa_kind_commit =>
  e.`f4_sa_kind <> f4_sa_kind_same_epoch_install =>
  !f4_sa_source_public_step current e.
proof.
  rewrite /f4_sa_source_public_step.
  by smt().
qed.

lemma f4_sa_dispatcher_rejection_never_receives_public_certificate
    (current : f4_native_trace_point)
    (e : f4_source_audited_event) :
  e.`f4_sa_kind = f4_sa_kind_dispatcher_rejected =>
  ! f4_sa_source_public_step current e.
proof.
  rewrite /f4_sa_source_public_step
          /f4_sa_kind_read /f4_sa_kind_commit
          /f4_sa_kind_same_epoch_install
          /f4_sa_kind_dispatcher_rejected.
  by smt().
qed.

lemma f4_sa_gap_never_disappears_under_any_finite_suffix
    (initial : bool * f4_native_trace_point)
    (events : f4_source_audited_event list) :
  ! initial.`1 =>
  ! (f4_sa_fold initial events).`1.
proof.
  rewrite /f4_sa_fold.
  elim: events initial => [| event rest ih] initial /=.
  + by [].
  move=> h.
  apply (ih (f4_sa_fold_step initial event)).
  rewrite /f4_sa_fold_step.
  by smt().
qed.

lemma f4_sa_any_unsupported_step_poison_all_future_coverage
    (current : f4_native_trace_point)
    (e : f4_source_audited_event)
    (suffix : f4_source_audited_event list) :
  e.`f4_sa_kind <> f4_sa_kind_read =>
  e.`f4_sa_kind <> f4_sa_kind_commit =>
  e.`f4_sa_kind <> f4_sa_kind_same_epoch_install =>
  ! (f4_sa_fold
       (f4_sa_fold_step (true, current) e) suffix).`1.
proof.
  move=> not_read not_commit not_install.
  apply f4_sa_gap_never_disappears_under_any_finite_suffix.
  rewrite /f4_sa_fold_step.
  have h := f4_sa_unproved_operation_never_receives_public_certificate
     current e not_read not_commit not_install.
  by smt().
qed.

(* A coverage-complete result is only a public transition shape, never
   a certificate of secret-kind completeness, actual physical erasure or
   independent UpdatePath entropy. F4 FreshQ/PCS/QPT remain external. *)
