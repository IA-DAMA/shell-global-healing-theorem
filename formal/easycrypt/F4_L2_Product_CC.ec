require import AllCore List.
require import F4_CC_Observation_Prefix.
require import F4_L1_Process_Window.
require import F4_Native_Accepted_Trace_Refinement.
require import F4_Native_Source_Semantic_Coverage.

(* L2 composes three already distinct boundaries:
   - the finite physical/ghost lifecycle relation for the twelve operation
     classes;
   - L1's process-exposure ledger at each prepare cut; and
   - the source-audit barrier, which makes every unsupported source event an
     irreversible coverage failure instead of silently treating it as a
     stutter or healing event. *)

lemma l2_every_operational_prefix ops s g :
  covered s g =>
  covered (foldl physical s ops) (foldl record g ops).
proof. exact (every_prefix ops s g). qed.

lemma l2_prepare_process_cut_is_recorded t :
  successor_typed_live t =>
  mem (gamma t) SuccessorState /\
  mem (gamma t) SuccessorExporter.
proof. exact (successor_is_accounted t). qed.

lemma l2_unsupported_source_step_stays_ineligible
    (current : f4_native_trace_point)
    (event : f4_source_audited_event)
    (suffix : f4_source_audited_event list) :
  event.`f4_sa_kind <> f4_sa_kind_read =>
  event.`f4_sa_kind <> f4_sa_kind_commit =>
  event.`f4_sa_kind <> f4_sa_kind_same_epoch_install =>
  ! (f4_sa_fold
       (f4_sa_fold_step (true, current) event) suffix).`1.
proof.
  exact (f4_sa_any_unsupported_step_poison_all_future_coverage
    current event suffix).
qed.

lemma l2_dispatcher_rejection_is_not_a_transition
    (current : f4_native_trace_point)
    (event : f4_source_audited_event) :
  event.`f4_sa_kind = f4_sa_kind_dispatcher_rejected =>
  ! f4_sa_source_public_step current event.
proof. exact (f4_sa_dispatcher_rejection_never_receives_public_certificate current event). qed.

(* Non-vacuity is inherited from a concrete abstract history containing an
   old capture, prepare, committed remove-error state, crash and restart.  The
   later grant/copy/retry makes the target ineligible; the earlier local state
   is nevertheless an admitted coverage prefix. *)
lemma l2_nonvacuous_admitted_prefix :
  admissible
    (foldl physical (foldl physical start prefix)
      (finish_without_grant (foldl physical start prefix))).
proof. exact adaptive_local_positive. qed.

lemma l2_joint_nonvacuity :
  covered start startg /\
  admissible (foldl physical start prefix) /\
  (foldl physical (foldl physical start prefix)
    (adapt (foldl physical start prefix))).`view.`4.
proof. exact witnessed. qed.

(* This theorem is a coverage/admission theorem.  It does not turn an
   unsupported Welcome, resync or private side effect into a proved Product
   transition; those histories remain outside Adm until a source certificate
   for their exact semantics is supplied. *)
