require import AllCore Int List.
require import F4_L3_Joint_Copy_Closure.
require import F4_Native_Source_Semantic_Coverage.
require import F4_Native_Accepted_Trace_Refinement.
require import F4_Typed_Challenge_Model.

(* L4 is the public decision/durable-effect refinement.  It intentionally
   projects no secret: secret-copy coverage is L1--L3.  Source events outside
   the audited read/commit/same-epoch-install subset set a permanent bad-ref
   bit and are outside Adm, rather than being silently erased as stuttering. *)

type l4_game_state = {
  l4_group : f4_group_id;
  l4_suite : f4_suite;
  l4_service : int;
  l4_epoch : int;
  l4_head : f4_head;
}.

op l4_project (p : f4_native_trace_point) : l4_game_state =
 {| l4_group = p.`f4_nt_group;
    l4_suite = p.`f4_nt_suite;
    l4_service = p.`f4_nt_service;
    l4_epoch = p.`f4_nt_epoch;
    l4_head = p.`f4_nt_head |}.

op l4_rel (p : f4_native_trace_point) (g : l4_game_state) =
  p.`f4_nt_verified /\ g = l4_project p.

type l4_coupled = {
  l4_covered : bool;
  l4_native : f4_native_trace_point;
  l4_game : l4_game_state;
}.

op l4_keep_coverage (old good : bool) = old /\ good.

op l4_step (s : l4_coupled) (e : f4_source_audited_event) : l4_coupled =
  let good = f4_sa_source_public_step s.`l4_native e in
 {| l4_covered = l4_keep_coverage s.`l4_covered good;
    l4_native = if good then e.`f4_sa_after else s.`l4_native;
    l4_game = if good then l4_project e.`f4_sa_after else s.`l4_game |}.

op l4_run (s : l4_coupled) (events : f4_source_audited_event list) =
  foldl l4_step s events.

op l4_initial (p : f4_native_trace_point) : l4_coupled =
 {| l4_covered = p.`f4_nt_verified;
    l4_native = p;
    l4_game = l4_project p |}.

op l4_good (s : l4_coupled) =
  s.`l4_covered /\ l4_rel s.`l4_native s.`l4_game.

lemma l4_supported_step_preserves_relation
    (s : l4_coupled) (e : f4_source_audited_event) :
  l4_good s =>
  f4_sa_source_public_step s.`l4_native e =>
  l4_good (l4_step s e).
proof.
  rewrite /l4_good /l4_rel /l4_step /l4_keep_coverage /=.
  by smt().
qed.

lemma l4_gap_never_disappears
    (s : l4_coupled) (events : f4_source_audited_event list) :
  !s.`l4_covered => !(l4_run s events).`l4_covered.
proof.
  rewrite /l4_run.
  elim: events s => [|e tail ih] s //=.
  move=> h; apply ih; rewrite /l4_step /l4_keep_coverage /=; smt().
qed.

lemma l4_finite_trace_refines_when_admitted
    (s : l4_coupled) (events : f4_source_audited_event list) :
  l4_good s =>
  (l4_run s events).`l4_covered =>
  l4_rel (l4_run s events).`l4_native (l4_run s events).`l4_game.
proof.
  elim: events s => [|e tail ih] s /=.
  + rewrite /l4_run /l4_good; smt().
  move=> hgood hfinal.
  have himmediate : (l4_step s e).`l4_covered.
  + case ((l4_step s e).`l4_covered) => // hnot.
    have hn := l4_gap_never_disappears (l4_step s e) tail hnot.
    by smt().
  have hstep : f4_sa_source_public_step s.`l4_native e.
  + move: himmediate; rewrite /l4_step /l4_keep_coverage /=; smt().
  have hnext := l4_supported_step_preserves_relation s e hgood hstep.
  exact (ih (l4_step s e) hnext hfinal).
qed.

(* Eliminated public reads are true stutters at the projected game boundary. *)
lemma l4_verified_read_stutters
    (current : f4_native_trace_point) (e : f4_source_audited_event) :
  e.`f4_sa_kind = f4_sa_kind_read =>
  f4_sa_source_public_step current e =>
  l4_project e.`f4_sa_after = l4_project current.
proof.
  move=> hk hs.
  have -> := f4_sa_audited_read_stutters current e hk hs.
  trivial.
qed.

(* A same-epoch installation can change installation-private state, but it is
   a stutter only for this public group/head/epoch projection.  L1--L3 retain
   the private copy effects separately. *)
lemma l4_same_epoch_install_publicly_stutters
    (current : f4_native_trace_point) (e : f4_source_audited_event) :
  e.`f4_sa_kind = f4_sa_kind_same_epoch_install =>
  f4_sa_source_public_step current e =>
  l4_project e.`f4_sa_after = l4_project current.
proof.
  rewrite /f4_sa_source_public_step /f4_sa_kind_read /f4_sa_kind_commit
    /f4_sa_kind_same_epoch_install /f4_native_source_installation /l4_project.
  by smt().
qed.

lemma l4_commit_advances_exactly_one
    (current : f4_native_trace_point) (e : f4_source_audited_event) :
  e.`f4_sa_kind = f4_sa_kind_commit =>
  f4_sa_source_public_step current e =>
  (l4_project e.`f4_sa_after).`l4_epoch =
    (l4_project current).`l4_epoch + 1 /\
  e.`f4_sa_after.`f4_nt_parent = Some current.`f4_nt_head.
proof.
  move=> hk hs.
  have h := f4_sa_audited_commit_has_exact_signed_parent_and_epoch
    current e hk hs.
  rewrite /l4_project; smt().
qed.

(* A source-audited read followed by one exact accepted commit witnesses that
   Adm is nonempty at L4. *)
lemma l4_two_step_nonvacuous
    (p : f4_native_trace_point)
    (read commit : f4_source_audited_event) :
  p.`f4_nt_verified =>
  f4_sa_source_public_step p read =>
  f4_sa_source_public_step read.`f4_sa_after commit =>
  (l4_run (l4_initial p) [read; commit]).`l4_covered /\
  l4_rel (l4_run (l4_initial p) [read; commit]).`l4_native
         (l4_run (l4_initial p) [read; commit]).`l4_game.
proof.
  rewrite /l4_run /l4_initial /l4_step /l4_keep_coverage
    /l4_rel /l4_project /=.
  by smt().
qed.

(* Consequently eps_ref is zero for the admitted source-typed public trace
   relation.  The probability of leaving this relation is not erased: it is
   the separate Bad_CC term in the final theorem. *)
