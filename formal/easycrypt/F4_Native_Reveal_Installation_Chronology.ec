require import AllCore Int List.
require import F4_Native_Accepted_Trace_Refinement.
require import F4_Adversarial_Query_Ledger.

(* F4 M2: source-shaped successful Product exporter Reveal and independently
   accepted same-epoch installation, as implemented TEST-ONLY by
   offline_product_f4_exposure.rs and
   offline_product_f4_adversarial_trace.rs.

   Rust mints Reveal only after signed CURRENT, protected MlsGroup::load,
   the native OpenMLS exporter, and matching signed/native reobservation.
   The recorded event's group/epoch/device and selected key context come
   from the native accepted Product, not a backend "success" Boolean.
   This model projects metadata of such a source-issued capability; it is
   not a universal compiler/Rust refinement or QPT secrecy theorem. *)

type f4_native_reveal_projection = {
  f4_rp_state : f4_native_trace_point;
  f4_rp_index : int;
  f4_rp_member : f4_member_id;
  f4_rp_device : f4_device_id;
  f4_rp_secret_kind : f4_secret_kind_id;
}.

op f4_source_native_reveal_query
    (rp : f4_native_reveal_projection) : f4_query_record =
  {| f4_q_index = rp.`f4_rp_index;
     f4_q_epoch = rp.`f4_rp_state.`f4_nt_epoch;
     f4_q_member = rp.`f4_rp_member;
     f4_q_device = rp.`f4_rp_device;
     f4_q_secret_kind = rp.`f4_rp_secret_kind;
     f4_q_corrupt = false;
     f4_q_reveal = true |}.

op f4_source_reveal_test_query
    (rp : f4_native_reveal_projection) (index : int) : f4_query_record =
  {| f4_q_index = index;
     f4_q_epoch = rp.`f4_rp_state.`f4_nt_epoch;
     f4_q_member = rp.`f4_rp_member;
     f4_q_device = rp.`f4_rp_device;
     f4_q_secret_kind = rp.`f4_rp_secret_kind;
     f4_q_corrupt = false;
     f4_q_reveal = false |}.

op f4_native_reveal_is_current
    (state : f4_native_trace_point)
    (rp : f4_native_reveal_projection) : bool =
  state.`f4_nt_verified /\
  rp.`f4_rp_state = state.

(* New device installation is NOT a ratchet update. It does not change the
   canonical group epoch/head and it cannot assert recovery. The test-only
   Rust Product trace now supports active same-head Genesis, ExternalJoin,
   OwnUpdate CatchUp, and Remove CatchUp. Welcome and resync have no
   authenticated source-issued constructor and remain inadmissible here. *)
op f4_native_source_installation
    (current installed : f4_native_trace_point) : bool =
  current.`f4_nt_verified /\ installed.`f4_nt_verified /\
  current.`f4_nt_group = installed.`f4_nt_group /\
  current.`f4_nt_suite = installed.`f4_nt_suite /\
  current.`f4_nt_service = installed.`f4_nt_service /\
  current.`f4_nt_head = installed.`f4_nt_head /\
  current.`f4_nt_epoch = installed.`f4_nt_epoch /\
  (installed.`f4_nt_op = f4_nt_op_genesis \/
   installed.`f4_nt_op = f4_nt_op_external_commit \/
   installed.`f4_nt_op = f4_nt_op_internal_own_update \/
   installed.`f4_nt_op = f4_nt_op_remove).

lemma f4_native_source_reveal_has_real_epoch_and_identity
    (rp : f4_native_reveal_projection) :
  (f4_source_native_reveal_query rp).`f4_q_epoch =
     rp.`f4_rp_state.`f4_nt_epoch /\
  (f4_source_native_reveal_query rp).`f4_q_member =
     rp.`f4_rp_member /\
  (f4_source_native_reveal_query rp).`f4_q_device =
     rp.`f4_rp_device /\
  !(f4_source_native_reveal_query rp).`f4_q_corrupt /\
  (f4_source_native_reveal_query rp).`f4_q_reveal.
proof.
  by rewrite /f4_source_native_reveal_query.
qed.

lemma f4_native_source_reveal_blocks_same_epoch_challenge
    (state : f4_native_trace_point)
    (rp : f4_native_reveal_projection) (index : int) :
  f4_native_reveal_is_current state rp =>
  rp.`f4_rp_index < index =>
  f4_exposed_before_challenge
    [f4_source_native_reveal_query rp]
    (f4_source_reveal_test_query rp index).
proof.
  rewrite /f4_native_reveal_is_current
          /f4_exposed_before_challenge /= /f4_prior_exposure_for
          /f4_source_native_reveal_query
          /f4_source_reveal_test_query.
  by smt().
qed.

lemma f4_source_reveal_remains_bad_through_any_exposure_suffix
    (rp : f4_native_reveal_projection)
    (later : f4_query_record list) (index : int) :
  rp.`f4_rp_index < index =>
  f4_exposed_before_challenge
    ([f4_source_native_reveal_query rp] ++ later)
    (f4_source_reveal_test_query rp index).
proof.
  rewrite /f4_exposed_before_challenge has_cat /=
          /f4_prior_exposure_for
          /f4_source_native_reveal_query
          /f4_source_reveal_test_query.
  by smt().
qed.

lemma f4_native_installation_cannot_advance_group_epoch
    (current installed : f4_native_trace_point) :
  f4_native_source_installation current installed =>
  installed.`f4_nt_epoch = current.`f4_nt_epoch /\
  installed.`f4_nt_head = current.`f4_nt_head /\
  installed.`f4_nt_group = current.`f4_nt_group.
proof.
  rewrite /f4_native_source_installation.
  by smt().
qed.

lemma f4_native_unsupported_op_cannot_be_reclassified_as_installation
    (current installed : f4_native_trace_point) :
  installed.`f4_nt_op <> f4_nt_op_genesis =>
  installed.`f4_nt_op <> f4_nt_op_external_commit =>
  installed.`f4_nt_op <> f4_nt_op_internal_own_update =>
  installed.`f4_nt_op <> f4_nt_op_remove =>
  ! f4_native_source_installation current installed.
proof.
  rewrite /f4_native_source_installation.
  by smt().
qed.

(* One globally accepted OwnUpdate may be installed by a second member
   at the SAME group epoch. This second local CatchUp must never mint
   another +1 group Commit, or a certificate that it owns the original
   committer's private UpdatePath. *)
lemma f4_native_ownupdate_catchup_cannot_double_advance_global_epoch
    (current installed : f4_native_trace_point) :
  f4_native_source_installation current installed =>
  installed.`f4_nt_op = f4_nt_op_internal_own_update =>
  ! f4_nt_local_successor current installed.
proof.
  rewrite /f4_native_source_installation /f4_nt_local_successor.
  by smt().
qed.

lemma f4_native_installation_cannot_erase_prior_reveal
    (current installed : f4_native_trace_point)
    (rp : f4_native_reveal_projection)
    (prefix later : f4_query_record list)
    (index : int) :
  f4_native_source_installation current installed =>
  rp.`f4_rp_index < index =>
  f4_exposed_before_challenge prefix
      (f4_source_reveal_test_query rp index) =>
  f4_exposed_before_challenge
      (prefix ++ later) (f4_source_reveal_test_query rp index).
proof.
  move=> _ _ h.
  apply (f4_prior_exposure_cannot_be_healed_by_appending
    prefix later (f4_source_reveal_test_query rp index) h).
qed.

(* An accepted native OwnUpdate may be a real healing candidate but
   cannot erase the *historical* Reveal event. Its successor epoch merely
   makes an EXACT-EPOCH-only exposure guard miss that prior disclosure.
   Whether the next epoch is actually secure is the separate computational
   causal-cut obligation, not a theorem obtained from this structural fact. *)
op f4_source_challenge_on_native_successor
    (point : f4_native_trace_point)
    (rp : f4_native_reveal_projection) (index : int) : f4_query_record =
  {| f4_q_index = index;
     f4_q_epoch = point.`f4_nt_epoch;
     f4_q_member = rp.`f4_rp_member;
     f4_q_device = rp.`f4_rp_device;
     f4_q_secret_kind = rp.`f4_rp_secret_kind;
     f4_q_corrupt = false;
     f4_q_reveal = false |}.

lemma f4_real_ownupdate_does_not_delete_previous_reveal_event
    (before after : f4_native_trace_point)
    (rp : f4_native_reveal_projection) (index : int) :
  f4_native_reveal_is_current before rp =>
  f4_nt_local_successor before after =>
  after.`f4_nt_op = f4_nt_op_internal_own_update =>
  after.`f4_nt_own_path_verified =>
  rp.`f4_rp_index < index =>
  ! f4_exposed_before_challenge
      [f4_source_native_reveal_query rp]
      (f4_source_challenge_on_native_successor after rp index).
proof.
  rewrite /f4_native_reveal_is_current
          /f4_nt_local_successor
          /f4_exposed_before_challenge /f4_prior_exposure_for
          /f4_source_native_reveal_query
          /f4_source_challenge_on_native_successor /=.
  by smt().
qed.

(* M2 real Product oracle result projection. Rust's integrated
   query_current_reveal/query_current_corrupt returns a SOURCE-ISSUED
   Success(secret-bearing capability) or Rejected and logs both attempts.
   The challenger must preserve ALL public attempts but only SUCCESSFUL
   disclosures may enter the attacker-key-exposure ledger. These are
   distinct constructors in Rust, not a backend-supplied success Boolean.
   This proof handles arbitrary finite sequences of rejected attempts. *)

type f4_native_dual_query_ledger = {
  f4_nd_attempts : f4_query_record list;
  f4_nd_successes : f4_query_record list;
}.

op f4_native_append_rejected_attempt
    (s : f4_native_dual_query_ledger) (attempt : f4_query_record) :
    f4_native_dual_query_ledger =
  {| f4_nd_attempts = s.`f4_nd_attempts ++ [attempt];
     f4_nd_successes = s.`f4_nd_successes |}.

op f4_native_append_source_success
    (s : f4_native_dual_query_ledger) (success : f4_query_record) :
    f4_native_dual_query_ledger =
  {| f4_nd_attempts = s.`f4_nd_attempts ++ [success];
     f4_nd_successes = s.`f4_nd_successes ++ [success] |}.

op f4_native_all_rejected_attempts
    (s : f4_native_dual_query_ledger)
    (attempts : f4_query_record list) : f4_native_dual_query_ledger =
  foldl f4_native_append_rejected_attempt s attempts.

lemma f4_native_single_denial_does_not_forge_disclosure
    (s : f4_native_dual_query_ledger) (attempt : f4_query_record) :
  (f4_native_append_rejected_attempt s attempt).`f4_nd_successes =
    s.`f4_nd_successes /\
  (f4_native_append_rejected_attempt s attempt).`f4_nd_attempts =
    s.`f4_nd_attempts ++ [attempt].
proof.
  by rewrite /f4_native_append_rejected_attempt.
qed.

lemma f4_native_any_number_of_denials_cannot_mint_success
    (s : f4_native_dual_query_ledger)
    (attempts : f4_query_record list) :
  (f4_native_all_rejected_attempts s attempts).`f4_nd_successes =
    s.`f4_nd_successes.
proof.
  rewrite /f4_native_all_rejected_attempts.
  elim: attempts s => [| attempt attempts ih] s /=.
  + by [].
  rewrite (ih (f4_native_append_rejected_attempt s attempt)).
  by rewrite /f4_native_append_rejected_attempt.
qed.

lemma f4_native_actual_success_appends_exact_disclosure
    (s : f4_native_dual_query_ledger) (success : f4_query_record) :
  (f4_native_append_source_success s success).`f4_nd_successes =
    s.`f4_nd_successes ++ [success] /\
  (f4_native_append_source_success s success).`f4_nd_attempts =
    s.`f4_nd_attempts ++ [success].
proof.
  by rewrite /f4_native_append_source_success.
qed.

(* Inductive generalization from the Rust F4NativeOracleResult constructors:
   Success is minted only by actual OpenMLS secret extraction; Rejected
   originates from an unsuccessful source call. The boolean here describes
   which variant the native oracle RETURNED; it is not a native backend
   check_freshq or permission for the challenger to choose success.

   This algebraic theorem handles EVERY FINITE ORDERED sequence of those
   already source-issued exposure outcomes. Proving the Rust-to-outcome
   abstraction exhaustive under concurrency/crashes is still a distinct,
   explicitly open source adequacy obligation. *)

type f4_native_source_query_outcome = {
  f4_nq_record : f4_query_record;
  f4_nq_was_success : bool;
}.

op f4_native_fold_source_outcome
    (s : f4_native_dual_query_ledger)
    (q : f4_native_source_query_outcome) : f4_native_dual_query_ledger =
  if q.`f4_nq_was_success
  then f4_native_append_source_success s q.`f4_nq_record
  else f4_native_append_rejected_attempt s q.`f4_nq_record.

op f4_native_fold_all_source_outcomes
    (s : f4_native_dual_query_ledger)
    (events : f4_native_source_query_outcome list) :
    f4_native_dual_query_ledger =
  foldl f4_native_fold_source_outcome s events.

op f4_native_expected_all_attempts
    (events : f4_native_source_query_outcome list) :
    f4_query_record list =
  map (fun q => q.`f4_nq_record) events.

op f4_native_expected_only_successes
    (events : f4_native_source_query_outcome list) :
    f4_query_record list =
  map (fun q => q.`f4_nq_record)
    (filter (fun q => q.`f4_nq_was_success) events).

lemma f4_native_all_finite_source_outcomes_exact_exposure_projection
    (s : f4_native_dual_query_ledger)
    (events : f4_native_source_query_outcome list) :
  (f4_native_fold_all_source_outcomes s events).`f4_nd_attempts =
    s.`f4_nd_attempts ++ f4_native_expected_all_attempts events /\
  (f4_native_fold_all_source_outcomes s events).`f4_nd_successes =
    s.`f4_nd_successes ++ f4_native_expected_only_successes events.
proof.
  rewrite /f4_native_fold_all_source_outcomes
          /f4_native_expected_all_attempts
          /f4_native_expected_only_successes.
  elim: events s => [| q rest ih] s /=.
  + by rewrite !cats0.
  rewrite /f4_native_fold_source_outcome
          /f4_native_append_source_success
          /f4_native_append_rejected_attempt.
  case: (q.`f4_nq_was_success = true) => [-> | h_not_true].
  + have h := ih (f4_native_append_source_success s q.`f4_nq_record).
    rewrite /f4_native_fold_source_outcome in h.
    rewrite /f4_native_append_source_success
            /f4_native_append_rejected_attempt in h.
    rewrite ifT 1:/#.
    rewrite ifT 1:/#.
    rewrite /=.
    rewrite /= in h.
    rewrite -!catA !cat1s in h.
    exact h.
  + have hfalse : q.`f4_nq_was_success = false by smt.
    move: hfalse => ->.
    have h := ih (f4_native_append_rejected_attempt s q.`f4_nq_record).
    rewrite /f4_native_fold_source_outcome in h.
    rewrite /f4_native_append_source_success
            /f4_native_append_rejected_attempt in h.
    rewrite ifF 1:/#.
    rewrite ifF 1:/#.
    rewrite /=.
    rewrite /= in h.
    rewrite -!catA !cat1s in h.
    exact h.
qed.

(* This fragment is a verified projection of source-issued event kinds, not
   a claim of universality: Welcome/resync, physical erasure, retained key
   schedules and the native-to-T1 adaptive simulation remain open. *)
