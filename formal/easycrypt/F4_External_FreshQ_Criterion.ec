require import AllCore Int List.

(* F4 FreshQ candidate for the GROUP EPOCH SECRET challenge.

   This is a conservative trace criterion, not a refinement proof for
   OpenMLS/Product. In particular, ff_authenticated, ff_accepted,
   ff_fresh_update_path and ff_target_is_recipient must be derived from
   authenticated native events and the TreeKEM path, not supplied by an
   untrusted backend. The draft deliberately refuses to infer healing from
   an epoch counter, External Commit, Welcome or resync installation.

   RFC 9420 requires an External Commit to carry a full path. This model's
   exclusion of External Commit as a healer is therefore a proof policy, not
   a claim that the wire operation lacks an UpdatePath. External actor
   authorization, independent path entropy, resync semantics and the ETK PCS
   restrictions have not been reduced to native facts here.

   Event kinds: 1 corrupt, 2 reveal, 3 internal Commit, 4 external Commit,
   5 Welcome installation, 6 resync installation, 7 external proposal,
   8 application send, 9 challenge. *)

op f4_kind_corrupt : int = 1.
op f4_kind_reveal : int = 2.
op f4_kind_internal_commit : int = 3.
op f4_kind_external_commit : int = 4.
op f4_kind_welcome : int = 5.
op f4_kind_resync : int = 6.
op f4_kind_external_proposal : int = 7.
op f4_kind_send : int = 8.
op f4_kind_challenge : int = 9.

type f4_fresh_event = {
  ff_index : int;
  ff_group : int;
  ff_epoch_before : int;
  ff_epoch_after : int;
  ff_member : int;
  ff_device : int;
  ff_secret_kind : int;
  ff_committer : int;
  ff_kind : int;
  ff_member_active : bool;
  ff_accepted : bool;
  ff_authenticated : bool;
  ff_full_update_path : bool;
  ff_fresh_update_path : bool;
  ff_target_is_recipient : bool;
}.

op f4_is_exposure_event (e : f4_fresh_event) : bool =
  e.`ff_kind = f4_kind_corrupt \/ e.`ff_kind = f4_kind_reveal.

op f4_is_external_operation (e : f4_fresh_event) : bool =
  e.`ff_kind = f4_kind_external_commit \/
  e.`ff_kind = f4_kind_welcome \/
  e.`ff_kind = f4_kind_resync \/
  e.`ff_kind = f4_kind_external_proposal.

(* For an epoch-secret challenge, any active member's extraction in the same
   group and secret class is relevant. This intentionally does not require
   the challenged member/device to equal the compromised member/device. *)
op f4_relevant_exposure (e ch : f4_fresh_event) : bool =
  f4_is_exposure_event e /\ e.`ff_member_active /\
  e.`ff_group = ch.`ff_group /\
  e.`ff_secret_kind = ch.`ff_secret_kind /\
  e.`ff_index < ch.`ff_index.

(* Conservative: a committer is not eligible to heal if any earlier corrupt
   or reveal for that member in this group appears in the observed trace.
   A tighter test could allow a previously exposed committer after a proved
   independent recovery, but no such recovery is assumed here. *)
op f4_committer_unexposed_before
    (trace : f4_fresh_event list) (commit : f4_fresh_event) : bool =
  !has (fun e => f4_is_exposure_event e /\ e.`ff_member_active /\
                 e.`ff_group = commit.`ff_group /\
                 e.`ff_member = commit.`ff_committer /\
                 e.`ff_index < commit.`ff_index) trace.

(* Only an accepted, authenticated, increasing internal UpdatePath Commit
   with fresh path entropy and the challenged recipient on its path can
   witness a healing step in this model. *)
op f4_internal_heal_witness
    (trace : f4_fresh_event list)
    (commit ch : f4_fresh_event) : bool =
  commit.`ff_kind = f4_kind_internal_commit /\
  commit.`ff_group = ch.`ff_group /\
  commit.`ff_index < ch.`ff_index /\
  commit.`ff_accepted /\ commit.`ff_authenticated /\
  commit.`ff_epoch_before < commit.`ff_epoch_after /\
  commit.`ff_full_update_path /\ commit.`ff_fresh_update_path /\
  commit.`ff_target_is_recipient /\
  f4_committer_unexposed_before trace commit.

op f4_exposure_before_challenge
    (trace : f4_fresh_event list) (ch : f4_fresh_event) : bool =
  has (fun e => f4_relevant_exposure e ch) trace.

op f4_exposure_after_commit_before_challenge
    (trace : f4_fresh_event list)
    (commit ch : f4_fresh_event) : bool =
  has (fun e => f4_relevant_exposure e ch /\
                 commit.`ff_index < e.`ff_index) trace.

(* An exposure is discharged only by a qualifying internal Commit after the
   last relevant exposure and before challenge. Later exposure resets the
   criterion; appending an epoch-changing external operation cannot heal it. *)
op f4_healed_since_last_exposure
    (trace : f4_fresh_event list) (ch : f4_fresh_event) : bool =
  has (fun commit => f4_internal_heal_witness trace commit ch /\
                     !f4_exposure_after_commit_before_challenge
                        trace commit ch) trace.

op f4_freshq_candidate
    (trace : f4_fresh_event list) (ch : f4_fresh_event) : bool =
  ch.`ff_kind = f4_kind_challenge /\
  (!f4_exposure_before_challenge trace ch \/
   f4_healed_since_last_exposure trace ch).

lemma f4_external_commit_never_witnesses_internal_healing
    (trace : f4_fresh_event list) (e ch : f4_fresh_event) :
  e.`ff_kind = f4_kind_external_commit =>
  !f4_internal_heal_witness trace e ch.
proof.
  rewrite /f4_internal_heal_witness.
  by smt().
qed.

lemma f4_welcome_never_witnesses_internal_healing
    (trace : f4_fresh_event list) (e ch : f4_fresh_event) :
  e.`ff_kind = f4_kind_welcome =>
  !f4_internal_heal_witness trace e ch.
proof.
  rewrite /f4_internal_heal_witness.
  by smt().
qed.

lemma f4_resync_never_witnesses_internal_healing
    (trace : f4_fresh_event list) (e ch : f4_fresh_event) :
  e.`ff_kind = f4_kind_resync =>
  !f4_internal_heal_witness trace e ch.
proof.
  rewrite /f4_internal_heal_witness.
  by smt().
qed.

lemma f4_epoch_advance_alone_does_not_witness_healing
    (trace : f4_fresh_event list) (e ch : f4_fresh_event) :
  e.`ff_epoch_before < e.`ff_epoch_after =>
  (e.`ff_kind = f4_kind_external_commit \/
   e.`ff_kind = f4_kind_welcome \/
   e.`ff_kind = f4_kind_resync \/
   !e.`ff_full_update_path \/
   !e.`ff_fresh_update_path \/
   !e.`ff_target_is_recipient \/
   !e.`ff_accepted \/ !e.`ff_authenticated \/
   !f4_committer_unexposed_before trace e) =>
  !f4_internal_heal_witness trace e ch.
proof.
  rewrite /f4_internal_heal_witness.
  by smt().
qed.

lemma f4_freshq_requires_challenge_kind
    (trace : f4_fresh_event list) (ch : f4_fresh_event) :
  f4_freshq_candidate trace ch => ch.`ff_kind = f4_kind_challenge.
proof.
  rewrite /f4_freshq_candidate.
  by smt().
qed.

lemma f4_freshq_rejects_unhealed_prior_exposure
    (trace : f4_fresh_event list) (ch : f4_fresh_event) :
  f4_exposure_before_challenge trace ch =>
  !f4_healed_since_last_exposure trace ch =>
  !f4_freshq_candidate trace ch.
proof.
  rewrite /f4_freshq_candidate.
  by smt().
qed.

lemma f4_freshq_after_exposure_iff_healed
    (trace : f4_fresh_event list) (ch : f4_fresh_event) :
  ch.`ff_kind = f4_kind_challenge =>
  f4_exposure_before_challenge trace ch =>
  (f4_freshq_candidate trace ch <=>
   f4_healed_since_last_exposure trace ch).
proof.
  move=> hc he.
  rewrite /f4_freshq_candidate hc he.
  by smt().
qed.

lemma f4_external_operation_never_witnesses_internal_healing
    (e ch : f4_fresh_event) (trace : f4_fresh_event list) :
  f4_is_external_operation e =>
  !f4_internal_heal_witness trace e ch.
proof.
  rewrite /f4_is_external_operation /f4_internal_heal_witness.
  by smt().
qed.

lemma f4_exposure_in_other_group_is_irrelevant
    (e ch : f4_fresh_event) :
  e.`ff_group <> ch.`ff_group =>
  !f4_relevant_exposure e ch.
proof.
  rewrite /f4_relevant_exposure.
  by smt().
qed.

lemma f4_exposure_in_other_secret_class_is_irrelevant
    (e ch : f4_fresh_event) :
  e.`ff_secret_kind <> ch.`ff_secret_kind =>
  !f4_relevant_exposure e ch.
proof.
  rewrite /f4_relevant_exposure.
  by smt().
qed.

lemma f4_no_prior_exposure_is_candidate_freshq
    (trace : f4_fresh_event list) (ch : f4_fresh_event) :
  ch.`ff_kind = f4_kind_challenge =>
  !f4_exposure_before_challenge trace ch =>
  f4_freshq_candidate trace ch.
proof.
  rewrite /f4_freshq_candidate.
  by smt().
qed.

(* This demonstrates the exact external-operation boundary: a previously
   compromised group epoch followed by only an accepted, epoch-advancing
   External Commit remains ineligible until a qualifying internal UpdatePath
   occurs. It is a model theorem, pending native-event refinement. *)
lemma f4_external_epoch_bump_does_not_discharge_exposure
    (trace : f4_fresh_event list) (ch : f4_fresh_event) :
  f4_exposure_before_challenge trace ch =>
  !f4_healed_since_last_exposure trace ch =>
  ch.`ff_kind = f4_kind_challenge =>
  !f4_freshq_candidate trace ch.
proof.
  move=> he hn hc.
  exact (f4_freshq_rejects_unhealed_prior_exposure trace ch he hn).
qed.
