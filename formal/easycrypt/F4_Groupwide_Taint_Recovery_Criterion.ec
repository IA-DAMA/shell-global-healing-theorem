require import AllCore Int List.
require import F4_External_FreshQ_Criterion.

(* F4-F: conservative TAINT recovery refinement, for the GROUP epoch secret.

   The earlier "one honest committer + full update path" test is insufficient
   for a group secret when an *other* still-active member's decryption key was
   compromised. That member can retain a route to the tree's path material.

   We therefore require, for EACH earlier successful active-member exposure,
   a later accepted, authenticated fresh OWN path update by the COMPROMISED
   MEMBER itself before any such secret may be called a FreshQ candidate.
   No further successful exposure of that member is allowed after the update.

   This is intentionally more restrictive than the final ETK/CGKA game:
   removal can eventually heal too, but only after native membership and
   tree-path dependency proofs, and is NOT certified by this predicate.
   Crucially, an unrelated member's own Commit and an External Commit cannot
   prove recovery of an uncompromised leaf key merely by advancing epochs.

   Fresh randomness, member identity and native acceptance are STILL
   formal-event assertions awaiting Rust/OpenMLS refinement and QPT proof.
   No abstract Boolean here is claimed to be an authenticated source fact.
*)

op f4_native_recovery_candidate
    (trace : f4_fresh_event list)
    (exposure update ch : f4_fresh_event) : bool =
  update.`ff_kind = f4_kind_internal_commit /\
  update.`ff_group = exposure.`ff_group /\
  update.`ff_committer = exposure.`ff_member /\
  exposure.`ff_index < update.`ff_index /\
  update.`ff_index < ch.`ff_index /\
  update.`ff_accepted /\ update.`ff_authenticated /\
  update.`ff_full_update_path /\ update.`ff_fresh_update_path /\
  update.`ff_target_is_recipient /\
  ! has (fun e => f4_is_exposure_event e /\
                 e.`ff_group = exposure.`ff_group /\
                 e.`ff_member = exposure.`ff_member /\
                 update.`ff_index < e.`ff_index /\
                 e.`ff_index < ch.`ff_index) trace.

op f4_exposure_has_native_recovery
    (trace : f4_fresh_event list)
    (exposure ch : f4_fresh_event) : bool =
  has (fun update => f4_native_recovery_candidate
                      trace exposure update ch) trace.

op f4_unhealed_native_exposure
    (trace : f4_fresh_event list) (ch : f4_fresh_event) : bool =
  has (fun e => f4_relevant_exposure e ch /\
                ! f4_exposure_has_native_recovery trace e ch) trace.

op f4_strict_freshq_candidate
    (trace : f4_fresh_event list) (ch : f4_fresh_event) : bool =
  ch.`ff_kind = f4_kind_challenge /\
  ! f4_unhealed_native_exposure trace ch.

(* Quantified over a separate recovery oracle trace: proof of the
   projection is independent of how that oracle recognizes native healing. *)
lemma f4_no_relevant_exposure_implies_no_unhealed_any_oracle
    (prefix complete : f4_fresh_event list)
    (ch : f4_fresh_event) :
  !has (fun e => f4_relevant_exposure e ch) prefix =>
  !has (fun e => f4_relevant_exposure e ch /\
                 !f4_exposure_has_native_recovery complete e ch) prefix.
proof.
  elim prefix => [| e tail ih] //=.
  by smt().
qed.

lemma f4_strict_freshq_without_prior_exposure
    (tr : f4_fresh_event list) (ch : f4_fresh_event) :
  ch.`ff_kind = f4_kind_challenge =>
  ! f4_exposure_before_challenge tr ch =>
  f4_strict_freshq_candidate tr ch.
proof.
  move=> hkind hnone.
  rewrite /f4_strict_freshq_candidate hkind
          /f4_unhealed_native_exposure /=.
  rewrite /f4_exposure_before_challenge in hnone.
  exact (f4_no_relevant_exposure_implies_no_unhealed_any_oracle
           tr tr ch hnone).
qed.

lemma f4_unrelated_member_commit_cannot_recover_exposure
    (tr : f4_fresh_event list)
    (e update ch : f4_fresh_event) :
  update.`ff_committer <> e.`ff_member =>
  ! f4_native_recovery_candidate tr e update ch.
proof.
  rewrite /f4_native_recovery_candidate.
  by smt().
qed.

lemma f4_external_commit_cannot_recover_exposed_member
    (tr : f4_fresh_event list)
    (e update ch : f4_fresh_event) :
  update.`ff_kind = f4_kind_external_commit =>
  ! f4_native_recovery_candidate tr e update ch.
proof.
  rewrite /f4_native_recovery_candidate.
  by smt().
qed.

lemma f4_other_member_update_does_not_heal_single_exposure
    (e update ch : f4_fresh_event) :
  f4_relevant_exposure e ch =>
  update.`ff_kind = f4_kind_internal_commit =>
  update.`ff_committer <> e.`ff_member =>
  ! f4_strict_freshq_candidate [e; update] ch.
proof.
  move=> he hu hdiff.
  rewrite /f4_strict_freshq_candidate /f4_unhealed_native_exposure
          /f4_exposure_has_native_recovery /f4_native_recovery_candidate
          /=.
  by smt().
qed.

lemma f4_external_commit_does_not_heal_single_exposure
    (e update ch : f4_fresh_event) :
  f4_relevant_exposure e ch =>
  update.`ff_kind = f4_kind_external_commit =>
  ! f4_strict_freshq_candidate [e; update] ch.
proof.
  move=> he hu.
  rewrite /f4_strict_freshq_candidate /f4_unhealed_native_exposure
          /f4_exposure_has_native_recovery /f4_native_recovery_candidate
          /=.
  by smt().
qed.

(* Exact specification-gap witness: the earlier 'honest updater'
   predicate accepts a different member's clean internal update even after
   a still-active member's prior successful corruption. The stricter
   recovery predicate cannot count that update for the exposed member.
   This is not an attack on Product but shows why the earlier candidate
   could not be used as a PCS theorem premise. *)
lemma f4_other_member_update_old_heal_policy_gap
    (exposure update ch : f4_fresh_event) :
  exposure.`ff_kind = f4_kind_corrupt =>
  exposure.`ff_member_active =>
  exposure.`ff_group = update.`ff_group =>
  exposure.`ff_member <> update.`ff_committer =>
  exposure.`ff_index < update.`ff_index =>
  update.`ff_kind = f4_kind_internal_commit =>
  update.`ff_group = ch.`ff_group =>
  update.`ff_index < ch.`ff_index =>
  update.`ff_accepted =>
  update.`ff_authenticated =>
  update.`ff_epoch_before < update.`ff_epoch_after =>
  update.`ff_full_update_path =>
  update.`ff_fresh_update_path =>
  update.`ff_target_is_recipient =>
  f4_internal_heal_witness [exposure; update] update ch /\
  !f4_native_recovery_candidate [exposure; update] exposure update ch.
proof.
  move=> hekind heactive hegroup hother hindex hukind hugroup hui
          hacc hauth hepoch hpath hfresh hrecipient.
  rewrite /f4_internal_heal_witness /f4_committer_unexposed_before
          /f4_native_recovery_candidate /f4_is_exposure_event
          /f4_kind_corrupt /f4_kind_reveal /f4_kind_internal_commit
          /=.
  by smt().
qed.

(* Even the strict candidate is NOT the computational PCS/QPT theorem.
   It must later be shown that every native "fresh path" is independent
   of all attacker-held HPKE decryption keys and recovery state. *)
