require import AllCore Int List.
require import F4_Adversarial_Query_Ledger F4_External_FreshQ_Criterion.

(* F4-E: the explicit information-preserving projection from a challenger-
   owned successful corrupt/reveal record to the group-wide FreshQ event
   calculus. The successful-exposure ledger, not the public attempt ledger,
   is the source of the q input.

   This deliberately accepts only a proven-active membership bit and
   authenticated group identity as parameters. No claim is made that the
   real OpenMLS code has supplied those proof witnesses; that is the
   Rust-to-EasyCrypt refinement obligation. *)

op f4_member_number : f4_member_id -> int.
op f4_device_number : f4_device_id -> int.
op f4_secret_number : f4_secret_kind_id -> int.

op f4_successful_disclosure_to_fresh_event
    (authenticated_group : int) (active : bool)
    (q : f4_query_record) : f4_fresh_event =
  {| ff_index = q.`f4_q_index;
     ff_group = authenticated_group;
     ff_epoch_before = q.`f4_q_epoch;
     ff_epoch_after = q.`f4_q_epoch;
     ff_member = f4_member_number q.`f4_q_member;
     ff_device = f4_device_number q.`f4_q_device;
     ff_secret_kind = f4_secret_number q.`f4_q_secret_kind;
     ff_committer = f4_member_number q.`f4_q_member;
     ff_kind = if q.`f4_q_corrupt then f4_kind_corrupt else f4_kind_reveal;
     ff_member_active = active;
     ff_accepted = false;
     ff_authenticated = false;
     ff_full_update_path = false;
     ff_fresh_update_path = false;
     ff_target_is_recipient = false |}.

lemma f4_successful_exposure_projected_as_exposure
    (group : int) (active : bool) (q : f4_query_record) :
  (q.`f4_q_corrupt \/ q.`f4_q_reveal) =>
  f4_is_exposure_event
    (f4_successful_disclosure_to_fresh_event group active q).
proof.
  rewrite /f4_is_exposure_event /f4_successful_disclosure_to_fresh_event
          /f4_kind_corrupt /f4_kind_reveal.
  by smt().
qed.

lemma f4_projected_successful_exposure_preserves_index
    (group : int) (active : bool) (q : f4_query_record) :
  (f4_successful_disclosure_to_fresh_event group active q).`ff_index =
  q.`f4_q_index.
proof.
  by rewrite /f4_successful_disclosure_to_fresh_event.
qed.

(* For a GROUP epoch-secret challenge, even a different member/device's
   successful exposure is relevant. This avoids the false inference that
   same-member/same-device/same-epoch direct guards are sufficient for PCS.
   No healer exists in the one-event prefix, irrespective of epoch labels. *)
lemma f4_single_successful_disclosure_blocks_group_freshq
    (group : int) (q : f4_query_record)
    (ch : f4_fresh_event) :
  (q.`f4_q_corrupt \/ q.`f4_q_reveal) =>
  ch.`ff_kind = f4_kind_challenge =>
  ch.`ff_group = group =>
  ch.`ff_secret_kind = f4_secret_number q.`f4_q_secret_kind =>
  q.`f4_q_index < ch.`ff_index =>
  ! f4_freshq_candidate
       [f4_successful_disclosure_to_fresh_event group true q] ch.
proof.
  move=> hex hkind hgroup hclass hindex.
  have hrel :
    f4_relevant_exposure
      (f4_successful_disclosure_to_fresh_event group true q) ch
    by rewrite /f4_relevant_exposure
               /f4_successful_disclosure_to_fresh_event
               /f4_is_exposure_event
               /f4_kind_corrupt /f4_kind_reveal; smt().
  have hexposure :
    f4_exposure_before_challenge
      [f4_successful_disclosure_to_fresh_event group true q] ch
    by rewrite /f4_exposure_before_challenge /=; exact hrel.
  have hnoheal :
    !f4_healed_since_last_exposure
      [f4_successful_disclosure_to_fresh_event group true q] ch
    by rewrite /f4_healed_since_last_exposure /f4_internal_heal_witness
               /f4_successful_disclosure_to_fresh_event
               /= /f4_kind_corrupt /f4_kind_reveal
                  /f4_kind_internal_commit; smt().
  exact (f4_freshq_rejects_unhealed_prior_exposure
           [f4_successful_disclosure_to_fresh_event group true q]
           ch hexposure hnoheal).
qed.

(* External Commit is NOT automatically a PCS healing event, even when it
   advances epochs, has a signed native receipt, and follows a disclosure.
   Here the event list contains no qualifying internal path update. *)
lemma f4_external_commit_after_disclosure_is_not_automatic_healing
    (group : int) (q : f4_query_record)
    (ext ch : f4_fresh_event) :
  (q.`f4_q_corrupt \/ q.`f4_q_reveal) =>
  ext.`ff_kind = f4_kind_external_commit =>
  ch.`ff_kind = f4_kind_challenge =>
  ch.`ff_group = group =>
  ch.`ff_secret_kind = f4_secret_number q.`f4_q_secret_kind =>
  q.`f4_q_index < ch.`ff_index =>
  ! f4_freshq_candidate
       [f4_successful_disclosure_to_fresh_event group true q; ext] ch.
proof.
  move=> hex hext hkind hgroup hclass hindex.
  have hrel :
    f4_relevant_exposure
      (f4_successful_disclosure_to_fresh_event group true q) ch
    by rewrite /f4_relevant_exposure
               /f4_successful_disclosure_to_fresh_event
               /f4_is_exposure_event
               /f4_kind_corrupt /f4_kind_reveal; smt().
  have hexposure :
    f4_exposure_before_challenge
      [f4_successful_disclosure_to_fresh_event group true q; ext] ch
    by rewrite /f4_exposure_before_challenge /=; smt().
  have hnoheal :
    !f4_healed_since_last_exposure
      [f4_successful_disclosure_to_fresh_event group true q; ext] ch
    by rewrite /f4_healed_since_last_exposure /= /f4_internal_heal_witness
               /f4_successful_disclosure_to_fresh_event
               /f4_kind_corrupt /f4_kind_reveal
               /f4_kind_internal_commit; smt().
  exact (f4_freshq_rejects_unhealed_prior_exposure
           [f4_successful_disclosure_to_fresh_event group true q; ext]
           ch hexposure hnoheal).
qed.
