require import AllCore Int List.
require import F4_Adaptive_Challenger_Ledger.

(* F4-E direct exposure gate for the challenger-owned chronological ledger.
   These definitions apply to observed same-epoch corruption/reveal only.
   The T1 FreshQ predicate, future healing, Rust event-source simulation and
   QPT PCS advantage are separate unproved obligations. *)

op f4_prior_direct_exposure (e ch : f4_adversarial_entry) : bool =
  f4_is_exposure e.`f4_e_query /\
  e.`f4_e_index < ch.`f4_e_index /\
  e.`f4_e_global_epoch_before = ch.`f4_e_global_epoch_before /\
  e.`f4_e_query.`f4_q_member = ch.`f4_e_query.`f4_q_member /\
  e.`f4_e_query.`f4_q_device = ch.`f4_e_query.`f4_q_device /\
  e.`f4_e_query.`f4_q_secret_kind =
    ch.`f4_e_query.`f4_q_secret_kind.

op f4_direct_bad_before
    (exposures : f4_adversarial_entry list)
    (ch : f4_adversarial_entry) : bool =
  has (fun e => f4_prior_direct_exposure e ch) exposures.

lemma f4_append_cannot_erase_direct_bad
    (prefix suffix : f4_adversarial_entry list)
    (ch : f4_adversarial_entry) :
  f4_direct_bad_before prefix ch =>
  f4_direct_bad_before (prefix ++ suffix) ch.
proof.
  rewrite /f4_direct_bad_before has_cat.
  by smt().
qed.

lemma f4_later_exposure_is_not_prior
    (e ch : f4_adversarial_entry) :
  ch.`f4_e_index <= e.`f4_e_index =>
  ! f4_prior_direct_exposure e ch.
proof.
  rewrite /f4_prior_direct_exposure.
  by smt().
qed.

lemma f4_different_target_cannot_match_direct
    (e ch : f4_adversarial_entry) :
  (e.`f4_e_query.`f4_q_member <> ch.`f4_e_query.`f4_q_member \/
   e.`f4_e_query.`f4_q_device <> ch.`f4_e_query.`f4_q_device \/
   e.`f4_e_query.`f4_q_secret_kind <>
      ch.`f4_e_query.`f4_q_secret_kind) =>
  ! f4_prior_direct_exposure e ch.
proof.
  rewrite /f4_prior_direct_exposure.
  by smt().
qed.

lemma f4_exposure_query_never_advances_epoch
    (q : f4_adversarial_query) :
  f4_is_exposure q => ! f4_advances_global_epoch q.
proof.
  rewrite /f4_is_exposure /f4_advances_global_epoch.
  by smt().
qed.

(* A corrupt/reveal immediately preceding a same-target challenge is
   detectable by the challenger, even if the device never reports it.
   This proves NO recovery after any accepted honest Commit. *)
lemma f4_corrupt_before_next_challenge_direct_bad
    (s : f4_adversarial_state)
    (q ch : f4_adversarial_query) :
  f4_is_exposure q =>
  f4_is_challenge ch =>
  q.`f4_q_member = ch.`f4_q_member =>
  q.`f4_q_device = ch.`f4_q_device =>
  q.`f4_q_secret_kind = ch.`f4_q_secret_kind =>
  f4_direct_bad_before
    (f4_adversarial_step s q).`f4_s_exposures
    (f4_before_entry (f4_adversarial_step s q) ch).
proof.
  move=> hex hch hm hd hk.
  have hno := f4_exposure_query_never_advances_epoch q hex.
  rewrite /f4_direct_bad_before /f4_adversarial_step hex /=.
  rewrite /f4_prior_direct_exposure /f4_before_entry
          /f4_is_exposure /f4_advances_global_epoch.
  by smt(has_cat size_cat size_ge0).
qed.
