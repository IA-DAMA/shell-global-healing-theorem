require import AllCore Int List.
require import F4_Adaptive_Challenger_Ledger.
require import F4_Direct_Exposure_Challenge F4_Adaptive_History_Induction.

(* F4-E: independent adversarial-world chronology.
   A product-visible epoch alone cannot reveal whether the challenger
   observed a hidden corrupt/reveal query: both operations may preserve
   the same public epoch while only one appends an exposure. This is a
   proven obstruction to deriving FreshQ from signed epoch equality.

   These lemmas do NOT instantiate OpenMLS, T1 FreshQ, or QPT PCS. *)

lemma f4_public_epoch_cannot_decide_hidden_exposure
    (s : f4_adversarial_state)
    (hidden public : f4_adversarial_query) :
  f4_is_exposure hidden =>
  !f4_is_exposure public =>
  !f4_advances_global_epoch public =>
  (f4_adversarial_step s hidden).`f4_s_global_epoch =
    (f4_adversarial_step s public).`f4_s_global_epoch /\
  (f4_adversarial_step s hidden).`f4_s_exposures =
    s.`f4_s_exposures ++ [f4_before_entry s hidden] /\
  (f4_adversarial_step s public).`f4_s_exposures =
    s.`f4_s_exposures.
proof.
  move=> hex hnot hstay.
  have hhidden := f4_exposure_query_never_advances_epoch hidden hex.
  rewrite /f4_adversarial_step hex hnot hhidden hstay.
  by smt().
qed.

(* Challenge selection is fixed by the challenger at the next query index,
   with the pre-challenge epoch, even if the preceding query was malicious. *)
lemma f4_next_challenge_index_and_epoch_are_prestate_bound
    (s : f4_adversarial_state)
    (q ch : f4_adversarial_query) :
  f4_is_challenge ch =>
  (f4_before_entry (f4_adversarial_step s q) ch).`f4_e_index =
    size s.`f4_s_queries + 1 /\
  (f4_before_entry (f4_adversarial_step s q) ch).`f4_e_global_epoch_before =
    (f4_adversarial_step s q).`f4_s_global_epoch /\
  (f4_adversarial_step (f4_adversarial_step s q) ch).`f4_s_challenges =
    (f4_adversarial_step s q).`f4_s_challenges ++
    [f4_before_entry (f4_adversarial_step s q) ch].
proof.
  move=> hch.
  split.
  + rewrite /f4_before_entry /f4_adversarial_step.
    by smt(size_cat).
  split.
  + exact (f4_query_records_pre_state_epoch (f4_adversarial_step s q) ch).
  + exact (f4_challenge_attempt_always_recorded (f4_adversarial_step s q) ch hch).
qed.

(* A same-target corrupt/reveal directly preceding a challenge cannot be
   retroactively removed from that challenge's fixed adversarial ledger.
   This is a challenger theorem, not a claim that later honest epochs
   cannot heal different future challenge secrets. *)
lemma f4_frozen_challenge_retains_prior_corruption_under_any_future_history
    (s : f4_adversarial_state)
    (q ch : f4_adversarial_query)
    (future : f4_adversarial_query list) :
  f4_is_exposure q =>
  f4_is_challenge ch =>
  q.`f4_q_member = ch.`f4_q_member =>
  q.`f4_q_device = ch.`f4_q_device =>
  q.`f4_q_secret_kind = ch.`f4_q_secret_kind =>
  f4_direct_bad_before
    (f4_adversarial_run
      (f4_adversarial_step (f4_adversarial_step s q) ch) future).`f4_s_exposures
    (f4_before_entry (f4_adversarial_step s q) ch).
proof.
  move=> hex hch hm hd hk.
  have hbad := f4_corrupt_before_next_challenge_direct_bad
    s q ch hex hch hm hd hk.
  have hnot : ! f4_is_exposure ch
    by rewrite /f4_is_exposure /f4_is_challenge in hch; smt().
  have hsame :
    (f4_adversarial_step (f4_adversarial_step s q) ch).`f4_s_exposures =
    (f4_adversarial_step s q).`f4_s_exposures
    by exact (f4_other_queries_cannot_erase_exposures
                (f4_adversarial_step s q) ch hnot).
  have hpre :
    f4_direct_bad_before
      (f4_adversarial_step (f4_adversarial_step s q) ch).`f4_s_exposures
      (f4_before_entry (f4_adversarial_step s q) ch)
    by rewrite hsame; exact hbad.
  exact (f4_arbitrary_history_preserves_direct_bad
           future (f4_adversarial_step (f4_adversarial_step s q) ch)
           (f4_before_entry (f4_adversarial_step s q) ch) hpre).
qed.
