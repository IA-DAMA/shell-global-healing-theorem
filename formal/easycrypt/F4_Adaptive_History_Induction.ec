require import AllCore Int List.
require import F4_Adaptive_Challenger_Ledger F4_Direct_Exposure_Challenge.

(* Induction over adversarial histories, including arbitrary interleaving of
   send/Welcome/Commit/challenge with corrupt/reveal. No fabricated native
   observations: these are challenger-side queries. This model still does not
   determine QPT FreshQ or prove Rust/OpenMLS refinement. *)

op f4_adversarial_run (s : f4_adversarial_state)
                      (qs : f4_adversarial_query list) :
                        f4_adversarial_state =
  foldl f4_adversarial_step s qs.

lemma f4_arbitrary_history_preserves_direct_bad
    (qs : f4_adversarial_query list)
    (s : f4_adversarial_state) (ch : f4_adversarial_entry) :
  f4_direct_bad_before s.`f4_s_exposures ch =>
  f4_direct_bad_before
    (f4_adversarial_run s qs).`f4_s_exposures ch.
proof.
  rewrite /f4_adversarial_run.
  elim: qs s => [| q qs ih] s /=.
  + by [].
  move=> h.
  apply (ih (f4_adversarial_step s q)).
  case (f4_is_exposure q).
  + move=> he.
    have hnext : (f4_adversarial_step s q).`f4_s_exposures =
       s.`f4_s_exposures ++ [f4_before_entry s q]
       by exact (f4_corrupt_or_reveal_persists s q he).
    rewrite hnext.
    exact (f4_append_cannot_erase_direct_bad
             s.`f4_s_exposures [f4_before_entry s q] ch h).
  + move=> hn.
    have hnext : (f4_adversarial_step s q).`f4_s_exposures =
       s.`f4_s_exposures
       by exact (f4_other_queries_cannot_erase_exposures s q hn).
    by rewrite hnext.
qed.

lemma f4_arbitrary_history_query_count
    (qs : f4_adversarial_query list)
    (s : f4_adversarial_state) :
  size (f4_adversarial_run s qs).`f4_s_queries =
  size s.`f4_s_queries + size qs.
proof.
  rewrite /f4_adversarial_run.
  elim: qs s => [| q qs ih] s /=.
  + by smt().
  rewrite (ih (f4_adversarial_step s q)).
  rewrite /f4_adversarial_step.
  by smt(size_cat).
qed.
