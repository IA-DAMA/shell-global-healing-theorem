require import AllCore List StdOrder F4_Adversarial_Query_Ledger F4_Interactive_PCS_Game.
require import ShellTypes F4_Post_Installation_Challenge.

(* For an arbitrary continuing adversary with precisely the public oracle
   interface, show that the current game admits no healing once a successful
   full-state corruption or reveal has been recorded. The suffix may include
   any number of authenticated commits. No losslessness assumption is needed
   for the zero probability of returning a selected challenge. *)
op prior (xs : f4_query_record list) n =
  has (fun q : f4_query_record => q.`f4_q_index < n) xs.

lemma later xs n : prior xs n => prior xs (n+1).
proof. rewrite /prior => /hasP [q [member old]]; apply/hasP; exists q; smt(). qed.

lemma append_later xs n q : prior xs n => prior (xs ++ [q]) (n+1).
proof. move=> h; have h1 := later xs n h; rewrite /prior has_cat; smt(). qed.

lemma new_prior q n epoch c r xs :
  prior (xs ++ [f4_challenger_tag q n epoch c r]) (n+1).
proof. by rewrite /prior has_cat /f4_challenger_tag /=; smt(). qed.

lemma disclosure_survives_suffix (B <: F4ProductPCSBackend{-F4Challenger})
    (A <: F4AdaptivePCSAdversary{-F4Challenger,-B}) :
  hoare [A(F4Challenger(B)).guess :
    prior F4Challenger.exposures F4Challenger.query_count ==>
    prior F4Challenger.exposures F4Challenger.query_count].
proof.
  proc (prior F4Challenger.exposures F4Challenger.query_count) => //;
    try (by proc; wp; call (_: true); auto; smt(later append_later));
    try (by proc; auto).
  proc.
  rcondt 3.
  + wp; skip; rewrite /prior; move=> &hr old.
    have hg := gate_fresh_exact F4Challenger.exposures{hr}
       (f4_challenger_tag q{hr} F4Challenger.query_count{hr} F4Challenger.global_epoch{hr} false false).
    rewrite /f4_challenger_tag /= in hg; smt().
  by auto; smt(later).
qed.

module AfterExposure(B:F4ProductPCSBackend,A:F4AdaptivePCSAdversary) = {
  proc run(capture : bool, q : f4_query_record, target : f4_query_record, ctx : context) : bool = {
    var exposed, snap, secret, key;
    if (capture) {
      snap <@ F4Challenger(B).corrupt(q);
      exposed <- snap <> None;
    } else {
      secret <@ F4Challenger(B).reveal(q);
      exposed <- secret <> None;
    }
    key <- None;
    if (exposed) {
      A(F4Challenger(B)).guess();
      key <@ F4Challenger(B).challenge(target,ctx);
    }
    return exposed /\ key <> None;
  }
}.

lemma zero_healed_challenges (B <: F4ProductPCSBackend{-F4Challenger})
    (A <: F4AdaptivePCSAdversary{-F4Challenger,-B}) &m cap q target ctx :
  Pr[AfterExposure(B,A).run(cap,q,target,ctx) @ &m : res] = 0%r.
proof.
  byphoare (_: true ==> res) => //; hoare.
  proc; seq 2 : (key = None /\ (!exposed \/ prior F4Challenger.exposures F4Challenger.query_count)).
  + wp; if; [inline F4Challenger(B).corrupt | inline F4Challenger(B).reveal];
      wp; call (_: true); auto; smt(new_prior).
  if; last by auto.
  call (successful_history_veto B); call (disclosure_survives_suffix B A); auto;
    rewrite /prior; smt().
qed.

lemma native_selection_error_floor (B <: F4ProductPCSBackend{-F4Challenger})
    (A <: F4AdaptivePCSAdversary{-F4Challenger,-B}) &m cap q target ctx p e :
  0%r <= p =>
  `|p - Pr[AfterExposure(B,A).run(cap,q,target,ctx) @ &m : res]| <= e =>
  p <= e.
proof. move=> hp; rewrite (zero_healed_challenges B A &m cap q target ctx) /=.
  by rewrite RealOrder.ger0_norm.
qed.
