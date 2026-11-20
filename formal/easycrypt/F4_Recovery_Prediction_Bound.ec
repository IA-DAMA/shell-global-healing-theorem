require import AllCore DInterval Distr StdOrder.
require import F4_Epoch_Continuation_Hop.

(* The predictor only receives information exposed to the decision procedure.
   QPT security must also cover efficient classical predictors. Existence
   of a predictor for a concrete Product trace is not assumed. *)
op f4_predict : f4_prior_view -> f4_epoch_public -> int.

module F4PredictionTest = {
  proc decide(v : f4_prior_view, obs : f4_selected_observation) : bool = {
    return obs <> None /\ (oget obs).`2 = Some (f4_predict v (oget obs).`1);
  }
}.

(* Shared branches cancel for any final binary effect, including effects
   applied to an auxiliary quantum register. The semantics supplying the
   acceptance probabilities and the cq coupling are in the companion note. *)
lemma f4_shared_branch_gap (common mass a b : real) :
  0%r <= mass <= 1%r => 0%r <= a <= 1%r => 0%r <= b <= 1%r =>
  `|(common + mass * a) - (common + mass * b)| <= mass.
proof.
  move=> hm ha hb.
  rewrite RealOrder.ler_norml.
  have hpa : 0%r <= mass * a by smt(RealOrder.mulr_ge0).
  have hpb : 0%r <= mass * b by smt(RealOrder.mulr_ge0).
  have hca : 0%r <= mass * (1%r-a) by smt(RealOrder.mulr_ge0).
  have hcb : 0%r <= mass * (1%r-b) by smt(RealOrder.mulr_ge0).
  smt().
qed.

lemma f4_same_uniform_path k :
  0 <= k < 2^384 => mu1 (dinter 0 (2^384-1)) k = 1%r / (2^384)%r.
proof.
  move=> h; have h' : 0 <= k <= 2^384-1 by smt().
  by rewrite dinter1E h' /=.
qed.

lemma f4_prediction_real p k pub y &m :
  f4_run_selected p k = Some (pub, Some y) =>
  f4_predict p.`old_view pub = y =>
  Pr[F4FinishEpoch(F4PredictionTest).run(false,p,k) @ &m : res] = 1%r.
proof.
  move=> ho hp.
  byphoare (_ : arg = (false,p,k) ==> res) => //.
  proc; inline F4PredictionTest.decide; wp; rcondf 2; first by auto.
  by auto; smt().
qed.

lemma f4_prediction_random prefix path pub y &m :
  f4_run_selected prefix path = Some (pub, Some y) =>
  0 <= f4_predict prefix.`old_view pub < 2^256 =>
  Pr[F4FinishEpoch(F4PredictionTest).run(true,prefix,path) @ &m : res] =
    1%r / (2^256)%r.
proof.
  move=> ho hr.
  byphoare (_ : random_output /\ p = prefix /\ k = path ==> res) => //.
  proc; inline F4PredictionTest.decide; wp; rcondt 2; first by auto; smt().
  wp; rnd (pred1 (f4_predict prefix.`old_view pub)); wp; skip.
  move=> &hr0 [[_ [hp hk]] _].
  rewrite dinter1E.
  have bound : 0 <= f4_predict prefix.`old_view pub <= 2^256 - 1 by smt().
  by rewrite hp hk ho bound /=.
qed.
