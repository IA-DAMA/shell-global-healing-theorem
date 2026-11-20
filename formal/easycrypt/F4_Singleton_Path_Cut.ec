require import AllCore List DInterval Distr StdOrder.
require import F4_Epoch_Continuation_Hop.
require import F4_Leaf_Cut_Fixture F4_Epoch_Schedule_Cut.

(* Restrict to the direct HPKE recipient route in a two-leaf tree. Route
   means that the matching private key AND its usable predecessor state
   are available, with the valid wire. All other material stays in v. *)
op f4_add_recipient_route v (route : bool) : f4_view =
  fun x => v x \/ (x = CommitInput /\ route).

lemma f4_recipient_cut_exact (v : f4_view) route :
  (exists d, foldl f4_learn (f4_add_recipient_route v route) d Output) <=>
  f4_output_route v \/ (route /\ v InitInput /\ v PskInput).
proof.
  rewrite f4_output_route_exact /f4_output_route /f4_add_recipient_route; smt().
qed.

lemma f4_removal_has_no_wire_recipient :
  let (old, next, before, after, rotated, path, active, removed_eq, survivor_eq) = removal_cut in
  old = 1 /\ next = 2 /\ before = 2 /\ after = 1 /\ rotated /\ path = [] /\
  !active /\ !removed_eq /\ survivor_eq.
proof. by rewrite /removal_cut. qed.

lemma f4_alternating_first_old_leaf_cut (v : f4_view) :
  let (e1,e2,e3,path2,path3,old2,old3,peer2,comparisons) = alternating_cut in
  v InitInput => v PskInput =>
  e1 = 1 /\ e2 = 2 /\ e3 = 3 /\ path2 = [1] /\ path3 = [1] /\ peer2 /\
  comparisons = [false;false;false;true] /\
  (exists d, foldl f4_learn (f4_add_recipient_route v old2) d Output) /\
  ((exists d, foldl f4_learn (f4_add_recipient_route v old3) d Output) <=> f4_output_route v).
proof. rewrite /alternating_cut /= !f4_recipient_cut_exact; smt(). qed.

(* The prefix may be chosen adaptively. This sampler is specialized to a
   fresh independent draw at the end of the prefix. Values derived from the
   draw, including public outputs, belong in the continuation. *)
module type F4BeforeSingletonDraw = { proc prefix() : f4_prefix }.
module F4SingletonSource(S:F4BeforeSingletonDraw) = {
  proc sample() : f4_prefix * int = {
    var p, k;
    p <@ S.prefix();
    k <$ dinter 0 (2^384-1);
    return (p,k);
  }
}.

lemma f4_singleton_path_identity
    (S <: F4BeforeSingletonDraw) (D <: F4ReadCommit{-S}) &m :
  Pr[F4CommitExperiment(F4SingletonSource(S),D).main(false) @ &m : res] =
  Pr[F4CommitExperiment(F4SingletonSource(S),D).main(true) @ &m : res].
proof.
  byequiv (_ : ={glob S, glob D} /\ !uniform_path{1} /\ uniform_path{2}
                ==> ={res}) => //.
  proc.
  rcondf{1} 2; first by move=> &hr; call (_: true); auto.
  rcondt{2} 2; first by move=> &hr; call (_: true); auto.
  call (_: ={arg,glob D} ==> ={res}); first by sim.
  inline F4SingletonSource(S).sample.
  wp; rnd; wp; rnd{2}; call (_: ={glob S} ==> ={glob S,res}); first by sim.
  have hll : is_lossless (dinter 0 (2^384-1)).
  + apply dinter_ll; smt(IntOrder.expr_gt0).
  by auto; progress; smt().
qed.

lemma f4_singleton_only_exporter_term
    (S <: F4BeforeSingletonDraw) (A <: F4ReadSelected{-S}) ek &m :
  `|Pr[F4SelectedExperiment(F4SingletonSource(S),A).main(true) @ &m : res] -
    Pr[F4RandomSelectedExperiment(F4SingletonSource(S),A).main(true) @ &m : res]| <= ek =>
  `|Pr[F4SelectedExperiment(F4SingletonSource(S),A).main(false) @ &m : res] -
    Pr[F4RandomSelectedExperiment(F4SingletonSource(S),A).main(false) @ &m : res]| <= ek.
proof.
  move=> h.
  have l := f4_singleton_path_identity S (F4CommitReduction(A)) &m.
  have r := f4_singleton_path_identity S (F4RandomOutputReduction(A)) &m.
  have bound := f4_one_epoch_recovery_bound (F4SingletonSource(S)) A 0%r ek 0%r &m.
  by rewrite l r /= in bound; smt().
qed.

(* Quantify the two endpoint simulations separately; ideal entropy cannot
   be substituted for an actual RNG for free. The variables real and ideal
   denote acceptance probabilities from the executions being refined. *)
lemma f4_singleton_endpoint_budget
    (S <: F4BeforeSingletonDraw) (A <: F4ReadSelected{-S}) real ideal eta_r eta_i ek &m :
  `|real - Pr[F4SelectedExperiment(F4SingletonSource(S),A).main(false) @ &m : res]| <= eta_r =>
  `|Pr[F4RandomSelectedExperiment(F4SingletonSource(S),A).main(false) @ &m : res] - ideal| <= eta_i =>
  `|Pr[F4SelectedExperiment(F4SingletonSource(S),A).main(true) @ &m : res] -
    Pr[F4RandomSelectedExperiment(F4SingletonSource(S),A).main(true) @ &m : res]| <= ek =>
  `|real - ideal| <= eta_r + ek + eta_i.
proof.
  move=> hr hi hk.
  have middle := f4_singleton_only_exporter_term S A ek &m hk.
  smt(RealOrder.ler_dist_add).
qed.
