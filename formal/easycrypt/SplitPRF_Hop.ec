require import AllCore.
require import ShellTypes QPCS Exporter SplitPRF ShellPCS_Games.

(* The final Shell adversary, packaged as a split-key PRF distinguisher. *)
module SplitPRFReduction(A:Adv) = {
  proc distinguish(k : kz) : bool = {
    var b;
    b <@ A.distinguish(k);
    return b;
  }
}.

lemma g2_is_splitprf_real (Q <: QPCS) (E <: Exporter{-Q})
                          (M <: SplitPRF{-E, -Q})
                          (A <: Adv{-M, -E, -Q})
                          (c : cexport) (ctx : context) :
  equiv [G2(Q,E,M,A).main ~
         SplitPRFReal(E,M,SplitPRFReduction(A)).main :
         ={c,ctx,glob E,glob M,glob A} ==> ={res}].
proof.
  proc.
  inline SplitPRFReduction(A).distinguish.
  sim.
qed.

lemma g3_is_splitprf_ideal (M <: SplitPRF) (A <: Adv{-M}) :
  equiv [G3(M,A).main ~ SplitPRFIdeal(M,SplitPRFReduction(A)).main :
         ={glob M,glob A} ==> ={res}].
proof.
  proc.
  inline SplitPRFReduction(A).distinguish.
  sim.
qed.

lemma g2_pr_splitprf_real (Q <: QPCS) (E <: Exporter{-Q})
                           (M <: SplitPRF{-E, -Q})
                           (A <: Adv{-M, -E, -Q})
                           (c : cexport) (ctx : context) &m :
  Pr[G2(Q,E,M,A).main(c,ctx) @ &m : res] =
  Pr[SplitPRFReal(E,M,SplitPRFReduction(A)).main(c,ctx) @ &m : res].
proof.
  by byequiv (g2_is_splitprf_real Q E M A c ctx).
qed.

lemma g3_pr_splitprf_ideal (M <: SplitPRF) (A <: Adv{-M}) &m :
  Pr[G3(M,A).main() @ &m : res] =
  Pr[SplitPRFIdeal(M,SplitPRFReduction(A)).main() @ &m : res].
proof.
  by byequiv (g3_is_splitprf_ideal M A).
qed.

(* Conditional quantitative G2 -> G3 reduction to the Q-fresh split-key PRF
   real-vs-ideal obligation. *)
lemma g2_g3_splitprf_reduction (Q <: QPCS) (E <: Exporter{-Q})
                               (M <: SplitPRF{-E, -Q})
                               (A <: Adv{-M, -E, -Q})
                               (c : cexport) (ctx : context)
                               (epsilon : real) &m :
  `| Pr[SplitPRFReal(E,M,SplitPRFReduction(A)).main(c,ctx) @ &m : res] -
     Pr[SplitPRFIdeal(M,SplitPRFReduction(A)).main() @ &m : res] | <= epsilon =>
  `| Pr[G2(Q,E,M,A).main(c,ctx) @ &m : res] -
     Pr[G3(M,A).main() @ &m : res] | <= epsilon.
proof.
  move=> hsplitprf.
  rewrite (g2_pr_splitprf_real Q E M A c ctx &m)
          (g3_pr_splitprf_ideal M A &m).
  exact hsplitprf.
qed.
