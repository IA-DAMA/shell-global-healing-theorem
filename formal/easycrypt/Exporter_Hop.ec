require import AllCore.
require import ShellTypes QPCS Exporter SplitPRF ShellPCS_Games.

(* The unchanged computation after the exporter challenge. *)
module ExporterReduction(M:SplitPRF, A:Adv) = {
  proc distinguish(qe : qexport, c : cexport, ctx : context) : bool = {
    var k, b;
    k <@ M.eval(c, qe, ctx);
    b <@ A.distinguish(k);
    return b;
  }
}.

lemma g1_is_exporter_real (Q <: QPCS) (E <: Exporter{-Q})
                          (M <: SplitPRF{-E, -Q})
                          (A <: Adv{-M, -E, -Q})
                          (c : cexport) (ctx : context) :
  equiv [G1(Q,E,M,A).main ~
         ExporterReal(Q,E,ExporterReduction(M,A)).main :
         ={c,ctx,glob Q,glob E,glob M,glob A} ==> ={res}].
proof.
  proc.
  inline ExporterReduction(M,A).distinguish.
  sim.
qed.

lemma g2_is_exporter_ideal (Q <: QPCS) (E <: Exporter{-Q})
                           (M <: SplitPRF{-E, -Q})
                           (A <: Adv{-M, -E, -Q})
                           (c : cexport) (ctx : context) :
  equiv [G2(Q,E,M,A).main ~
         ExporterIdeal(E,ExporterReduction(M,A)).main :
         ={c,ctx,glob E,glob M,glob A} ==> ={res}].
proof.
  proc.
  inline ExporterReduction(M,A).distinguish.
  sim.
qed.

lemma g1_pr_exporter_real (Q <: QPCS) (E <: Exporter{-Q})
                           (M <: SplitPRF{-E, -Q})
                           (A <: Adv{-M, -E, -Q})
                           (c : cexport) (ctx : context) &m :
  Pr[G1(Q,E,M,A).main(c,ctx) @ &m : res] =
  Pr[ExporterReal(Q,E,ExporterReduction(M,A)).main(c,ctx) @ &m : res].
proof.
  by byequiv (g1_is_exporter_real Q E M A c ctx).
qed.

lemma g2_pr_exporter_ideal (Q <: QPCS) (E <: Exporter{-Q})
                            (M <: SplitPRF{-E, -Q})
                            (A <: Adv{-M, -E, -Q})
                            (c : cexport) (ctx : context) &m :
  Pr[G2(Q,E,M,A).main(c,ctx) @ &m : res] =
  Pr[ExporterIdeal(E,ExporterReduction(M,A)).main(c,ctx) @ &m : res].
proof.
  by byequiv (g2_is_exporter_ideal Q E M A c ctx).
qed.

(* Conditional quantitative G1 -> G2 reduction to Lemma E's exact
   exporter real-vs-ideal obligation. *)
lemma g1_g2_exporter_reduction (Q <: QPCS) (E <: Exporter{-Q})
                               (M <: SplitPRF{-E, -Q})
                               (A <: Adv{-M, -E, -Q})
                               (c : cexport) (ctx : context)
                               (epsilon : real) &m :
  `| Pr[ExporterReal(Q,E,ExporterReduction(M,A)).main(c,ctx) @ &m : res] -
     Pr[ExporterIdeal(E,ExporterReduction(M,A)).main(c,ctx) @ &m : res] | <= epsilon =>
  `| Pr[G1(Q,E,M,A).main(c,ctx) @ &m : res] -
     Pr[G2(Q,E,M,A).main(c,ctx) @ &m : res] | <= epsilon.
proof.
  move=> hexporter.
  rewrite (g1_pr_exporter_real Q E M A c ctx &m)
          (g2_pr_exporter_ideal Q E M A c ctx &m).
  exact hexporter.
qed.
