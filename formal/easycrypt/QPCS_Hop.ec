require import AllCore.
require import ShellTypes QPCS Exporter SplitPRF ShellPCS_Games.

(* Explicit reduction context for the G0 -> G1 hop.
   The continuation below is exactly the Shell computation after the QPCS
   challenge: exporter, split-key combiner, then adversary. *)

module Continue(E:Exporter, M:SplitPRF, A:Adv) = {
  proc run(q : qsecret, c : cexport, ctx : context) : bool = {
    var qe, k, b;
    qe <@ E.derive(q, ctx);
    k <@ M.eval(c, qe, ctx);
    b <@ A.distinguish(k);
    return b;
  }
}.

module RealHop(Q:QPCS, E:Exporter, M:SplitPRF, A:Adv) = {
  proc main(c : cexport, ctx : context) : bool = {
    var q, b;
    q <@ Q.real(ctx);
    b <@ Continue(E,M,A).run(q,c,ctx);
    return b;
  }
}.

module IdealHop(Q:QPCS, E:Exporter, M:SplitPRF, A:Adv) = {
  proc main(c : cexport, ctx : context) : bool = {
    var q, b;
    q <@ Q.ideal(ctx);
    b <@ Continue(E,M,A).run(q,c,ctx);
    return b;
  }
}.

(* Factor the structural argument before relating whole games.
   This lemma isolates the only abstraction barrier introduced by RealHop:
   Continue.run versus its explicit body. *)
module ExplicitContinue(E:Exporter, M:SplitPRF, A:Adv) = {
  proc run(q : qsecret, c : cexport, ctx : context) : bool = {
    var qe, k, b;
    qe <@ E.derive(q, ctx);
    k <@ M.eval(c, qe, ctx);
    b <@ A.distinguish(k);
    return b;
  }
}.

lemma continue_is_explicit (Q <: QPCS) (E <: Exporter{-Q})
                           (M <: SplitPRF{-E, -Q})
                           (A <: Adv{-M, -E, -Q})
                           (q : qsecret) (c : cexport) (ctx : context) :
  equiv [Continue(E,M,A).run ~ ExplicitContinue(E,M,A).run :
         ={q,c,ctx,glob E,glob M,glob A} ==> ={res}].
proof.
  proc.
  do 3! call (_: true); auto.
qed.

(* The Shell continuation, packaged as a generic QPCS distinguisher.  This is
   the actual reduction: it receives the QPCS challenge q and runs the rest of
   the unchanged Shell computation. *)
module QPCSReduction(E:Exporter, M:SplitPRF, A:Adv) = {
  proc distinguish(q : qsecret, c : cexport, ctx : context) : bool = {
    var b;
    b <@ Continue(E,M,A).run(q, c, ctx);
    return b;
  }
}.

(* Whole-game structural equivalences.  Equality of module globals is the
   standard EasyCrypt precondition for comparing the same stateful abstract
   providers/adversary in two memories; it is not a cryptographic assumption. *)
lemma g0_is_qpcs_real (Q <: QPCS) (E <: Exporter{-Q})
                      (M <: SplitPRF{-E, -Q})
                      (A <: Adv{-M, -E, -Q})
                      (c : cexport) (ctx : context) :
  equiv [G0(Q,E,M,A).main ~ QPCSReal(Q,QPCSReduction(E,M,A)).main :
         ={c,ctx,glob Q,glob E,glob M,glob A} ==> ={res}].
proof.
  proc.
  inline QPCSReduction(E,M,A).distinguish Continue(E,M,A).run.
  sim.
qed.

lemma g1_is_qpcs_ideal (Q <: QPCS) (E <: Exporter{-Q})
                       (M <: SplitPRF{-E, -Q})
                       (A <: Adv{-M, -E, -Q})
                       (c : cexport) (ctx : context) :
  equiv [G1(Q,E,M,A).main ~ QPCSIdeal(Q,QPCSReduction(E,M,A)).main :
         ={c,ctx,glob Q,glob E,glob M,glob A} ==> ={res}].
proof.
  proc.
  inline QPCSReduction(E,M,A).distinguish Continue(E,M,A).run.
  sim.
qed.

lemma g0_pr_qpcs_real (Q <: QPCS) (E <: Exporter{-Q})
                      (M <: SplitPRF{-E, -Q})
                      (A <: Adv{-M, -E, -Q})
                      (c : cexport) (ctx : context) &m :
  Pr[G0(Q,E,M,A).main(c,ctx) @ &m : res] =
  Pr[QPCSReal(Q,QPCSReduction(E,M,A)).main(c,ctx) @ &m : res].
proof.
  by byequiv (g0_is_qpcs_real Q E M A c ctx).
qed.

lemma g1_pr_qpcs_ideal (Q <: QPCS) (E <: Exporter{-Q})
                       (M <: SplitPRF{-E, -Q})
                       (A <: Adv{-M, -E, -Q})
                       (c : cexport) (ctx : context) &m :
  Pr[G1(Q,E,M,A).main(c,ctx) @ &m : res] =
  Pr[QPCSIdeal(Q,QPCSReduction(E,M,A)).main(c,ctx) @ &m : res].
proof.
  by byequiv (g1_is_qpcs_ideal Q E M A c ctx).
qed.

(* Quantitative G0 -> G1 reduction.  The premise is exactly the imported
   QPCS real-vs-ideal bound instantiated with QPCSReduction.  No Shell
   security axiom is introduced: any upstream theorem matching this game can
   discharge the premise. *)
lemma g0_g1_qpcs_reduction (Q <: QPCS) (E <: Exporter{-Q})
                           (M <: SplitPRF{-E, -Q})
                           (A <: Adv{-M, -E, -Q})
                           (c : cexport) (ctx : context)
                           (epsilon : real) &m :
  `| Pr[QPCSReal(Q,QPCSReduction(E,M,A)).main(c,ctx) @ &m : res] -
     Pr[QPCSIdeal(Q,QPCSReduction(E,M,A)).main(c,ctx) @ &m : res] | <= epsilon =>
  `| Pr[G0(Q,E,M,A).main(c,ctx) @ &m : res] -
     Pr[G1(Q,E,M,A).main(c,ctx) @ &m : res] | <= epsilon.
proof.
  move=> hqpcs.
  rewrite (g0_pr_qpcs_real Q E M A c ctx &m)
          (g1_pr_qpcs_ideal Q E M A c ctx &m).
  exact hqpcs.
qed.

(* Next independent hops: G1 -> G2 (Exporter) and G2 -> G3 (SplitPRF). *)
