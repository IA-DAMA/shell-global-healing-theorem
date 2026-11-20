require import AllCore Real StdOrder.
require import ShellTypes QPCS Exporter SplitPRF ShellPCS_Games.
require import QPCS_Hop Exporter_Hop SplitPRF_Hop.
import RealOrder.

(* Proof skeleton only.  No circular ShellSecure axiom is permitted.
   Required hops:
     G0 ~ G1 : imported QPCS PCS advantage, under FreshQ/AuthSafe.
     G1 ~ G2 : Exporter Preservation / KDF PRF advantage.
     G2 ~ G3 : MSS26 split-key PRF advantage with c exposed.
   History/auth failures are explicit bad-event terms in the final theorem.
*)

(* T1's cryptographic core.  Each premise is an external primitive-security
   obligation instantiated with the concrete reduction defined by the
   corresponding hop file.  The conclusion is only the G0 -> G3 hybrid bound:
   history and authentication bad events are deliberately not claimed here. *)
lemma t1_crypto_core_bound (Q <: QPCS) (E <: Exporter{-Q})
                           (M <: SplitPRF{-E, -Q})
                           (A <: Adv{-M, -E, -Q})
                           (c : cexport) (ctx : context)
                           (epsilon_qpcs epsilon_exporter
                            epsilon_splitprf : real) &m :
  `| Pr[QPCSReal(Q,QPCSReduction(E,M,A)).main(c,ctx) @ &m : res] -
     Pr[QPCSIdeal(Q,QPCSReduction(E,M,A)).main(c,ctx) @ &m : res] |
       <= epsilon_qpcs =>
  `| Pr[ExporterReal(Q,E,ExporterReduction(M,A)).main(c,ctx) @ &m : res] -
     Pr[ExporterIdeal(E,ExporterReduction(M,A)).main(c,ctx) @ &m : res] |
       <= epsilon_exporter =>
  `| Pr[SplitPRFReal(E,M,SplitPRFReduction(A)).main(c,ctx) @ &m : res] -
     Pr[SplitPRFIdeal(M,SplitPRFReduction(A)).main() @ &m : res] |
       <= epsilon_splitprf =>
  `| Pr[G0(Q,E,M,A).main(c,ctx) @ &m : res] -
     Pr[G3(M,A).main() @ &m : res] |
       <= epsilon_qpcs + epsilon_exporter + epsilon_splitprf.
proof.
  move=> hqpcs hexporter hsplitprf.
  have h01 := g0_g1_qpcs_reduction Q E M A c ctx epsilon_qpcs &m hqpcs.
  have h12 := g1_g2_exporter_reduction Q E M A c ctx epsilon_exporter &m hexporter.
  have h23 := g2_g3_splitprf_reduction Q E M A c ctx epsilon_splitprf &m hsplitprf.
  have h02 :
    `| Pr[G0(Q,E,M,A).main(c,ctx) @ &m : res] -
       Pr[G2(Q,E,M,A).main(c,ctx) @ &m : res] |
      <= epsilon_qpcs + epsilon_exporter.
  + apply (ler_trans
      (`| Pr[G0(Q,E,M,A).main(c,ctx) @ &m : res] -
          Pr[G1(Q,E,M,A).main(c,ctx) @ &m : res] | +
        `| Pr[G1(Q,E,M,A).main(c,ctx) @ &m : res] -
          Pr[G2(Q,E,M,A).main(c,ctx) @ &m : res] |)).
    - exact (StdOrder.RealOrder.ler_dist_add
        (Pr[G1(Q,E,M,A).main(c,ctx) @ &m : res])
        (Pr[G0(Q,E,M,A).main(c,ctx) @ &m : res])
        (Pr[G2(Q,E,M,A).main(c,ctx) @ &m : res])).
    - exact (ler_add _ _ _ _ h01 h12).
  apply (ler_trans
    (`| Pr[G0(Q,E,M,A).main(c,ctx) @ &m : res] -
        Pr[G2(Q,E,M,A).main(c,ctx) @ &m : res] | +
      `| Pr[G2(Q,E,M,A).main(c,ctx) @ &m : res] -
        Pr[G3(M,A).main() @ &m : res] |)).
  + exact (StdOrder.RealOrder.ler_dist_add
      (Pr[G2(Q,E,M,A).main(c,ctx) @ &m : res])
      (Pr[G0(Q,E,M,A).main(c,ctx) @ &m : res])
      (Pr[G3(M,A).main() @ &m : res])).
  + exact (ler_add _ _ _ _ h02 h23).
qed.
