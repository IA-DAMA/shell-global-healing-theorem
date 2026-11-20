require import AllCore Real.
require import ShellTypes QPCS Exporter SplitPRF ShellPCS_Games.
require import QPCS_Hop Exporter_Hop SplitPRF_Hop ShellPCS_T1.

(* Exact advantage shape extracted from MSS26, Theorem 1:

     Adv_M <= 2 q (Adv_PRG + Adv_Ext) + Adv_PRF.

   This file does not re-prove the MSS26 theorem or instantiate its PRF, PRG,
   and resilient extractor.  It makes that imported contract explicit at the
   Shell composition boundary instead of hiding it behind one opaque epsilon.
*)
op mss26_bound (q epsilon_prg epsilon_ext epsilon_prf : real) : real =
  2%r * q * (epsilon_prg + epsilon_ext) + epsilon_prf.

lemma t1_mss26_crypto_core_bound
    (Q <: QPCS) (E <: Exporter{-Q})
    (M <: SplitPRF{-E, -Q})
    (A <: Adv{-M, -E, -Q})
    (c : cexport) (ctx : context)
    (epsilon_qpcs epsilon_exporter q
     epsilon_prg epsilon_ext epsilon_prf : real) &m :
  `| Pr[QPCSReal(Q,QPCSReduction(E,M,A)).main(c,ctx) @ &m : res] -
     Pr[QPCSIdeal(Q,QPCSReduction(E,M,A)).main(c,ctx) @ &m : res] |
       <= epsilon_qpcs =>
  `| Pr[ExporterReal(Q,E,ExporterReduction(M,A)).main(c,ctx) @ &m : res] -
     Pr[ExporterIdeal(E,ExporterReduction(M,A)).main(c,ctx) @ &m : res] |
       <= epsilon_exporter =>
  `| Pr[SplitPRFReal(E,M,SplitPRFReduction(A)).main(c,ctx) @ &m : res] -
     Pr[SplitPRFIdeal(M,SplitPRFReduction(A)).main() @ &m : res] |
       <= mss26_bound q epsilon_prg epsilon_ext epsilon_prf =>
  `| Pr[G0(Q,E,M,A).main(c,ctx) @ &m : res] -
     Pr[G3(M,A).main() @ &m : res] |
       <= epsilon_qpcs + epsilon_exporter +
          mss26_bound q epsilon_prg epsilon_ext epsilon_prf.
proof.
  move=> hqpcs hexporter hmss26.
  exact (t1_crypto_core_bound Q E M A c ctx
           epsilon_qpcs epsilon_exporter
           (mss26_bound q epsilon_prg epsilon_ext epsilon_prf) &m
           hqpcs hexporter hmss26).
qed.
