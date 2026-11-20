require import AllCore Real.
require import ShellTypes QPCS Exporter SplitPRF ShellPCS_Games.
require import QPCS_Hop Exporter_Hop SplitPRF_Hop.
require import ShellPCS_MSS26 Phi_Refinement Phi_Trace_Model.
require import Phi_Canonical_Events Phi_Window_Fold Phi_Safe_TTKEM.
require import Phi_Membership_Fold.

(* Provider-neutral Shell T1.

   This theorem closes the conditional composition statement and nothing
   stronger.  The concrete provider must discharge the premise named
   provider_pcs_under_shell_contract.  In particular, this file does not turn
   an RFC, a ciphersuite name, or an executable OpenMLS profile into a QPT PCS
   theorem.

   The trace-side freshness premise is not an opaque post-hoc boolean:
   event_projection_ok and membership_enumerators_canonical force Shell and
   the provider to interpret the same accepted event stream, and covered_fold
   is then transported to safe_ttkem_fold by a proved refinement lemma.
*)

op oracle_correspondence : shell_trace -> challenge_binding -> bool.
op challenge_context_binding :
  shell_trace -> challenge_binding -> context -> bool.
op authentication_conditions : shell_trace -> challenge_binding -> bool.
op clone_session_conditions : shell_trace -> challenge_binding -> bool.
op composition_side_conditions :
  shell_trace -> challenge_binding -> context -> bool.

lemma t1_shell_pcs_conditional_bound
    (Q <: QPCS) (E <: Exporter{-Q})
    (M <: SplitPRF{-E, -Q})
    (A <: Adv{-M, -E, -Q})
    (tr : shell_trace) (ch : challenge_binding)
    (c : cexport) (ctx : context)
    (epsilon_qpcs epsilon_exporter q
     epsilon_prg epsilon_ext epsilon_prf : real) &m :
  event_projection_ok tr ch =>
  membership_enumerators_canonical tr ch =>
  covered_fold tr ch =>
  oracle_correspondence tr ch =>
  challenge_context_binding tr ch ctx =>
  authentication_conditions tr ch =>
  clone_session_conditions tr ch =>
  composition_side_conditions tr ch ctx =>
  (safe_ttkem_fold (phi tr ch) =>
   oracle_correspondence tr ch =>
   challenge_context_binding tr ch ctx =>
   authentication_conditions tr ch =>
   clone_session_conditions tr ch =>
   composition_side_conditions tr ch ctx =>
   `| Pr[QPCSReal(Q,QPCSReduction(E,M,A)).main(c,ctx) @ &m : res] -
      Pr[QPCSIdeal(Q,QPCSReduction(E,M,A)).main(c,ctx) @ &m : res] |
        <= epsilon_qpcs) =>
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
  move=> he hm hf ho hc ha hs hx hp he_exporter hmss26.
  have hsafe :=
    covered_to_safe_from_single_event_projection tr ch he hm hf.
  have hqpcs := hp hsafe ho hc ha hs hx.
  exact (t1_mss26_crypto_core_bound Q E M A c ctx
           epsilon_qpcs epsilon_exporter q
           epsilon_prg epsilon_ext epsilon_prf &m
           hqpcs he_exporter hmss26).
qed.

(* The theorem above proves the exact implication requested by the Shell
   architecture:

     provider safety + valid Shell/provider correspondence +
     authenticated transition context + secure composition
       => Shell challenge-key security bound.

   A concrete OpenMLS/TTKEM/QPT corollary remains a separate instantiation
   obligation and is intentionally not asserted here. *)
