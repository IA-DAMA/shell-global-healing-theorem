require import AllCore Real.
require import ShellTypes QPCS ProviderPCS_Adapter.
require import F4_Typed_Challenge_Model F4_Oracle_Call_Projection.

(* F4 game-level adapter: the entire F4 typed public call is passed as one
   context parameter to the already-defined provider PCS experiment. No
   additional axiom, cryptographic assumption, or ideal/real oracle is added.

   This is NOT a Rust-to-EasyCrypt extraction. A separately checked concrete
   implementation-to-PCS oracle semantics is still required. *)

op f4_encode_context : f4_oracle_call -> context.

(* Both provider experiments receive exactly the same chosen, accepted
   public challenge and context. This equality is over actual procedures
   ProviderPCSReal/ProviderPCSIdeal, not merely a record equality. *)
lemma f4_provider_real_game_call_equality
    (P <: ProviderPCS) (D <: QPCSDistinguisher{-P})
    (s : f4_shell) (p : f4_provider) (ch : f4_candidate)
    (c : cexport) &m :
  f4_guard s p ch =>
  Pr[ProviderPCSReal(P,D).main(c, f4_encode_context (f4_shell_oracle_call s)) @ &m : res] =
  Pr[ProviderPCSReal(P,D).main(c, f4_encode_context (f4_provider_oracle_call p)) @ &m : res].
proof.
  move=> hg.
  have [hsp _] := f4_typed_oracle_call_alignment s p ch hg.
  by rewrite hsp.
qed.

lemma f4_provider_ideal_game_call_equality
    (P <: ProviderPCS) (D <: QPCSDistinguisher{-P})
    (s : f4_shell) (p : f4_provider) (ch : f4_candidate)
    (c : cexport) &m :
  f4_guard s p ch =>
  Pr[ProviderPCSIdeal(P,D).main(c, f4_encode_context (f4_shell_oracle_call s)) @ &m : res] =
  Pr[ProviderPCSIdeal(P,D).main(c, f4_encode_context (f4_provider_oracle_call p)) @ &m : res].
proof.
  move=> hg.
  have [hsp _] := f4_typed_oracle_call_alignment s p ch hg.
  by rewrite hsp.
qed.

(* Actual game invocation under QPCS interface is transported losslessly
   from the matching provider call by the already-proved adapter lemma. *)
lemma f4_qpcs_real_equals_provider_real
    (P <: ProviderPCS) (D <: QPCSDistinguisher{-P})
    (s : f4_shell) (p : f4_provider) (ch : f4_candidate)
    (c : cexport) &m :
  f4_guard s p ch =>
  Pr[QPCSReal(ProviderPCSAdapter(P),D).main(c, f4_encode_context (f4_shell_oracle_call s)) @ &m : res] =
  Pr[ProviderPCSReal(P,D).main(c, f4_encode_context (f4_provider_oracle_call p)) @ &m : res].
proof.
  move=> hg.
  rewrite (qpcs_adapter_real_pr P D c
             (f4_encode_context (f4_shell_oracle_call s)) &m).
  exact (f4_provider_real_game_call_equality P D s p ch c &m hg).
qed.

lemma f4_qpcs_ideal_equals_provider_ideal
    (P <: ProviderPCS) (D <: QPCSDistinguisher{-P})
    (s : f4_shell) (p : f4_provider) (ch : f4_candidate)
    (c : cexport) &m :
  f4_guard s p ch =>
  Pr[QPCSIdeal(ProviderPCSAdapter(P),D).main(c, f4_encode_context (f4_shell_oracle_call s)) @ &m : res] =
  Pr[ProviderPCSIdeal(P,D).main(c, f4_encode_context (f4_provider_oracle_call p)) @ &m : res].
proof.
  move=> hg.
  rewrite (qpcs_adapter_ideal_pr P D c
             (f4_encode_context (f4_shell_oracle_call s)) &m).
  exact (f4_provider_ideal_game_call_equality P D s p ch c &m hg).
qed.

lemma f4_provider_pcs_bound_preserves_exact_advantage
    (P <: ProviderPCS) (D <: QPCSDistinguisher{-P})
    (s : f4_shell) (p : f4_provider) (ch : f4_candidate)
    (c : cexport) &m :
  f4_guard s p ch =>
  `|Pr[QPCSReal(ProviderPCSAdapter(P),D).main(c, f4_encode_context (f4_shell_oracle_call s)) @ &m : res] -
     Pr[QPCSIdeal(ProviderPCSAdapter(P),D).main(c, f4_encode_context (f4_shell_oracle_call s)) @ &m : res] | =
  `|Pr[ProviderPCSReal(P,D).main(c, f4_encode_context (f4_provider_oracle_call p)) @ &m : res] -
     Pr[ProviderPCSIdeal(P,D).main(c, f4_encode_context (f4_provider_oracle_call p)) @ &m : res] |.
proof.
  move=> hg.
  rewrite (f4_qpcs_real_equals_provider_real P D s p ch c &m hg).
  by rewrite (f4_qpcs_ideal_equals_provider_ideal P D s p ch c &m hg).
qed.
