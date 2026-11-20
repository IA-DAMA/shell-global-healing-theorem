require import AllCore.
require import ShellTypes Phi_Refinement F4_Typed_Challenge_Model ShellPCS_T1_Conditional.

(* Concrete-instantiation bridge, with an independently selected authority.
   All observations remain typed and abstract. The proof isolates the
   *one unresolved semantic refinement*, not a false F4_FULL claim. *)

type f4_external_authority.
type f4_signed_selection.
type f4_signer_key.

op f4_current_generation : f4_external_authority -> int.
op f4_current_head : f4_external_authority -> f4_head.
op f4_claim_generation : f4_signed_selection -> int.
op f4_claim_head : f4_signed_selection -> f4_head.
op f4_claim_candidate : f4_signed_selection -> f4_candidate.
op f4_claim_leg : f4_signed_selection -> int.
op f4_selected_leg : f4_candidate -> int.
op f4_valid_authority_signature : f4_signed_selection -> f4_signer_key -> bool.
op f4_honest_issuer_issued : f4_signed_selection -> bool.

(* The signature relation is NOT assumed unforgeable. If a signed, unissued
   selection verifies, we explicitly classify that outcome as bad signature. *)
op f4_bad_signature (w : f4_signed_selection) (key : f4_signer_key) : bool =
  f4_valid_authority_signature w key /\ !f4_honest_issuer_issued w.

(* No transition is authorized by this read-only predicate. The trusted
   current authority head/generation/key must be provided OUTSIDE local SQLite. *)
op f4_external_gate (a : f4_external_authority)
                    (w : f4_signed_selection)
                    (key : f4_signer_key)
                    (s : f4_shell) (p : f4_provider)
                    (c : f4_candidate) : bool =
  f4_valid_authority_signature w key /\
  0 < f4_current_generation a /\
  f4_claim_generation w = f4_current_generation a /\
  f4_claim_head w = f4_current_head a /\
  f4_claim_head w = f4_s_head s /\
  f4_claim_candidate w = c /\
  f4_claim_leg w = f4_selected_leg c /\
  f4_guard s p c.

(* This is a VALID symbolic theorem: selected head, typed challenge and
   accepted OpenMLS view agree, provided the guards are true. *)
lemma f4_external_selection_implies_same
      (a : f4_external_authority) (w : f4_signed_selection)
      (key : f4_signer_key) (s : f4_shell)
      (p : f4_provider) (c : f4_candidate) :
  f4_external_gate a w key s p c =>
  f4_challenge_same s p /\ !f4_bad_challenge s p c /\
  f4_s_head s = f4_current_head a.
proof.
  rewrite /f4_external_gate /f4_guard /f4_bad_challenge
          /f4_challenge_same /f4_shell_matches /f4_provider_matches.
  by smt().
qed.

lemma f4_modified_local_head_is_rejected
      (a : f4_external_authority) (w : f4_signed_selection)
      (key : f4_signer_key) (s : f4_shell)
      (p : f4_provider) (c : f4_candidate) :
  f4_s_head s <> f4_current_head a =>
  !f4_external_gate a w key s p c.
proof.
  rewrite /f4_external_gate.
  by smt().
qed.

lemma f4_stale_generation_is_rejected
      (a : f4_external_authority) (w : f4_signed_selection)
      (key : f4_signer_key) (s : f4_shell)
      (p : f4_provider) (c : f4_candidate) :
  f4_claim_generation w <> f4_current_generation a =>
  !f4_external_gate a w key s p c.
proof.
  rewrite /f4_external_gate.
  by smt().
qed.

lemma f4_unissued_signature_is_explicit_bad
      (a : f4_external_authority) (w : f4_signed_selection)
      (key : f4_signer_key) (s : f4_shell)
      (p : f4_provider) (c : f4_candidate) :
  f4_external_gate a w key s p c =>
  !f4_honest_issuer_issued w =>
  f4_bad_signature w key.
proof.
  rewrite /f4_external_gate /f4_bad_signature.
  by smt().
qed.

(* Exact T1 projection shapes. No claim that they are implemented or proved. *)
op f4_trace_of : f4_shell -> shell_trace.
op f4_challenge_of : f4_candidate -> challenge_binding.
op f4_context_of : f4_candidate -> context.

(* THIS is the remaining semantic obligation:
   an accepted real provider and independently authenticated Shell authority
   must refine the oracle context used by T1. Do not assert it as an axiom. *)
op f4_provider_oracle_refinement (s : f4_shell) (p : f4_provider)
                                 (c : f4_candidate) : bool =
  f4_guard s p c =>
  challenge_context_binding (f4_trace_of s)
                            (f4_challenge_of c)
                            (f4_context_of c).

lemma f4_t1_binding_reduction
      (a : f4_external_authority) (w : f4_signed_selection)
      (key : f4_signer_key) (s : f4_shell)
      (p : f4_provider) (c : f4_candidate) :
  f4_provider_oracle_refinement s p c =>
  f4_external_gate a w key s p c =>
  challenge_context_binding (f4_trace_of s)
                            (f4_challenge_of c)
                            (f4_context_of c).
proof.
  rewrite /f4_provider_oracle_refinement /f4_external_gate.
  by smt().
qed.
