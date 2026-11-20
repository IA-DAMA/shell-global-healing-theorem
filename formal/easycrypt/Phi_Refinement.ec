require import AllCore.
require import ShellTypes.

(* Research-only T1 refinement boundary. *)
type shell_trace.
type challenge_binding.
type provider_view.

op phi : shell_trace -> challenge_binding -> provider_view.
op covered_fresh_q : shell_trace -> challenge_binding -> bool.
op safe_provider : provider_view -> bool.

op l1_membership : shell_trace -> challenge_binding -> bool.
op l2_key_source : shell_trace -> challenge_binding -> bool.
op l3_corruption_window : shell_trace -> challenge_binding -> bool.
op l4_generator : shell_trace -> challenge_binding -> bool.
op l5_challenge_position : shell_trace -> challenge_binding -> bool.
op l6_acceptance : shell_trace -> challenge_binding -> bool.
op l7_selected_state : shell_trace -> challenge_binding -> bool.

op phi_preserves (tr : shell_trace) (ch : challenge_binding) : bool =
  l1_membership tr ch /\ l2_key_source tr ch /\
  l3_corruption_window tr ch /\ l4_generator tr ch /\
  l5_challenge_position tr ch /\ l6_acceptance tr ch /\
  l7_selected_state tr ch.

(* This lemma is intentionally only the decomposition gate. It does not assume
   or prove CoveredFreshQ -> SafeProvider. The substantive refinement theorem
   must derive safe_provider(phi tr ch) from concrete trace semantics. *)
lemma phi_preservation_decomposes (tr : shell_trace) (ch : challenge_binding) :
  phi_preserves tr ch =>
  l1_membership tr ch /\ l2_key_source tr ch /\
  l3_corruption_window tr ch /\ l4_generator tr ch /\
  l5_challenge_position tr ch /\ l6_acceptance tr ch /\
  l7_selected_state tr ch.
proof.
  by rewrite /phi_preserves.
qed.
