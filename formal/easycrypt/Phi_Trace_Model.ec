require import AllCore Int List.
require import Phi_Refinement.

(* Finite provider-relevant trace model for the T1-COVERED track.
   This file deliberately models only the information needed by the upstream
   safe predicate. Global history uniqueness remains outside T1. *)

type member.
type position.

type accepted_view = {
  av_members : member list;
  av_generator : member;
  av_challenge_pos : position;
}.

op shell_view : shell_trace -> challenge_binding -> accepted_view.
op provider_view_of : provider_view -> accepted_view.

op current_key_source_shell :
  shell_trace -> challenge_binding -> member -> position.
op current_key_source_provider :
  provider_view -> member -> position.

op exposed_shell :
  shell_trace -> challenge_binding -> member -> position -> position -> bool.
op exposed_provider :
  provider_view -> member -> position -> position -> bool.

op accepted_shell : shell_trace -> challenge_binding -> bool.
op accepted_provider : provider_view -> bool.

(* Concrete meaning of the preservation gates used by Phi_Refinement. *)
axiom L1_meaning (tr : shell_trace) (ch : challenge_binding) :
  l1_membership tr ch =>
  (shell_view tr ch).`av_members =
  (provider_view_of (phi tr ch)).`av_members.

axiom L2_meaning (tr : shell_trace) (ch : challenge_binding) (u : member) :
  l2_key_source tr ch =>
  current_key_source_shell tr ch u =
  current_key_source_provider (phi tr ch) u.

axiom L3_meaning (tr : shell_trace) (ch : challenge_binding)
                 (u : member) (lo hi : position) :
  l3_corruption_window tr ch =>
  exposed_shell tr ch u lo hi =
  exposed_provider (phi tr ch) u lo hi.

axiom L4_meaning (tr : shell_trace) (ch : challenge_binding) :
  l4_generator tr ch =>
  (shell_view tr ch).`av_generator =
  (provider_view_of (phi tr ch)).`av_generator.

axiom L5_meaning (tr : shell_trace) (ch : challenge_binding) :
  l5_challenge_position tr ch =>
  (shell_view tr ch).`av_challenge_pos =
  (provider_view_of (phi tr ch)).`av_challenge_pos.

axiom L6_meaning (tr : shell_trace) (ch : challenge_binding) :
  l6_acceptance tr ch =>
  accepted_shell tr ch = accepted_provider (phi tr ch).

(* L7 prevents a session selector from silently swapping the provider state.
   It is intentionally separate from global fork consistency. *)
op selected_shell_provider_view :
  shell_trace -> challenge_binding -> provider_view.

axiom L7_meaning (tr : shell_trace) (ch : challenge_binding) :
  l7_selected_state tr ch =>
  selected_shell_provider_view tr ch = phi tr ch.

lemma phi_preserves_membership (tr : shell_trace) (ch : challenge_binding) :
  phi_preserves tr ch =>
  (shell_view tr ch).`av_members =
  (provider_view_of (phi tr ch)).`av_members.
proof.
  move=> hp.
  apply (L1_meaning tr ch).
  move: hp; rewrite /phi_preserves.
  move=> [h1 hrest].
  exact h1.
qed.

lemma phi_preserves_generator (tr : shell_trace) (ch : challenge_binding) :
  phi_preserves tr ch =>
  (shell_view tr ch).`av_generator =
  (provider_view_of (phi tr ch)).`av_generator.
proof.
  move=> hp.
  apply (L4_meaning tr ch).
  move: hp; rewrite /phi_preserves.
  move=> [h1 [h2 [h3 [h4 hrest]]]].
  exact h4.
qed.

lemma phi_preserves_challenge_position
    (tr : shell_trace) (ch : challenge_binding) :
  phi_preserves tr ch =>
  (shell_view tr ch).`av_challenge_pos =
  (provider_view_of (phi tr ch)).`av_challenge_pos.
proof.
  move=> hp.
  apply (L5_meaning tr ch).
  move: hp; rewrite /phi_preserves.
  move=> [h1 [h2 [h3 [h4 [h5 hrest]]]]].
  exact h5.
qed.
