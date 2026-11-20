require import AllCore List.
require import Phi_Refinement Phi_Trace_Model Phi_Canonical_Events.
require import Phi_Window_Fold Phi_Safe_TTKEM.

(* Membership is derived from the same canonical event stream as the critical
   window. This removes a second independent interpretation of the challenge. *)

op genesis_members : member list.
op member_eq : member -> member -> bool.

op remove_member (u : member) (ms : member list) : member list =
  filter (fun x => ! member_eq x u) ms.

op membership_step (ms : member list) (e : event) : member list =
  if ev_remove e then remove_member (ev_member e) ms else ms.

op membership_fold (es : event list) : member list =
  foldl membership_step genesis_members es.

op shell_members_from_events
  (tr : shell_trace) (ch : challenge_binding) : member list =
  membership_fold (canonical_shell_events tr ch).

op provider_members_from_events (pv : provider_view) : member list =
  membership_fold (canonical_provider_events pv).

lemma equal_projection_equal_membership
    (tr : shell_trace) (ch : challenge_binding) :
  event_projection_ok tr ch =>
  shell_members_from_events tr ch =
  provider_members_from_events (phi tr ch).
proof.
  move=> h.
  rewrite /shell_members_from_events /provider_members_from_events.
  by rewrite (event_projection_is_same_list tr ch h).
qed.

(* The challenge enumerators are now required to be the event-derived
   membership, not independently supplied lists. *)
op membership_enumerators_canonical
  (tr : shell_trace) (ch : challenge_binding) : bool =
  challenge_members tr ch = shell_members_from_events tr ch /\
  provider_challenge_members (phi tr ch) =
    provider_members_from_events (phi tr ch).

lemma event_projection_implies_membership_projection
    (tr : shell_trace) (ch : challenge_binding) :
  event_projection_ok tr ch =>
  membership_enumerators_canonical tr ch =>
  membership_projection_ok tr ch.
proof.
  move=> he hc.
  move: hc; rewrite /membership_enumerators_canonical.
  move=> [hcs hcp].
  rewrite /membership_projection_ok.
  have hm := equal_projection_equal_membership tr ch he.
  rewrite hcs hcp.
  exact hm.
qed.

lemma covered_to_safe_from_single_event_projection
    (tr : shell_trace) (ch : challenge_binding) :
  event_projection_ok tr ch =>
  membership_enumerators_canonical tr ch =>
  covered_fold tr ch =>
  safe_ttkem_fold (phi tr ch).
proof.
  move=> he hc hf.
  have hm := event_projection_implies_membership_projection tr ch he hc.
  exact (covered_fold_to_safe_ttkem_fold tr ch he hm hf).
qed.

(* Result: once challenge membership is defined by the same projected accepted
   events, both the critical-window state and membership cross Phi from one
   event_projection_ok obligation. *)
