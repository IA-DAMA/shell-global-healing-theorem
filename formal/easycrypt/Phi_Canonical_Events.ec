require import AllCore Int List.
require import Phi_Refinement Phi_Trace_Model Phi_Critical_Window.

(* Provider-relevant event algebra.  Network delivery attempts that never alter
   accepted provider state are intentionally absent from the critical-window
   projection. *)

type event.

op ev_accept_update : event -> bool.
op ev_corrupt_start : event -> bool.
op ev_corrupt_end : event -> bool.
op ev_reveal : event -> bool.
op ev_remove : event -> bool.
op ev_challenge : event -> bool.

op ev_member : event -> member.
op ev_pos : event -> position.

op shell_events : shell_trace -> challenge_binding -> event list.
op provider_events : provider_view -> event list.

(* Security-relevant projection: the concrete instantiation must erase only
   events that cannot affect membership, current-key source, exposure windows,
   acceptance, generator or challenge position. *)
op relevant : event -> bool =
  fun e =>
    ev_accept_update e \/ ev_corrupt_start e \/ ev_corrupt_end e \/
    ev_reveal e \/ ev_remove e \/ ev_challenge e.

op project (es : event list) : event list = filter relevant es.

op canonical_shell_events
  (tr : shell_trace) (ch : challenge_binding) : event list =
  project (shell_events tr ch).

op canonical_provider_events (pv : provider_view) : event list =
  project (provider_events pv).

op event_projection_ok
  (tr : shell_trace) (ch : challenge_binding) : bool =
  canonical_shell_events tr ch =
  canonical_provider_events (phi tr ch).

lemma event_projection_is_same_list
    (tr : shell_trace) (ch : challenge_binding) :
  event_projection_ok tr ch =>
  canonical_shell_events tr ch =
  canonical_provider_events (phi tr ch).
proof.
  by rewrite /event_projection_ok.
qed.

(* The next bridge is deliberately explicit: canonical_trace must be a
   deterministic interpretation of the projected event list. *)
op interpret_events : event list -> canonical_trace.

op canonicalize_shell_events
  (tr : shell_trace) (ch : challenge_binding) : canonical_trace =
  interpret_events (canonical_shell_events tr ch).

op canonicalize_provider_events (pv : provider_view) : canonical_trace =
  interpret_events (canonical_provider_events pv).

lemma event_projection_implies_critical_projection
    (tr : shell_trace) (ch : challenge_binding) :
  event_projection_ok tr ch =>
  canonicalize_shell_events tr ch =
  canonicalize_provider_events (phi tr ch).
proof.
  move=> h.
  rewrite /canonicalize_shell_events /canonicalize_provider_events.
  by rewrite (event_projection_is_same_list tr ch h).
qed.

(* Mutation hooks.  These are predicates over the projection boundary; a
   concrete refinement proof must show that dropping/moving a relevant event
   makes event_projection_ok false. *)
op drops_relevant_event :
  shell_trace -> challenge_binding -> bool.
op moves_relevant_event_across_challenge :
  shell_trace -> challenge_binding -> bool.
op invents_acceptance :
  shell_trace -> challenge_binding -> bool.

op projection_well_formed
  (tr : shell_trace) (ch : challenge_binding) : bool =
  ! drops_relevant_event tr ch /\
  ! moves_relevant_event_across_challenge tr ch /\
  ! invents_acceptance tr ch.

lemma projection_well_formed_decomposes
    (tr : shell_trace) (ch : challenge_binding) :
  projection_well_formed tr ch =>
  ! drops_relevant_event tr ch /\
  ! moves_relevant_event_across_challenge tr ch /\
  ! invents_acceptance tr ch.
proof.
  by rewrite /projection_well_formed.
qed.
