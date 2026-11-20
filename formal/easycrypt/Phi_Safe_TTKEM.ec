require import AllCore List.
require import Phi_Refinement Phi_Trace_Model Phi_Canonical_Events Phi_Window_Fold.

(* T1-COVERED safety over the canonical event fold.
   This is deliberately a provider-track theorem, not T2/global history. *)

op member_current_and_safe
  (tr : shell_trace) (ch : challenge_binding) (u : member) : bool =
  ! (shell_member_fold tr ch u).`mf_removed /\
  ! (shell_member_fold tr ch u).`mf_exposed_current.

op provider_member_current_and_safe
  (pv : provider_view) (u : member) : bool =
  ! (provider_member_fold pv u).`mf_removed /\
  ! (provider_member_fold pv u).`mf_exposed_current.

(* Membership enumeration at the challenge boundary. *)
op challenge_members :
  shell_trace -> challenge_binding -> member list.

op provider_challenge_members :
  provider_view -> member list.

op covered_fold
  (tr : shell_trace) (ch : challenge_binding) : bool =
  all (fun u => member_current_and_safe tr ch u)
      (challenge_members tr ch).

op safe_ttkem_fold (pv : provider_view) : bool =
  all (fun u => provider_member_current_and_safe pv u)
      (provider_challenge_members pv).

(* L1 at the event-model boundary.  This is now the sole membership bridge
   needed by the fold theorem; the next concrete refinement must derive it
   from accepted membership events/challenge binding. *)
op membership_projection_ok
  (tr : shell_trace) (ch : challenge_binding) : bool =
  challenge_members tr ch =
  provider_challenge_members (phi tr ch).

lemma event_projection_preserves_member_safety
    (tr : shell_trace) (ch : challenge_binding) (u : member) :
  event_projection_ok tr ch =>
  member_current_and_safe tr ch u =
  provider_member_current_and_safe (phi tr ch) u.
proof.
  move=> hp.
  rewrite /member_current_and_safe /provider_member_current_and_safe.
  have hf := equal_projection_equal_member_fold tr ch u hp.
  by rewrite hf.
qed.

lemma covered_fold_to_safe_ttkem_fold
    (tr : shell_trace) (ch : challenge_binding) :
  event_projection_ok tr ch =>
  membership_projection_ok tr ch =>
  covered_fold tr ch =>
  safe_ttkem_fold (phi tr ch).
proof.
  move=> he hm hc.
  rewrite /covered_fold in hc.
  rewrite /safe_ttkem_fold.
  rewrite /membership_projection_ok in hm.
  rewrite -hm.
  apply (List.allP (fun u => provider_member_current_and_safe (phi tr ch) u)
                   (challenge_members tr ch)).
  move=> u hu.
  have hs :
    member_current_and_safe tr ch u.
  + move/List.allP: hc => hall.
    exact (hall u hu).
  have hp := event_projection_preserves_member_safety tr ch u he.
  move: hs.
  by rewrite hp.
qed.

(* No post-hoc adversary-win term appears in either covered_fold or
   safe_ttkem_fold.  The theorem depends only on the pre-challenge event
   projection and membership projection. *)
