require import AllCore Int List.
require import Phi_Refinement Phi_Trace_Model Phi_Canonical_Events.
require import Phi_Window_Fold Phi_Safe_TTKEM Phi_Membership_Fold.

(* Explicit dual-log event trace under an accepted-message gate.
   This is a precise state-machine MODEL. A Rust/OpenMLS event-source
   refinement remains separate. Corrupt, reveal, removal, challenge may
   never be silently filtered as harmless network-only events. *)

type f4_acceptance_trace = {
  f4_shell_log : event list;
  f4_provider_log : event list;
}.

op f4_empty_trace : f4_acceptance_trace =
  {| f4_shell_log = []; f4_provider_log = [] |}.

op f4_logs_aligned (t : f4_acceptance_trace) : bool =
  t.`f4_shell_log = t.`f4_provider_log.

(* An attempted but not accepted update is NOT installed. Other relevant
   events, especially corruption, are still inserted when observed. *)
op f4_observe_pair (t : f4_acceptance_trace) (e : event)
                   (accepted_update : bool) : f4_acceptance_trace =
  if ev_accept_update e /\ !accepted_update then t
  else if relevant e then
    {| f4_shell_log = t.`f4_shell_log ++ [e];
       f4_provider_log = t.`f4_provider_log ++ [e] |}
  else t.

op f4_member_exposed_shell (t : f4_acceptance_trace) (u : member) : bool =
  (fold_member u (t.`f4_shell_log)).`mf_exposed_current.

op f4_member_exposed_provider (t : f4_acceptance_trace) (u : member) : bool =
  (fold_member u (t.`f4_provider_log)).`mf_exposed_current.

op f4_challenge_fresh_shell (t : f4_acceptance_trace)
                            (ms : member list) : bool =
  all (fun u => ! f4_member_exposed_shell t u) ms.

op f4_challenge_fresh_provider (t : f4_acceptance_trace)
                               (ms : member list) : bool =
  all (fun u => ! f4_member_exposed_provider t u) ms.

lemma f4_empty_trace_aligned : f4_logs_aligned f4_empty_trace.
proof.
  by rewrite /f4_logs_aligned /f4_empty_trace.
qed.

lemma f4_pair_step_preserves_logs (t : f4_acceptance_trace)
    (e : event) (accepted_update : bool) :
  f4_logs_aligned t =>
  f4_logs_aligned (f4_observe_pair t e accepted_update).
proof.
  move=> h.
  rewrite /f4_logs_aligned /f4_observe_pair.
  case (ev_accept_update e /\ !accepted_update).
  + exact h.
  case (relevant e).
  + by rewrite /f4_logs_aligned in h; rewrite h.
  exact h.
qed.

lemma f4_unaccepted_update_cannot_change_trace (t : f4_acceptance_trace)
    (e : event) :
  ev_accept_update e =>
  f4_observe_pair t e false = t.
proof.
  move=> h.
  by rewrite /f4_observe_pair h.
qed.

lemma f4_equal_logs_equal_exposure (t : f4_acceptance_trace)
    (u : member) :
  f4_logs_aligned t =>
  f4_member_exposed_shell t u = f4_member_exposed_provider t u.
proof.
  move=> h.
  rewrite /f4_member_exposed_shell /f4_member_exposed_provider.
  move: h; rewrite /f4_logs_aligned => h.
  by rewrite h.
qed.

lemma f4_equal_logs_equal_challenge_freshness
    (t : f4_acceptance_trace) (ms : member list) :
  f4_logs_aligned t =>
  f4_challenge_fresh_shell t ms =
  f4_challenge_fresh_provider t ms.
proof.
  move=> h.
  rewrite /f4_challenge_fresh_shell /f4_challenge_fresh_provider
          /f4_member_exposed_shell /f4_member_exposed_provider.
  move: h; rewrite /f4_logs_aligned => h.
  by rewrite h.
qed.

(* This establishes preservation inside the operational event MODEL.
   It DOES NOT claim that OpenMLS 0.9.0/Rust raises all these events or
   satisfies a computational PCS/QPT security bound. *) 
