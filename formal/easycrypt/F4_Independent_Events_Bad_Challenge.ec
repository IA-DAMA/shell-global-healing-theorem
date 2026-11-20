require import AllCore Int List.
require import F4_Typed_Challenge_Model Phi_Canonical_Events.

(* Independent event observations: unlike a paired append function, the
   provider and Shell inputs are independently supplied. Corruption, removal,
   reveal and challenge events are all relevant. No new axioms or unproved
   security assumption. *)

op f4_independent_events_aligned (shell provider : event list) : bool =
  project shell = project provider.

op f4_independent_bad_challenge
    (s : f4_shell) (p : f4_provider) (c : f4_candidate)
    (shell provider : event list) : bool =
  f4_bad_challenge s p c \/
  ! f4_independent_events_aligned shell provider.

op f4_independent_full_gate
    (s : f4_shell) (p : f4_provider) (c : f4_candidate)
    (shell provider : event list) : bool =
  f4_guard s p c /\
  f4_independent_events_aligned shell provider.

lemma f4_independent_gate_excludes_both_bad_events
    (s : f4_shell) (p : f4_provider) (c : f4_candidate)
    (shell provider : event list) :
  f4_independent_full_gate s p c shell provider =>
  ! f4_independent_bad_challenge s p c shell provider.
proof.
  rewrite /f4_independent_full_gate /f4_independent_bad_challenge.
  move=> [hgate halign].
  have hbad := f4_accepted_excludes_bad_challenge s p c hgate.
  by smt().
qed.

(* The second side may independently observe a previously unseen relevant
   event. Such a missing event is visible even if the 15 public selectors
   still match. This includes corruption and reveal, not just Commit. *)
lemma f4_unilateral_relevant_event_breaks_projection
    (shell provider : event list) (e : event) :
  f4_independent_events_aligned shell provider =>
  relevant e =>
  ! f4_independent_events_aligned shell (provider ++ [e]).
proof.
  rewrite /f4_independent_events_aligned /project.
  move=> halign he.
  rewrite filter_cat /= he.
  have hsize :
    size (filter relevant shell) = size (filter relevant provider)
    by rewrite halign.
  by smt(size_cat size_ge0).
qed.

lemma f4_missing_provider_corruption_is_bad_challenge
    (s : f4_shell) (p : f4_provider) (c : f4_candidate)
    (shell provider : event list) (e : event) :
  f4_independent_full_gate s p c shell provider =>
  ev_corrupt_start e =>
  f4_independent_bad_challenge s p c shell (provider ++ [e]).
proof.
  move=> hgood hcorrupt.
  have halign : f4_independent_events_aligned shell provider
    by move: hgood; rewrite /f4_independent_full_gate; smt().
  have hrel : relevant e by rewrite /relevant; smt().
  have hdrop := f4_unilateral_relevant_event_breaks_projection
    shell provider e halign hrel.
  rewrite /f4_independent_bad_challenge.
  by smt().
qed.

lemma f4_independent_bad_event_blocks_challenge
    (s : f4_shell) (p : f4_provider) (c : f4_candidate)
    (shell provider : event list) :
  f4_independent_bad_challenge s p c shell provider =>
  ! f4_independent_full_gate s p c shell provider.
proof.
  rewrite /f4_independent_bad_challenge /f4_independent_full_gate.
  have h := f4_bad_challenge_rejects s p c.
  by smt().
qed.

(* Same accepted event stream is sufficient for model alignment but not for
   source-complete observation. An adversarial operation invisible to BOTH
   observers remains invisible here; proving source completeness requires
   the actual OpenMLS/Product event API refinement. *)
lemma f4_same_independent_event_lists_align (events : event list) :
  f4_independent_events_aligned events events.
proof.
  by rewrite /f4_independent_events_aligned.
qed.
