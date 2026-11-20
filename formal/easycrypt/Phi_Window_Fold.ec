require import AllCore Int List.
require import Phi_Refinement Phi_Trace_Model Phi_Canonical_Events.

(* Fold state for one member at the T1 challenge boundary.  Positions are
   carried from the canonical event stream; no history uniqueness is claimed. *)
type member_fold = {
  mf_key_source : position;
  mf_corrupt : bool;
  mf_exposed_current : bool;
  mf_removed : bool;
  mf_challenged : bool;
}.

op initial_pos : position.

op initial_member_fold : member_fold = {|
  mf_key_source = initial_pos;
  mf_corrupt = false;
  mf_exposed_current = false;
  mf_removed = false;
  mf_challenged = false;
|}.

(* Deterministic transition for events concerning u.  An accepted update
   replaces the current-key source and clears exposure of the previous key only
   when the member is not currently corrupted.  EndCorrupt alone never heals. *)
op step_member (u : member) (s : member_fold) (e : event) : member_fold =
  if ev_member e <> u then s
  else if ev_challenge e then {| s with mf_challenged = true |}
  else if ev_remove e then {| s with mf_removed = true |}
  else if ev_corrupt_start e then
    {| s with mf_corrupt = true; mf_exposed_current = true |}
  else if ev_reveal e then
    {| s with mf_exposed_current = true |}
  else if ev_corrupt_end e then
    {| s with mf_corrupt = false |}
  else if ev_accept_update e then
    {| s with
       mf_key_source = ev_pos e;
       mf_exposed_current = s.`mf_corrupt |}
  else s.

op fold_member (u : member) (es : event list) : member_fold =
  foldl (step_member u) initial_member_fold es.

op shell_member_fold
  (tr : shell_trace) (ch : challenge_binding) (u : member) : member_fold =
  fold_member u (canonical_shell_events tr ch).

op provider_member_fold
  (pv : provider_view) (u : member) : member_fold =
  fold_member u (canonical_provider_events pv).

lemma equal_projection_equal_member_fold
    (tr : shell_trace) (ch : challenge_binding) (u : member) :
  event_projection_ok tr ch =>
  shell_member_fold tr ch u =
  provider_member_fold (phi tr ch) u.
proof.
  move=> h.
  rewrite /shell_member_fold /provider_member_fold.
  by rewrite (event_projection_is_same_list tr ch h).
qed.

lemma event_projection_preserves_key_source
    (tr : shell_trace) (ch : challenge_binding) (u : member) :
  event_projection_ok tr ch =>
  (shell_member_fold tr ch u).`mf_key_source =
  (provider_member_fold (phi tr ch) u).`mf_key_source.
proof.
  move=> h.
  by rewrite (equal_projection_equal_member_fold tr ch u h).
qed.

lemma event_projection_preserves_exposure
    (tr : shell_trace) (ch : challenge_binding) (u : member) :
  event_projection_ok tr ch =>
  (shell_member_fold tr ch u).`mf_exposed_current =
  (provider_member_fold (phi tr ch) u).`mf_exposed_current.
proof.
  move=> h.
  by rewrite (equal_projection_equal_member_fold tr ch u h).
qed.

lemma event_projection_preserves_removal
    (tr : shell_trace) (ch : challenge_binding) (u : member) :
  event_projection_ok tr ch =>
  (shell_member_fold tr ch u).`mf_removed =
  (provider_member_fold (phi tr ch) u).`mf_removed.
proof.
  move=> h.
  by rewrite (equal_projection_equal_member_fold tr ch u h).
qed.

(* Negative semantic controls, expressed as state facts rather than axioms:
   - EndCorrupt changes mf_corrupt only; it cannot clear mf_exposed_current.
   - AcceptUpdate while still corrupted leaves the replacement key exposed.
   - AcceptUpdate after corruption ended installs a new unexposed current key.
   These are the exact temporal distinctions needed by the TTKEM critical
   window mapping. *)

lemma end_corrupt_does_not_heal
    (u : member) (s : member_fold) (e : event) :
  ev_member e = u =>
  ! ev_challenge e => ! ev_remove e => ! ev_corrupt_start e =>
  ! ev_reveal e =>
  ev_corrupt_end e =>
  (step_member u s e).`mf_exposed_current = s.`mf_exposed_current.
proof.
  move=> hu hch hrm hcs hrv he.
  by rewrite /step_member hu hch hrm hcs hrv he.
qed.

lemma accepted_update_during_corruption_stays_exposed
    (u : member) (s : member_fold) (e : event) :
  ev_member e = u =>
  ! ev_challenge e => ! ev_remove e => ! ev_corrupt_start e =>
  ! ev_reveal e => ! ev_corrupt_end e => ev_accept_update e =>
  s.`mf_corrupt =>
  (step_member u s e).`mf_exposed_current.
proof.
  move=> hu hch hrm hcs hrv hce hau hc.
  rewrite /step_member hu hch hrm hcs hrv hce hau.
  exact hc.
qed.

lemma accepted_update_after_corruption_can_clear_old_exposure
    (u : member) (s : member_fold) (e : event) :
  ev_member e = u =>
  ! ev_challenge e => ! ev_remove e => ! ev_corrupt_start e =>
  ! ev_reveal e => ! ev_corrupt_end e => ev_accept_update e =>
  ! s.`mf_corrupt =>
  ! (step_member u s e).`mf_exposed_current.
proof.
  move=> hu hch hrm hcs hrv hce hau hc.
  rewrite /step_member hu hch hrm hcs hrv hce hau.
  exact hc.
qed.
