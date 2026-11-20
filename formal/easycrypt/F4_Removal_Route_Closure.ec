require import AllCore List.
require import F4_Epoch_Schedule_Cut F4_Retained_Copy_Cut.

(* Facts are scoped to immutable objects and to one product challenge. Each
   binary rule requires BOTH inputs. Nullary facts enter via the history,
   unary rules can repeat their premise; auxiliaries encode longer guards. *)
type f4_route_fact = [ Bytes of f4_copy_id | Opening of f4_copy_id
                     | Opened of f4_copy_id | Material of f4_material ].
type f4_route_rule = f4_route_fact * f4_route_fact * f4_route_fact.
type f4_route_set = f4_route_fact -> bool.
op contains (v w : f4_route_set) = forall x, v x => w x.
op step (allowed : f4_route_rule -> bool) (v : f4_route_set) (r : f4_route_rule) =
  fun x => v x \/ (allowed r /\ v r.`1 /\ v r.`2 /\ x = r.`3).
op run allowed v trail = foldl (step allowed) v trail.
op reachable allowed v x = exists trail, run allowed v trail x.
op closed allowed (v : f4_route_set) =
  forall a b c, allowed (a,b,c) => v a => v b => v c.

lemma step_mono allowed v w r :
  contains v w => contains (step allowed v r) (step allowed w r).
proof. rewrite /contains /step; smt(). qed.

lemma run_mono allowed trail v w :
  contains v w => contains (run allowed v trail) (run allowed w trail).
proof.
  elim: trail v w => [|r rs ih] v w h //=.
  change (contains (run allowed (step allowed v r) rs) (run allowed (step allowed w r) rs)).
  apply ih; exact (step_mono allowed v w r h).
qed.

lemma run_keeps allowed trail v : contains v (run allowed v trail).
proof.
  elim: trail v => [|r rs ih] v /=; first by rewrite /contains /run /=.
  have keep := ih (step allowed v r).
  rewrite /contains /run /step /= in keep.
  rewrite /contains /run /step /=; smt().
qed.

lemma closed_bounds_run allowed v w trail :
  closed allowed w => contains v w => contains (run allowed v trail) w.
proof.
  elim: trail v => [|r rs ih] v hc hv //=.
  change (contains (run allowed (step allowed v r) rs) w).
  apply ih => //.
  case: r => a b c /=.
  rewrite /closed in hc; rewrite /contains in hv; rewrite /contains /step /=; smt().
qed.

lemma reach_closed allowed v : closed allowed (reachable allowed v).
proof.
  rewrite /closed => a b c hr [la ha] [lb hb].
  have ka := run_keeps allowed lb (run allowed v la).
  have kb := run_mono allowed lb v (run allowed v la) (run_keeps allowed la v).
  exists ((la ++ lb) ++ [(a,b,c)]).
  rewrite /run !foldl_cat /= /step.
  right; split => //; split; first exact (ka a ha).
  split; first exact (kb b hb).
  trivial.
qed.

(* Dual characterization. A complete backwards argument can provide a
   closed envelope. A missed prerequisite or cross-copy chain invalidates
   that envelope. No bounded search, acyclicity or disjoint owners assumed. *)
lemma no_route_iff_closed_envelope allowed v target :
  !reachable allowed v target <=>
  exists safe, contains v safe /\ closed allowed safe /\ !safe target.
proof.
  split.
  + move=> hn; exists (reachable allowed v); split.
    - rewrite /contains => x hx; exists []; by rewrite /run /=.
    by split => //; apply reach_closed.
  + move=> [safe [hv [hc hn]]].
    have nowhere : forall trail, !run allowed v trail target.
    - move=> trail; have bound := closed_bounds_run allowed v safe trail hc hv.
      rewrite /contains in bound; smt().
    rewrite /reachable; smt().
qed.

(* Time-sensitive rules are valid only in their own phase. Keep the
   consequences learned while authorized, never the permission itself.
   Within each phase reusable deductions can be interleaved arbitrarily. *)
type f4_phase = (f4_route_rule -> bool) * f4_route_set.
op plus (a b : f4_route_set) = fun x => a x \/ b x.
op advance (v : f4_route_set) (p : f4_phase) =
  reachable p.`1 (plus v p.`2).
op final_view phases v = foldl advance v phases.
op certified (ps : f4_phase list) (v : f4_route_set) (target : f4_route_fact) =
  with ps = [] => !v target
  with ps = p :: tail => exists w,
    contains (plus v p.`2) w /\ closed p.`1 w /\ certified tail w target.

lemma final_mono ps v w : contains v w =>
  contains (final_view ps v) (final_view ps w).
proof.
  elim: ps v w => [|p tail ih] v w inc //=.
  change (contains (final_view tail (advance v p)) (final_view tail (advance w p))).
  apply ih; rewrite /advance /contains /reachable => x [trail hx].
  exists trail; apply (run_mono _ _ _ _ _ x hx).
  rewrite /contains /plus; smt().
qed.

lemma temporal_cut_exact ps v target :
  !final_view ps v target <=> certified ps v target.
proof.
  elim: ps v => [|p tail ih] v //=.
  change (!final_view tail (advance v p) target <=>
    exists w, contains (plus v p.`2) w /\ closed p.`1 w /\ certified tail w target).
  split.
  + move=> hn; exists (advance v p); split.
    - rewrite /advance /contains => x hx; exists []; by rewrite /run /=.
    split; first exact (reach_closed _ _).
    by rewrite -(ih (advance v p) ).
  + move=> [w [hinc [hc htail]]].
    have sub : contains (advance v p) w.
    - rewrite /advance /contains /reachable => x [trail hx].
      exact (closed_bounds_run _ _ _ trail hc hinc x hx).
    have later := final_mono tail _ _ sub.
    rewrite -(ih w) in htail; rewrite /contains in later; smt().
qed.

(* One one-shot authorised service operation, usable only during its window.
   Its rule is not itself a fact remembered after the window expires. *)
op nothing : f4_route_set = fun _ => false.
op no_rules : f4_route_rule -> bool = fun _ => false.
op grant b (r : f4_route_rule) = r = (Bytes b, Bytes b, Material Output).
op received b : f4_route_set = fun x => x = Bytes b.

lemma bytes_after_window b :
  !final_view [(grant b,nothing); (no_rules,received b)] nothing (Material Output).
proof.
  rewrite temporal_cut_exact /=.
  exists nothing; split; first by rewrite /contains /plus /nothing.
  split; first by rewrite /closed /nothing.
  exists (received b); split; first by rewrite /contains /plus /nothing.
  split; first by rewrite /closed /no_rules.
  by rewrite /received.
qed.

lemma bytes_during_window b :
  final_view [(grant b,received b); (no_rules,nothing)] nothing (Material Output).
proof.
  rewrite /final_view /=.
  have hb : reachable (grant b) (plus nothing (received b)) (Bytes b).
  + exists []; by rewrite /run /plus /received /=.
  have resulting := reach_closed (grant b) (plus nothing (received b)).
  have target : reachable (grant b) (plus nothing (received b)) (Material Output).
  + by apply (resulting (Bytes b) (Bytes b) (Material Output)) => //.
  exists []; by rewrite /run /plus /advance /= target.
qed.

(* A capability may itself be in an encrypted backup. The two inputs for a
   join may come from different times or different copies. puts is a typed
   inventory of what opening a particular object actually makes usable.
   extra admits additional Product rules (including signed restore, Welcome
   and paths); none of these are collapsed into "epoch advanced". *)
op archival (puts : f4_copy_id -> f4_route_fact -> bool) r =
  (exists id, r = (Bytes id, Opening id, Opened id)) \/
  (exists id x, puts id x /\ r = (Opened id, Opened id, x)).
op schedule (r : f4_route_rule) =
  mem [(Material InitInput, Material CommitInput, Material Extracted);
       (Material Extracted, Material Extracted, Material Joiner);
       (Material Joiner, Material PskInput, Material Intermediate);
       (Material Intermediate, Material Intermediate, Material EpochKey);
       (Material EpochKey, Material EpochKey, Material ExporterKey);
       (Material ExporterKey, Material ExporterKey, Material LabelKey);
       (Material LabelKey, Material LabelKey, Material Output)] r.
op routes puts extra r = archival puts r \/ schedule r \/ extra r.

lemma reach_base rules v x : v x => reachable rules v x.
proof. move=> hx; exists []; by rewrite /run /=. qed.

lemma use_rule rules v a b c : rules (a,b,c) =>
  reachable rules v a => reachable rules v b => reachable rules v c.
proof. exact (reach_closed rules v a b c). qed.

lemma archive_contents_reached puts extra v id x :
  puts id x =>
  reachable (routes puts extra) v (Bytes id) =>
  reachable (routes puts extra) v (Opening id) =>
  reachable (routes puts extra) v x.
proof.
  move=> h hb hk.
  have hopen : reachable (routes puts extra) v (Opened id).
  + apply (use_rule _ _ (Bytes id) (Opening id)) => //.
    rewrite /routes /archival; smt().
  apply (use_rule _ _ (Opened id) (Opened id)) => //.
  rewrite /routes /archival; smt().
qed.

lemma matching_nested_copy_recovers puts extra v keycopy groupcopy :
  puts keycopy (Opening groupcopy) => puts groupcopy (Material ExporterKey) =>
  v (Bytes keycopy) => v (Opening keycopy) => v (Bytes groupcopy) =>
  reachable (routes puts extra) v (Material Output).
proof.
  move=> pk pg b1 k1 b2.
  have open2 := archive_contents_reached puts extra v keycopy (Opening groupcopy) pk
                    (reach_base _ _ _ b1) (reach_base _ _ _ k1).
  have ek := archive_contents_reached puts extra v groupcopy (Material ExporterKey) pg
                    (reach_base _ _ _ b2) open2.
  have lk : reachable (routes puts extra) v (Material LabelKey).
  + by apply (use_rule _ _ (Material ExporterKey) (Material ExporterKey)) => //.
  by apply (use_rule _ _ (Material LabelKey) (Material LabelKey)) => //.
qed.

(* A concrete sufficient safe envelope for a singleton removal. Opening an
   arbitrary number of old objects is allowed provided all content stays in
   the envelope; particular keys can remain unavailable forever. In this
   profile allow target init and PSK to be public. Hidden intermediate
   material and target-output capabilities still cannot enter the envelope. *)
op envelope (objects : f4_route_set) (x : f4_route_fact) =
  with x = Bytes i => objects (Bytes i)
  with x = Opening i => objects (Opening i)
  with x = Opened i => objects (Opened i)
  with x = Material m => m = InitInput \/ m = PskInput.

lemma singleton_schedule_closed objects : closed schedule (envelope objects).
proof.
  have hm : forall m, envelope objects (Material m) = (m = InitInput \/ m = PskInput)
    by move=> m; rewrite /envelope.
  rewrite /closed /schedule => a b c; simplify; smt().
qed.

lemma singleton_remove_no_derivation v puts extra objects :
  contains v (envelope objects) =>
  closed (archival puts) (envelope objects) =>
  closed extra (envelope objects) =>
  !reachable (routes puts extra) v (Material Output).
proof.
  move=> init archives external.
  rewrite (no_route_iff_closed_envelope (routes puts extra) v (Material Output)); exists (envelope objects).
  have ks := singleton_schedule_closed objects.
  rewrite /closed in ks.
  rewrite /closed in archives; rewrite /closed in external.
  split => //; split; last by rewrite /envelope.
  rewrite /closed /routes; smt().
qed.
