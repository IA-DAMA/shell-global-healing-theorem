require import AllCore List.

(* One selected successor, fixed group context and exporter call. Inputs denote
   availability of actual values. A zero/pathless input or empty PSK counts
   as available. A Welcome contributes only the values actually disclosed.
   Resync is likewise an ingress, never an erasure. The input set may include
   previously retained snapshots. This finite algebra covers public forward
   derivations, not guessing, inversion or all private storage routes. *)
type f4_material = [ InitInput | CommitInput | Extracted | Joiner | PskInput
                   | Intermediate | EpochKey | ExporterKey | LabelKey | Output ].
type f4_view = f4_material -> bool.

op f4_ready (v : f4_view) (m : f4_material) =
  if m = Extracted then v InitInput /\ v CommitInput else
  if m = Joiner then v Extracted else
  if m = Intermediate then v Joiner /\ v PskInput else
  if m = EpochKey then v Intermediate else
  if m = ExporterKey then v EpochKey else
  if m = LabelKey then v ExporterKey else
  if m = Output then v LabelKey else false.

op f4_learn (v : f4_view) (m : f4_material) : f4_view =
  fun x => v x \/ (x = m /\ f4_ready v m).

op f4_schedule_order =
  [Extracted; Joiner; Intermediate; EpochKey; ExporterKey; LabelKey; Output].

op f4_saturated (v : f4_view) : f4_view =
  let extracted = v Extracted \/ (v InitInput /\ v CommitInput) in
  let joiner = v Joiner \/ extracted in
  let intermediate = v Intermediate \/ (joiner /\ v PskInput) in
  let epoch = v EpochKey \/ intermediate in
  let exporter = v ExporterKey \/ epoch in
  let labeled = v LabelKey \/ exporter in
  fun x => if x = Extracted then extracted else if x = Joiner then joiner
    else if x = Intermediate then intermediate else if x = EpochKey then epoch
    else if x = ExporterKey then exporter else if x = LabelKey then labeled
    else if x = Output then v Output \/ labeled else v x.
op f4_subview (v w : f4_view) = forall x, v x => w x.

lemma f4_saturation_contains v : f4_subview v (f4_saturated v).
proof.
  rewrite /f4_subview => x; case: x; rewrite /f4_saturated /=; smt().
qed.

lemma f4_saturation_closed v x :
  f4_ready (f4_saturated v) x => f4_saturated v x.
proof.
  case: x; rewrite /f4_ready /f4_saturated /=; smt().
qed.

lemma f4_learn_bounded v w m :
  f4_subview v (f4_saturated w) =>
  f4_subview (f4_learn v m) (f4_saturated w).
proof.
  move=> h.
  have hc := f4_saturation_closed w m.
  rewrite /f4_subview in h.
  rewrite /f4_ready in hc.
  rewrite /f4_subview /f4_learn /f4_ready.
  smt().
qed.

lemma f4_any_derivation_bounded steps v w :
  f4_subview v (f4_saturated w) =>
  f4_subview (foldl f4_learn v steps) (f4_saturated w).
proof.
  elim: steps v => [|m rest ih] v //=.
  move=> h; apply ih; exact (f4_learn_bounded v w m h).
qed.

(* Exact normal form for arbitrary scheduling, retries and retained inputs.
   In particular a revealed intermediate can bypass an upstream cut. *)
op f4_output_route (v : f4_view) =
  v Output \/ v LabelKey \/ v ExporterKey \/ v EpochKey \/ v Intermediate \/
  (v PskInput /\ (v Joiner \/ v Extracted \/ (v InitInput /\ v CommitInput))).

lemma f4_saturated_output v : f4_saturated v Output = f4_output_route v.
proof.
  rewrite /f4_saturated /f4_output_route /=.
  smt().
qed.

lemma f4_output_route_exact v :
  (exists steps, foldl f4_learn v steps Output) <=> f4_output_route v.
proof.
  split.
  + move=> [steps h].
    have bound := f4_any_derivation_bounded steps v v (f4_saturation_contains v).
    rewrite -f4_saturated_output; exact (bound Output h).
  + move=> h; exists f4_schedule_order.
    rewrite /f4_schedule_order /=.
    rewrite /f4_learn /f4_ready /=.
    rewrite /f4_output_route in h; smt().
qed.

(* The challenge freezes a prefix. The value view is the union of all
   disclosures in that prefix, not just the newest epoch's observation. *)
op f4_retained (observations : f4_view list) : f4_view =
  fun x => has (fun v => v x) observations.

lemma f4_retained_append prefix suffix x :
  f4_retained (prefix ++ suffix) x = (f4_retained prefix x \/ f4_retained suffix x).
proof. by rewrite /f4_retained has_cat. qed.

lemma f4_known_output_survives_suffix prefix suffix :
  f4_output_route (f4_retained prefix) =>
  f4_output_route (f4_retained (prefix ++ suffix)).
proof. rewrite /f4_output_route !f4_retained_append; smt(). qed.

lemma f4_after_init_exposure_public_psk_cut history :
  let v = f4_retained history in
  v InitInput => v PskInput =>
  (!(exists steps, foldl f4_learn v steps Output) <=>
    !(v CommitInput \/ v Extracted \/ v Joiner \/ v Intermediate \/
      v EpochKey \/ v ExporterKey \/ v LabelKey \/ v Output)).
proof. simplify; rewrite f4_output_route_exact /f4_output_route; smt(). qed.

(* Disclosures may arrive between evaluations. A step adds its newly
   available material before attempting one public derivation. Empty
   disclosures and input-only derivations model stuttering. The target
   remains fixed throughout; other epochs enter only through actual input
   dependencies, never by equating distinct epoch secrets. *)
type f4_schedule_event = f4_view * f4_material.
op f4_union (v w : f4_view) : f4_view = fun x => v x \/ w x.
op f4_schedule_step (v : f4_view) (ev : f4_schedule_event) =
  f4_learn (f4_union v ev.`1) ev.`2.
op f4_seen (v : f4_view) (h : f4_schedule_event list) =
  f4_union v (f4_retained (map fst h)).

lemma f4_timeline_upper h v w :
  f4_subview (f4_seen v h) (f4_saturated w) =>
  f4_subview (foldl f4_schedule_step v h) (f4_saturated w).
proof.
  elim: h v => [|ev rest ih] v /=.
  + by rewrite /f4_seen /f4_union /f4_retained /f4_subview /=.
  move=> hbound; apply ih.
  have one : f4_subview (f4_union v ev.`1) (f4_saturated w).
  + rewrite /f4_seen /f4_union /f4_retained /f4_subview /= in hbound.
    rewrite /f4_subview /f4_union; smt().
  have learned := f4_learn_bounded (f4_union v ev.`1) w ev.`2 one.
  rewrite /f4_seen /f4_union /f4_retained /f4_subview /= in hbound.
  rewrite /f4_subview => x.
  have hl := learned x.
  have hb := hbound x.
  change ((f4_learn (f4_union v ev.`1) ev.`2 x \/
           has (fun z => z x) (map fst rest)) => f4_saturated w x).
  smt().
qed.

lemma f4_timeline_keeps_disclosures h v :
  f4_subview (f4_seen v h) (foldl f4_schedule_step v h).
proof.
  elim: h v => [|ev rest ih] v /=.
  + by rewrite /f4_seen /f4_union /f4_retained /f4_subview /=.
  have kept := ih (f4_schedule_step v ev).
  rewrite /f4_seen /f4_union /f4_retained /f4_subview /f4_schedule_step /f4_learn /= in kept.
  rewrite /f4_seen /f4_union /f4_retained /f4_subview /f4_schedule_step /f4_learn /=.
  smt().
qed.

lemma f4_interleaved_cut_exact h v :
  (exists suffix, foldl f4_learn (foldl f4_schedule_step v h) suffix Output)
  <=> f4_output_route (f4_seen v h).
proof.
  split.
  + move=> [suffix reached].
    have bound := f4_timeline_upper h v (f4_seen v h) (f4_saturation_contains (f4_seen v h)).
    have final := f4_any_derivation_bounded suffix _ _ bound.
    rewrite -f4_saturated_output; exact (final Output reached).
  + rewrite f4_output_route_exact.
    have kept := f4_timeline_keeps_disclosures h v.
    rewrite /f4_subview in kept; rewrite /f4_output_route; smt().
qed.
