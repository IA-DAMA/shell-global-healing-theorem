require import AllCore List F4_Recovery_Word_Experiment.

(* 's includes the selected target, all prior knowledge, and the current
   owner/capability context. A returning API error with durable side effects
   is a transition to the actual resulting state. None is a disabled edge. *)
op walk ['s 'c] (next : 's -> 'c -> 's option) (s : 's) (w : 'c list) : 's option =
  with w = [] => Some s
  with w = c :: cs =>
    if next s c = None then None else walk next (oget (next s c)) cs.

op safe ['s 'c] (next : 's -> 'c -> 's option) (known : 's -> bool) (s : 's) =
  forall w t, walk next s w = Some t => !known t.

op invariant ['s 'c] (next : 's -> 'c -> 's option) (known cert : 's -> bool) =
  forall s, cert s =>
    !known s /\ (forall c t, next s c = Some t => cert t).

lemma safe_is_invariant ['s 'c] (next : 's -> 'c -> 's option) known :
  invariant next known (safe next known).
proof.
  rewrite /invariant /safe => s hs; split.
  + by apply (hs [] s).
  move=> c t he w t' ht.
  apply (hs (c::w) t'); by rewrite /= he.
qed.

lemma cert_bounds_walk ['s 'c] (next : 's -> 'c -> 's option) known cert :
  invariant next known cert =>
  forall w s t, cert s => walk next s w = Some t => cert t.
proof.
  rewrite /invariant => hc; elim => [|c cs ih] s t hs /=.
  + by smt().
  case (next s c = None) => ez /=; first by smt().
  apply ih.
  have he : next s c = Some (oget (next s c)) by case: (next s c) ez.
  smt().
qed.

lemma exact_online_certificate ['s 'c] (next : 's -> 'c -> 's option) known s :
  safe next known s <=> exists cert, invariant next known cert /\ cert s.
proof.
  split.
  + move=> hs; exists (safe next known); split => //.
    exact (safe_is_invariant next known).
  move=> [cert [hi hs]]; rewrite /safe => w t hw.
  have ht := cert_bounds_walk next known cert hi w s t hs hw.
  by have := hi t ht.
qed.

(* Permissions here are fixed for the whole suffix. Evolving permissions
   can instead be part of 's above. The model predicts the two authenticated
   commands on a retained survivor snapshot under the pinned head/custody. *)
op permitted (can_apply : bool) s c =
  if c = ApplyReceipt /\ !can_apply then None else Some (step s c).

lemma online_receipt_cut can_apply s :
  safe (permitted can_apply) readable s <=>
    s = Early \/ (s = Prepared /\ !can_apply).
proof.
  split.
  + rewrite /safe => hs.
    have h0 := hs [] s.
    have h1 := hs [ApplyReceipt] Applied.
    by case: s h0 h1 hs; case: can_apply; rewrite /permitted /readable /step /=; smt().
  + move=> hs; rewrite exact_online_certificate.
    exists (fun t => t = Early \/ (t = Prepared /\ !can_apply)); split => //.
    rewrite /invariant => t ht; split; first by rewrite /readable; smt().
    move=> c u; case: t ht; case: can_apply; case: c;
      by rewrite /permitted /step /=; smt().
qed.



(* Local obligations for a concrete source step. A single API call may
   commit several abstract steps, also when it returns Err. Stuttering is
   represented by []. We require observation inclusion only on related states. *)
lemma transfer_certificate ['s 'a 'c 'd]
   (src : 's -> 'c -> 's option) (model : 'a -> 'd -> 'a option)
   (learned : 's -> bool) (exposed cert : 'a -> bool)
   (rep : 's -> 'a -> bool) :
  invariant model exposed cert =>
  (forall s a, rep s a => learned s => exposed a) =>
  (forall s a c t, rep s a => src s c = Some t =>
     exists word b, walk model a word = Some b /\ rep t b) =>
  forall s a, rep s a => cert a => safe src learned s.
proof.
  move=> hi ho hs s a hra hca; rewrite exact_online_certificate.
  exists (fun s' => exists a', rep s' a' /\ cert a'); split; last by exists a.
  rewrite /invariant => s' [a' [hr hc]]; split.
  + by have := hi a' hc; smt().
  move=> c t hst; have [word b [hw hb]] := hs s' a' c t hr hst.
  exists b; split => //.
  exact (cert_bounds_walk model exposed cert hi word a' b hc hw).
qed.

(* Grant is a later legitimate authority event, independent of the challenge
   bytes. Revoking this permission never erases an already readable phase.
   This only models authority to apply the fixed signed receipt; custody
   remains available to this modeled observer throughout. *)
type authority_command = [ Grant | Withdraw | Use of command ].
op evolving (s : copy_phase * bool) c =
  with c = Grant => Some (s.`1,true)
  with c = Withdraw => Some (s.`1,false)
  with c = Use cmd =>
    if cmd = ApplyReceipt /\ !s.`2 then None else Some (step s.`1 cmd,s.`2).
op epoch_known (s : copy_phase * bool) = readable s.`1.

lemma online_cut_with_later_grant phase permission :
  safe evolving epoch_known (phase,permission) <=> phase = Early.
proof.
  split.
  + rewrite /safe => hs; have h := hs [Grant;Use ApplyReceipt] (Applied,true).
    by case: phase h hs; rewrite /evolving /step /epoch_known /readable /=; smt().
  move=> ->; rewrite exact_online_certificate.
  exists (fun (s : copy_phase * bool) => s.`1 = Early); split => //.
  rewrite /invariant => s he; split; first by rewrite /epoch_known /readable he.
  by move=> c u; case: c => [| |cmd] /=; rewrite he; smt().
qed.
