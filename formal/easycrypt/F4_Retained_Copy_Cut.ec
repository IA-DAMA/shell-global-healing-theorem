require import AllCore List.
require import F4_Epoch_Schedule_Cut.
require import F4_Installation_Fixture.

(* A copy id identifies the immutable sealed bytes and their wrapping
   context. Outcomes are observations available to the challenger. Merely
   possessing the honest database or submitting an API call is not a leak. *)
type f4_copy_id.
type f4_copy_observation =
  [ Captured of f4_copy_id | UsableOpening of f4_copy_id
  | DirectKnowledge of f4_material ].
type f4_copy_content = f4_copy_id -> f4_view.

(* Projection of the synthetic DIRECT and GROUP runs. These are facts about
   replayed records. Neither asserts universal semantics for an entrypoint. *)
lemma f4_direct_interruption_and_copy_replay :
  let (epoch, record_at_error, bundle_at_error, bundle_after,
       copied_bundle_after, recovery_equal) = f4_direct_recovery in
  epoch = 1 /\ !record_at_error /\ bundle_at_error /\
  !bundle_after /\ copied_bundle_after /\ recovery_equal.
proof. by rewrite /f4_direct_recovery. qed.

lemma f4_group_partial_replacement_replay :
  let (partial, retried) = f4_replacement_epochs in
  partial = 3 /\ retried = partial + 1.
proof. by rewrite /f4_replacement_epochs. qed.

op f4_has_copy (h : f4_copy_observation list) c = mem h (Captured c).
op f4_can_open (h : f4_copy_observation list) c = mem h (UsableOpening c).
op f4_copy_view (content : f4_copy_content) h : f4_view = fun x =>
  mem h (DirectKnowledge x) \/
  exists c, f4_has_copy h c /\ f4_can_open h c /\ content c x.

lemma f4_copy_view_monotone content h tail :
  f4_subview (f4_copy_view content h) (f4_copy_view content (h ++ tail)).
proof.
  rewrite /f4_subview /f4_copy_view /f4_has_copy /f4_can_open.
  smt(mem_cat).
qed.

lemma f4_sealed_alone_does_not_disclose content c x :
  ! f4_copy_view content [Captured c] x.
proof. by rewrite /f4_copy_view /f4_has_copy /f4_can_open /=; smt(). qed.

lemma f4_distinct_opening_does_not_disclose content c d x :
  c <> d => ! f4_copy_view content [Captured c; UsableOpening d] x.
proof. by rewrite /f4_copy_view /f4_has_copy /f4_can_open /=; smt(). qed.

lemma f4_later_opening_preserves_past_copy content before middle after c x :
  content c x =>
  f4_copy_view content (before ++ [Captured c] ++ middle ++ [UsableOpening c] ++ after) x.
proof. rewrite /f4_copy_view /f4_has_copy /f4_can_open; smt(mem_cat mem_head). qed.

lemma f4_opening_retained_before_capture content before middle after c x :
  content c x =>
  f4_copy_view content (before ++ [UsableOpening c] ++ middle ++ [Captured c] ++ after) x.
proof. rewrite /f4_copy_view /f4_has_copy /f4_can_open; smt(mem_cat mem_head). qed.

(* Complete exactly for the defined sealed-copy disclosure and single-epoch
   public derivation rules. Content is scoped to one immutable challenge.
   Mapping reachable Product storage and custody capabilities to content and
   observations is a separate semantic refinement obligation. *)
lemma f4_copy_schedule_route_exact content h steps :
  (exists later,
     foldl f4_learn (foldl f4_schedule_step (f4_copy_view content h) steps)
           later Output) <=>
  f4_output_route (f4_seen (f4_copy_view content h) steps).
proof. exact (f4_interleaved_cut_exact steps (f4_copy_view content h)). qed.

(* Authenticated epoch selection is implicit in the fixed target here.
   opens_joiner c w means the bundle in c actually opens these specific
   Welcome bytes to the selected epoch's joiner secret. This relation must
   be justified by the native decoding and HPKE/AEAD operations. No rule
   infers it merely from admission, group membership, or matching epochs. *)
type f4_welcome_id.
op f4_with_welcomes content h (wire : f4_welcome_id list)
    (opens_joiner : f4_copy_id -> f4_welcome_id -> bool) : f4_view = fun x =>
  f4_copy_view content h x \/
  (x = Joiner /\ exists c w, f4_has_copy h c /\ f4_can_open h c /\
                             mem wire w /\ opens_joiner c w).

lemma f4_matching_retained_welcome_reaches_output content h wire opens c w :
  f4_has_copy h c => f4_can_open h c => mem wire w => opens c w =>
  f4_copy_view content h PskInput =>
  exists derivation, foldl f4_learn (f4_with_welcomes content h wire opens)
                               derivation Output.
proof.
  rewrite f4_output_route_exact /f4_output_route /f4_with_welcomes.
  smt().
qed.

lemma f4_unmatched_welcomes_leave_cut_unchanged content h wire opens :
  (forall c w, f4_has_copy h c => f4_can_open h c =>
               mem wire w => !opens c w) =>
  (exists d, foldl f4_learn (f4_with_welcomes content h wire opens) d Output)
    <=> f4_output_route (f4_copy_view content h).
proof.
  move=> hu; rewrite f4_output_route_exact /f4_output_route /f4_with_welcomes.
  smt().
qed.
