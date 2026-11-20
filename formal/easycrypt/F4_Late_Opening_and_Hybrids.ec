require import AllCore List DInterval Distr StdOrder.
require import F4_Leaf_Cut_Fixture F4_Installation_Fixture F4_OpenMLS_Exporter_Program.
import Range.

(* Fixed continuation on a selected successful trace. The recovery value
   models a later permitted response. It is independent of the challenge
   coin; the decision procedure sees it only after challenge selection. *)
module LateOpening = {
  proc disclose(saved : int option) : int option = { return saved; }
  proc test(ideal : bool, selected : int, saved : int option) : bool = {
    var ch, late;
    ch <- selected;
    if (ideal) { ch <$ dinter 0 (2^256-1); }
    late <@ disclose(saved);
    return late = Some ch;
  }
}.

lemma real_match y &m :
  Pr[LateOpening.test(false,y,Some y) @ &m : res] = 1%r.
proof.
  byphoare (_ : arg = (false,y,Some y) ==> res) => //.
  proc; inline LateOpening.disclose; wp; rcondf 2; first by auto.
  by auto.
qed.

lemma ideal_match y &m : 0 <= y < 2^256 =>
  Pr[LateOpening.test(true,y,Some y) @ &m : res] = 1%r / (2^256)%r.
proof.
  move=> hr.
  byphoare (_ : ideal /\ saved = Some y ==> res) => //.
  proc; inline LateOpening.disclose; wp; rcondt 2; first by auto.
  rnd (pred1 y); wp; skip => &m0 [[hi hs] _].
  have hb : 0 <= y <= 2^256-1 by smt().
  by rewrite dinter1E hb hs /pred1 /=; smt().
qed.

lemma fixed_restored_gap y &m : 0 <= y < 2^256 =>
  Pr[LateOpening.test(false,y,Some y) @ &m : res] -
  Pr[LateOpening.test(true,y,Some y) @ &m : res] = 1%r - 1%r / (2^256)%r.
proof. move=> hy; by rewrite real_match (ideal_match y &m hy). qed.

lemma removal_recovery_observation :
  removal_copy_equal = [false; true; true].
proof. by rewrite /removal_copy_equal. qed.

(* Two snapshots present the same admission bit at the fixed signed
   successor. Feeding both the same continuation gives different results. *)
lemma current_admission_insufficient (classify : bool -> bool) :
  map classify same_receipt_cut.`1 <> same_receipt_cut.`2.
proof. rewrite /same_receipt_cut /=; smt(). qed.

lemma restoration_observations :
  f4_direct_epoch_record_equal /\ f4_replacement_epochs = (3,4) /\
  f4_replacement_export_equal = [false; true; true].
proof. by rewrite /f4_direct_epoch_record_equal /f4_replacement_epochs /f4_replacement_export_equal. qed.

(* The native comparison fixes the bytes, using the same deserializer in
   both runs. This lemma needs neither a random-oracle model nor injectivity
   of the serialization: equal records give equal decoded key and calls. *)
lemma same_epoch_record_all_calls ['r] (decode : 'r -> F4_OpenMLS_Exporter_Algorithm.f4_kdf_secret)
    (a b : 'r) : a=b => forall oc,
  f4_mir_derive_with_key (decode a) oc = f4_mir_derive_with_key (decode b) oc.
proof. by move=> ->. qed.

(* Information theoretic obstruction for any deterministic expansion at a
   fixed stream position. Image membership need not be efficient. *)
op seed_image (expand : int -> int) (ns : int) = map expand (range 0 ns).

lemma actual_sample_in_image expand ns seed : 0 <= seed < ns =>
  mem (seed_image expand ns) (expand seed).
proof.
  move=> hs; apply/mapP; exists seed; by rewrite mem_range.
qed.

lemma ideal_image_mass expand ns no : 0 <= ns => 0 < no =>
  mu (dinter 0 (no-1)) (mem (seed_image expand ns)) <= ns%r * (1%r/no%r).
proof.
  move=> hns hno.
  have each : forall x, mu1 (dinter 0 (no-1)) x <= 1%r/no%r.
  + move=> x; rewrite dinter1E /=; case: (0 <= x <= no-1) => //=.
    smt(RealOrder.divr_ge0).
  have h := mu_mem_le_mu1 (dinter 0 (no-1)) (seed_image expand ns) (1%r/no%r) each.
  by rewrite /seed_image size_map size_range /= /max in h; smt().
qed.

(* An adaptive, online replacement with a cap on instance count pads
   unused indices with a zero hop. Bounds are supplied per adjacent pair;
   the lemma neither assumes that streams are independent in Rust nor
   upgrades classical primitive bounds to quantum ones. *)
op hops (xs : (real * real) list) (start : real) =
  with xs = [] => true
  with xs = item :: rest => `|start-item.`1| <= item.`2 /\ hops rest item.`1.
op allowances (xs : (real * real) list) = foldr (fun (x : real * real) acc => x.`2 + acc) 0%r xs.
op endpoint (xs : (real * real) list) (start : real) =
  foldl (fun (previous : real) (x : real * real) => x.`1) start xs.

(* The two endpoints can have different RNGs, continuation costs and bad
   event masses. Charge disjoint/overlapping failures conservatively; this
   statement makes no independence assumption about them. *)
lemma finite_hybrid xs start : hops xs start =>
  `|start - endpoint xs start| <= allowances xs.
proof.
  elim: xs start => [|item rest ih] start /=.
  + by rewrite /endpoint /allowances /=.
  move=> [hhere hrest]; have bound := ih item.`1 hrest.
  rewrite /endpoint /allowances /=; rewrite /endpoint /allowances in bound.
  smt(RealOrder.ler_dist_add).
qed.

lemma two_endpoint_budget real ideal lhs rhs gap :
  hops lhs real => hops rhs ideal =>
  `|endpoint lhs real - endpoint rhs ideal| <= gap =>
  `|real-ideal| <= allowances lhs + gap + allowances rhs.
proof.
  move=> hl hr hm; have l := finite_hybrid lhs real hl.
  have r := finite_hybrid rhs ideal hr.
  smt(RealOrder.ler_dist_add RealOrder.ler_norml).
qed.

(* Numerical meaning of "bad" for the unmasked acceptance bit. Even when
   the accepted fresh branches agree, the raw games need not agree. *)
lemma raw_with_late_failures goodR goodI badR badI dr di gap :
  0%r <= badR <= dr => 0%r <= badI <= di =>
  `|goodR-goodI| <= gap =>
  `|(goodR+badR)-(goodI+badI)| <= gap + (if dr <= di then di else dr).
proof. rewrite !RealOrder.ler_norml; smt(). qed.

(* d records the selected index on accepting classical transcripts. Its
   missing mass can represent rejection. Uniform guessing is private and
   independent; the implementation of an embedded oracle is a separate
   obligation. The identity makes no distributional assumption about d. *)
require import RealSeries.
op guessed_index (q : int) (d : int distr) =
  dlet d (fun i => dmap (dinter 0 (q-1)) (pred1 i)).

lemma private_index_guess q d : 0 < q =>
  mu (guessed_index q d) (pred1 true) =
  (1%r / q%r) * mu d (fun i => 0 <= i < q).
proof.
  move=> hq; rewrite /guessed_index dletE (muE d) -sumZ.
  apply eq_sum => i /=.
  rewrite dmapE.
  have he : mu (dinter 0 (q-1)) (pred1 true \o pred1 i) =
            mu1 (dinter 0 (q-1)) i by apply mu_eq => x; rewrite /pred1 /(\o) /=; smt().
  rewrite he dinter1E /=.
  case: (0 <= i < q) => hi.
  + have -> : 0 <= i <= q-1 by smt().
    smt().
  + have -> : !(0 <= i <= q-1) by smt().
    smt().
qed.

lemma private_index_gap q dr di : 0 < q =>
  mu (guessed_index q dr) (pred1 true) - mu (guessed_index q di) (pred1 true) =
  (1%r / q%r) * (mu dr (fun i => 0 <= i < q) - mu di (fun i => 0 <= i < q)).
proof. move=> hq; rewrite !private_index_guess //; ring. qed.
