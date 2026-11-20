require import AllCore List Distr DInterval StdOrder RealSeries.

(* An admitted successor of this exact removal, at a fixed signed head.
   The two commands use synthetic custody and the original receipt/journal.
   Step is a specification. The native fixture compares all length-two words. *)
type copy_phase = [ Early | Prepared | Applied ].
type command = [ ApplyReceipt | CatchUp ].

op step s c =
  if s = Prepared /\ c = ApplyReceipt then Applied else s.
op readable s = s = Applied.
op reaches s (commands : command list) = readable (foldl step s commands).

lemma reached_iff s commands :
  reaches s commands <=> s = Applied \/ (s = Prepared /\ mem commands ApplyReceipt).
proof.
  rewrite /reaches. elim: commands s => [|c cs ih] s /=.
  + by case: s.
  + rewrite ih /step. by case: s; case: c; simplify; smt().
qed.

(* The present observation and the response after a single Apply distinguish
   all three phases. Any exact summary for all continuations must do so. *)
lemma observation_complete s t :
  (forall cmds, reaches s cmds = reaches t cmds) <=> s=t.
proof.
  split; last by move=> ->.
  move=> h; have h0 := h []; have h1 := h [ApplyReceipt].
  clear h; move: h0 h1. by case: s; case: t; rewrite !reached_iff /=.
qed.

(* Each inventory entry carries its own finite schedule. Copies, schedules,
   the target, and admission may be arbitrarily correlated in the prefix. *)
type inventory = (copy_phase * command list) list.
op can_compare (bags : inventory) =
  has (fun b : copy_phase * command list => reaches b.`1 b.`2) bags.
type sample = bool * inventory * int.
op usable (h : sample) = h.`1 /\ can_compare h.`2 /\ 0 <= h.`3 < 2^256.
op matches (h : sample) (u : int) = usable h /\ u = h.`3.
op ideal_test (h : sample) =
  dmap (dinter 0 (2^256-1)) (matches h).

lemma ideal_one h :
  mu1 (ideal_test h) true = (if usable h then 1%r / (2^256)%r else 0%r).
proof.
  rewrite /ideal_test dmapE.
  case (usable h) => hu.
  + have he : mu (dinter 0 (2^256-1)) (pred1 true \o matches h) = mu1 (dinter 0 (2^256-1)) h.`3.
    - by apply mu_eq => u; rewrite /pred1 /(\o) /matches hu /=; smt().
    have hh : 0 <= h.`3 <= 2^256-1 by move: hu; rewrite /usable; smt().
    by rewrite he dinter1E hh /=.
  + have he : mu (dinter 0 (2^256-1)) (pred1 true \o matches h) = mu (dinter 0 (2^256-1)) pred0.
    - by apply mu_eq => u; rewrite /pred1 /pred0 /(\o) /matches hu.
    by rewrite he mu0.
qed.

(* No estimate of the distribution of Product histories is assumed here.
   Failure, exclusion and loss of mass are not conditioned away. *)
lemma ideal_mixture (d : sample distr) :
  mu1 (dlet d ideal_test) true = (1%r / (2^256)%r) * mu d usable.
proof.
  rewrite dlet1E muE -sumZ. apply eq_sum => h /=.
  rewrite ideal_one. case: (usable h) => /=; smt().
qed.

lemma exact_gap (d : sample distr) :
  mu d usable - mu1 (dlet d ideal_test) true =
  mu d usable * (1%r - 1%r/(2^256)%r).
proof. by rewrite ideal_mixture; ring. qed.


(* A usable decision procedure sees only the returned candidate and the
   challenge. A successful call that returns a DIFFERENT epoch's bytes must
   count in the ideal false-positive rate. No oracle for match/correctness. *)
type outcome = int * int option.
op compare (z : int option) (c : int) = z = Some c.
op correct (h : outcome) = compare h.`2 h.`1.
op in_range (h : outcome) =
  h.`2 <> None /\ 0 <= oget h.`2 < 2^256.
op ideal_compare (h : outcome) =
  dmap (dinter 0 (2^256-1)) (compare h.`2).

lemma comparison_one h :
  mu1 (ideal_compare h) true =
    (if in_range h then 1%r/(2^256)%r else 0%r).
proof.
  case: h => y [|z] /=.
  + rewrite /ideal_compare /in_range /= dmapE.
    have he : mu (dinter 0 (2^256-1)) (pred1 true \o compare None) =
              mu (dinter 0 (2^256-1)) pred0.
    - by apply mu_eq => u; rewrite /pred1 /pred0 /(\o) /compare /=.
    by rewrite he mu0.
  + rewrite /ideal_compare /in_range /= dmapE.
    have he : mu (dinter 0 (2^256-1)) (pred1 true \o compare (Some z)) =
              mu1 (dinter 0 (2^256-1)) z.
    - by apply mu_eq => u; rewrite /pred1 /(\o) /compare /=; smt().
    rewrite he dinter1E /=. smt().
qed.

lemma blind_continuation_gap (d : outcome distr) :
  mu d correct - mu1 (dlet d ideal_compare) true =
  mu d correct - (1%r/(2^256)%r) * mu d in_range.
proof.
  have he : mu1 (dlet d ideal_compare) true =
            (1%r/(2^256)%r) * mu d in_range.
  + rewrite dlet1E (muE d) -sumZ. apply eq_sum => h /=.
    rewrite comparison_one. case: (in_range h) => /=; smt().
  by rewrite he.
qed.

lemma blind_continuation_lower (d : outcome distr) :
  mu d correct - 1%r/(2^256)%r <=
    mu d correct - mu1 (dlet d ideal_compare) true.
proof.
  rewrite blind_continuation_gap.
  have hp : 0 < 2^256 by smt(IntOrder.expr_gt0).
  have hn : 0%r <= 1%r/(2^256)%r by smt(RealOrder.divr_ge0).
  have hl : (1%r/(2^256)%r) * mu d in_range <= 1%r/(2^256)%r
    by apply RealOrder.ler_pimulr; smt(mu_bounded).
  smt().
qed.


type receipt_result =
  [ Missing | JournalRejected | PendingPosition | Advanced | Repeated | Current ].
type report = receipt_result * int * bool * bool option.
op report_after s c : report =
  with s = Early =>
    ((if c = ApplyReceipt then Missing else JournalRejected),
     (if c = ApplyReceipt then 0 else 1), true, None)
  with s = Prepared =>
    if c = ApplyReceipt then (Advanced, 0, false, Some true)
    else (PendingPosition, 0, false, None)
  with s = Applied =>
    ((if c = ApplyReceipt then Repeated else Current), 0, false, Some true).

op report_word s (w : command list) : report list =
  with w = [] => []
  with w = c :: cs => report_after s c :: report_word (step s c) cs.
op command_pairs = [[ApplyReceipt;ApplyReceipt];[ApplyReceipt;CatchUp];
                    [CatchUp;ApplyReceipt];[CatchUp;CatchUp]].
op phase_rows s = map (fun w => (s, w, report_word s w)) command_pairs.
op expected_rows = phase_rows Early ++ phase_rows Prepared ++ phase_rows Applied.

lemma report_tracks_readability s c :
  (report_after s c).`4 = (if readable (step s c) then Some true else None).
proof. by case: s; case: c. qed.
