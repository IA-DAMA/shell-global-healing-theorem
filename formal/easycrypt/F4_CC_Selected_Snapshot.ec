(* Projection of the two cuts measured inside a successful synthetic REMOVE.
   No key material.  A scheduler can know its own position: that position
   is deliberately absent from the database observation, not from FreshQ. *)
require import AllCore.

type phase = [ BeforeMerge | AfterRollback ].
type sample = { stored_epoch : int; staged : bool; selector_accepted : bool }.

op disk_view (e : int) (_ : phase) =
  {| stored_epoch = e; staged = true; selector_accepted = false |}.

op live_epoch (e : int) (p : phase) =
  with p = BeforeMerge => e
  with p = AfterRollback => e + 1.

lemma disk_and_decision_insufficient (e : int) (predict : sample -> int) :
  (forall p, predict (disk_view e p) = live_epoch e p) => false.
proof.
  move=> h; have a := h BeforeMerge; have b := h AfterRollback.
  by move: a b; rewrite /disk_view /live_epoch /=; smt().
qed.

(* Adding the causal phase suffices for the installed epoch at THESE two cuts.
   It says nothing about the derivability from a staged commit, OS copies or Q. *)
op reconstruct (s : sample) (p : phase) =
  s.`stored_epoch + (if p = AfterRollback then 1 else 0).

lemma phase_recovers_live_epoch e p :
  reconstruct (disk_view e p) p = live_epoch e p.
proof. by case: p; rewrite /reconstruct /disk_view /live_epoch /=; smt(). qed.
