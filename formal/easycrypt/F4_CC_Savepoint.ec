require import AllCore List.

(* Causal cut inside prepare's validation probe. A Boolean denotes installation
   of the selected generation at a particular location, not the value of a key.
   A pending database record may itself suffice to install the same generation
   later; this projection makes NO assertion that the early DB is safe. *)
type state = { ram:bool; db:bool; saved:bool; open_tx:bool; captured:bool }.
type action = [ Begin | Merge | Rollback | ObserveProcess | ObserveStore | Drop | Die ].
op run s a =
  with a=Begin => {|s with saved=s.`db;open_tx=true|}
  with a=Merge => if s.`open_tx then {|s with ram=true;db=true|} else s
  with a=Rollback => if s.`open_tx then {|s with db=s.`saved;open_tx=false|} else s
  with a=ObserveProcess => {|s with captured=s.`captured \/ s.`ram|}
  with a=ObserveStore => {|s with captured=s.`captured \/ s.`db|}
  with a=Drop => {|s with ram=false|}
  with a=Die => {|s with db=if s.`open_tx then s.`saved else s.`db;ram=false;open_tx=false|}.
op initial = {|ram=false;db=false;saved=false;open_tx=false;captured=false|}.
op probe = [Begin;Merge;Rollback].
op run_all = foldl run.

lemma store_only_impossible (predict : bool -> bool) :
  (forall h, predict (run_all initial h).`db = (run_all initial h).`ram) => false.
proof.
  move=> H; have early := H []; have late := H probe.
  by move: early late; rewrite /probe /run_all /initial /=; smt().
qed.

lemma acquisition_persists s a : s.`captured => (run s a).`captured.
proof. by case: a; simplify; smt(). qed.
lemma acquisition_persists_suffix s xs : s.`captured => (run_all s xs).`captured.
proof. rewrite /run_all; elim: xs s => [|a rest ih] s h //=; apply ih; exact (acquisition_persists s a h). qed.
lemma observed_between_rollback_and_drop xs :
  (run_all (run_all initial (probe ++ [ObserveProcess;Drop;Die])) xs).`captured.
proof. apply acquisition_persists_suffix; by rewrite /probe /run_all /initial /=. qed.
lemma disk_sample_different :
  !(run_all initial (probe ++ [ObserveStore;Drop;Die])).`captured.
proof. by rewrite /probe /run_all /initial /=. qed.
