require import AllCore List F4_Removal_Route_Closure.

(* Coordinates are certificate variables, not probabilities. Unit facts
   persist. Only the current phase's rules may fire in that phase. *)
type weights = f4_route_fact -> real.
op indicator (s : f4_route_set) : weights = fun a => if s a then 1%r else 0%r.
op units (x : weights) : f4_route_set = fun a => x a = 1%r.
op row_ok (p : f4_phase) (x y : weights) =
  (forall a, 0%r <= y a <= 1%r) /\
  (forall a, x a <= y a) /\
  (forall a, p.`2 a => y a = 1%r) /\
  (forall a b c, p.`1 (a,b,c) => y a + y b - 1%r <= y c).
op linear_cert (ps : f4_phase list) (x : weights) (t : f4_route_fact) =
  with ps = [] => x t = 0%r
  with ps = p :: rest => exists y, row_ok p x y /\ linear_cert rest y t.

lemma row_round p x y : row_ok p x y =>
  contains (plus (units x) p.`2) (units y) /\ closed p.`1 (units y).
proof. rewrite /row_ok /units /plus /contains /closed; smt(). qed.

lemma row_embed (p : f4_phase) v w : contains (plus v p.`2) w => closed p.`1 w =>
  row_ok p (indicator v) (indicator w).
proof. rewrite /row_ok /indicator /plus /contains /closed; smt(). qed.

lemma linear_to_temporal ps x t : linear_cert ps x t => certified ps (units x) t.
proof.
  elim: ps x => [|p rest ih] x /=.
  + rewrite /units; smt().
  move=> [y [hr hc]]; exists (units y).
  have [hi hk] := row_round p x y hr.
  by split => //; split => //; apply ih.
qed.

lemma temporal_to_linear ps v t : certified ps v t => linear_cert ps (indicator v) t.
proof.
  elim: ps v => [|p rest ih] v /=.
  + by rewrite /indicator => ->.
  move=> [w [hi [hk ht]]]; exists (indicator w).
  by split; [apply row_embed | apply ih].
qed.

lemma linear_temporal_exact ps v t :
  linear_cert ps (indicator v) t <=> !final_view ps v t.
proof.
  rewrite temporal_cut_exact; split.
  + move=> hl; have h := linear_to_temporal ps (indicator v) t hl.
    have eu : units (indicator v) = v by apply fun_ext => a; rewrite /units /indicator; case: (v a) => //=; smt().
    by rewrite -eu.
  exact (temporal_to_linear ps v t).
qed.
