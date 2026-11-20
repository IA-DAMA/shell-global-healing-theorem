require import AllCore List Distr F4_M5_Exporter_Reopening F4_QSF_Oracle_Embedding StdOrder.
(* A private state is threaded through an instrument. Its classical outcome
   AND the corresponding residual state are returned together. This allows
   measurement-dependent control flow without turning the prior into a
   classical transcript or drawing an independent residual state. *)
type 's boundary = [ Finished of 's | FirstRead of ('s * table) ].

op cut ['s] (choose : 's -> (coord option * 's) distr)
   (receive : 's -> word32 option -> 's distr) (star : coord)
   (m : table) (s : 's) (fuel : unit list) : 's boundary distr =
  with fuel = [] => dunit (Finished s)
  with fuel = t :: ts =>
    dlet (choose s) (fun (z : coord option * 's) =>
      if z.`1 = Some star then dunit (FirstRead (z.`2,m)) else
      if z.`1 = None then dlet (receive z.`2 None)
        (fun w => cut choose receive star m w ts) else
      let x = oget z.`1 in
      dlet sample32 (fun fresh =>
        let v = read m x fresh in
        dlet (receive z.`2 (Some v)) (fun w =>
          cut choose receive star (put m x v) w ts))).

(* Keep the selected value OUTSIDE the stopped table. Both executions run
   with this same off-coordinate table until the first read. Thus the
   stopped state may be passed to a world-specific continuation, including
   arbitrarily many further operations, without discarding the prior. *)
op off (m : table) x = fun y => if y=x then None else m y.
op mask ['s] x (r : 's boundary) =
  with r = Finished s => Finished s
  with r = FirstRead p => FirstRead (p.`1,off p.`2 x).
op hit ['s] (r : 's boundary) =
  with r = Finished s => false
  with r = FirstRead p => true.

lemma stopped_law ['s] (choose : 's -> (coord option * 's) distr) receive star fuel s m n :
  (forall y, y<>star => m y = n y) =>
  dmap (cut choose receive star m s fuel) (mask star) =
  dmap (cut choose receive star n s fuel) (mask star).
proof.
  elim: fuel s m n => [|t ts ih] s m n agree //=.
  rewrite !dmap_dlet; apply eq_dlet => // z.
  case (z.`1=Some star) => yes; rewrite yes /=.
  + have h : off m star = off n star by apply fun_ext => y; rewrite /off; case (y=star) => // yz; apply agree; exact yz.
    by rewrite !dmap_dunit /= h.
  case (z.`1=None) => no /=.
  + rewrite !dmap_dlet; apply eq_dlet => // w; apply ih; exact agree.
  rewrite !dmap_dlet; apply eq_dlet => // fresh.
  have hx : oget z.`1 <> star by clear ih; case: (z.`1) yes no; smt().
  have ry : read m (oget z.`1) fresh = read n (oget z.`1) fresh
    by rewrite /read (agree _ hx).
  simplify; rewrite ry !dmap_dlet; apply eq_dlet => // w; apply ih.
  by move=> y hy; rewrite /put; clear ih; smt().
qed.

(* Both continuations consume the same stopped distribution. A Finished
   result has the same final measurement; only FirstRead can differ. *)
op finish ['s] (measure : 's -> bool distr) (resume : 's * table -> bool distr)
   (r : 's boundary) =
  with r = Finished s => measure s
  with r = FirstRead p => resume p.

lemma first_read_budget ['s] (d : 's boundary distr) measure real ideal :
  `|mu1 (dlet d (finish measure real)) true - mu1 (dlet d (finish measure ideal)) true|
    <= mu d hit.
proof.
  have eqon : forall r, !hit r => finish measure real r = finish measure ideal r
    by case => //.
  have l := conditional_charge_one d hit (finish measure real) (finish measure ideal) eqon.
  have rev : forall r, !hit r => finish measure ideal r = finish measure real r by smt().
  have r := conditional_charge_one d hit (finish measure ideal) (finish measure real) rev.
  rewrite RealOrder.ler_norml; smt().
qed.
lemma same_boundary_budget ['s] (choose : 's -> (coord option * 's) distr)
    receive star fuel state m n measure real ideal :
  (forall y, y <> star => m y = n y) =>
  let l = dmap (cut choose receive star m state fuel) (mask star) in
  let r = dmap (cut choose receive star n state fuel) (mask star) in
  `|mu1 (dlet l (finish measure real)) true - mu1 (dlet r (finish measure ideal)) true|
     <= mu l hit.
proof.
  move=> same.
  have e := stopped_law choose receive star fuel state m n same.
  have b := first_read_budget (dmap (cut choose receive star m state fuel) (mask star)) measure real ideal.
  by rewrite -e.
qed.
