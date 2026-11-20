require import AllCore List Distr DInterval DList.
require import F4_Provider_Stream_Cut F4_Counter_Block_Adapter F4_M5_Singleton_Schedule
  F4_M5_Epoch_Exporter_Hops.

(* One bounded provider instance; a position fixed before this stream is sampled.
   A single continuation receives BOTH pieces outside the selected slice, and
   the outputs derived with that slice. Never resample the other pieces per use. *)
op finish_schedule (p:params) (c:bytes) =
  let t = mac384 p.`old_init c in
  let j = mac384 t p.`join_input in
  let m = mac384 j p.`psk in (mac384 m welcome_slot, mac384 m p.`epoch_input).

module Direct = {
  proc real(p:params) = { var c; c <$ tape 48; return finish_schedule p c; }
}.
module type PairTest = { proc run(w e:bytes):bool }.
module Formula(D:PairTest) = {
  proc main(p:params) = { var we,b; we <@ Direct.real(p); b <@ D.run(we.`1,we.`2); return b; }
}.
lemma schedule_formula (D <: PairTest) par &m :
  Pr[Formula(D).main(par) @ &m : res] = Pr[Schedule(D).real(par) @ &m : res].
proof. byequiv (_: ={arg,glob D} ==> ={res}) => //.
  proc; inline Direct.real; wp; call (_: ={arg,glob D} ==> ={res}); first by sim.
  by wp; rnd; auto; rewrite /finish_schedule.
qed.

op parts pre (t:bytes) = (take pre t, take 48 (drop pre t), drop 48 (drop pre t)).
op slices pre post = tape pre `*` (tape 48 `*` tape post).
op flatten3 (v:bytes * (bytes * bytes)) = v.`1 ++ (v.`2.`1 ++ v.`2.`2).
op tuple3 (v:bytes * (bytes * bytes)) = (v.`1,v.`2.`1,v.`2.`2).

lemma split_input pre post : 0 <= pre => 0 <= post =>
  tape (pre+(48+post)) = dmap (slices pre post) flatten3.
proof. move=> hp hs; rewrite independent_48_byte_slice // /slices /flatten3 /append_pair.
  by rewrite dmap_dprodR dmap_comp.
qed.

lemma slice_law pre post : 0 <= pre => 0 <= post =>
  dmap (tape (pre+(48+post))) (parts pre) = dmap (slices pre post) tuple3.
proof.
  move=> hp hs; rewrite split_input // dmap_comp.
  apply eq_dmap_in => -[l [c r]] /supp_dprod [hl /supp_dprod [hc hr]] /=.
  have vl : size l=pre by apply (supp_dlist_size octet pre l hp hl).
  have vc : size c=48 by apply (supp_dlist_size octet 48 c _ hc).
  by rewrite /parts /flatten3 /tuple3 /= (take_size_cat pre l _ vl) (drop_size_cat pre l _ vl) (take_size_cat 48 c r vc) (drop_size_cat 48 c r vc).
qed.

op process (configure : bytes -> bytes -> params)
    (observe : bytes -> bytes -> (bytes * bytes) -> bool distr)
    (v : bytes * bytes * bytes) =
  observe v.`1 v.`3 (finish_schedule (configure v.`1 v.`3) v.`2).

lemma block_to_schedule ['k] (f : 'k -> int -> bytes) (keys : 'k distr)
    (fuel : unit list) pre post configure observe :
  0 <= pre => 0 <= post => 64 * size fuel = pre+(48+post) =>
  size fuel <= 2^64 =>
  let k = process configure observe in
  mu1 (dlet (dmap keys (fun seed => realblocks f seed 0 (size fuel)))
        (fun t => k (parts pre t))) true -
  mu1 (dlet (dmap (slices pre post) tuple3) k) true =
  mu1 (dlet keys (fun seed => k (parts pre (flatten (map (f seed) (range 0 (size fuel))))))) true -
  mu1 (dlet (freshblocks fuel) (fun t => k (parts pre t))) true.
proof. move=> hp hs hcap hcounter /=.
  rewrite -(slice_law pre post hp hs) dlet_dmap -hcap.
  by rewrite dlet_dmap blocks_are_tape /realblocks.
qed.
