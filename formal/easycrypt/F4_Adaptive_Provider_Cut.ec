require import AllCore List Distr DInterval DList F4_Provider_Stream_Cut.

(* A stop decision sees all previously consumed octets, never the unread
   tape. At most size fuel further octets may be inspected to find a cut.
   Keep the unused suffix in the result so that later calls are simulated
   on the same tape. None records exhaustion without selecting a challenge. *)
type cut = (int list * int list * int list) option.
op here (seen rest : int list) : cut =
  Some (seen, take 48 rest, drop 48 rest).
op from_tape (stop : int list -> bool) (fuel : unit list)
    (seen rest : int list) : cut =
  with fuel = [] => if stop seen then here seen rest else None
  with fuel = u :: fs =>
    if stop seen then here seen rest else
      from_tape stop fs (seen ++ [head 0 rest]) (behead rest).

op at_cut (seen : int list) (left : int) : cut distr =
  dmap (tape 48 `*` tape left)
       (fun p : int list * int list => Some (seen, p.`1, p.`2)).
op online (stop : int list -> bool) (fuel : unit list) (seen : int list) : cut distr =
  with fuel = [] => if stop seen then at_cut seen 0 else MUnit.dunit None
  with fuel = u :: fs =>
    if stop seen then at_cut seen (size fs + 1) else
      dlet octet (fun x => online stop fs (seen ++ [x])).

lemma now_exact seen n : 0 <= n =>
  dmap (tape (48+n)) (here seen) = at_cut seen n.
proof.
  move=> hn; rewrite /at_cut /tape dlist_add // dmap_comp.
  apply eq_dmap_in => -[x y] /supp_dprod [hx hy] /=.
  have hs : size x = 48 by smt(supp_dlist_size).
  by rewrite /here /= (take_size_cat 48 x y hs) (drop_size_cat 48 x y hs).
qed.

lemma adaptive_slice_exact stop fuel seen :
  dmap (tape (48+size fuel)) (from_tape stop fuel seen) = online stop fuel seen.
proof.
  elim: fuel seen => [|u fs ih] seen /=.
  + case (stop seen) => h /=.
    - have -> : from_tape stop [] seen = here seen by apply fun_ext => r; rewrite /= h.
      exact (now_exact seen 0 _); trivial.
    - have -> : from_tape stop [] seen = (fun r => None) by apply fun_ext => r; rewrite /= h.
      by rewrite dmap_cst // /tape dlist_ll // /octet dinter_ll.
  + case (stop seen) => h /=.
    - have -> : from_tape stop (u::fs) seen = here seen by apply fun_ext => r; rewrite /= h.
      clear ih. have hs := size_ge0 fs.
      rewrite (_ : 49+size fs = 48+(size fs+1)) 1:/#.
      apply now_exact; smt().
    - have eqn : 49+size fs = (48+size fs)+1 by ring.
      have hn : 0 <= 48+size fs by clear ih; smt(size_ge0).
      rewrite /tape eqn (dlistS octet (48+size fs) hn) /= dmap_comp dmap_dprodE.
      apply eq_dlet => // x /=.
      have H := ih (seen ++ [x]).
      rewrite /tape in H; rewrite -H.
      apply eq_dmap => r /=.
      by rewrite h.
qed.
