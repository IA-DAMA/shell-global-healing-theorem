require import AllCore List Distr DList DInterval IntDiv StdOrder.
require import F4_Provider_Stream_Cut.
import Range.

(* A successful rand_core 0.6.4 u32 fill consumes words, even when
   its caller uses only a prefix of the last word. *)
op rounded (n : int) = 4 * ((n + 3) %/ 4).
lemma rounding n : 0 <= n => n <= rounded n <= n + 3.
proof.
  move=> hn; rewrite /rounded.
  have h := divz_eq (n+3) 4.
  smt(modz_ge0 ltz_pmod).
qed.

op splitread n (xs : int list) =
  (take n xs, take (rounded n-n) (drop n xs), drop (rounded n) xs).

lemma split_exact n rest : 0 <= n => 0 <= rest =>
  dmap (tape (rounded n + rest)) (splitread n) =
    dmap (tape n `*` (tape (rounded n-n) `*` tape rest))
       (fun p : int list * (int list * int list) => (p.`1,p.`2.`1,p.`2.`2)).
proof.
  move=> hn hr; have hp := rounding n hn.
  have hpad : 0 <= rounded n-n by smt().
  have htail : 0 <= rounded n-n+rest by smt().
  rewrite (_ : rounded n+rest=n+(rounded n-n+rest)) 1:/#.
  rewrite /tape (dlist_add octet n _ hn htail) (dlist_add octet (rounded n-n) rest hpad hr).
  rewrite dmap_dprodR !dmap_comp.
  apply eq_dmap_in => -[v [gap tail]] /supp_dprod [hv /supp_dprod [hg ht]] /=.
  have sv : size v = n by smt(supp_dlist_size).
  have sg : size gap = rounded n-n by smt(supp_dlist_size).
  rewrite /splitread (take_size_cat n v _ sv) (drop_size_cat n v _ sv).
  rewrite (take_size_cat (rounded n-n) gap tail sg) catA.
  have both : size (v++gap) = rounded n by rewrite size_cat sv sg; smt().
  by rewrite (drop_size_cat (rounded n) _ tail both).
qed.

(* A cache is the unread suffix of a u32 buffer, followed by further
   refills. It may be empty. The outer loop never drops a partial word
   between caches: an exhausted cache ends on a word boundary. *)
op cached n (cs : int list list) : int list * int list =
  with cs = [] => ([],[])
  with cs = c::rest =>
    if n <= size c then (take n c, drop (rounded n) c ++ flatten rest)
    else let more = cached (n-size c) rest in (c ++ more.`1,more.`2).

lemma rounded_shift k n : rounded (4*k+n) = 4*k+rounded n.
proof. rewrite /rounded (_ : 4*k+n+3 = k*4+(n+3)) 1:/# divzMDl //; ring. qed.

lemma aligned_cache_equivalence cs n :
  (forall c, mem cs c => exists k, size c = 4*k) =>
  0 <= n <= size (flatten cs) =>
  cached n cs = (take n (flatten cs), drop (rounded n) (flatten cs)).
proof.
  elim: cs n => [|c rest ih] n /=.
  + by trivial.
  rewrite flatten_cons. move=> ha hn; have [k hk] := ha c _; first by smt().
  have hr : forall b, mem rest b => exists j, size b=4*j by smt().
  case (n <= size c) => hs /=.
  + have r := rounding n _; first by smt().
    have rr : rounded n = 4*((n+3) %/ 4) by rewrite /rounded.
    have rd : rounded n <= size c by smt().
    by rewrite take_catl // drop_catl.
  have he : n = 4*k+(n-size c) by smt().
  have shift : rounded n = size c + rounded (n-size c)
    by have := rounded_shift k (n-size c); smt().
  have tail_size : 0 <= n-size c <= size (flatten rest) by move: hn; rewrite size_cat; smt().
  rewrite (ih (n-size c) hr tail_size) /= take_catr 1:/# drop_catr.
  + by have := rounding n _; smt().
  by rewrite shift /=; smt().
qed.

(* Gen takes a 256-bit seed; F is a 64-byte block family indexed by a
   fixed-nonce 64-bit counter. Each cache refill evaluates four counters.
   A bound on public capacity is fixed before the hybrid. *)
op realblocks ['k] (f : 'k -> int -> int list) (key : 'k) start count =
  flatten (map (f key) (range start (start+count))).

op freshblocks (fuel : unit list) : int list distr =
  with fuel = [] => dunit []
  with fuel = u::us => dmap (tape 64 `*` freshblocks us) append_pair.

lemma distinct_counter_window start count :
  0 <= start => 0 <= count => start+count <= 2^64 =>
  uniq (range start (start+count)) /\
  forall i, mem (range start (start+count)) i => 0 <= i < 2^64.
proof. move=> hf hn hb; split; first by apply range_uniq.
  by move=> i; rewrite mem_range; smt().
qed.

lemma blocks_are_tape fuel : freshblocks fuel = tape (64 * size fuel).
proof.
  elim: fuel => [|u us ih] /=.
  + by rewrite /tape dlist0.
  rewrite ih (_ : 64*(1+size us) = 64+64*size us) 1:/#.
  have hz : 0 <= 64*size us by smt(size_ge0).
  by rewrite /tape (dlist_add octet 64 (64*size us) _ hz) // /append_pair.
qed.

(* The primitive test sees only its classical counter responses. It can
   keep arbitrary auxiliary state; this EasyCrypt equality implements its
   classical tape adapter. The quantum interpretation is stated separately. *)
lemma counter_reduction ['k] (f : 'k -> int -> int list) (dk : 'k distr)
    (fuel : unit list) (decide : int list -> bool distr) :
  mu1 (dlet (dmap dk (fun k => realblocks f k 0 (size fuel))) decide) true -
  mu1 (dlet (tape (64*size fuel)) decide) true =
  mu1 (dlet dk (fun k => decide (flatten (map (f k) (range 0 (size fuel)))))) true -
  mu1 (dlet (freshblocks fuel) decide) true.
proof. by rewrite dlet_dmap /realblocks /= blocks_are_tape. qed.


(* Two instances are swapped separately only AFTER admission of their joint
   seed distribution. 'use' may process the two tapes in any order. *)
op pairview (x y : int list distr) (use : int list -> int list -> bool distr) =
  mu1 (dlet (x `*` y) (fun v : int list * int list => use v.`1 v.`2)) true.

lemma pair_budget x y ix iy use native ds dx dy :
  `|native - pairview x y use| <= ds =>
  `|pairview x y use - pairview ix y use| <= dx =>
  `|pairview ix y use - pairview ix iy use| <= dy =>
  `|native - pairview ix iy use| <= ds + dx + dy.
proof. rewrite !RealOrder.ler_norml; smt(). qed.
