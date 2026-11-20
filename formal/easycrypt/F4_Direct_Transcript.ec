require import AllCore List Distr DBool DInterval StdOrder.
require import F4_Late_Opening_and_Hybrids F4_Online_Recovery_Cut.

(* A concrete operation provides a sequence of observations, including any
   public reply and the actual post-error effects visible to this observer.
   Its state can include inaccessible private records. Only classical
   transcript entries are appended. No quantum register is copied. *)
op record ['s 'c 'o] (step : 's -> 'c -> 's * 'o list)
    (state : 's * 'o list) (c : 'c) : 's * 'o list =
  let (t,out) = step state.`1 c in (t,state.`2 ++ out).

lemma entire_prefix ['s 'c 'o] (step : 's -> 'c -> 's * 'o list)
    (word : 'c list) (s : 's) (before : 'o list) :
  foldl (record step) (s,before) word =
    let (t,tail) = foldl (record step) (s,[]) word in (t,before ++ tail).
proof.
  elim: word s before => [|c cs ih] s before /=; first by rewrite cats0.
  rewrite /record /=.
  case: (step s c) => t out /=.
  have h1 := ih t (before ++ out).
  have h2 := ih t out.
  by case: (foldl (record step) (t,[]) cs) h1 h2 => u tail /=; smt(catA).
qed.

(* Feedback is explicit: a strategy can read every return so far before
   choosing the next command. Local simulation must cover returned errors
   and their residual state just as it covers successful results. *)
op interact ['s 'c 'o] (step : 's -> 'c -> 's * 'o list)
    (state : 's * 'o list) (policy : 'o list -> 'c) =
  record step state (policy state.`2).

lemma adaptive_transcript_transfer ['s 't 'c 'o]
    (src : 's -> 'c -> 's * 'o list) (model : 't -> 'c -> 't * 'o list)
    (rel : 's -> 't -> bool) :
  (forall s t c, rel s t => rel (src s c).`1 (model t c).`1 /\
                             (src s c).`2 = (model t c).`2) =>
  forall (choices : ('o list -> 'c) list) s t h, rel s t =>
    let l = foldl (interact src) (s,h) choices in
    let r = foldl (interact model) (t,h) choices in
    rel l.`1 r.`1 /\ l.`2 = r.`2.
proof.
  move=> stepok; elim => [|choose rest ih] s t h hr /=; first by smt().
  have hh := stepok s t (choose h) hr.
  rewrite /interact /record /=.
  case: (src s (choose h)) hh => ls lo /=.
  case: (model t (choose h)) => rs ro /= [hrel heq].
  rewrite heq. exact (ih ls rs (h ++ ro) hrel).
qed.

(* One bit visible, the remaining 255 bits uniform, even given old records.
   This is a sufficiency countermodel, not a leakage assumption about Rust.
   h is any fixed prior history. The unknown suffix is sampled afterwards. *)
op suffixes = dinter 0 (2^255 - 1).
lemma whole_prediction ['h] (predict : 'h -> bool -> int) h b :
  mu1 suffixes (predict h b) <= 1%r/(2^255)%r.
proof.
  have hn : 0 < 2^255 by smt(IntOrder.expr_gt0).
  have hpos := ge0_mu1 (dinter 0 (2^255-1)) 0.
  rewrite dinter1E /= in hpos.
  rewrite /suffixes dinter1E /=.
  case: (0 <= predict h b <= 2^255 - 1) => //=; smt().
qed.

(* Any independent uniform ideal key has a uniform first bit. A key with
   first bit b is consistent with 2^255 suffixes. Hypotheses about which
   complete outputs are recoverable cannot eliminate this distinguisher. *)
lemma partial_view_gap b :
  1%r - mu1 dbool b = 1%r/2%r.
proof. by rewrite dboolE; case: b => /=; smt(). qed.

(* Structural knowledge means that the entire selected key is forced by
   the observer's transcript. Every command here may depend on the previous
   public data, but contributes no information about the missing suffix. *)
op log_step ['cmd] (s : bool * 'cmd list) (c : 'cmd) = Some (s.`1, s.`2 ++ [c]).
op compatible ['cmd] (s : bool * 'cmd list) (candidate : bool * int) =
  candidate.`1 = s.`1 /\ 0 <= candidate.`2 < 2^255.
op key_forced ['cmd] (s : bool * 'cmd list) =
  exists k, forall y, compatible s y => y = k.
lemma no_full_key ['cmd] (s : bool * 'cmd list) : !key_forced s.
proof.
  have hpow : 2^255 = 2 * 2^254 by have := Ring.IntID.exprS 2 254; smt().
  have hp : 0 < 2^254 by smt(IntOrder.expr_gt0).
  have hn : 1 < 2^255 by smt().
  have h0 : compatible s (s.`1,0) by rewrite /compatible /=; smt().
  have h1 : compatible s (s.`1,1) by rewrite /compatible /=; smt().
  rewrite /key_forced; smt().
qed.

lemma whole_cut_and_nonzero_gap ['cmd] (s : bool * 'cmd list) :
  safe log_step key_forced s /\ 1%r - mu1 dbool s.`1 = 1%r/2%r.
proof.
  split; last by apply partial_view_gap.
  rewrite /safe => w t _; exact (no_full_key t).
qed.

(* The ideal transcript is an equal mixture of the two values of the first
   bit, with identical prior memory and suffix distribution. a and b are
   acceptance probabilities for any final effect, including quantum ones.
   The equality test a=1,b=0 attains the upper bound. *)
lemma binary_effect_bound (a b : real) :
  0%r <= a <= 1%r => 0%r <= b <= 1%r =>
  `|a - (a+b)/2%r| <= 1%r/2%r.
proof. rewrite RealOrder.ler_norml; smt(). qed.

(* A second countermodel holds no exact classical flag in the old
   register. For prior states |0> and |+>, measuring Z and guessing 1
   only on outcome 1 succeeds with probability 3/4 for an equiprobable
   hidden bit. The ideal challenge bit matches this guess with probability
   1/2. No postselection is involved. *)
type real_two = real * real * real * real.
op times2 (a b : real_two) : real_two =
  (a.`1*b.`1 + a.`2*b.`3, a.`1*b.`2 + a.`2*b.`4,
   a.`3*b.`1 + a.`4*b.`3, a.`3*b.`2 + a.`4*b.`4).
op zstate : real_two = (1%r,0%r,0%r,0%r).
op plusstate : real_two = (1%r/2%r,1%r/2%r,1%r/2%r,1%r/2%r).
op difference (a b : real_two) =
  (a.`1-b.`1, a.`2-b.`2, a.`3-b.`3, a.`4-b.`4).

lemma nonorthogonal_memory :
  let product = times2 zstate plusstate in product.`1 + product.`4 = 1%r/2%r.
proof. by rewrite /times2 /zstate /plusstate /=; smt(). qed.

lemma memory_spectrum_certificate :
  let d = difference zstate plusstate in
  times2 d d = (1%r/2%r,0%r,0%r,1%r/2%r).
proof. by rewrite /times2 /difference /zstate /plusstate /=; smt(). qed.

lemma computational_basis_test_gap :
  (zstate.`1 + plusstate.`4)/2%r - 1%r/2%r = 1%r/4%r.
proof. by rewrite /zstate /plusstate /=; smt(). qed.

(* Heisenberg pullbacks of final tests. The state argument can denote a
   joint classical/quantum density operator on a common simulation space.
   Both world instruments include all returns, rejection and a retained
   observer. This abstract lemma does not assert a native instrument bound.
   The error hypothesis is local, on every allowed input and continuation
   test. This avoids guessing a path in an adaptive tree. *)
type 's instrument = ('s -> real) -> 's -> real.
op pull ['s] (ops : 's instrument list) (finish : 's -> real) =
  foldr (fun op1 test => op1 test) finish ops.

lemma pull_closed ['s] (allowed : ('s -> real) -> bool)
    (ops : 's instrument list) finish :
  (forall op1, mem ops op1 => forall test, allowed test => allowed (op1 test)) =>
  allowed finish => allowed (pull ops finish).
proof.
  elim: ops => [|op1 ops ih] //=.
  move=> hc hf; rewrite /pull /=; apply hc; first by smt().
  apply ih => //; smt().
qed.

(* Neighboring worlds on one application operation, with arbitrary past
   and arbitrary adaptive continuation represented in its registers. *)
lemma bounded_pullback ['s] (allow : ('s -> real) -> bool)
    (lhs rhs : 's instrument) (realtest idealtest : 's -> real) slack tailerr :
  (forall s, `|lhs realtest s - lhs idealtest s| <= tailerr) =>
  allow idealtest =>
  (forall f, allow f => forall s, `|lhs f s - rhs f s| <= slack) =>
  forall s, `|lhs realtest s - rhs idealtest s| <= tailerr + slack.
proof.
  move=> hc ha hop s; have bound := hop idealtest ha s.
  have previous := hc s. smt(RealOrder.ler_dist_add).
qed.

type 's hop = ('s instrument * 's instrument * real).
op local_hop ['s] (allow : ('s -> real) -> bool) (h : 's hop) =
  (forall f, allow f => allow (h.`2 f)) /\
  (forall f, allow f => forall s, `|h.`1 f s - h.`2 f s| <= h.`3) /\
  (forall (f g : 's -> real) budget,
    (forall s, `|f s-g s| <= budget) =>
    forall s, `|h.`1 f s - h.`1 g s| <= budget).

op error_sum ['s] (hs : 's hop list) =
  foldr (fun (h : 's hop) r => r+h.`3) 0%r hs.

lemma adaptive_effect_budget ['s] (allow : ('s -> real) -> bool)
    (hs : 's hop list) (finish : 's -> real) :
  allow finish => (forall h, mem hs h => local_hop allow h) =>
  let rf = pull (map (fun (h : 's hop) => h.`1) hs) finish in
  let idf = pull (map (fun (h : 's hop) => h.`2) hs) finish in
  allow idf /\ forall s, `|rf s-idf s| <= error_sum hs.
proof.
  move=> hf; elim: hs => [|h hs ih] /=.
  + by rewrite /pull /error_sum /=; smt().
  move=> hall; have [hclose [hgap hcontract]] := hall h _; first by smt().
  have [htest htail] := ih _; first by smt().
  rewrite /pull /error_sum /=; split; first by apply hclose.
  move=> s; apply (bounded_pullback allow h.`1 h.`2 _ _ h.`3 _);
    try exact htest; try exact hgap.
  + apply hcontract; exact htail.
qed.

(* A verified DIRECT comparison supplies equality of two byte strings.
   The same injective unsigned decoding of these 32 bytes gives the same
   integer. This lemma consumes that equality instead of assuming a
   distribution of recoveries for the entire application. *)
lemma exact_selected_direct_gap k restored &m :
  0 <= k < 2^256 => restored=k =>
  Pr[LateOpening.test(false,k,Some restored) @ &m : res] -
  Pr[LateOpening.test(true,k,Some restored) @ &m : res] = 1%r - 1%r/(2^256)%r.
proof. move=> hk ->. exact (fixed_restored_gap k &m hk). qed.
