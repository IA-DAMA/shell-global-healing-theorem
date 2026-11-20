require import AllCore List Distr StdOrder.
require Subtype.
require import F4_Late_Opening_and_Hybrids.

(* Figure 8, Theorem 2. All query/return values are classical. Raw DH wire
   encodings are preserved, including encodings giving equal DH results. *)
subtype b32 = { xs : int list | size xs = 32 /\ all (fun b => 0 <= b < 256) xs }.
realize inhabited.
proof. exists (nseq 32 0); split; first by rewrite size_nseq. apply/allP => x; rewrite mem_nseq; smt(). qed.
type pqct.
type kemct = pqct * b32.
type input06 = b32 * b32 * b32.
type answer = kemct -> b32 option.
op repr (b : b32) = val b.
op sha3_256 : int list -> b32.
op h06 (k : b32) (u : input06) : b32 =
  sha3_256 (repr k ++ repr u.`1 ++ repr u.`2 ++ repr u.`3 ++ [92;46;47;47;94;92]).
op inp (dh : b32 -> b32) pk x : input06 = (dh x,x,pk).

op ordinary (star : kemct) dec dh pk (c : kemct) : b32 option =
  if c=star then None else
  omap (fun k => h06 k (inp dh pk c.`2)) (dec c.`1).

(* The KEM reduction never forwards the forbidden ML-KEM challenge. The
   PRF reduction uses Eval only for the challenge KEM ciphertext; all
   other ciphertexts take ordinary local decapsulation. *)
op embedded (star : kemct) dec dh pk (eval : input06 -> b32)
    (c : kemct) : b32 option =
  if c = star then None else
  if c.`1 = star.`1 then Some (eval (inp dh pk c.`2))
  else omap (fun k => h06 k (inp dh pk c.`2)) (dec c.`1).

lemma kem_simulation_correct (star : kemct) dec dh pk k :
  dec star.`1 = Some k =>
  ordinary star dec dh pk = embedded star dec dh pk (h06 k).
proof. move=> h; apply fun_ext => c; rewrite /ordinary /embedded.
  case: (c=star) => //; case: (c.`1=star.`1) => // ->; by rewrite h. qed.

op patch_at (u : input06) (value : b32) (table : input06 -> b32) x =
  if x=u then value else table x.

(* For an allowed same-PQ-ciphertext query, raw c2 is necessarily distinct.
   The challenge coordinate of a consistent random function can be
   resampled without altering any answer, even for repeated queries. *)
lemma dec_cannot_read_star (star : kemct) dec dh pk value table :
  embedded star dec dh pk (patch_at (inp dh pk star.`2) value table) =
  embedded star dec dh pk table.
proof. apply fun_ext => c; rewrite /embedded /patch_at /inp.
  case: (c=star) => //; case: (c.`1=star.`1) => //; smt(). qed.

(* A is the continuation after receiving public parameters (fixed in A),
   the selected key and the interactive answer interface. Equal interfaces
   induce the same adaptive execution. No implementation can inspect the
   reduction's hidden state through a mathematical function oracle. *)
op kem_view (a : b32 -> answer -> bool distr) star dec dh pk challenge =
  a challenge (ordinary star dec dh pk).
op outer_view (a : b32 -> answer -> bool distr) star dec dh pk k challenge =
  a challenge (embedded star dec dh pk (h06 k)).

lemma outer_endpoints a (star : kemct) dec dh pk k challenge :
  dec star.`1 = Some k =>
  kem_view a star dec dh pk challenge = outer_view a star dec dh pk k challenge.
proof. move=> h; by rewrite /kem_view /outer_view (kem_simulation_correct _ _ _ _ _ h). qed.

op prf_view (a : b32 -> answer -> bool distr) (star : kemct) dec dh pk
     (eval : input06 -> b32) (independent : b32 option) =
  a (if independent=None then eval (inp dh pk star.`2) else oget independent)
    (embedded star dec dh pk eval).

lemma g1_matches_prf_real a (star : kemct) dec dh pk random_k :
  outer_view a star dec dh pk random_k (h06 random_k (inp dh pk star.`2)) =
  prf_view a star dec dh pk (h06 random_k) None.
proof. by rewrite /outer_view /prf_view. qed.

lemma g2_same_for_both_reductions a (star : kemct) dec dh pk value table :
  prf_view a star dec dh pk (patch_at (inp dh pk star.`2) value table) None =
  prf_view a star dec dh pk table (Some value).
proof. by rewrite /prf_view /= dec_cannot_read_star /patch_at. qed.

lemma g3_matches_prf_real a (star : kemct) dec dh pk random_k independent :
  prf_view a star dec dh pk (h06 random_k) (Some independent) =
  outer_view a star dec dh pk random_k independent.
proof. by rewrite /outer_view /prf_view. qed.

(* Private, non-rewinding guess of one of N_path possible slots. dr and
   di carry the mass of accepting runs at their selected slot. No claim
   that a Product execution can embed a primitive at a guessed slot. *)
lemma selected_path_loss n dr di : 0 < n =>
  mu dr (fun i => 0 <= i < n) - mu di (fun i => 0 <= i < n) =
    n%r * (mu (guessed_index n dr) (pred1 true) -
           mu (guessed_index n di) (pred1 true)).
proof. move=> hn; rewrite private_index_gap //; field; smt(). qed.

(* Off-star entries are sampled once and shared between both views.
   Enumerating a finite domain describes its law, not efficient QPT code.
   A complete, duplicate-free list gives the independent-coordinate table.
   Unqueried coordinates can equivalently be supplied lazily, but no runtime
   bound on such a simulator is proved by this finite-table lemma. *)
op entries (coins : b32 distr) (inputs : input06 list) : (input06 -> b32) distr =
  with inputs = [] => dunit (fun _ => witness)
  with inputs = u :: us => dlet (entries coins us)
      (fun t => dmap coins (fun v => patch_at u v t)).

lemma middle_distribution a (star : kemct) dec dh pk coins rest :
  dlet (entries coins ((inp dh pk star.`2)::rest))
    (fun t => prf_view a star dec dh pk t None) =
  dlet (entries coins rest)
    (fun t => dlet coins (fun v => prf_view a star dec dh pk t (Some v))).
proof. rewrite /= dlet_dlet; apply eq_dlet => // t.
  rewrite dlet_dmap; apply eq_dlet => // v.
  exact (g2_same_for_both_reductions a star dec dh pk v t). qed.

(* Common random tape for the honest setup. Outputs of the two
   continuations can be coupled identically when decapsulation is correct on the selected ciphertext.
   This lemma charges the exceptional event once for each exterior hop. *)
lemma correctness_charge ['a] (d : 'a distr) (bad l r : 'a -> bool) :
  (forall x, x \in d => !bad x => l x = r x) =>
  `|mu d l - mu d r| <= mu d bad.
proof. move=> agree.
  have good : mu d (predI l (predC bad)) = mu d (predI r (predC bad))
    by apply mu_eq_support => x hx; rewrite /predI /predC; smt().
  have hl : mu d (predI l bad) <= mu d bad by apply mu_le => x _; rewrite /predI; smt().
  have hr : mu d (predI r bad) <= mu d bad by apply mu_le => x _; rewrite /predI; smt().
  have pl := mu_bounded d (predI l bad); have pr := mu_bounded d (predI r bad).
  rewrite (mu_split d l bad) (mu_split d r bad) RealOrder.ler_norml; smt().
qed.

require import RealSeries.
lemma conditional_charge_one ['a] (d : 'a distr) (bad : 'a -> bool)
    (l r : 'a -> bool distr) :
  (forall x, !bad x => l x = r x) =>
  mu1 (dlet d l) true <= mu1 (dlet d r) true + mu d bad.
proof.
  move=> same; rewrite /mu1 !dletE (muE d bad) -sumD /=.
  + apply summable_mu1_wght; smt(mu_bounded).
  + exact (summable_mu1_cond d bad).
  apply ler_sum => /=.
  + move=> x; case: (bad x) => h.
    - have a := mu_bounded (l x) (pred1 true).
      have b := mu_bounded (r x) (pred1 true).
      have c := ge0_mu1 d x; smt().
    - by rewrite (same x _); smt().
  + apply summable_mu1_wght; smt(mu_bounded).
  + apply summableD; last exact (summable_mu1_cond d bad).
    apply summable_mu1_wght; smt(mu_bounded).
qed.

type pqpk.
type setup = { pk1 : pqpk; pk2 : b32; ct : kemct; k1 : b32;
               dhfun : b32 -> b32; dec1 : pqct -> b32 option }.
type strategy = pqpk -> b32 -> kemct -> b32 -> answer -> bool distr.

op public_view (a : strategy) s = a s.`pk1 s.`pk2 s.`ct.
op starin s = inp s.`dhfun s.`pk2 s.`ct.`2.
op failed s = s.`dec1 s.`ct.`1 <> Some s.`k1.
op native_end a s v = kem_view (public_view a s) s.`ct s.`dec1 s.`dhfun s.`pk2 v.
op kem_test a s k v = outer_view (public_view a s) s.`ct s.`dec1 s.`dhfun s.`pk2 k v.
op prf_test a s f v = prf_view (public_view a s) s.`ct s.`dec1 s.`dhfun s.`pk2 f v.
op accept (d : setup distr) (run : setup -> bool distr) = mu1 (dlet d run) true.

op g0 a s = native_end a s (h06 s.`k1 (starin s)).
op b0 a s = kem_test a s s.`k1 (h06 s.`k1 (starin s)).
op b1 a coins s = dlet coins (fun k => kem_test a s k (h06 k (starin s))).
op d0 a coins s = dlet coins (fun k => prf_test a s (h06 k) None).
op d1 a coins rest s = dlet (entries coins (starin s :: rest s))
                              (fun f => prf_test a s f None).
op e1 a coins rest s = dlet (entries coins (starin s :: rest s))
                         (fun f => dlet coins (fun v => prf_test a s f (Some v))).
op e0 a coins s = dlet coins (fun k =>
                    dlet coins (fun v => prf_test a s (h06 k) (Some v))).
op c1 a coins s = dlet coins (fun k =>
                    dlet coins (fun v => kem_test a s k v)).
op c0 a coins s = dlet coins (fun v => kem_test a s s.`k1 v).
op g4 a coins s = dlet coins (fun v => native_end a s v).

lemma middle_same a coins rest s : is_lossless coins =>
  d1 a coins rest s = e1 a coins rest s.
proof. move=> ll; rewrite /d1 /e1 /prf_test /starin.
  rewrite middle_distribution /= dlet_dlet; apply eq_dlet => // t.
  rewrite dlet_dmap /=.
  have h : forall w v, prf_view (public_view a s) s.`ct s.`dec1 s.`dhfun s.`pk2
     (patch_at (inp s.`dhfun s.`pk2 s.`ct.`2) w t) (Some v) =
       prf_view (public_view a s) s.`ct s.`dec1 s.`dhfun s.`pk2 t (Some v)
       by move=> w v; rewrite /prf_view /= dec_cannot_read_star.
  have -> : (fun w => dlet coins (fun v =>
     prf_view (public_view a s) s.`ct s.`dec1 s.`dhfun s.`pk2
       (patch_at (inp s.`dhfun s.`pk2 s.`ct.`2) w t) (Some v))) =
     (fun (_ : b32) => dlet coins (fun v => prf_view (public_view a s) s.`ct
         s.`dec1 s.`dhfun s.`pk2 t (Some v))) by apply fun_ext => w; apply eq_dlet => // v; exact (h w v).
  by rewrite dlet_cst.
qed.

lemma chain6 (x0 x1 x2 x3 x4 x5 x6 d : real) :
  x0-x1 <= d => x1-x0 <= d => x5-x6 <= d => x6-x5 <= d =>
  `|x0-x6| <= `|x1-x2| + `|x2-x3| + `|x3-x4| + `|x4-x5| + 2%r*d.
proof.
  have a : `|x1-x2| <= `|x1-x2| by trivial.
  have b : `|x2-x3| <= `|x2-x3| by trivial.
  have c : `|x3-x4| <= `|x3-x4| by trivial.
  have e : `|x4-x5| <= `|x4-x5| by trivial.
  move: a b c e; rewrite !RealOrder.ler_norml; smt().
qed.

lemma four_embeddings (a : strategy) d coins rest : is_lossless coins =>
 `|accept d (g0 a) - accept d (g4 a coins)| <=
 `|accept d (b0 a) - accept d (b1 a coins)| +
 `|accept d (d0 a coins) - accept d (d1 a coins rest)| +
 `|accept d (e1 a coins rest) - accept d (e0 a coins)| +
 `|accept d (c1 a coins) - accept d (c0 a coins)| + 2%r * mu d failed.
proof. move=> ll.
  have left : forall s, !failed s => g0 a s = b0 a s
    by move=> s; rewrite /failed /g0 /b0 /native_end /kem_test => h; apply outer_endpoints; smt().
  have right : forall s, !failed s => g4 a coins s = c0 a coins s
    by move=> s; rewrite /failed => h; rewrite /g4 /c0; apply eq_dlet => // v;
       rewrite /native_end /kem_test; apply outer_endpoints; smt().
  have h1 : b1 a coins = d0 a coins by apply fun_ext => s; rewrite /b1 /d0;
    apply eq_dlet => // k; exact (g1_matches_prf_real (public_view a s) s.`ct s.`dec1 s.`dhfun s.`pk2 k).
  have h2 : d1 a coins rest = e1 a coins rest by apply fun_ext => s; apply middle_same.
  have h3 : e0 a coins = c1 a coins by apply fun_ext => s; rewrite /e0 /c1;
    apply eq_dlet => // k; apply eq_dlet => // v; exact (g3_matches_prf_real (public_view a s) s.`ct s.`dec1 s.`dhfun s.`pk2 k v).
  have l := conditional_charge_one d failed _ _ left.
  have r := conditional_charge_one d failed _ _ right.
  have l' := conditional_charge_one d failed (b0 a) (g0 a) _; first by smt().
  have r' := conditional_charge_one d failed (c0 a coins) (g4 a coins) _; first by smt().
  rewrite -h1 -h2 h3 /accept; apply chain6.
  + by apply RealOrder.ler_subl_addl; exact l.
  + by apply RealOrder.ler_subl_addl; exact l'.
  + by apply RealOrder.ler_subl_addl; exact r'.
  + by apply RealOrder.ler_subl_addl; exact r.
qed.
