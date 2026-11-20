require import AllCore List Distr DList DInterval FMap StdOrder.
require import F4_Provider_Stream_Cut.

(* Successful fixed-suite, fixed-label calls. A SHA-384 output is 48 bytes.
   Each HKDF-Expand uses exactly its first HMAC block (counter octet 01).
   All length prefixes in these particular TLS VLBytes fit in one octet. *)
type bytes = int list.
op mac384 : bytes -> bytes -> bytes.
op hash384 : bytes -> bytes.
op prefix = [77;76;83;32;49;46;48;32].
op short_input (n : int) (label ctx : bytes) =
  [0;n;size (prefix ++ label)] ++ prefix ++ label ++ [size ctx] ++ ctx ++ [1].
op epoch_slot = short_input 48 [101;120;112;111;114;116;101;114] [].
op label_slot = short_input 48 [108;105;110;107;97;46;115;104;101;108;108;46;102;52;46;112;114;111;100;117;99;116;46;97;99;99;101;112;116;101;100;47;49] [].
op final_slot ctx = short_input 32 [101;120;112;111;114;116;101;100] (hash384 ctx).
op from_label k ctx = take 32 (mac384 k (final_slot ctx)).
op from_master k ctx = from_label (mac384 k label_slot) ctx.

module type Eval = { proc eval(x:bytes) : bytes }.
module type Sibling = { proc query(x:bytes) : bytes option }.
module type Continuation(S:Sibling) = {
  proc choose() : bytes
  proc finish(value:bytes) : bool
}.

module Keyed = {
  var key : bytes
  proc init() = { key <$ tape 48; }
  proc eval(x:bytes) = { return mac384 key x; }
}.

module Others = {
  var mem : (bytes,bytes) fmap
  proc init() = { mem <- empty; }
  proc eval(x:bytes) = {
    var v;
    if (x \notin mem) { v <$ tape 48; mem.[x] <- v; }
    return oget mem.[x];
  }
}.

(* A random function with a distinguished, pre-sampled coordinate. Other
   coordinates are sampled lazily. Both init and queries take polynomial
   work in the number and size of classical queries, excluding mac cost. *)
module SplitRF = {
  var star : bytes
  proc init() = { Others.init(); star <$ tape 48; }
  proc eval(x:bytes) = {
    var v;
    v <- star;
    if (x <> epoch_slot) { v <@ Others.eval(x); }
    return v;
  }
}.
module Hide(O:Eval) = {
  proc query(x:bytes) = {
    var v, r;
    r <- None;
    if (x <> epoch_slot) { v <@ O.eval(x); r <- Some v; }
    return r;
  }
}.
module Draw = { proc eval(x:bytes) = { var z; z <$ tape 48; return z; } }.
module type Test(O:Eval) = { proc run(independent:bool) : bool }.
module type Family = { proc init():unit proc eval(x:bytes):bytes }.
module Game(F:Family,T:Test) = {
  proc main(independent:bool) = {
    var b; F.init(); b <@ T(F).run(independent); return b;
  }
}.

(* The root distinguisher can pass every sibling block, including repeated
   queries, to the same continuation before AND after the selected output. *)
module Root(A:Continuation,O:Eval) = {
  proc run(independent:bool) = {
    var ctx, master, z, wide, b;
    ctx <@ A(Hide(O)).choose();
    master <@ O.eval(epoch_slot);
    if (independent) { wide <$ tape 48; z <- take 32 wide; } else { z <- from_master master ctx; }
    b <@ A(Hide(O)).finish(z); return b;
  }
}.

(* Only a SINGLE query is made to the embedded inner primitive. Drawing
   independent coins per call therefore implements its random-function case.
   A obtains a different, consistent oracle for all allowed siblings. *)
module Inner(A:Continuation,O:Eval) = {
  proc run(last:bool) = {
    var ctx, k, z, b;
    Others.init();
    ctx <@ A(Hide(Others)).choose();
    if (last) { z <@ O.eval(final_slot ctx); z <- take 32 z; }
    else { k <@ O.eval(label_slot); z <- from_label k ctx; }
    b <@ A(Hide(Others)).finish(z); return b;
  }
}.
module One(A:Continuation) = {
  proc real(last:bool) = {
    var b; Keyed.init(); b <@ Inner(A,Keyed).run(last); return b;
  }
  proc random(last:bool) = {
    var b; b <@ Inner(A,Draw).run(last); return b;
  }
}.
lemma same_siblings :
  equiv [Hide(SplitRF).query ~ Hide(Others).query :
    ={arg,glob Others} ==> ={res,glob Others}].
proof.
  proc; inline SplitRF.eval; sp; if => //.
  + sp; rcondt{1} 1; first by auto.
    wp; call (_: ={arg,glob Others} ==> ={res,glob Others}); first by sim.
    by auto.
qed.

section Hops.
declare module A <: Continuation{-Others,-SplitRF,-Keyed}.
local lemma choose_same :
  equiv [A(Hide(SplitRF)).choose ~ A(Hide(Others)).choose :
    ={glob A,glob Others} ==> ={res,glob A,glob Others}].
proof. proc (={glob Others}) => //; conseq same_siblings; smt(). qed.
local lemma finish_same :
  equiv [A(Hide(SplitRF)).finish ~ A(Hide(Others)).finish :
    ={arg,glob A,glob Others} ==> ={res}].
proof. proc (={glob Others}) => //; conseq same_siblings; smt(). qed.

lemma master_handoff &m :
  Pr[Game(SplitRF,Root(A)).main(false) @ &m : res] =
  Pr[One(A).real(false) @ &m : res].
proof.
  byequiv (_: ={glob A} /\ !independent{1} /\ !last{2} ==> ={res}) => //.
  proc; inline SplitRF.init Root(A,SplitRF).run Keyed.init Inner(A,Keyed).run.
  inline Others.init SplitRF.eval Keyed.eval.
  wp.
  call finish_same.
  wp.
  rcondf{1} 7; first by move=> &m0; wp; call (_:true); auto.
  rcondf{1} 8; first by move=> &m0; wp; call (_:true); auto.
  wp; call choose_same; wp; rnd; auto; smt().
qed.

lemma label_handoff &m :
  Pr[One(A).random(false) @ &m : res] = Pr[One(A).real(true) @ &m : res].
proof.
  byequiv (_: ={glob A} /\ !last{1} /\ last{2} ==> ={res}) => //.
  proc; inline Inner(A,Draw).run Inner(A,Keyed).run Draw.eval Keyed.init Keyed.eval Others.init.
  wp; call (_: ={arg,glob A,glob Others} ==> ={res}); first by sim.
  rcondf{1} 4; first by move=> &m0; wp; call (_:true); auto.
  wp. swap{2} 1 3. rnd. wp.
  call (_: ={glob A,glob Others} ==> ={glob A,glob Others,res}); first by sim.
  by auto.
qed.

lemma truncated_uniform :
  dmap (tape 48) (take 32) = tape 32.
proof.
  rewrite /tape (_: 48=32+16) // (dlist_add octet 32 16) // dmap_comp.
  have h : dmap (dlist octet 32 `*` dlist octet 16) (fun p : bytes * bytes => take 32 (p.`1 ++ p.`2)) =
    dmap (dlist octet 32 `*` dlist octet 16) (fun p : bytes * bytes => p.`1).
  + apply eq_dmap_in => -[x y] /supp_dprod [hx _] /=.
    apply take_size_cat; smt(supp_dlist_size).
  have ll : is_lossless (dlist octet 16) by apply dlist_ll; rewrite /octet; apply dinter_ll.
  rewrite h (dprod_marginalL _ _ (fun x : bytes => x)) dmap_id ll /=.
  by rewrite dscalar1.
qed.
lemma ideal_handoff &m :
  Pr[Game(SplitRF,Root(A)).main(true) @ &m : res] =
  Pr[One(A).random(true) @ &m : res].
proof.
  byequiv (_: ={glob A} /\ independent{1} /\ last{2} ==> ={res}) => //.
  proc; inline SplitRF.init Root(A,SplitRF).run Inner(A,Draw).run Draw.eval Others.init SplitRF.eval.
  wp; call finish_same.
  rcondf{1} 7; first by move=> &m0; wp; call (_:true); auto.
  rcondt{1} 8; first by move=> &m0; wp; call (_:true); auto.
  rcondt{2} 4; first by move=> &m0; wp; call (_:true); auto.
  wp; rnd; wp; call choose_same; wp; rnd{1}; auto.
  have ll : is_lossless (tape 48) by apply dlist_ll; rewrite /octet; apply dinter_ll.
  smt().
qed.

(* Two root tests are charged: the visible sibling transcript stays real at
   BOTH exterior endpoints. Inner tests query HMAC only once each. *)
lemma fixed_exporter_bound &m :
  `|Pr[Game(Keyed,Root(A)).main(false) @ &m : res] -
    Pr[Game(Keyed,Root(A)).main(true) @ &m : res]| <=
  `|Pr[Game(Keyed,Root(A)).main(false) @ &m : res] -
    Pr[Game(SplitRF,Root(A)).main(false) @ &m : res]| +
  `|Pr[One(A).real(false) @ &m : res] - Pr[One(A).random(false) @ &m : res]| +
  `|Pr[One(A).real(true) @ &m : res] - Pr[One(A).random(true) @ &m : res]| +
  `|Pr[Game(SplitRF,Root(A)).main(true) @ &m : res] -
    Pr[Game(Keyed,Root(A)).main(true) @ &m : res]|.
proof.
  rewrite (master_handoff &m) (ideal_handoff &m) (label_handoff &m).
  smt(RealOrder.ler_dist_add).
qed.
end section Hops.
