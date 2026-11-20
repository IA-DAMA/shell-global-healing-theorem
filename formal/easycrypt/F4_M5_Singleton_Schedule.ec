require import AllCore List Distr StdOrder FMap.
require import F4_M5_Epoch_Exporter_Hops F4_Provider_Stream_Cut.

(* join_input and epoch_input are the serialized HKDF labels with counter 01.
   They may contain a long serialized GroupContext. No one-byte length
   approximation is used for that context. The roles of salt and IKM in
   the first Extract are deliberately reversed relative to an ordinary PRF. *)
type params = { old_init : bytes; join_input : bytes; psk : bytes; epoch_input : bytes }.
op welcome_slot = short_input 48 [119;101;108;99;111;109;101] [].

module type End = { proc run(welcome epoch:bytes) : bool }.
module type Outputs = { proc eval(x:bytes) : bytes }.
module RightKey = {
  var ikm : bytes
  proc init() = { ikm <$ tape 48; }
  proc eval(salt : bytes) = { return mac384 salt ikm; }
}.

module Schedule(D:End) = {
  proc real(p:params) = {
    var c, extracted, joiner, mid, w, e, b;
    c <$ tape 48;
    extracted <- mac384 p.`old_init c;
    joiner <- mac384 extracted p.`join_input;
    mid <- mac384 joiner p.`psk;
    w <- mac384 mid welcome_slot;
    e <- mac384 mid p.`epoch_input;
    b <@ D.run(w,e);
    return b;
  }
  proc independent() = {
    var e,w,b; w <$ tape 48; e <$ tape 48; b <@ D.run(w,e); return b;
  }
}.

(* These distinguishers receive a primitive oracle; no intermediate hidden
   real key is passed to them. The right-keyed test queries the old salt. *)
module ExtractTest(D:End,O:Outputs) = {
  proc run(p:params) = {
    var t,j,m,b; t <@ O.eval(p.`old_init);
    j <- mac384 t p.`join_input; m <- mac384 j p.`psk;
    b <@ D.run(mac384 m welcome_slot,mac384 m p.`epoch_input); return b;
  }
}.
module JoinTest(D:End,O:Outputs) = {
  proc run(p:params) = {
    var j,m,b; j <@ O.eval(p.`join_input); m <- mac384 j p.`psk;
    b <@ D.run(mac384 m welcome_slot,mac384 m p.`epoch_input); return b;
  }
}.
module PSKTest(D:End,O:Outputs) = {
  proc run(p:params) = {
    var m,b; m <@ O.eval(p.`psk);
    b <@ D.run(mac384 m welcome_slot,mac384 m p.`epoch_input); return b;
  }
}.
module EpochTest(D:End,O:Outputs) = {
  proc run(p:params) = {
    var w,e,b; w <@ O.eval(welcome_slot); e <@ O.eval(p.`epoch_input);
    b <@ D.run(w,e); return b;
  }
}.
module type TestP(O:Outputs) = { proc run(p:params):bool }.
module type InitO = { proc init():unit proc eval(x:bytes):bytes }.
module RunP(O:InitO,T:TestP) = {
  proc main(p:params) = { var b; O.init(); b <@ T(O).run(p); return b; }
}.
module IndependentDraw = {
  proc init() = { }
  proc eval = Draw.eval
}.
module Lazy = { proc init = Others.init proc eval = Others.eval }.

section Chain.
declare module D <: End{-RightKey,-Keyed,-Others}.
local lemma begin_exact p &m :
  Pr[Schedule(D).real(p) @ &m : res] = Pr[RunP(RightKey,ExtractTest(D)).main(p) @ &m : res].
proof.
  byequiv (_: ={arg,glob D} ==> ={res}) => //. proc; inline *; wp.
  call (_: ={arg,glob D} ==> ={res}); first by sim.
  by wp; rnd; auto.
qed.
local lemma join_exact p &m :
  Pr[RunP(IndependentDraw,ExtractTest(D)).main(p) @ &m : res] =
  Pr[RunP(Keyed,JoinTest(D)).main(p) @ &m : res].
proof.
  byequiv (_: ={arg,glob D} ==> ={res}) => //. proc; inline *; wp.
  call (_: ={arg,glob D} ==> ={res}); first by sim.
  by wp; rnd; auto.
qed.
local lemma psk_exact p &m :
  Pr[RunP(IndependentDraw,JoinTest(D)).main(p) @ &m : res] =
  Pr[RunP(Keyed,PSKTest(D)).main(p) @ &m : res].
proof.
  byequiv (_: ={arg,glob D} ==> ={res}) => //. proc; inline *; wp.
  call (_: ={arg,glob D} ==> ={res}); first by sim.
  by wp; rnd; auto.
qed.
local lemma epoch_exact p &m :
  Pr[RunP(IndependentDraw,PSKTest(D)).main(p) @ &m : res] =
  Pr[RunP(Keyed,EpochTest(D)).main(p) @ &m : res].
proof.
  byequiv (_: ={arg,glob D} ==> ={res}) => //. proc; inline *; wp.
  call (_: ={arg,glob D} ==> ={res}); first by sim.
  by wp; rnd; auto.
qed.
local lemma split_exact p &m : p.`epoch_input <> welcome_slot =>
  Pr[RunP(Lazy,EpochTest(D)).main(p) @ &m : res] =
  Pr[Schedule(D).independent() @ &m : res].
proof.
  move=> diff; byequiv (_: arg{1}=p /\ ={glob D} ==> ={res}) => //.
  proc; inline Others.init Others.eval EpochTest(D,Lazy).run.
  wp; call (_: ={arg,glob D} ==> ={res}); first by sim.
  wp; rcondt{1} 4; first by move=> &hr; auto; smt(mem_empty).
  rcondt{1} 8; first by move=> &hr; auto; smt(get_setE mem_set mem_empty).
  wp; rnd; wp; rnd; auto; smt(get_setE mem_set mem_empty).
qed.
lemma schedule_bound p &m : p.`epoch_input <> welcome_slot =>
  `|Pr[Schedule(D).real(p) @ &m : res] - Pr[Schedule(D).independent() @ &m : res]| <=
  `|Pr[RunP(RightKey,ExtractTest(D)).main(p) @ &m : res] -
    Pr[RunP(IndependentDraw,ExtractTest(D)).main(p) @ &m : res]| +
  `|Pr[RunP(Keyed,JoinTest(D)).main(p) @ &m : res] -
    Pr[RunP(IndependentDraw,JoinTest(D)).main(p) @ &m : res]| +
  `|Pr[RunP(Keyed,PSKTest(D)).main(p) @ &m : res] -
    Pr[RunP(IndependentDraw,PSKTest(D)).main(p) @ &m : res]| +
  `|Pr[RunP(Keyed,EpochTest(D)).main(p) @ &m : res] -
    Pr[RunP(Lazy,EpochTest(D)).main(p) @ &m : res]|.
proof.
  move=> sep. rewrite (begin_exact p &m) (join_exact p &m) (psk_exact p &m)
    (epoch_exact p &m) (split_exact p &m sep).
  smt(RealOrder.ler_dist_add).
qed.
end section Chain.

module type WithWelcome(S:Sibling) = {
  proc choose(w:bytes):bytes
  proc finish(y:bytes):bool
}.
module FreshWelcome(A:WithWelcome,S:Sibling) = {
  proc choose() = { var w,c; w <$ tape 48; c <@ A(S).choose(w); return c; }
  proc finish = A(S).finish
}.
module Installed = {
  var key : bytes
  proc eval(x:bytes) = { return mac384 key x; }
}.
module Finish(A:WithWelcome) = {
  proc common(w e:bytes, independent:bool) = {
    var ctx,wide,y,b;
    Installed.key <- e;
    ctx <@ A(Hide(Installed)).choose(w);
    if (independent) { wide <$ tape 48; y <- take 32 wide; }
    else { y <- from_master (mac384 e epoch_slot) ctx; }
    b <@ A(Hide(Installed)).finish(y); return b;
  }
  proc real(w e:bytes) = { var b; b <@ common(w,e,false); return b; }
  proc ideal(w e:bytes) = { var b; b <@ common(w,e,true); return b; }
}.
module RealEnd(A:WithWelcome) = { proc run = Finish(A).real }.
module IdealEnd(A:WithWelcome) = { proc run = Finish(A).ideal }.

section Whole.
declare module A <: WithWelcome{-Installed,-Keyed,-RightKey,-Others,-SplitRF}.
local lemma obs :
  equiv [Hide(Installed).query ~ Hide(Keyed).query :
    ={arg} /\ Installed.key{1}=Keyed.key{2} ==> ={res} /\ Installed.key{1}=Keyed.key{2}].
proof. proc; inline *; auto. qed.
local lemma choose_eq :
  equiv [A(Hide(Installed)).choose ~ A(Hide(Keyed)).choose :
    ={arg,glob A} /\ Installed.key{1}=Keyed.key{2} ==>
    ={res,glob A} /\ Installed.key{1}=Keyed.key{2}].
proof. proc (Installed.key{1}=Keyed.key{2}) => //; conseq obs; smt(). qed.
local lemma finish_eq :
  equiv [A(Hide(Installed)).finish ~ A(Hide(Keyed)).finish :
    ={arg,glob A} /\ Installed.key{1}=Keyed.key{2} ==> ={res}].
proof. proc (Installed.key{1}=Keyed.key{2}) => //; conseq obs; smt(). qed.

local lemma pair_real &m :
  Pr[Schedule(RealEnd(A)).independent() @ &m : res] =
  Pr[Game(Keyed,Root(FreshWelcome(A))).main(false) @ &m : res].
proof.
  byequiv (_: ={glob A} /\ !independent{2} ==> ={res}) => //.
  proc; inline *; wp; call finish_eq; wp.
  rcondf{1} 10; first by move=> &hr; wp; call (_:true); auto.
  rcondf{2} 8; first by move=> &hr; wp; call (_:true); auto.
  wp; call choose_eq; wp; swap{1} 1 1; rnd; wp; rnd; auto.
qed.
local lemma pair_ideal &m :
  Pr[Schedule(IdealEnd(A)).independent() @ &m : res] =
  Pr[Game(Keyed,Root(FreshWelcome(A))).main(true) @ &m : res].
proof.
  byequiv (_: ={glob A} /\ independent{2} ==> ={res}) => //.
  proc; inline *; wp; call finish_eq; wp.
  rcondt{1} 10; first by move=> &hr; wp; call (_:true); auto.
  rcondt{2} 8; first by move=> &hr; wp; call (_:true); auto.
  wp; rnd; wp; call choose_eq; wp; swap{1} 1 1; rnd; wp; rnd; auto.
qed.
lemma fresh_commit_to_export p &m : p.`epoch_input <> welcome_slot =>
  `|Pr[Schedule(RealEnd(A)).real(p) @ &m : res] -
    Pr[Schedule(IdealEnd(A)).real(p) @ &m : res]| <=
  (`|Pr[RunP(RightKey,ExtractTest(RealEnd(A))).main(p) @ &m : res] -
    Pr[RunP(IndependentDraw,ExtractTest(RealEnd(A))).main(p) @ &m : res]| +
  `|Pr[RunP(Keyed,JoinTest(RealEnd(A))).main(p) @ &m : res] -
    Pr[RunP(IndependentDraw,JoinTest(RealEnd(A))).main(p) @ &m : res]| +
  `|Pr[RunP(Keyed,PSKTest(RealEnd(A))).main(p) @ &m : res] -
    Pr[RunP(IndependentDraw,PSKTest(RealEnd(A))).main(p) @ &m : res]| +
  `|Pr[RunP(Keyed,EpochTest(RealEnd(A))).main(p) @ &m : res] -
    Pr[RunP(Lazy,EpochTest(RealEnd(A))).main(p) @ &m : res]|) +
  (`|Pr[Game(Keyed,Root(FreshWelcome(A))).main(false) @ &m : res] -
    Pr[Game(SplitRF,Root(FreshWelcome(A))).main(false) @ &m : res]| +
  `|Pr[One(FreshWelcome(A)).real(false) @ &m : res] - Pr[One(FreshWelcome(A)).random(false) @ &m : res]| +
  `|Pr[One(FreshWelcome(A)).real(true) @ &m : res] - Pr[One(FreshWelcome(A)).random(true) @ &m : res]| +
  `|Pr[Game(SplitRF,Root(FreshWelcome(A))).main(true) @ &m : res] -
    Pr[Game(Keyed,Root(FreshWelcome(A))).main(true) @ &m : res]|) +
  (`|Pr[RunP(RightKey,ExtractTest(IdealEnd(A))).main(p) @ &m : res] -
    Pr[RunP(IndependentDraw,ExtractTest(IdealEnd(A))).main(p) @ &m : res]| +
  `|Pr[RunP(Keyed,JoinTest(IdealEnd(A))).main(p) @ &m : res] -
    Pr[RunP(IndependentDraw,JoinTest(IdealEnd(A))).main(p) @ &m : res]| +
  `|Pr[RunP(Keyed,PSKTest(IdealEnd(A))).main(p) @ &m : res] -
    Pr[RunP(IndependentDraw,PSKTest(IdealEnd(A))).main(p) @ &m : res]| +
  `|Pr[RunP(Keyed,EpochTest(IdealEnd(A))).main(p) @ &m : res] -
    Pr[RunP(Lazy,EpochTest(IdealEnd(A))).main(p) @ &m : res]|).
proof.
  move=> distinct.
  have left := schedule_bound (RealEnd(A)) p &m distinct.
  have right := schedule_bound (IdealEnd(A)) p &m distinct.
  have middle := fixed_exporter_bound (FreshWelcome(A)) &m.
  rewrite (pair_real &m) in left; rewrite (pair_ideal &m) in right.
  have tri : forall (a b c d l m r : real), `|a-b| <= l => `|b-c| <= m =>
     `|d-c| <= r => `|a-d| <= l+m+r by move=> a b c d l m r; rewrite !RealOrder.ler_norml; smt().
  exact (tri _ _ _ _ _ _ _ left middle right).
qed.
end section Whole.
