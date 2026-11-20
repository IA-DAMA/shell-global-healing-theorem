require import AllCore List Distr DInterval DList.

(* Uniform tape after a successful computational replacement of one bounded
   stream. Keep BOTH sides of the target slice in the same continuation.
   Cursor positions count consumed bytes, including any discarded tail. *)
op octet = dinter 0 255.
op tape (count : int) = dlist octet count.
op append_pair (p : int list * int list) = p.`1 ++ p.`2.

lemma independent_48_byte_slice before after : 0 <= before => 0 <= after =>
  tape (before + (48 + after)) =
    dmap (tape before `*` (dmap (tape 48 `*` tape after) append_pair)) append_pair.
proof.
  move=> hb ha; rewrite /tape /append_pair.
  rewrite (dlist_add octet before (48+after)) 1,2:/#.
  by rewrite (dlist_add octet 48 after).
qed.

(* Keep the actual entropy source separate from deterministic expansion.
   The primitive game takes a uniform SEED, then tests the full bounded
   stream against independent octets. The consumer runs a single adaptive
   continuation, optionally including subsequent public outputs. *)
op expand_stream : int -> int -> int list.
module type StreamUse = { proc consume(t : int list) : bool }.
module SeedUse(C:StreamUse) = {
  proc consume(s : int, cap : int) : bool = {
    var b; b <@ C.consume(expand_stream s cap); return b;
  }
}.
module type SeedSource = { proc next() : int }.
module ProviderUse(S:SeedSource,C:StreamUse) = {
  proc main(cap : int) : bool = {
    var seed,b; seed <@ S.next(); b <@ C.consume(expand_stream seed cap); return b;
  }
}.
module EntropyGame(S:SeedSource,C:StreamUse) = {
  proc main(cap : int) : bool = {
    var seed,b; seed <@ S.next(); b <@ SeedUse(C).consume(seed,cap); return b;
  }
}.
module UniformSeed = { proc next() : int = {
   var seed; seed <$ dinter 0 (2^256-1); return seed;
} }.
module StreamGame(C:StreamUse) = {
  proc main(is_real : bool, cap : int) : bool = {
    var seed,bytes,b;
    if (is_real) {
      seed <$ dinter 0 (2^256-1); bytes <- expand_stream seed cap;
    } else { bytes <$ tape cap; }
    b <@ C.consume(bytes); return b;
  }
}.

lemma entropy_endpoint_exact (S <: SeedSource) (C <: StreamUse{-S}) cap &m :
  Pr[ProviderUse(S,C).main(cap) @ &m : res] =
  Pr[EntropyGame(S,C).main(cap) @ &m : res].
proof. byequiv (_ : ={arg, glob S, glob C} ==> ={res}) => //.
  proc; inline SeedUse(C).consume; sim.
qed.

lemma seeded_endpoint_exact (C <: StreamUse) cap &m :
  Pr[ProviderUse(UniformSeed,C).main(cap) @ &m : res] =
  Pr[StreamGame(C).main(true,cap) @ &m : res].
proof.
  byequiv (_ : ={cap,glob C} /\ is_real{2} ==> ={res}) => //.
  proc; inline UniformSeed.next; rcondt{2} 1; first by auto.
  call (_ : ={arg,glob C} ==> ={res}); first by sim.
  wp; rnd; auto; smt().
qed.
