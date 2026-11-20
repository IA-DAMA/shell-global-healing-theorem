require import AllCore.
(* F4-F draft-06 concrete-keygen gap, not the PCS theorem.

   The peer-reviewed X-Wing construction (Barbosa et al., 2024, Fig. 1)
   models a longer component-based secret key. X-Wing draft-06 (IETF
   2024-08-19, section 5.2) uses a 32-byte random seed and
   SHAKE256(seed,96) to derive the ML-KEM-768 keygen coins and the
   X25519 private input. Those distributions are NOT IDENTICAL by
   syntax. Their interchange needs a SHAKE expansion PRG game hop.

   This file gives an exact, zero-loss reduction of ANY public-key
   continuation to that expansion game, without assuming MLS PCS.
   'f4_expand_public' is still abstract: this is NOT a source-level
   correspondence with hpke-rs, nor a security proof for SHAKE.
*)

type f4_expanded96.
type f4_xwing_public1216.

op f4_expand_public : f4_expanded96 -> f4_xwing_public1216.

module type F4_SHAKE256_Expansion_Game = {
  proc real() : f4_expanded96
  proc ideal() : f4_expanded96
}.

module type F4_XWing_Public_Distinguisher = {
  proc decide(pk : f4_xwing_public1216) : bool
}.

module F4_SHAKE_Expansion_Real
    (E:F4_SHAKE256_Expansion_Game,
     D:F4_XWing_Public_Distinguisher) = {
  proc main() : bool = {
    var expanded, pk, b;
    expanded <@ E.real();
    pk <- f4_expand_public expanded;
    b <@ D.decide(pk);
    return b;
  }
}.

module F4_SHAKE_Expansion_Ideal
    (E:F4_SHAKE256_Expansion_Game,
     D:F4_XWing_Public_Distinguisher) = {
  proc main() : bool = {
    var expanded, pk, b;
    expanded <@ E.ideal();
    pk <- f4_expand_public expanded;
    b <@ D.decide(pk);
    return b;
  }
}.

module F4_SHAKE_PRG_Reduction(D:F4_XWing_Public_Distinguisher) = {
  proc distinguish(expanded : f4_expanded96) : bool = {
    var pk, b;
    pk <- f4_expand_public expanded;
    b <@ D.decide(pk);
    return b;
  }
}.

module F4_SHAKE_PRG_Real
    (E:F4_SHAKE256_Expansion_Game,
     D:F4_XWing_Public_Distinguisher) = {
  proc main() : bool = {
    var expanded, b;
    expanded <@ E.real();
    b <@ F4_SHAKE_PRG_Reduction(D).distinguish(expanded);
    return b;
  }
}.

module F4_SHAKE_PRG_Ideal
    (E:F4_SHAKE256_Expansion_Game,
     D:F4_XWing_Public_Distinguisher) = {
  proc main() : bool = {
    var expanded, b;
    expanded <@ E.ideal();
    b <@ F4_SHAKE_PRG_Reduction(D).distinguish(expanded);
    return b;
  }
}.

lemma f4_draft06_seed_prg_real_exact
    (E <: F4_SHAKE256_Expansion_Game)
    (D <: F4_XWing_Public_Distinguisher{-E}) :
  equiv [F4_SHAKE_Expansion_Real(E,D).main ~
         F4_SHAKE_PRG_Real(E,D).main :
         ={glob E,glob D} ==> ={res}].
proof.
  proc.
  inline F4_SHAKE_PRG_Reduction(D).distinguish.
  sim.
qed.

lemma f4_draft06_seed_prg_ideal_exact
    (E <: F4_SHAKE256_Expansion_Game)
    (D <: F4_XWing_Public_Distinguisher{-E}) :
  equiv [F4_SHAKE_Expansion_Ideal(E,D).main ~
         F4_SHAKE_PRG_Ideal(E,D).main :
         ={glob E,glob D} ==> ={res}].
proof.
  proc.
  inline F4_SHAKE_PRG_Reduction(D).distinguish.
  sim.
qed.

lemma f4_draft06_seed_prg_real_pr
    (E <: F4_SHAKE256_Expansion_Game)
    (D <: F4_XWing_Public_Distinguisher{-E}) &m :
  Pr[F4_SHAKE_Expansion_Real(E,D).main() @ &m : res] =
  Pr[F4_SHAKE_PRG_Real(E,D).main() @ &m : res].
proof.
  by byequiv (f4_draft06_seed_prg_real_exact E D).
qed.

lemma f4_draft06_seed_prg_ideal_pr
    (E <: F4_SHAKE256_Expansion_Game)
    (D <: F4_XWing_Public_Distinguisher{-E}) &m :
  Pr[F4_SHAKE_Expansion_Ideal(E,D).main() @ &m : res] =
  Pr[F4_SHAKE_PRG_Ideal(E,D).main() @ &m : res].
proof.
  by byequiv (f4_draft06_seed_prg_ideal_exact E D).
qed.

lemma f4_draft06_seed_prg_advantage_zero_loss
    (E <: F4_SHAKE256_Expansion_Game)
    (D <: F4_XWing_Public_Distinguisher{-E}) &m :
  Pr[F4_SHAKE_Expansion_Real(E,D).main() @ &m : res] -
  Pr[F4_SHAKE_Expansion_Ideal(E,D).main() @ &m : res] =
  Pr[F4_SHAKE_PRG_Real(E,D).main() @ &m : res] -
  Pr[F4_SHAKE_PRG_Ideal(E,D).main() @ &m : res].
proof.
  rewrite (f4_draft06_seed_prg_real_pr E D &m)
          (f4_draft06_seed_prg_ideal_pr E D &m).
  by [].
qed.
