require import AllCore Real StdOrder.
import RealOrder.

(* F4-F -- quantitative composition of the FOUR explicit X-Wing/QSF
   hybrid hops from Barbosa et al., CiC 1(1), 2024, Theorem 2,
   DOI 10.62056/a3qj89n4e, PDF p.13 (Figure 8).

   G0: real QSF KEM ciphertext/shared key (adaptive CCA game).
   G1: ML-KEM challenge shared key replaced with independent uniform key.
   G2: keyed-combiner answers replaced with independent uniform values.
   G3: the keyed-combiner answers restored, preserving the hybrid key hop.
   G4: ideal independent uniform QSF challenge shared key.

   This file proves the NUMERIC FOUR-HOP reduction from concrete game
   probabilities to primitive-game hop bounds, without assuming QPCS PCS.
   The individual IND-CCA and PRF hop proofs are Theorem 2 of the paper,
   NOT re-proved here. In particular the abstract module below is NOT
   a verified encoding of OpenMLS Rust, and ETK/adaptive epoch security
   is NOT obtained by this theorem.

   Theorem 2: Adv_QSF <= Adv_MLKEM(B) + Adv_MLKEM(C) +
                         Adv_SHA3-PRF(D) + Adv_SHA3-PRF(E) + 2*kem_failure.
*)

module type F4QSF_Hybrids = {
  proc g0() : bool
  proc g1() : bool
  proc g2() : bool
  proc g3() : bool
  proc g4() : bool
}.

op f4_xwing_primitive_bound (kem_b kem_c prf_d prf_e kem_failure : real) : real =
  kem_b + kem_c + prf_d + prf_e + 2%r * kem_failure.

lemma f4_xwing_four_game_quantitative_reduction
    (G <: F4QSF_Hybrids)
    (kem_b kem_c prf_d prf_e kem_failure : real) &m :
  `| Pr[G.g0() @ &m : res] - Pr[G.g1() @ &m : res] |
      <= kem_b + kem_failure =>
  `| Pr[G.g1() @ &m : res] - Pr[G.g2() @ &m : res] |
      <= prf_d =>
  `| Pr[G.g2() @ &m : res] - Pr[G.g3() @ &m : res] |
      <= prf_e =>
  `| Pr[G.g3() @ &m : res] - Pr[G.g4() @ &m : res] |
      <= kem_c + kem_failure =>
  `| Pr[G.g0() @ &m : res] - Pr[G.g4() @ &m : res] |
      <= f4_xwing_primitive_bound kem_b kem_c prf_d prf_e kem_failure.
proof.
  move=> h01 h12 h23 h34.
  have h02 :
    `| Pr[G.g0() @ &m : res] - Pr[G.g2() @ &m : res] |
       <= kem_b + kem_failure + prf_d.
  + apply (ler_trans
      (`| Pr[G.g0() @ &m : res] - Pr[G.g1() @ &m : res] | +
       `| Pr[G.g1() @ &m : res] - Pr[G.g2() @ &m : res] |)).
    - exact (StdOrder.RealOrder.ler_dist_add
        (Pr[G.g1() @ &m : res])
        (Pr[G.g0() @ &m : res])
        (Pr[G.g2() @ &m : res])).
    - exact (ler_add _ _ _ _ h01 h12).
  have h03 :
    `| Pr[G.g0() @ &m : res] - Pr[G.g3() @ &m : res] |
       <= kem_b + kem_failure + prf_d + prf_e.
  + apply (ler_trans
      (`| Pr[G.g0() @ &m : res] - Pr[G.g2() @ &m : res] | +
       `| Pr[G.g2() @ &m : res] - Pr[G.g3() @ &m : res] |)).
    - exact (StdOrder.RealOrder.ler_dist_add
        (Pr[G.g2() @ &m : res])
        (Pr[G.g0() @ &m : res])
        (Pr[G.g3() @ &m : res])).
    - exact (ler_add _ _ _ _ h02 h23).
  rewrite /f4_xwing_primitive_bound.
  apply (ler_trans
      (`| Pr[G.g0() @ &m : res] - Pr[G.g3() @ &m : res] | +
       `| Pr[G.g3() @ &m : res] - Pr[G.g4() @ &m : res] |)).
  + exact (StdOrder.RealOrder.ler_dist_add
      (Pr[G.g3() @ &m : res])
      (Pr[G.g0() @ &m : res])
      (Pr[G.g4() @ &m : res])).
  + have hsum := ler_add _ _ _ _ h03 h34.
    by smt().
qed.
