require import AllCore Real StdOrder.
require import F4_XWing_Quantum_Primitive_Hops.
import RealOrder.

(* Conditional additive budget for the intended restricted PCS theorem.
   Read g0..g4 as: Product real, FreshQ/event-projected, draft-06 seed ideal,
   multi-use X-Wing hybrid, and ideal exporter/key schedule. This proves only
   arithmetic composition. Every adjacent game bound—especially native
   FreshQ/refinement, SHAKE256, multi-use X-Wing, and HKDF—remains a premise. *)

op f4_concrete_pcs_budget
    (p_bad_freshq p_bad_external p_bad_trace eps_sig eps_shake
     n_path eps_ml_b eps_ml_c eps_h06_d eps_h06_e delta_ml eps_hkdf : real)
    : real =
  p_bad_freshq + p_bad_external + p_bad_trace + eps_sig + eps_shake +
  n_path * f4_xwing_primitive_bound
              eps_ml_b eps_ml_c eps_h06_d eps_h06_e delta_ml + eps_hkdf.

lemma f4_concrete_pcs_budget_composes
    (g0 g1 g2 g3 g4 : real)
    (p_bad_freshq p_bad_external p_bad_trace eps_sig eps_shake
     n_path eps_ml_b eps_ml_c eps_h06_d eps_h06_e delta_ml eps_hkdf : real) :
  `|g0 - g1| <= p_bad_freshq + p_bad_external + p_bad_trace + eps_sig =>
  `|g1 - g2| <= eps_shake =>
  `|g2 - g3| <= n_path * f4_xwing_primitive_bound
                 eps_ml_b eps_ml_c eps_h06_d eps_h06_e delta_ml =>
  `|g3 - g4| <= eps_hkdf =>
  `|g0 - g4| <= f4_concrete_pcs_budget
                 p_bad_freshq p_bad_external p_bad_trace eps_sig eps_shake
                 n_path eps_ml_b eps_ml_c eps_h06_d eps_h06_e delta_ml eps_hkdf.
proof.
  move=> h01 h12 h23 h34.
  have h02 :
    `|g0 - g2| <=
      p_bad_freshq + p_bad_external + p_bad_trace + eps_sig + eps_shake.
  + apply (ler_trans (`|g0 - g1| + `|g1 - g2|)).
    - exact (StdOrder.RealOrder.ler_dist_add g1 g0 g2).
    - exact (ler_add _ _ _ _ h01 h12).
  have h03 :
    `|g0 - g3| <=
      p_bad_freshq + p_bad_external + p_bad_trace + eps_sig + eps_shake +
      n_path * f4_xwing_primitive_bound
        eps_ml_b eps_ml_c eps_h06_d eps_h06_e delta_ml.
  + apply (ler_trans (`|g0 - g2| + `|g2 - g3|)).
    - exact (StdOrder.RealOrder.ler_dist_add g2 g0 g3).
    - exact (ler_add _ _ _ _ h02 h23).
  rewrite /f4_concrete_pcs_budget.
  apply (ler_trans (`|g0 - g3| + `|g3 - g4|)).
  + exact (StdOrder.RealOrder.ler_dist_add g3 g0 g4).
  + have hsum := ler_add _ _ _ _ h03 h34.
    by smt().
qed.
