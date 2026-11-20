require import AllCore Real StdOrder.
require import F4_L5_QPT_Blackbox_Bridge.
import RealOrder.

(* L6 composes the five independently named boundaries.  None of these
   terms is defined as the conclusion.  The Product-to-covered, refinement,
   service and environment premises are local neighboring-world bounds; the
   cryptographic middle edge is discharged by L5's black-box reductions. *)

module type L6ProductWorlds = {
  proc real(aux : l5_qaux) : bool
  proc ideal(aux : l5_qaux) : bool
}.

op l6_global_bound (eps_pq eps_ref bad_cc eps_svc eps_env : real) =
  eps_pq + eps_ref + bad_cc + eps_svc + eps_env.

lemma l6_chain_five
    (x0 x1 x2 x3 x4 x5 e01 e12 e23 e34 e45 : real) :
  `|x0-x1| <= e01 =>
  `|x1-x2| <= e12 =>
  `|x2-x3| <= e23 =>
  `|x3-x4| <= e34 =>
  `|x4-x5| <= e45 =>
  `|x0-x5| <= e01+e12+e23+e34+e45.
proof.
  move=> h01 h12 h23 h34 h45.
  have t02 := StdOrder.RealOrder.ler_dist_add x1 x0 x2.
  have h02 : `|x0-x2| <= e01+e12.
  + apply (ler_trans (`|x0-x1| + `|x1-x2|)); first exact t02.
    exact (ler_add _ _ _ _ h01 h12).
  have t03 := StdOrder.RealOrder.ler_dist_add x2 x0 x3.
  have h03 : `|x0-x3| <= e01+e12+e23.
  + apply (ler_trans (`|x0-x2| + `|x2-x3|)); first exact t03.
    exact (ler_add _ _ _ _ h02 h23).
  have t04 := StdOrder.RealOrder.ler_dist_add x3 x0 x4.
  have h04 : `|x0-x4| <= e01+e12+e23+e34.
  + apply (ler_trans (`|x0-x3| + `|x3-x4|)); first exact t04.
    exact (ler_add _ _ _ _ h03 h34).
  have t05 := StdOrder.RealOrder.ler_dist_add x4 x0 x5.
  apply (ler_trans (`|x0-x4| + `|x4-x5|)); first exact t05.
  exact (ler_add _ _ _ _ h04 h45).
qed.

lemma f4_global_conditional_qpt_bound
    (P <: L6ProductWorlds)
    (G <: L5Generator{-P}) (H <: L5Hmac{-P,-G})
    (E <: L5Exporter{-P,-G,-H})
    (A <: L5QPTAdversary{-P,-G,-H,-E})
    (aux0 : l5_qaux) covered refined serviced
    eps_gen eps_hmac eps_exporter eps_ref bad_cc eps_svc eps_env &m :
  (* CC: an observation omitted by the ledger is charged, not erased. *)
  `|Pr[P.real(aux0) @ &m : res] - covered| <= bad_cc =>
  (* L4: source/game divergence is charged by eps_ref. *)
  `|covered - refined| <= eps_ref =>
  (* The serviced real endpoint is the concrete L5 real game. *)
  serviced = Pr[L5G0(G,H,E,A).main(aux0) @ &m : res] =>
  (* Authentication/authority boundary, including active service forgery. *)
  `|refined - serviced| <= eps_svc =>
  (* Three QPT primitive games, all with the same threaded qaux. *)
  `|Pr[L5GenReal(G,H,E,A).main(aux0) @ &m : res] -
    Pr[L5GenIdeal(G,H,E,A).main(aux0) @ &m : res]| <= eps_gen =>
  `|Pr[L5HmacReal(G,H,E,A).main(aux0) @ &m : res] -
    Pr[L5HmacIdeal(G,H,E,A).main(aux0) @ &m : res]| <= eps_hmac =>
  `|Pr[L5ExporterReal(G,H,E,A).main(aux0) @ &m : res] -
    Pr[L5ExporterIdeal(G,H,E,A).main(aux0) @ &m : res]| <= eps_exporter =>
  (* Environment/idealization boundary; this is not primitive security. *)
  `|Pr[L5G3(G,H,E,A).main(aux0) @ &m : res] -
    Pr[P.ideal(aux0) @ &m : res]| <= eps_env =>
  `|Pr[P.real(aux0) @ &m : res] - Pr[P.ideal(aux0) @ &m : res]| <=
    l6_global_bound
      (l5_qpt_classical_bound eps_gen eps_hmac eps_exporter)
      eps_ref bad_cc eps_svc eps_env.
proof.
  move=> hcc href -> hsvc hgen hhmac hexporter henv.
  have hpq := l5_blackbox_nonrewinding_composition G H E A aux0
    eps_gen eps_hmac eps_exporter &m hgen hhmac hexporter.
  have h := l6_chain_five
    (Pr[P.real(aux0) @ &m : res]) covered refined
    (Pr[L5G0(G,H,E,A).main(aux0) @ &m : res])
    (Pr[L5G3(G,H,E,A).main(aux0) @ &m : res])
    (Pr[P.ideal(aux0) @ &m : res])
    bad_cc eps_ref eps_svc
    (l5_qpt_classical_bound eps_gen eps_hmac eps_exporter) eps_env
    hcc href hsvc hpq henv.
  rewrite /l6_global_bound.
  have order :
    bad_cc + eps_ref + eps_svc +
      l5_qpt_classical_bound eps_gen eps_hmac eps_exporter + eps_env =
    l5_qpt_classical_bound eps_gen eps_hmac eps_exporter + eps_ref +
      bad_cc + eps_svc + eps_env by ring.
  by rewrite -order.
qed.

(* A concrete non-vacuity witness for the arithmetic theorem.  It does not
   assert that Product has zero residual terms; it shows that the quantified
   domain contains an admitted exact execution. *)
lemma l6_exact_execution_nonvacuous (p : real) :
  `|p-p| <= l6_global_bound 0%r 0%r 0%r 0%r 0%r.
proof. by rewrite /l6_global_bound /=. qed.

(* Ed25519 is the deployed service-authentication term, not a QPT signature
   hypothesis.  Therefore an active-QPT corollary may set eps_svc negligible
   only under a named PQ-authentication assumption or an adversary restriction;
   L6 itself deliberately keeps eps_svc visible. *)
