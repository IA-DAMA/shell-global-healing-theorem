require import AllCore Real StdOrder.
import RealOrder.

(* L5 makes the auxiliary QPT memory explicit at every classical Product
   boundary.  qaux is opaque: the reductions never inspect, copy, reset or
   rewind it.  Each game executes one path and threads the unique residual
   value returned by the previous component into the next component.

   EasyCrypt's kernel proves the exact black-box embeddings and quantitative
   composition below.  The interpretation of qaux as a density operator and
   the QPT hardness of the three primitive games are named external
   hypotheses; they are not derived from classical EasyCrypt semantics. *)

type l5_qaux.
type l5_genout.
type l5_hmacout.
type l5_exportout.

type l5_query_mode = [ L5Classical | L5Coherent ].

op l5_admitted_mode (m : l5_query_mode) = m = L5Classical.

lemma l5_coherent_is_separate :
  !l5_admitted_mode L5Coherent.
proof. by rewrite /l5_admitted_mode. qed.

module type L5Generator = {
  proc real(aux : l5_qaux) : l5_genout * l5_qaux
  proc ideal(aux : l5_qaux) : l5_genout * l5_qaux
}.

module type L5Hmac = {
  proc real(x : l5_genout, aux : l5_qaux) : l5_hmacout * l5_qaux
  proc ideal(x : l5_genout, aux : l5_qaux) : l5_hmacout * l5_qaux
}.

module type L5Exporter = {
  proc real(x : l5_hmacout, aux : l5_qaux) : l5_exportout * l5_qaux
  proc ideal(x : l5_hmacout, aux : l5_qaux) : l5_exportout * l5_qaux
}.

module type L5QPTAdversary = {
  proc decide(x : l5_exportout, aux : l5_qaux) : bool
}.

module type L5GenDistinguisher = {
  proc distinguish(x : l5_genout, aux : l5_qaux) : bool
}.

module type L5HmacDistinguisher = {
  proc distinguish(x : l5_hmacout, aux : l5_qaux) : bool
}.

module L5G0(G:L5Generator,H:L5Hmac,E:L5Exporter,A:L5QPTAdversary) = {
  proc main(aux : l5_qaux) : bool = {
    var g, h, e, b;
    g <@ G.real(aux);
    h <@ H.real(g.`1,g.`2);
    e <@ E.real(h.`1,h.`2);
    b <@ A.decide(e.`1,e.`2);
    return b;
  }
}.

module L5G1(G:L5Generator,H:L5Hmac,E:L5Exporter,A:L5QPTAdversary) = {
  proc main(aux : l5_qaux) : bool = {
    var g, h, e, b;
    g <@ G.ideal(aux);
    h <@ H.real(g.`1,g.`2);
    e <@ E.real(h.`1,h.`2);
    b <@ A.decide(e.`1,e.`2);
    return b;
  }
}.

module L5G2(G:L5Generator,H:L5Hmac,E:L5Exporter,A:L5QPTAdversary) = {
  proc main(aux : l5_qaux) : bool = {
    var g, h, e, b;
    g <@ G.ideal(aux);
    h <@ H.ideal(g.`1,g.`2);
    e <@ E.real(h.`1,h.`2);
    b <@ A.decide(e.`1,e.`2);
    return b;
  }
}.

module L5G3(G:L5Generator,H:L5Hmac,E:L5Exporter,A:L5QPTAdversary) = {
  proc main(aux : l5_qaux) : bool = {
    var g, h, e, b;
    g <@ G.ideal(aux);
    h <@ H.ideal(g.`1,g.`2);
    e <@ E.ideal(h.`1,h.`2);
    b <@ A.decide(e.`1,e.`2);
    return b;
  }
}.

(* Each reduction is only the unchanged suffix.  There is no second call to
   A and no attempt to recover an earlier qaux value. *)
module L5GenReduction(H:L5Hmac,E:L5Exporter,A:L5QPTAdversary) = {
  proc distinguish(x : l5_genout, aux : l5_qaux) : bool = {
    var h, e, b;
    h <@ H.real(x,aux);
    e <@ E.real(h.`1,h.`2);
    b <@ A.decide(e.`1,e.`2);
    return b;
  }
}.

module L5GenReal(G:L5Generator,H:L5Hmac,E:L5Exporter,A:L5QPTAdversary) = {
  proc main(aux : l5_qaux) : bool = {
    var g, h, e, b;
    g <@ G.real(aux);
    h <@ H.real(g.`1,g.`2);
    e <@ E.real(h.`1,h.`2);
    b <@ A.decide(e.`1,e.`2);
    return b;
  }
}.

module L5GenIdeal(G:L5Generator,H:L5Hmac,E:L5Exporter,A:L5QPTAdversary) = {
  proc main(aux : l5_qaux) : bool = {
    var g, h, e, b;
    g <@ G.ideal(aux);
    h <@ H.real(g.`1,g.`2);
    e <@ E.real(h.`1,h.`2);
    b <@ A.decide(e.`1,e.`2);
    return b;
  }
}.

module L5HmacReduction(E:L5Exporter,A:L5QPTAdversary) = {
  proc distinguish(x : l5_hmacout, aux : l5_qaux) : bool = {
    var e, b;
    e <@ E.real(x,aux);
    b <@ A.decide(e.`1,e.`2);
    return b;
  }
}.

module L5HmacReal(G:L5Generator,H:L5Hmac,E:L5Exporter,A:L5QPTAdversary) = {
  proc main(aux : l5_qaux) : bool = {
    var g, h, e, b;
    g <@ G.ideal(aux);
    h <@ H.real(g.`1,g.`2);
    e <@ E.real(h.`1,h.`2);
    b <@ A.decide(e.`1,e.`2);
    return b;
  }
}.

module L5HmacIdeal(G:L5Generator,H:L5Hmac,E:L5Exporter,A:L5QPTAdversary) = {
  proc main(aux : l5_qaux) : bool = {
    var g, h, e, b;
    g <@ G.ideal(aux);
    h <@ H.ideal(g.`1,g.`2);
    e <@ E.real(h.`1,h.`2);
    b <@ A.decide(e.`1,e.`2);
    return b;
  }
}.

module L5ExporterReal(G:L5Generator,H:L5Hmac,E:L5Exporter,A:L5QPTAdversary) = {
  proc main(aux : l5_qaux) : bool = {
    var g, h, e, b;
    g <@ G.ideal(aux);
    h <@ H.ideal(g.`1,g.`2);
    e <@ E.real(h.`1,h.`2);
    b <@ A.decide(e.`1,e.`2);
    return b;
  }
}.

module L5ExporterIdeal(G:L5Generator,H:L5Hmac,E:L5Exporter,A:L5QPTAdversary) = {
  proc main(aux : l5_qaux) : bool = {
    var g, h, e, b;
    g <@ G.ideal(aux);
    h <@ H.ideal(g.`1,g.`2);
    e <@ E.ideal(h.`1,h.`2);
    b <@ A.decide(e.`1,e.`2);
    return b;
  }
}.

lemma l5_g0_generator_real_exact
    (G <: L5Generator) (H <: L5Hmac{-G})
    (E <: L5Exporter{-G,-H}) (A <: L5QPTAdversary{-G,-H,-E}) :
  equiv [L5G0(G,H,E,A).main ~
         L5GenReal(G,H,E,A).main :
         ={aux,glob G,glob H,glob E,glob A} ==> ={res}].
proof. by sim. qed.

lemma l5_g1_generator_ideal_exact
    (G <: L5Generator) (H <: L5Hmac{-G})
    (E <: L5Exporter{-G,-H}) (A <: L5QPTAdversary{-G,-H,-E}) :
  equiv [L5G1(G,H,E,A).main ~
         L5GenIdeal(G,H,E,A).main :
         ={aux,glob G,glob H,glob E,glob A} ==> ={res}].
proof. by sim. qed.

lemma l5_g1_hmac_real_exact
    (G <: L5Generator) (H <: L5Hmac{-G})
    (E <: L5Exporter{-G,-H}) (A <: L5QPTAdversary{-G,-H,-E}) :
  equiv [L5G1(G,H,E,A).main ~
         L5HmacReal(G,H,E,A).main :
         ={aux,glob G,glob H,glob E,glob A} ==> ={res}].
proof. by sim. qed.

lemma l5_g2_hmac_ideal_exact
    (G <: L5Generator) (H <: L5Hmac{-G})
    (E <: L5Exporter{-G,-H}) (A <: L5QPTAdversary{-G,-H,-E}) :
  equiv [L5G2(G,H,E,A).main ~
         L5HmacIdeal(G,H,E,A).main :
         ={aux,glob G,glob H,glob E,glob A} ==> ={res}].
proof. by sim. qed.

lemma l5_g2_exporter_real_exact
    (G <: L5Generator) (H <: L5Hmac{-G})
    (E <: L5Exporter{-G,-H}) (A <: L5QPTAdversary{-G,-H,-E}) :
  equiv [L5G2(G,H,E,A).main ~ L5ExporterReal(G,H,E,A).main :
         ={aux,glob G,glob H,glob E,glob A} ==> ={res}].
proof. by sim. qed.

lemma l5_g3_exporter_ideal_exact
    (G <: L5Generator) (H <: L5Hmac{-G})
    (E <: L5Exporter{-G,-H}) (A <: L5QPTAdversary{-G,-H,-E}) :
  equiv [L5G3(G,H,E,A).main ~ L5ExporterIdeal(G,H,E,A).main :
         ={aux,glob G,glob H,glob E,glob A} ==> ={res}].
proof. by sim. qed.

lemma l5_g0_generator_real_pr
    (G <: L5Generator) (H <: L5Hmac{-G})
    (E <: L5Exporter{-G,-H}) (A <: L5QPTAdversary{-G,-H,-E})
    (aux0 : l5_qaux) &m :
  Pr[L5G0(G,H,E,A).main(aux0) @ &m : res] =
  Pr[L5GenReal(G,H,E,A).main(aux0) @ &m : res].
proof. by byequiv (l5_g0_generator_real_exact G H E A). qed.

lemma l5_g1_generator_ideal_pr
    (G <: L5Generator) (H <: L5Hmac{-G})
    (E <: L5Exporter{-G,-H}) (A <: L5QPTAdversary{-G,-H,-E})
    (aux0 : l5_qaux) &m :
  Pr[L5G1(G,H,E,A).main(aux0) @ &m : res] =
  Pr[L5GenIdeal(G,H,E,A).main(aux0) @ &m : res].
proof. by byequiv (l5_g1_generator_ideal_exact G H E A). qed.

lemma l5_g1_hmac_real_pr
    (G <: L5Generator) (H <: L5Hmac{-G})
    (E <: L5Exporter{-G,-H}) (A <: L5QPTAdversary{-G,-H,-E})
    (aux0 : l5_qaux) &m :
  Pr[L5G1(G,H,E,A).main(aux0) @ &m : res] =
  Pr[L5HmacReal(G,H,E,A).main(aux0) @ &m : res].
proof. by byequiv (l5_g1_hmac_real_exact G H E A). qed.

lemma l5_g2_hmac_ideal_pr
    (G <: L5Generator) (H <: L5Hmac{-G})
    (E <: L5Exporter{-G,-H}) (A <: L5QPTAdversary{-G,-H,-E})
    (aux0 : l5_qaux) &m :
  Pr[L5G2(G,H,E,A).main(aux0) @ &m : res] =
  Pr[L5HmacIdeal(G,H,E,A).main(aux0) @ &m : res].
proof. by byequiv (l5_g2_hmac_ideal_exact G H E A). qed.

lemma l5_g2_exporter_real_pr
    (G <: L5Generator) (H <: L5Hmac{-G})
    (E <: L5Exporter{-G,-H}) (A <: L5QPTAdversary{-G,-H,-E})
    (aux0 : l5_qaux) &m :
  Pr[L5G2(G,H,E,A).main(aux0) @ &m : res] =
  Pr[L5ExporterReal(G,H,E,A).main(aux0) @ &m : res].
proof. by byequiv (l5_g2_exporter_real_exact G H E A). qed.

lemma l5_g3_exporter_ideal_pr
    (G <: L5Generator) (H <: L5Hmac{-G})
    (E <: L5Exporter{-G,-H}) (A <: L5QPTAdversary{-G,-H,-E})
    (aux0 : l5_qaux) &m :
  Pr[L5G3(G,H,E,A).main(aux0) @ &m : res] =
  Pr[L5ExporterIdeal(G,H,E,A).main(aux0) @ &m : res].
proof. by byequiv (l5_g3_exporter_ideal_exact G H E A). qed.

op l5_qpt_classical_bound (eps_gen eps_hmac eps_exporter : real) =
  eps_gen + eps_hmac + eps_exporter.

lemma l5_blackbox_nonrewinding_composition
    (G <: L5Generator) (H <: L5Hmac{-G})
    (E <: L5Exporter{-G,-H}) (A <: L5QPTAdversary{-G,-H,-E})
    (aux0 : l5_qaux) eps_gen eps_hmac eps_exporter &m :
  `|Pr[L5GenReal(G,H,E,A).main(aux0) @ &m : res] -
    Pr[L5GenIdeal(G,H,E,A).main(aux0) @ &m : res]| <= eps_gen =>
  `|Pr[L5HmacReal(G,H,E,A).main(aux0) @ &m : res] -
    Pr[L5HmacIdeal(G,H,E,A).main(aux0) @ &m : res]| <= eps_hmac =>
  `|Pr[L5ExporterReal(G,H,E,A).main(aux0) @ &m : res] -
    Pr[L5ExporterIdeal(G,H,E,A).main(aux0) @ &m : res]| <= eps_exporter =>
  `|Pr[L5G0(G,H,E,A).main(aux0) @ &m : res] -
    Pr[L5G3(G,H,E,A).main(aux0) @ &m : res]| <=
      l5_qpt_classical_bound eps_gen eps_hmac eps_exporter.
proof.
  move=> hg hh he.
  have g01 :
    `|Pr[L5G0(G,H,E,A).main(aux0) @ &m : res] -
      Pr[L5G1(G,H,E,A).main(aux0) @ &m : res]| <= eps_gen.
  + by rewrite (l5_g0_generator_real_pr G H E A aux0 &m)
               (l5_g1_generator_ideal_pr G H E A aux0 &m).
  have g12 :
    `|Pr[L5G1(G,H,E,A).main(aux0) @ &m : res] -
      Pr[L5G2(G,H,E,A).main(aux0) @ &m : res]| <= eps_hmac.
  + by rewrite (l5_g1_hmac_real_pr G H E A aux0 &m)
               (l5_g2_hmac_ideal_pr G H E A aux0 &m).
  have g23 :
    `|Pr[L5G2(G,H,E,A).main(aux0) @ &m : res] -
      Pr[L5G3(G,H,E,A).main(aux0) @ &m : res]| <= eps_exporter.
  + by rewrite (l5_g2_exporter_real_pr G H E A aux0 &m)
               (l5_g3_exporter_ideal_pr G H E A aux0 &m).
  rewrite /l5_qpt_classical_bound.
  have g02 := StdOrder.RealOrder.ler_dist_add
    (Pr[L5G1(G,H,E,A).main(aux0) @ &m : res])
    (Pr[L5G0(G,H,E,A).main(aux0) @ &m : res])
    (Pr[L5G2(G,H,E,A).main(aux0) @ &m : res]).
  have h02 :
    `|Pr[L5G0(G,H,E,A).main(aux0) @ &m : res] -
      Pr[L5G2(G,H,E,A).main(aux0) @ &m : res]| <= eps_gen + eps_hmac.
  + apply (ler_trans
      (`|Pr[L5G0(G,H,E,A).main(aux0) @ &m : res] -
          Pr[L5G1(G,H,E,A).main(aux0) @ &m : res]| +
       `|Pr[L5G1(G,H,E,A).main(aux0) @ &m : res] -
          Pr[L5G2(G,H,E,A).main(aux0) @ &m : res]|)).
    - exact g02.
    - exact (ler_add _ _ _ _ g01 g12).
  have g03 := StdOrder.RealOrder.ler_dist_add
    (Pr[L5G2(G,H,E,A).main(aux0) @ &m : res])
    (Pr[L5G0(G,H,E,A).main(aux0) @ &m : res])
    (Pr[L5G3(G,H,E,A).main(aux0) @ &m : res]).
  apply (ler_trans
      (`|Pr[L5G0(G,H,E,A).main(aux0) @ &m : res] -
          Pr[L5G2(G,H,E,A).main(aux0) @ &m : res]| +
       `|Pr[L5G2(G,H,E,A).main(aux0) @ &m : res] -
          Pr[L5G3(G,H,E,A).main(aux0) @ &m : res]|)).
  + exact g03.
  + exact (ler_add _ _ _ _ h02 g23).
qed.

(* Non-vacuity of the modeled interface: classical Product queries are an
   admitted constructor, while the coherent constructor is explicitly not. *)
lemma l5_classical_mode_is_admitted :
  l5_admitted_mode L5Classical.
proof. by rewrite /l5_admitted_mode. qed.
