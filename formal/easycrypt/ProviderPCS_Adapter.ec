require import AllCore.
require import ShellTypes QPCS.

(* A provider theorem normally speaks about a provider-specific execution
   view: group state, epoch, accepted transcript and the challenge position.
   Shell's context is translated into that view by phi.  This file proves
   only that the resulting wrapper introduces no additional advantage.  It
   deliberately does not assert that phi preserves freshness or that all
   Shell oracle calls are admitted by an upstream provider game. *)
type provider_view.
op phi : context -> provider_view.

module type ProviderPCS = {
  proc real(view : provider_view) : qsecret
  proc ideal(view : provider_view) : qsecret
}.

module ProviderPCSAdapter(P:ProviderPCS) : QPCS = {
  proc real(ctx : context) : qsecret = {
    var q, view;
    view <- phi ctx;
    q <@ P.real(view);
    return q;
  }

  proc ideal(ctx : context) : qsecret = {
    var q, view;
    view <- phi ctx;
    q <@ P.ideal(view);
    return q;
  }
}.

(* Direct provider games, kept separate so an upstream PCS theorem can bind
   to them without mentioning Shell's QPCS interface. *)
module ProviderPCSReal(P:ProviderPCS, D:QPCSDistinguisher) = {
  proc main(c : cexport, ctx : context) : bool = {
    var q, view, b;
    view <- phi ctx;
    q <@ P.real(view);
    b <@ D.distinguish(q, c, ctx);
    return b;
  }
}.

module ProviderPCSIdeal(P:ProviderPCS, D:QPCSDistinguisher) = {
  proc main(c : cexport, ctx : context) : bool = {
    var q, view, b;
    view <- phi ctx;
    q <@ P.ideal(view);
    b <@ D.distinguish(q, c, ctx);
    return b;
  }
}.

lemma qpcs_adapter_real_equiv
    (P <: ProviderPCS) (D <: QPCSDistinguisher{-P})
    (c : cexport) (ctx : context) :
  equiv [QPCSReal(ProviderPCSAdapter(P),D).main ~
         ProviderPCSReal(P,D).main :
         ={c,ctx,glob P,glob D} ==> ={res}].
proof.
  proc.
  inline ProviderPCSAdapter(P).real.
  sim.
qed.

lemma qpcs_adapter_ideal_equiv
    (P <: ProviderPCS) (D <: QPCSDistinguisher{-P})
    (c : cexport) (ctx : context) :
  equiv [QPCSIdeal(ProviderPCSAdapter(P),D).main ~
         ProviderPCSIdeal(P,D).main :
         ={c,ctx,glob P,glob D} ==> ={res}].
proof.
  proc.
  inline ProviderPCSAdapter(P).ideal.
  sim.
qed.

lemma qpcs_adapter_real_pr
    (P <: ProviderPCS) (D <: QPCSDistinguisher{-P})
    (c : cexport) (ctx : context) &m :
  Pr[QPCSReal(ProviderPCSAdapter(P),D).main(c,ctx) @ &m : res] =
  Pr[ProviderPCSReal(P,D).main(c,ctx) @ &m : res].
proof.
  by byequiv (qpcs_adapter_real_equiv P D c ctx).
qed.

lemma qpcs_adapter_ideal_pr
    (P <: ProviderPCS) (D <: QPCSDistinguisher{-P})
    (c : cexport) (ctx : context) &m :
  Pr[QPCSIdeal(ProviderPCSAdapter(P),D).main(c,ctx) @ &m : res] =
  Pr[ProviderPCSIdeal(P,D).main(c,ctx) @ &m : res].
proof.
  by byequiv (qpcs_adapter_ideal_equiv P D c ctx).
qed.

(* Zero-loss transport at the already-matched game boundary.  The substantive
   P2b obligations remain outside this lemma: FreshQ -> provider Safe, oracle
   simulation, and authentication/context correspondence. *)
lemma provider_pcs_to_qpcs_zero_loss
    (P <: ProviderPCS) (D <: QPCSDistinguisher{-P})
    (c : cexport) (ctx : context) (epsilon : real) &m :
  `| Pr[ProviderPCSReal(P,D).main(c,ctx) @ &m : res] -
     Pr[ProviderPCSIdeal(P,D).main(c,ctx) @ &m : res] | <= epsilon =>
  `| Pr[QPCSReal(ProviderPCSAdapter(P),D).main(c,ctx) @ &m : res] -
     Pr[QPCSIdeal(ProviderPCSAdapter(P),D).main(c,ctx) @ &m : res] | <= epsilon.
proof.
  move=> hp.
  rewrite (qpcs_adapter_real_pr P D c ctx &m)
          (qpcs_adapter_ideal_pr P D c ctx &m).
  exact hp.
qed.
