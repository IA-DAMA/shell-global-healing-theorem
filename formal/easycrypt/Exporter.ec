require import ShellTypes QPCS.

module type Exporter = {
  proc derive(q : qsecret, ctx : context) : qexport
  proc ideal(ctx : context) : qexport
}.

(* Generic real/ideal game for the exporter-preservation obligation.  In the
   real game q is already the idealized QPCS secret from G1; the hop asks only
   whether derive(q,ctx) can be replaced by the ideal qexport used in G2. *)
module type ExporterDistinguisher = {
  proc distinguish(qe : qexport, c : cexport, ctx : context) : bool
}.

module ExporterReal(Q:QPCS, E:Exporter, D:ExporterDistinguisher) = {
  proc main(c : cexport, ctx : context) : bool = {
    var q, qe, b;
    q <@ Q.ideal(ctx);
    qe <@ E.derive(q, ctx);
    b <@ D.distinguish(qe, c, ctx);
    return b;
  }
}.

module ExporterIdeal(E:Exporter, D:ExporterDistinguisher) = {
  proc main(c : cexport, ctx : context) : bool = {
    var qe, b;
    qe <@ E.ideal(ctx);
    b <@ D.distinguish(qe, c, ctx);
    return b;
  }
}.
