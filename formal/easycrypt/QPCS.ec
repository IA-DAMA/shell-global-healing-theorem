require import ShellTypes.

module type QPCS = {
  proc real(ctx : context) : qsecret
  proc ideal(ctx : context) : qsecret
}.

(* Generic distinguisher and real/ideal games for the imported QPCS
   assumption.  The public classical export and Shell context are explicit
   inputs; only q changes between the two games. *)
module type QPCSDistinguisher = {
  proc distinguish(q : qsecret, c : cexport, ctx : context) : bool
}.

module QPCSReal(Q:QPCS, D:QPCSDistinguisher) = {
  proc main(c : cexport, ctx : context) : bool = {
    var q, b;
    q <@ Q.real(ctx);
    b <@ D.distinguish(q, c, ctx);
    return b;
  }
}.

module QPCSIdeal(Q:QPCS, D:QPCSDistinguisher) = {
  proc main(c : cexport, ctx : context) : bool = {
    var q, b;
    q <@ Q.ideal(ctx);
    b <@ D.distinguish(q, c, ctx);
    return b;
  }
}.
