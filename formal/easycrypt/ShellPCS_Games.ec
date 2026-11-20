require import ShellTypes QPCS Exporter SplitPRF.

module type Adv = {
  proc distinguish(k : kz) : bool
}.

module G0(Q:QPCS, E:Exporter, M:SplitPRF, A:Adv) = {
  proc main(c : cexport, ctx : context) : bool = {
    var q, qe, k, b;
    q <@ Q.real(ctx);
    qe <@ E.derive(q, ctx);
    k <@ M.eval(c, qe, ctx);
    b <@ A.distinguish(k);
    return b;
  }
}.

module G1(Q:QPCS, E:Exporter, M:SplitPRF, A:Adv) = {
  proc main(c : cexport, ctx : context) : bool = {
    var q, qe, k, b;
    q <@ Q.ideal(ctx);
    qe <@ E.derive(q, ctx);
    k <@ M.eval(c, qe, ctx);
    b <@ A.distinguish(k);
    return b;
  }
}.

module G2(Q:QPCS, E:Exporter, M:SplitPRF, A:Adv) = {
  proc main(c : cexport, ctx : context) : bool = {
    var qe, k, b;
    qe <@ E.ideal(ctx);
    k <@ M.eval(c, qe, ctx);
    b <@ A.distinguish(k);
    return b;
  }
}.

module G3(M:SplitPRF, A:Adv) = {
  proc main() : bool = {
    var k, b;
    k <@ M.ideal();
    b <@ A.distinguish(k);
    return b;
  }
}.
