require import ShellTypes Exporter.

module type SplitPRF = {
  proc eval(c : cexport, q : qexport, ctx : context) : kz
  proc ideal() : kz
}.

(* Generic real/ideal game for the Q-fresh split-key direction.  The public or
   adversarial classical leg c remains an explicit input in the real game. *)
module type SplitPRFDistinguisher = {
  proc distinguish(k : kz) : bool
}.

module SplitPRFReal(E:Exporter, M:SplitPRF, D:SplitPRFDistinguisher) = {
  proc main(c : cexport, ctx : context) : bool = {
    var qe, k, b;
    qe <@ E.ideal(ctx);
    k <@ M.eval(c, qe, ctx);
    b <@ D.distinguish(k);
    return b;
  }
}.

module SplitPRFIdeal(M:SplitPRF, D:SplitPRFDistinguisher) = {
  proc main() : bool = {
    var k, b;
    k <@ M.ideal();
    b <@ D.distinguish(k);
    return b;
  }
}.
