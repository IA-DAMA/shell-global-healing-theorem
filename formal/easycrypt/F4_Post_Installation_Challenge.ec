require import AllCore List StdOrder ShellTypes F4_Adversarial_Query_Ledger.
require import F4_Interactive_PCS_Game F4_Native_Interactive_Game_Refinement.

lemma blocked_query (B <: F4ProductPCSBackend{-F4Challenger}) :
  hoare [F4Challenger(B).challenge : F4Challenger.bad_challenge ==>
    F4Challenger.bad_challenge /\ res = None].
proof.
  proc. seq 2 : (F4Challenger.bad_challenge /\ out = None); first by auto.
  rcondt 1; first by skip; smt().
  by auto.
qed.

(* An arbitrary interactive suffix has exactly the oracle methods of the
   existing game. Its module and backend cannot modify the challenger
   outside that interface; the adversary cannot call initialize. *)
lemma blocked_suffix (B <: F4ProductPCSBackend{-F4Challenger})
    (A <: F4AdaptivePCSAdversary{-F4Challenger, -B}) :
  hoare [A(F4Challenger(B)).guess : F4Challenger.bad_challenge ==>
    F4Challenger.bad_challenge].
proof.
  proc (F4Challenger.bad_challenge) => //;
    try (by proc; wp; call (_: true); auto; smt());
    try (by proc; auto).
  conseq (blocked_query B); smt().
qed.

module PostInstallation(B:F4ProductPCSBackend,A:F4AdaptivePCSAdversary) = {
  proc next(via_welcome : bool, q : f4_query_record, ctx : context) : int list option = {
    var result;
    if (via_welcome) {
      F4Challenger(B).welcome_install(q);
    } else {
      F4Challenger(B).resync_install(q);
    }
    A(F4Challenger(B)).guess();
    result <@ F4Challenger(B).challenge(q,ctx);
    return result;
  }
}.

lemma post_installation_refuses (B <: F4ProductPCSBackend{-F4Challenger})
    (A <: F4AdaptivePCSAdversary{-F4Challenger, -B}) :
  hoare [PostInstallation(B,A).next : true ==> res = None].
proof.
  proc. call (blocked_query B); call (blocked_suffix B A).
  if.
  + call (f4_interactive_unproved_welcome_poison_challenge B); auto.
  + call (f4_interactive_unproved_resync_poison_challenge B); auto.
qed.


lemma no_selected_mass (B <: F4ProductPCSBackend{-F4Challenger})
    (A <: F4AdaptivePCSAdversary{-F4Challenger, -B}) &m via q ctx :
  Pr[PostInstallation(B,A).next(via,q,ctx) @ &m : res <> None] = 0%r.
proof.
  byphoare (_ : true ==> res <> None) => //.
  hoare. conseq (post_installation_refuses B A); smt().
qed.


(* The source has assigned a mass p to a successful post-installation
   selection under a specified eligibility rule. Testing the public option
   tag needs no secret. Hence any approximation preserving that tag must
   spend at least p probability error on this family of histories. *)
lemma selection_error_at_least_source_mass
    (B <: F4ProductPCSBackend{-F4Challenger})
    (A <: F4AdaptivePCSAdversary{-F4Challenger, -B}) (p slack : real) &m via q ctx :
  0%r <= p =>
  `|p - Pr[PostInstallation(B,A).next(via,q,ctx) @ &m : res <> None]| <= slack =>
  p <= slack.
proof.
  move=> hp; rewrite (no_selected_mass B A &m via q ctx) /=.
  by rewrite RealOrder.ger0_norm.
qed.

require import F4_Installation_Fixture.
lemma observed_direct_cut :
  let (epoch, record_at_error, bundle_at_error, bundle_after, copy_after, equal)
      = f4_direct_recovery in
  epoch = 1 /\ !record_at_error /\ bundle_at_error /\ !bundle_after /\ copy_after /\
  equal /\ f4_direct_epoch_record_equal /\ f4_direct_epoch_writes = [0;0;0].
proof.
  by rewrite /f4_direct_recovery /f4_direct_epoch_record_equal /f4_direct_epoch_writes.
qed.

lemma successful_history_veto (B <: F4ProductPCSBackend{-F4Challenger}) :
  hoare [F4Challenger(B).challenge :
    has (fun q : f4_query_record => q.`f4_q_index < F4Challenger.query_count)
        F4Challenger.exposures ==> F4Challenger.bad_challenge /\ res = None].
proof.
  proc. seq 2 : (!f4_gate_fresh F4Challenger.exposures x /\ out=None).
  + auto; smt(gate_fresh_exact f4_challenger_forced_epoch).
  rcondt 1; first by skip; smt().
  by auto.
qed.
