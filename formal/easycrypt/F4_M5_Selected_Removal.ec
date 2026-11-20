require import AllCore List Distr.
require import F4_Native_Accepted_Trace_Refinement F4_Leaf_Cut_Fixture
  F4_Recovery_Word_Experiment F4_Online_Recovery_Cut F4_M5_Singleton_Schedule.

(* Entries are the phases of retained survivor copies for ONE fixed receipt.
   None represents a copy whose phase is not classified. Completeness of
   the input list is an external refinement obligation, never inferred from
   equality of outputs or from an absence of failed API calls. *)
type copies = copy_phase option list.
op early_only (xs : copies) = all (fun x => x = Some Early) xs.
op singleton_shape (oldn newn : int) (rotated : bool) (widths : int list) =
  oldn = 2 /\ newn = 1 /\ rotated /\ widths = [].
op admits before after oldn newn rotated widths xs =
  f4_nt_local_successor before after /\ after.`f4_nt_op = f4_nt_op_remove /\
  singleton_shape oldn newn rotated widths /\ early_only xs.

lemma each_copy_stays_closed (xs : copies) s permission :
  early_only xs => mem xs (Some s) => safe evolving epoch_known (s,permission).
proof. rewrite /early_only allP online_cut_with_later_grant; smt(). qed.

lemma unclassified_copy_blocks (xs : copies) : mem xs None => !early_only xs.
proof. rewrite /early_only allP; smt(). qed.

lemma prepared_copy_blocks (xs : copies) s :
  mem xs (Some s) => s <> Early => !early_only xs.
proof. rewrite /early_only allP; smt(). qed.

lemma fixture_shape : singleton_shape removal_cut.`3 removal_cut.`4
  removal_cut.`5 removal_cut.`6.
proof. by rewrite /singleton_shape /removal_cut. qed.

lemma classified_past_exposure_admitted before after :
  f4_nt_local_successor before after => after.`f4_nt_op = f4_nt_op_remove =>
  admits before after 2 1 true [] [Some Early].
proof. by rewrite /admits /singleton_shape /early_only /=. qed.

module Selected(D:End) = {
  proc run(before after : f4_native_trace_point, oldn newn:int,
           rotated:bool, widths:int list, xs:copies, p:params) = {
    var b, result;
    result <- None;
    if (admits before after oldn newn rotated widths xs) {
      b <@ Schedule(D).real(p); result <- Some b;
    }
    return result;
  }
}.

lemma accepted_probability (D <: End) pre post a b rot ws inventory par &m :
  admits pre post a b rot ws inventory =>
  Pr[Selected(D).run(pre,post,a,b,rot,ws,inventory,par) @ &m : res=Some true] =
  Pr[Schedule(D).real(par) @ &m : res].
proof. move=> h; byequiv (_: p{1}=arg{2} /\ ={glob D} /\
  admits before{1} after{1} oldn{1} newn{1} rotated{1} widths{1} xs{1} ==> res{1}=Some res{2}) => //.
proc *; inline Selected(D).run.
  rcondt{1} 10; first by auto.
  wp; call (_: ={arg,glob D} ==> ={res}); first by sim.
  auto.
  smt().
qed.
