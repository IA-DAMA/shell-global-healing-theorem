require import AllCore List Distr DInterval DList StdOrder.
require import F4_QSF_Oracle_Embedding F4_OpenMLS_Exporter_Program.
require import F4_Typed_Challenge_Model F4_Oracle_Call_Projection F4_OpenMLS_Exporter_Algorithm.

(* Coordinates are the arguments actually reaching the final ExpandWithLabel.
   In particular two database objects can select the same coordinate. *)
type coord = f4_suite * f4_kdf_secret * f4_kdf_label * f4_context_hash * int.
op coordinate (ek : f4_kdf_secret) (o : f4_oracle_call) : coord option =
  let s = o.`f4_oc_suite in
  let h = f4_context_hash s o.`f4_oc_exporter_context in
  let k = f4_derive_secret s ek (f4_user_exporter_label o.`f4_oc_exporter_label) in
  if h = None \/ k = None \/ !f4_expand_length_supported (f4_hash_bytes s) o.`f4_oc_length
  then None else Some (s,oget k,f4_internal_exported_label,oget h,o.`f4_oc_length).

op evaluate (x : coord) =
  f4_kdf_expand_with_label x.`1 x.`2 x.`3 x.`4 x.`5.

lemma final_call ek o :
  (f4_mir_derive_with_key ek o).`2 = obind evaluate (coordinate ek o).
proof.
  rewrite /f4_mir_derive_with_key /coordinate /evaluate
          /F4_OpenMLS_Exporter_MIR.f4_derive_mir.
  smt().
qed.

(* In the random-function hybrid for successful 32-byte calls, a transcript
   can determine the selected input. Preserve the table for every previous
   reply AND all private strategy state. Independent coins below are drawn
   only after selection. All oracle calls here are classical. *)
type word32 = int list.
type table = coord -> word32 option.
op put (m : table) x v = fun u => if u=x then Some v else m u.
op read (m : table) x u = odflt u (m x).
op sample32 = dlist (dinter 0 255) 32.

(* One fresh tape entry per step, unused on a hit or silent step. A policy
   can interrupt, issue the same request again, or continue after recovery.
   None is a silent step. The private state is updated even on silent steps. *)
op suffix ['s] (ask : 's -> coord option)
    (observe : 's -> word32 option -> 's)
    (star : coord) (m : table) (s : 's) (coins : word32 list) : 's * bool =
  with coins = [] => (s,false)
  with coins = v :: vs =>
    if ask s = None then suffix ask observe star m (observe s None) vs else
    let x = oget (ask s) in
    let y = read m x v in
    let r = suffix ask observe star (put m x y) (observe s (Some y)) vs in
    (r.`1, x=star \/ r.`2).

lemma until_read ['s] (ask : 's -> coord option) observe star coins s (m n : table) :
  (forall x, x<>star => m x = n x) =>
  (suffix ask observe star m s coins).`2 = (suffix ask observe star n s coins).`2 /\
  (!(suffix ask observe star m s coins).`2 =>
      (suffix ask observe star m s coins).`1 = (suffix ask observe star n s coins).`1).
proof.
  elim: coins s m n => [|v vs ih] s m n same //=.
  case: (ask s = None) => empty /=; first by apply ih.
  pose x := oget (ask s).
  case: (x=star) => eqx; first by smt().
  have y : read m x v = read n x v by rewrite /read (same x eqx).
  have post : forall z, z<>star => put m x (read m x v) z = put n x (read n x v) z
    by move=> z hz; rewrite /put y; smt().
  have h := ih (observe s (Some (read n x v))) _ _ post.
  smt().
qed.

type 's prefix = 's * table * coord.
type 's coins = 's prefix * word32 * word32 * word32 list.
op experiment ['s] (prefixes : 's prefix distr) q : 's coins distr =
  dlet prefixes (fun p => dlet sample32 (fun c => dlet sample32 (fun u =>
    dmap (dlist sample32 q) (fun tape => (p,c,u,tape))))).

op play ['s] (real : bool) (give : 's -> word32 -> 's) ask observe (r : 's coins) =
  let (p,c,u,tape) = r in
  let (s,m,x) = p in
  let actual = read m x (if real then c else u) in
  suffix ask observe x (put m x actual) (give s (if real then actual else c)) tape.

op reopened ['s] give ask observe (r : 's coins) =
  r.`1.`2 r.`1.`3 <> None \/ (play true give ask observe r).`2.

lemma consistent_until_reopening ['s] give ask observe (r : 's coins) :
  !reopened give ask observe r =>
  (play true give ask observe r).`1 = (play false give ask observe r).`1.
proof.
  case: r => -[s m x] c u tape; rewrite /reopened /play /=.
  case (m x = None) => hx; last by smt().
  rewrite /read hx /=.
  have h := until_read ask observe x tape (give s c) (put m x c) (put m x u) _.
  + by move=> z hz; rewrite /put hz.
  smt().
qed.

lemma adaptive_final_hybrid ['s] (prefixes : 's prefix distr) q give ask observe
    (decide : 's -> bool) :
  let d = experiment prefixes q in
  `|mu d (fun r => decide (play true give ask observe r).`1) -
    mu d (fun r => decide (play false give ask observe r).`1)| <=
    mu d (reopened give ask observe).
proof.
  apply (correctness_charge (experiment prefixes q) (reopened give ask observe)
    (fun r => decide (play true give ask observe r).`1)
    (fun r => decide (play false give ask observe r).`1) _).
  move=> r _ safe; have h := consistent_until_reopening give ask observe r safe.
  smt().
qed.
(* Observable actions can be controlled by a recovery state machine. A
   certificate must be preserved for every reply, including failed lookups.
   This suffices for zero reopening probability for arbitrary suffix length. *)
lemma suffix_closed ['s] (cert : 's -> bool) ask observe x :
  (forall s, cert s => ask s <> Some x) =>
  (forall s y, cert s => cert (observe s y)) =>
  forall coins m s, cert s => !(suffix ask observe x m s coins).`2.
proof.
  move=> cut keep; elim => [|v vs ih] m s hs //=.
  have n := cut s hs.
  case (ask s = None) => empty /=.
  + exact (ih _ _ (keep s None hs)).
  have z : oget (ask s) <> x by case: (ask s) empty n; smt().
  rewrite z /=; apply ih; apply keep; exact hs.
qed.

require import F4_Online_Recovery_Cut F4_Recovery_Word_Experiment.

(* A positive example with arbitrary adaptive grant, withdrawal and receipt
   operations in the existing recovery automaton. The strategy has its own
   memory and may use every previous reply to decide its next operation. *)
lemma early_receipt_suffix ['a] (x : coord) (ask : (copy_phase * bool) * 'a -> coord option)
    (observe : (copy_phase * bool) * 'a -> word32 option -> (copy_phase * bool) * 'a)
    (cmd : (copy_phase * bool) * 'a -> word32 option -> authority_command) :
  (forall s, ask s = Some x => epoch_known s.`1) =>
  (forall s y, (observe s y).`1 = odflt s.`1 (evolving s.`1 (cmd s y))) =>
  forall coins m (s : (copy_phase * bool) * 'a), s.`1.`1 = Early => !(suffix ask observe x m s coins).`2.
proof.
  move=> admission step.
  apply (suffix_closed (fun (s : (copy_phase * bool) * 'a) => s.`1.`1 = Early)).
  + move=> s hs; have h := admission s; rewrite /epoch_known /readable hs in h; smt().
  + move=> s y hs; have h := step s y.
    case: (cmd s y) h => [| |c] /=; smt().
qed.

require import QPCS Exporter SplitPRF ShellPCS_Games ShellPCS_MSS26 ShellTypes
  Phi_Trace_Model Phi_Refinement Phi_Safe_TTKEM Phi_Membership_Fold Phi_Canonical_Events
  ShellPCS_T1_Conditional QPCS_Hop Exporter_Hop SplitPRF_Hop.

op lazy_accept ['s] world (prefixes : 's prefix distr) q give ask observe decide =
  mu (experiment prefixes q) (fun r => decide (play world give ask observe r).`1).

(* Instantiate the existing T1 provider premise with THREE explicit terms.
   Admission is still on the original trace; neither endpoint transition
   from the real provider to this last random-function hybrid is free. *)
lemma m5_t1_reopening_bound
    (Q <: QPCS) (E <: Exporter{-Q}) (M <: SplitPRF{-E,-Q}) (A <: Adv{-M,-E,-Q})
    (tr : shell_trace) (ch : challenge_binding) (c : cexport) (ctx : context)
    (prefixes : 's prefix distr) steps give ask observe (decide : 's -> bool)
    err_real err_ideal eps_export n eps_prg eps_ext eps_prf &m :
  event_projection_ok tr ch => membership_enumerators_canonical tr ch =>
  covered_fold tr ch => oracle_correspondence tr ch => challenge_context_binding tr ch ctx =>
  authentication_conditions tr ch => clone_session_conditions tr ch =>
  composition_side_conditions tr ch ctx =>
  `|Pr[QPCSReal(Q,QPCSReduction(E,M,A)).main(c,ctx) @ &m : res] -
    lazy_accept true prefixes steps give ask observe decide| <= err_real =>
  `|lazy_accept false prefixes steps give ask observe decide -
    Pr[QPCSIdeal(Q,QPCSReduction(E,M,A)).main(c,ctx) @ &m : res]| <= err_ideal =>
  `|Pr[ExporterReal(Q,E,ExporterReduction(M,A)).main(c,ctx) @ &m : res] -
    Pr[ExporterIdeal(E,ExporterReduction(M,A)).main(c,ctx) @ &m : res]| <= eps_export =>
  `|Pr[SplitPRFReal(E,M,SplitPRFReduction(A)).main(c,ctx) @ &m : res] -
    Pr[SplitPRFIdeal(M,SplitPRFReduction(A)).main() @ &m : res]| <=
      mss26_bound n eps_prg eps_ext eps_prf =>
  `|Pr[G0(Q,E,M,A).main(c,ctx) @ &m : res] - Pr[G3(M,A).main() @ &m : res]| <=
    err_real + mu (experiment prefixes steps) (reopened give ask observe) + err_ideal +
    eps_export + mss26_bound n eps_prg eps_ext eps_prf.
proof.
  move=> hp hm hc ho hb ha hs hx hr hi he hd.
  apply (t1_shell_pcs_conditional_bound Q E M A tr ch c ctx _ eps_export n
           eps_prg eps_ext eps_prf &m hp hm hc ho hb ha hs hx _ he hd).
  move=> _ _ _ _ _ _.
  have mid := adaptive_final_hybrid prefixes steps give ask observe decide.
  rewrite /lazy_accept in hr; rewrite /lazy_accept in hi.
  smt(RealOrder.ler_dist_add).
qed.
