require import AllCore Int List Distr DList DInterval.
require import ShellTypes F4_Adversarial_Query_Ledger.
require import F4_Native_Accepted_Trace_Refinement.
require import F4_Epoch_Schedule_Cut F4_External_FreshQ_Criterion.
require import F4_Successful_Exposure_FreshQ_Bridge.

(* This game follows one group. A full-state capture includes the stored
   epoch exporter secret. A different member, device or public exporter
   context does not give it a different epoch exporter master secret. *)
op f4_group_capture_before (events : f4_query_record list) (ch : f4_query_record) =
  has (fun q => q.`f4_q_corrupt /\ q.`f4_q_epoch = ch.`f4_q_epoch /\
                q.`f4_q_index < ch.`f4_q_index) events.

op f4_observed_exporter_view events ch : f4_view =
  fun m => (m = ExporterKey /\ f4_group_capture_before events ch) \/
           (m = Output /\ f4_exposed_before_challenge events ch).

lemma f4_observed_route events ch :
  f4_output_route (f4_observed_exporter_view events ch) =
    (f4_exposed_before_challenge events ch \/ f4_group_capture_before events ch).
proof. rewrite /f4_output_route /f4_observed_exporter_view /=; smt(). qed.

(* Interactive adversarial PCS oracle with explicit corruption/reveal,
   accepted Commit, external Commit, Welcome, resync and selected challenge.
   No concrete Rust/OpenMLS semantics or QPT advantage is assumed.
   The challenger evaluates a conservative projection of the candidate;
   check_freshq can only veto it. Universal native healing is still open.
   FreshQ receives BOTH the complete attempted-query chronology and the
   successful-disclosure ledger; the former alone cannot distinguish failed
   queries from actual exposed secrets. This is an information-flow repair,
   not a native-backed FreshQ proof. *)

(* Conservative single-group projection. A successful disclosure may cross
   secret classes. In the absence of an authenticated path-recipient witness
   it is charged to the selected class; no epoch increment discharges it.
   The full underlying ledger remains available to the backend veto. *)
op f4_project_gate_exposure (ch q : f4_query_record) =
  {| (f4_successful_disclosure_to_fresh_event 0 true q) with
      ff_secret_kind = f4_secret_number ch.`f4_q_secret_kind |}.

op f4_gate_fresh exposures (ch : f4_query_record) =
  f4_freshq_candidate (map (f4_project_gate_exposure ch) exposures)
    {| (f4_successful_disclosure_to_fresh_event 0 true ch) with
       ff_kind = f4_kind_challenge |}.

lemma gate_fresh_exact xs ch :
  f4_gate_fresh xs ch =
    !has (fun q : f4_query_record => q.`f4_q_index < ch.`f4_q_index) xs.
proof.
  rewrite /f4_gate_fresh /f4_freshq_candidate /f4_exposure_before_challenge
    /f4_healed_since_last_exposure !has_map /=.
  have absent : !has (fun (q : f4_query_record) =>
    f4_internal_heal_witness (map (f4_project_gate_exposure ch) xs)
       (f4_project_gate_exposure ch q)
       {| (f4_successful_disclosure_to_fresh_event 0 true ch) with ff_kind = f4_kind_challenge |}
    /\ !f4_exposure_after_commit_before_challenge (map (f4_project_gate_exposure ch) xs)
       (f4_project_gate_exposure ch q)
       {| (f4_successful_disclosure_to_fresh_event 0 true ch) with ff_kind = f4_kind_challenge |}) xs.
  + apply/negP => /hasP [q [_ h]]; move: h;
      rewrite /f4_internal_heal_witness /f4_project_gate_exposure
        /f4_successful_disclosure_to_fresh_event /= /f4_kind_corrupt
        /f4_kind_reveal /f4_kind_internal_commit; smt().
  have same : forall q, f4_relevant_exposure (f4_project_gate_exposure ch q)
    {| (f4_successful_disclosure_to_fresh_event 0 true ch) with ff_kind = f4_kind_challenge |}
    = (q.`f4_q_index < ch.`f4_q_index).
  + move=> q; rewrite /f4_relevant_exposure /f4_is_exposure_event
      /f4_project_gate_exposure /f4_successful_disclosure_to_fresh_event /=; smt().
  move: absent; rewrite /preim /=; smt(eq_has).
qed.

op f4_internal_tag (q : f4_query_record) (i : int)
                   (is_corrupt is_reveal : bool) : f4_query_record =
 {| f4_q_index = i;
    f4_q_epoch = q.`f4_q_epoch;
    f4_q_member = q.`f4_q_member;
    f4_q_device = q.`f4_q_device;
    f4_q_secret_kind = q.`f4_q_secret_kind;
    f4_q_corrupt = is_corrupt;
    f4_q_reveal = is_reveal |}.

(* Unlike caller supplied query epochs, this tag is minted from the
   challenger-owned accepted epoch. The backend must later be refined to
   authenticated native Product acceptance; Some alone is not proof of it. *)
op f4_challenger_tag (q : f4_query_record) (i epoch : int)
                     (is_corrupt is_reveal : bool) : f4_query_record =
 {| f4_q_index = i;
    f4_q_epoch = epoch;
    f4_q_member = q.`f4_q_member;
    f4_q_device = q.`f4_q_device;
    f4_q_secret_kind = q.`f4_q_secret_kind;
    f4_q_corrupt = is_corrupt;
    f4_q_reveal = is_reveal |}.

type f4_corrupt_snapshot.
type f4_revealed_secret.
type f4_accepted_transition = f4_native_trace_point.
type f4_install_witness.

module type F4ProductPCSBackend = {
 proc init() : f4_accepted_transition
 proc corrupt(q : f4_query_record) : f4_corrupt_snapshot option
 proc reveal(q : f4_query_record) : f4_revealed_secret option
 proc send(q : f4_query_record) : bool
 proc accepted_commit(q : f4_query_record) : f4_accepted_transition option
 proc accepted_external_commit(q : f4_query_record) : f4_accepted_transition option
 proc welcome_install(q : f4_query_record) : f4_install_witness option
 proc resync_install(q : f4_query_record) : f4_install_witness option
 proc check_freshq(q : f4_query_record, prior : f4_query_record list,
                   successful_exposures : f4_query_record list) : bool
 proc selected_exporter(q : f4_query_record, ctx : context) : int list option
}.

module type F4AdaptivePCSOracle = {
 proc corrupt(q : f4_query_record) : f4_corrupt_snapshot option
 proc reveal(q : f4_query_record) : f4_revealed_secret option
 proc send(q : f4_query_record) : bool
 proc accepted_commit(q : f4_query_record) : f4_accepted_transition option
 proc accepted_external_commit(q : f4_query_record) : f4_accepted_transition option
 proc welcome_install(q : f4_query_record) : f4_install_witness option
 proc resync_install(q : f4_query_record) : f4_install_witness option
 proc challenge(q : f4_query_record, ctx : context) : int list option
 proc bad() : bool
}.

module type F4AdaptivePCSAdversary(O:F4AdaptivePCSOracle) = {
 proc guess() : bool
}.

module F4Challenger(B:F4ProductPCSBackend) = {
 var bit : bool
 var query_count : int
 var global_epoch : int
 var last_native_state : f4_native_trace_point
 var accepted_parent : f4_native_trace_point
 var exposures : f4_query_record list
 var public_queries : f4_query_record list
 var bad_challenge : bool
 var challenge_selected : bool

 proc initialize(world : bool) : unit = {
   var first;
   bit <- world;
   query_count <- 0;
   exposures <- [];
   public_queries <- [];
   bad_challenge <- false;
   challenge_selected <- false;
   first <@ B.init();
   last_native_state <- first;
   accepted_parent <- first;
   global_epoch <- first.`f4_nt_epoch;
   if (!first.`f4_nt_verified) { bad_challenge <- true; }
 }
 proc corrupt(q : f4_query_record) : f4_corrupt_snapshot option = {
   var x, result;
   x <- f4_challenger_tag q query_count global_epoch true false;
   result <- None;
   (* SOURCE-ADEQUACY: Product may really disclose native private state
      even after selection of the challenge. Hiding the call creates a
      false universal trace refinement. Preserve every actual successful
      disclosure, and mark post-challenge success as bad for security. *)
   result <@ B.corrupt(x);
   if (result <> None) {
     exposures <- exposures ++ [x];
     if (challenge_selected) { bad_challenge <- true; }
   }
   public_queries <- public_queries ++ [x];
   query_count <- query_count + 1;
   return result;
 }
 proc reveal(q : f4_query_record) : f4_revealed_secret option = {
   var x, result;
   x <- f4_challenger_tag q query_count global_epoch false true;
   (* A real Product exporter can be disclosed after the challenge.
      Record it, then mark the post-challenge disclosure as bad rather
      than silently replacing the native successful Reveal with None. *)
   result <@ B.reveal(x);
   if (result <> None) {
     exposures <- exposures ++ [x];
     if (challenge_selected) { bad_challenge <- true; }
   }
   public_queries <- public_queries ++ [x];
   query_count <- query_count + 1;
   return result;
 }
 proc send(q : f4_query_record) : bool = {
   var x, ok;
   x <- f4_challenger_tag q query_count global_epoch false false;
   ok <@ B.send(x);
   public_queries <- public_queries ++ [x];
   query_count <- query_count + 1;
   return ok;
 }
 proc accepted_commit(q : f4_query_record) : f4_accepted_transition option = {
   var x, ok;
   x <- f4_challenger_tag q query_count global_epoch false false;
   ok <@ B.accepted_commit(x);
   accepted_parent <- last_native_state;
   if (ok <> None) {
     if (f4_nt_local_successor accepted_parent (oget ok) /\
         ((oget ok).`f4_nt_op = f4_nt_op_internal_own_update \/
          (oget ok).`f4_nt_op = f4_nt_op_remove)) {
       last_native_state <- oget ok;
       global_epoch <- last_native_state.`f4_nt_epoch;
     } else {
       ok <- None;
       bad_challenge <- true;
     }
   }
   public_queries <- public_queries ++ [x];
   query_count <- query_count + 1;
   return ok;
 }
 proc accepted_external_commit(q : f4_query_record) : f4_accepted_transition option = {
   var x, ok;
   x <- f4_challenger_tag q query_count global_epoch false false;
   ok <@ B.accepted_external_commit(x);
   accepted_parent <- last_native_state;
   if (ok <> None) {
     if (f4_nt_local_successor accepted_parent (oget ok) /\
         (oget ok).`f4_nt_op = f4_nt_op_external_commit) {
       last_native_state <- oget ok;
       global_epoch <- last_native_state.`f4_nt_epoch;
     } else {
       ok <- None;
       bad_challenge <- true;
     }
   }
   public_queries <- public_queries ++ [x];
   query_count <- query_count + 1;
   return ok;
 }
 proc welcome_install(q : f4_query_record) : f4_install_witness option = {
   var x, ok;
   x <- f4_challenger_tag q query_count global_epoch false false;
   ok <@ B.welcome_install(x);
   (* The option reports the API result only. DIRECT setup can return an
      error after the GROUP transaction and before DEVICE consumption. *)
   bad_challenge <- true;
   public_queries <- public_queries ++ [x];
   query_count <- query_count + 1;
   return ok;
 }
 proc resync_install(q : f4_query_record) : f4_install_witness option = {
   var x, ok;
   x <- f4_challenger_tag q query_count global_epoch false false;
   ok <@ B.resync_install(x);
   (* Replacement may have committed REMOVE when applying JOIN fails.
      Neither return variant establishes a complete private footprint. *)
   bad_challenge <- true;
   public_queries <- public_queries ++ [x];
   query_count <- query_count + 1;
   return ok;
 }
 proc challenge(q : f4_query_record, ctx : context) : int list option = {
   var x, out, fresh, bytes;
   x <- f4_challenger_tag q query_count global_epoch false false;
   out <- None;
   if (bad_challenge \/ challenge_selected \/ !f4_gate_fresh exposures x \/
       (f4_exposed_before_challenge exposures x \/ f4_group_capture_before exposures x)) {
     bad_challenge <- true;
   } else {
     fresh <@ B.check_freshq(x, public_queries, exposures);
     if (!fresh) {
       bad_challenge <- true;
     } else {
       (* Select exactly one test. Subsequent native corrupt/reveal
          calls still occur, preserving source traces; any successful
          disclosure after this point marks bad_challenge. Security
          bounds therefore apply only when this bad event is excluded. *)
       challenge_selected <- true;
       out <@ B.selected_exporter(x, ctx);
       if (out = None \/ size (oget out) <> 32 \/
           !all (fun b => 0 <= b < 256) (oget out)) {
         out <- None;
         bad_challenge <- true;
       } else {
         if (!bit) {
           bytes <$ dlist (dinter 0 255) 32;
           out <- Some bytes;
         }
       }
     }
   }
   public_queries <- public_queries ++ [x];
   query_count <- query_count + 1;
   return out;
 }
 proc bad() : bool = { return bad_challenge; }
}.

module F4AdaptiveReal(B:F4ProductPCSBackend, A:F4AdaptivePCSAdversary) = {
 proc main() : bool = {
   var output;
   F4Challenger(B).initialize(true);
   output <@ A(F4Challenger(B)).guess();
   return output;
 }
}.

module F4AdaptiveIdeal(B:F4ProductPCSBackend, A:F4AdaptivePCSAdversary) = {
 proc main() : bool = {
   var output;
   F4Challenger(B).initialize(false);
   output <@ A(F4Challenger(B)).guess();
   return output;
 }
}.

(* The challenger controls query indices and tags. Corrupt/reveal methods
   cannot be relabeled as benign by an adversary submitting false flags. *)
(* A backend Some is NOT acceptance by itself: the challenger advances only
   when the authenticated native successor's group/head/parent/epoch follows
   the last selected canonical state. Failed or replayed transitions cannot
   advance its epoch. Installations without native linkage poison the test. *)
lemma f4_challenger_forced_epoch
    (q : f4_query_record) (i epoch : int)
    (c r : bool) :
  (f4_challenger_tag q i epoch c r).`f4_q_epoch = epoch.
proof.
  by rewrite /f4_challenger_tag.
qed.

lemma f4_challenger_epoch_ignores_adversarial_hint
    (q ch : f4_query_record) (i epoch : int)
    (c r : bool) :
  (f4_challenger_tag q i epoch c r).`f4_q_epoch =
  (f4_challenger_tag ch i epoch c r).`f4_q_epoch.
proof.
  by rewrite /f4_challenger_tag.
qed.

lemma f4_forced_corruption_is_detected_at_next_query
    (q ch : f4_query_record) (i epoch : int) :
  q.`f4_q_member = ch.`f4_q_member =>
  q.`f4_q_device = ch.`f4_q_device =>
  q.`f4_q_secret_kind = ch.`f4_q_secret_kind =>
  f4_exposed_before_challenge
    [f4_challenger_tag q i epoch true false]
    (f4_challenger_tag ch (i+1) epoch false false).
proof.
  rewrite /f4_exposed_before_challenge /= /f4_prior_exposure_for
          /f4_challenger_tag.
  by smt().
qed.

lemma f4_forced_reveal_is_detected_at_next_query
    (q ch : f4_query_record) (i epoch : int) :
  q.`f4_q_member = ch.`f4_q_member =>
  q.`f4_q_device = ch.`f4_q_device =>
  q.`f4_q_secret_kind = ch.`f4_q_secret_kind =>
  f4_exposed_before_challenge
    [f4_challenger_tag q i epoch false true]
    (f4_challenger_tag ch (i+1) epoch false false).
proof.
  rewrite /f4_exposed_before_challenge /= /f4_prior_exposure_for
          /f4_challenger_tag.
  by smt().
qed.
