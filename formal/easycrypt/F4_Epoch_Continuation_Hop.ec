require import AllCore Int DInterval StdOrder.
require import F4_Oracle_Call_Projection F4_OpenMLS_Exporter_Algorithm F4_OpenMLS_Exporter_Program.
import RealOrder.

(* One selected, active successful internal commit in the SHA-384 profile.
   Prefix.sample is upstream of confirmation. Its auxiliary view can contain
   the retained state, auxiliary correlations and available path ciphertexts;
   whether an actual path hop is sound for that joint view is a separate
   obligation. Descendants of the replaced secret must be recomputed. *)
type f4_prior_view.
type f4_group_context_bytes.
type f4_confirmed_transcript_hash.
type f4_confirmation_tag.
type f4_authenticator_digest.
type f4_signed_group_info_digest.
type f4_selection_inputs.
type f4_prefix = {
  old_view : f4_prior_view;
  init_input : f4_kdf_secret;
  psk_input : f4_kdf_secret;
  group_ctx : f4_group_context_bytes;
  confirmed_hash : f4_confirmed_transcript_hash;
  selection_inputs : f4_selection_inputs
}.

type f4_epoch_public = {
  epoch_tag : f4_confirmation_tag;
  auth_digest : f4_authenticator_digest;
  info_digest : f4_signed_group_info_digest;
  selected_call : f4_oracle_call
}.

(* Distinct fallible operations: Extract(init,commit) + Expand("joiner",ctx),
   Extract(joiner,psk), Expand("epoch",ctx), then labelled epoch branches.
   The tag operation includes the confirmation key and confirmed transcript
   hash. The exporter branch uses the MIR projection on the derived key.
   No ideal-PRF law is asserted for these operators. *)
op f4_joiner_from_commit : f4_kdf_secret -> int -> f4_group_context_bytes -> f4_kdf_secret option.
op f4_intermediate_from_psk : f4_kdf_secret -> f4_kdf_secret -> f4_kdf_secret option.
op f4_epoch_from_context : f4_kdf_secret -> f4_group_context_bytes -> f4_kdf_secret option.
op f4_confirmation_from_epoch : f4_kdf_secret -> f4_confirmed_transcript_hash -> f4_confirmation_tag option.
op f4_exporter_from_epoch : f4_kdf_secret -> f4_kdf_secret option.
op f4_auth_digest_from_epoch : f4_kdf_secret -> f4_authenticator_digest option.
op f4_final_info : f4_selection_inputs -> f4_confirmation_tag ->
                   f4_signed_group_info_digest option.
op f4_build_call : f4_selection_inputs -> f4_signed_group_info_digest ->
                   f4_authenticator_digest -> f4_oracle_call option.
(* Interpret the actual returned 32 bytes as an unsigned integer. The
   native decoding correspondence belongs to the implementation boundary. *)
op f4_decode_bytes32 : f4_derived_bytes -> int.

type f4_selected_observation = (f4_epoch_public * int option) option.
op f4_run_selected (p : f4_prefix) (commit : int) : f4_selected_observation =
  let j = f4_joiner_from_commit p.`init_input commit p.`group_ctx in
  if j = None then None else
  let i = f4_intermediate_from_psk (oget j) p.`psk_input in
  if i = None then None else
  let e = f4_epoch_from_context (oget i) p.`group_ctx in
  if e = None then None else
  let k = f4_exporter_from_epoch (oget e) in
  if k = None then None else
  let tag = f4_confirmation_from_epoch (oget e) p.`confirmed_hash in
  if tag = None then None else
  let auth = f4_auth_digest_from_epoch (oget e) in
  if auth = None then None else
  let info = f4_final_info p.`selection_inputs (oget tag) in
  if info = None then None else
  let oc = f4_build_call p.`selection_inputs (oget info) (oget auth) in
  if oc = None then None else
  let pub = {| epoch_tag = oget tag; auth_digest = oget auth;
               info_digest = oget info; selected_call = oget oc |} in
  let out = if (oget oc).`f4_oc_length <> 32 then None else
            (f4_mir_derive_with_key (oget k) (oget oc)).`2 in
  if out = None then Some (pub, None) else
  let n = f4_decode_bytes32 (oget out) in
  Some (pub, if 0 <= n < 2^256 then Some n else None).

module type F4PrefixSource = { proc sample() : f4_prefix * int }.
module type F4ReadSelected = {
  proc decide(v : f4_prior_view, obs : f4_selected_observation) : bool
}.
module type F4ReadCommit = { proc decide(p : f4_prefix, commit : int) : bool }.

module F4FinishEpoch(A:F4ReadSelected) = {
  proc run(random_output : bool, p : f4_prefix, k : int) : bool = {
    var b, obs, u;
    obs <- f4_run_selected p k;
    if (random_output /\ obs <> None /\ (oget obs).`2 <> None) {
      u <$ dinter 0 (2^256 - 1);
      obs <- Some ((oget obs).`1, Some u);
    }
    b <@ A.decide(p.`old_view,obs);
    return b;
  }
}.
module F4CommitReduction(A:F4ReadSelected) = {
  proc decide(p : f4_prefix, commit : int) : bool = {
    var b;
    b <@ F4FinishEpoch(A).run(false,p,commit);
    return b;
  }
}.

module F4CommitExperiment(S:F4PrefixSource,D:F4ReadCommit) = {
  proc main(uniform_path : bool) : bool = {
    var p, k, b;
    (p,k) <@ S.sample();
    if (uniform_path) { k <$ dinter 0 (2^384 - 1); }
    b <@ D.decide(p,k);
    return b;
  }
}.

module F4SelectedExperiment(S:F4PrefixSource,A:F4ReadSelected) = {
  proc main(uniform_path : bool) : bool = {
    var p, k, b;
    (p,k) <@ S.sample();
    if (uniform_path) { k <$ dinter 0 (2^384 - 1); }
    b <@ F4FinishEpoch(A).run(false,p,k);
    return b;
  }
}.

module F4RandomSelectedExperiment(S:F4PrefixSource,A:F4ReadSelected) = {
  proc main(uniform_path : bool) : bool = {
    var p, k, b;
    (p,k) <@ S.sample();
    if (uniform_path) { k <$ dinter 0 (2^384 - 1); }
    b <@ F4FinishEpoch(A).run(true,p,k);
    return b;
  }
}.

lemma f4_selected_commit_hop_exact
    (S <: F4PrefixSource) (A <: F4ReadSelected{-S}) uniform_path &m :
  Pr[F4SelectedExperiment(S,A).main(uniform_path) @ &m : res] =
  Pr[F4CommitExperiment(S,F4CommitReduction(A)).main(uniform_path) @ &m : res].
proof.
  byequiv (_: ={glob S,glob A} /\ ={arg} ==> ={res}) => //.
  proc; inline F4CommitReduction(A).decide.
  sim; smt().
qed.

(* Real vs ideal challenge must keep the REAL transcript distribution. Use
   the path hop twice: once for the real challenge and once for the random
   challenge. A one-hop comparison ending on a replaced public transcript
   would be a different experiment. *)
module F4RandomOutputReduction(A:F4ReadSelected) = {
  proc decide(p : f4_prefix, commit : int) : bool = {
    var b;
    b <@ F4FinishEpoch(A).run(true,p,commit);
    return b;
  }
}.

lemma f4_random_output_commit_hop_exact
    (S <: F4PrefixSource) (A <: F4ReadSelected{-S}) uniform_path &m :
  Pr[F4RandomSelectedExperiment(S,A).main(uniform_path) @ &m : res] =
  Pr[F4CommitExperiment(S,F4RandomOutputReduction(A)).main(uniform_path) @ &m : res].
proof.
  byequiv (_: ={glob S,glob A} /\ ={arg} ==> ={res}) => //.
  proc; inline F4RandomOutputReduction(A).decide; sim; smt().
qed.

lemma f4_one_epoch_recovery_bound
    (S <: F4PrefixSource) (A <: F4ReadSelected{-S}) e1 ek e2 &m :
  `|Pr[F4CommitExperiment(S,F4CommitReduction(A)).main(false) @ &m : res] -
    Pr[F4CommitExperiment(S,F4CommitReduction(A)).main(true) @ &m : res]| <= e1 =>
  `|Pr[F4SelectedExperiment(S,A).main(true) @ &m : res] -
    Pr[F4RandomSelectedExperiment(S,A).main(true) @ &m : res]| <= ek =>
  `|Pr[F4CommitExperiment(S,F4RandomOutputReduction(A)).main(true) @ &m : res] -
    Pr[F4CommitExperiment(S,F4RandomOutputReduction(A)).main(false) @ &m : res]| <= e2 =>
  `|Pr[F4SelectedExperiment(S,A).main(false) @ &m : res] -
    Pr[F4RandomSelectedExperiment(S,A).main(false) @ &m : res]| <= e1 + ek + e2.
proof.
  move=> h1 hk h2.
  rewrite -(f4_selected_commit_hop_exact S A false &m)
          -(f4_selected_commit_hop_exact S A true &m) in h1.
  rewrite -(f4_random_output_commit_hop_exact S A true &m)
          -(f4_random_output_commit_hop_exact S A false &m) in h2.
  smt(RealOrder.ler_dist_add).
qed.
