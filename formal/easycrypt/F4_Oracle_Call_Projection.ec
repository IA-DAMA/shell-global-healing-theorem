require import AllCore.
require import F4_Typed_Challenge_Model F4_Signed_Authority_Refinement_Conditional.

(* Concrete public call shape of the F4 candidate. No new axioms and no
   opaque provider-PCS call is asserted to implement this structure. The
   executed Rust adapter passes exporter label/context/length to OpenMLS. *)

type f4_oracle_call = {
  f4_oc_domain : f4_domain;
  f4_oc_provider_id : f4_provider_id;
  f4_oc_provider_version : f4_provider_version;
  f4_oc_suite : f4_suite;
  f4_oc_group_id : f4_group_id;
  f4_oc_head : f4_head;
  f4_oc_parent : f4_parent;
  f4_oc_epoch : int;
  f4_oc_membership_digest : f4_membership_digest;
  f4_oc_generator : f4_generator;
  f4_oc_authenticator : f4_authenticator;
  f4_oc_exporter_label : f4_exporter_label;
  f4_oc_exporter_context : f4_exporter_context;
  f4_oc_purpose : f4_purpose;
  f4_oc_length : int;
  f4_oc_accepted : bool;
}.

op f4_shell_oracle_call (s : f4_shell) : f4_oracle_call =
  {| f4_oc_domain = f4_s_domain s;
    f4_oc_provider_id = f4_s_provider_id s;
    f4_oc_provider_version = f4_s_provider_version s;
    f4_oc_suite = f4_s_suite s;
    f4_oc_group_id = f4_s_group_id s;
    f4_oc_head = f4_s_head s;
    f4_oc_parent = f4_s_parent s;
    f4_oc_epoch = f4_s_epoch s;
    f4_oc_membership_digest = f4_s_membership_digest s;
    f4_oc_generator = f4_s_generator s;
    f4_oc_authenticator = f4_s_authenticator s;
    f4_oc_exporter_label = f4_s_exporter_label s;
    f4_oc_exporter_context = f4_s_exporter_context s;
    f4_oc_purpose = f4_s_purpose s;
    f4_oc_length = f4_s_length s;
    f4_oc_accepted = f4_shell_accepted s |}.

op f4_provider_oracle_call (p : f4_provider) : f4_oracle_call =
  {| f4_oc_domain = f4_p_domain p;
    f4_oc_provider_id = f4_p_provider_id p;
    f4_oc_provider_version = f4_p_provider_version p;
    f4_oc_suite = f4_p_suite p;
    f4_oc_group_id = f4_p_group_id p;
    f4_oc_head = f4_p_head p;
    f4_oc_parent = f4_p_parent p;
    f4_oc_epoch = f4_p_epoch p;
    f4_oc_membership_digest = f4_p_membership_digest p;
    f4_oc_generator = f4_p_generator p;
    f4_oc_authenticator = f4_p_authenticator p;
    f4_oc_exporter_label = f4_p_exporter_label p;
    f4_oc_exporter_context = f4_p_exporter_context p;
    f4_oc_purpose = f4_p_purpose p;
    f4_oc_length = f4_p_length p;
    f4_oc_accepted = f4_provider_accepted p /\ f4_provider_no_pending p /\ f4_peer_accepted p /\ f4_exporter_peer_equal p |}.

op f4_candidate_oracle_call (c : f4_candidate) : f4_oracle_call =
  {| f4_oc_domain = f4_c_domain c;
    f4_oc_provider_id = f4_c_provider_id c;
    f4_oc_provider_version = f4_c_provider_version c;
    f4_oc_suite = f4_c_suite c;
    f4_oc_group_id = f4_c_group_id c;
    f4_oc_head = f4_c_head c;
    f4_oc_parent = f4_c_parent c;
    f4_oc_epoch = f4_c_epoch c;
    f4_oc_membership_digest = f4_c_membership_digest c;
    f4_oc_generator = f4_c_generator c;
    f4_oc_authenticator = f4_c_authenticator c;
    f4_oc_exporter_label = f4_c_exporter_label c;
    f4_oc_exporter_context = f4_c_exporter_context c;
    f4_oc_purpose = f4_c_purpose c;
    f4_oc_length = f4_c_length c;
    f4_oc_accepted = f4_candidate_accepted c |}.

(* Positive, definitional statement: once BOTH independently computed public
   candidate and provider fields pass the verified F4 gate, the EXACT public
   oracle arguments agree. This is the deterministic API argument bridge. *)
lemma f4_typed_oracle_call_alignment
    (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_guard s p c =>
  f4_shell_oracle_call s = f4_provider_oracle_call p /\
  f4_shell_oracle_call s = f4_candidate_oracle_call c.
proof.
  rewrite /f4_guard /f4_shell_matches /f4_provider_matches
          /f4_shell_oracle_call /f4_provider_oracle_call
          /f4_candidate_oracle_call.
  by smt().
qed.

lemma f4_external_selection_aligns_oracle_calls
    (a : f4_external_authority) (w : f4_signed_selection)
    (key : f4_signer_key) (s : f4_shell)
    (p : f4_provider) (c : f4_candidate) :
  f4_external_gate a w key s p c =>
  f4_shell_oracle_call s = f4_provider_oracle_call p /\
  f4_shell_oracle_call s = f4_candidate_oracle_call c.
proof.
  rewrite /f4_external_gate.
  by move=> [_ [_ [_ [_ [_ [_ [_ h]]]]]]];
     exact (f4_typed_oracle_call_alignment s p c h).
qed.

(* Individual exporter call arguments are a subprojection of the full
   challenge. Equality is established without a PCS hardness or OpenMLS
   implementation claim; a real/ideal oracle game still needs a refinement. *)
type f4_exporter_call = {
  f4_ex_label : f4_exporter_label;
  f4_ex_context : f4_exporter_context;
  f4_ex_length : int;
}.

op f4_exporter_from_call (o : f4_oracle_call) : f4_exporter_call =
  {| f4_ex_label = o.`f4_oc_exporter_label;
    f4_ex_context = o.`f4_oc_exporter_context;
    f4_ex_length = o.`f4_oc_length |}.

lemma f4_exporter_call_alignment
    (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_guard s p c =>
  f4_exporter_from_call (f4_shell_oracle_call s) =
  f4_exporter_from_call (f4_provider_oracle_call p) /\
  f4_exporter_from_call (f4_provider_oracle_call p) =
  f4_exporter_from_call (f4_candidate_oracle_call c).
proof.
  move=> h.
  have [hsp hsc] := f4_typed_oracle_call_alignment s p c h.
  split.
  + by rewrite hsp.
  + by rewrite -hsp hsc.
qed.
