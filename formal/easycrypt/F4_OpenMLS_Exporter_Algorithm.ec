require import AllCore Int.
require import F4_Typed_Challenge_Model F4_Oracle_Call_Projection.

(* OpenMLS 0.9.0 export_secret algorithmic boundary, modeled with explicit
   call shape and KDF stages, NOT new cryptographic security axioms.

   Actual upstream source at openmls-v0.9.0:
     openmls/src/group/mls_group/exporting.rs: MlsGroup::export_secret
     openmls/src/schedule/mod.rs: ExporterSecret::new and
                                   derive_exported_secret

   exporter_secret = DeriveSecret(epoch_secret, "exporter")
   exported_key = ExpandWithLabel(DeriveSecret(exporter_secret, label),
                    "exported", Hash(context), key_length)

   The secrets and KDF operators remain uninterpreted pure operations.
   This is an algebraic API trace, NOT a machine-checked translation from Rust. *)

type f4_kdf_secret.
type f4_kdf_label.
type f4_context_hash.
type f4_derived_bytes.

op f4_internal_exported_label : f4_kdf_label.
op f4_user_exporter_label : f4_exporter_label -> f4_kdf_label.

(* The epoch exporter secret is already stored at entry. A provider call can
   fail even for a valid output length. No successful primitive is assumed. *)
op f4_active_group : f4_provider -> bool.
op f4_stored_exporter_secret : f4_provider -> f4_kdf_secret.
op f4_hash_bytes : f4_suite -> int.
op f4_derive_secret : f4_suite -> f4_kdf_secret -> f4_kdf_label -> f4_kdf_secret option.
op f4_context_hash : f4_suite -> f4_exporter_context -> f4_context_hash option.
op f4_kdf_expand_with_label :
    f4_suite -> f4_kdf_secret -> f4_kdf_label -> f4_context_hash ->
    int -> f4_derived_bytes option.

op f4_expand_length_supported (hash_bytes n : int) =
  0 < n /\ n <= 255 * hash_bytes.

op f4_exporter_derive (p : f4_provider) (o : f4_oracle_call) : f4_derived_bytes option =
  let suite = o.`f4_oc_suite in
  let h = f4_context_hash suite o.`f4_oc_exporter_context in
  if h = None then None else
  let k = f4_derive_secret suite (f4_stored_exporter_secret p)
            (f4_user_exporter_label o.`f4_oc_exporter_label) in
  if k = None then None else
  if !f4_expand_length_supported (f4_hash_bytes suite) o.`f4_oc_length then None else
  f4_kdf_expand_with_label suite (oget k) f4_internal_exported_label
    (oget h) o.`f4_oc_length.

(* The real Rust entrypoint rejects length greater than u16::MAX and
   non-active groups. The < 0 branch is the int-to-usize domain boundary. *)
op f4_exporter_result (p : f4_provider) (o : f4_oracle_call) :
      f4_derived_bytes option =
  if o.`f4_oc_length < 0 \/ 65535 < o.`f4_oc_length then None
  else if ! f4_active_group p then None
  else f4_exporter_derive p o.

lemma f4_exporter_rejects_unsupported_length p o :
  !f4_expand_length_supported (f4_hash_bytes o.`f4_oc_suite) o.`f4_oc_length =>
  f4_exporter_result p o = None.
proof. rewrite /f4_exporter_result /f4_exporter_derive; smt(). qed.

lemma f4_sha384_exporter_boundaries :
  !f4_expand_length_supported 48 0 /\ f4_expand_length_supported 48 32 /\
  f4_expand_length_supported 48 12240 /\ !f4_expand_length_supported 48 12241.
proof. by rewrite /f4_expand_length_supported. qed.

lemma f4_exporter_algorithm_selected_call_equality
    (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_guard s p c =>
  f4_exporter_result p (f4_shell_oracle_call s) =
  f4_exporter_result p (f4_provider_oracle_call p).
proof.
  move=> hg.
  have [hsp _] := f4_typed_oracle_call_alignment s p c hg.
  by rewrite hsp.
qed.

lemma f4_exporter_algorithm_candidate_call_equality
    (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_guard s p c =>
  f4_exporter_result p (f4_provider_oracle_call p) =
  f4_exporter_result p (f4_candidate_oracle_call c).
proof.
  move=> hg.
  have [hsp hsc] := f4_typed_oracle_call_alignment s p c hg.
  by rewrite -hsp hsc.
qed.

lemma f4_exporter_selected_call_not_bad
    (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_guard s p c =>
  ! f4_bad_challenge s p c /\
  f4_exporter_result p (f4_shell_oracle_call s) =
  f4_exporter_result p (f4_candidate_oracle_call c).
proof.
  move=> hg.
  have hb := f4_accepted_excludes_bad_challenge s p c hg.
  have [hsp hsc] := f4_typed_oracle_call_alignment s p c hg.
  split; first exact hb.
  by rewrite hsc.
qed.
