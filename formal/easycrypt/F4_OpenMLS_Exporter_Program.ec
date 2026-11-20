require import AllCore Int List.
require import F4_Typed_Challenge_Model F4_Oracle_Call_Projection.
require import F4_OpenMLS_Exporter_Algorithm.
require import F4_OpenMLS_Exporter_MIR.

(* All valid sizes, activity states, log choices and normal provider returns.
   Collapsing Rust error variants to inner None is the observation boundary. *)
lemma f4_mir_normal_return n active static_log runtime_log derived :
  f4_export_mir n active static_log runtime_log derived =
    Some (if 65535 < n \/ !active then None else derived).
proof. rewrite /f4_export_mir. case: derived => //=; smt(). qed.

lemma f4_mir_exporter_result p o static_log runtime_log :
  0 <= o.`f4_oc_length =>
  f4_export_mir o.`f4_oc_length (f4_active_group p) static_log runtime_log
    (f4_exporter_derive p o) = Some (f4_exporter_result p o).
proof. rewrite f4_mir_normal_return /f4_exporter_result; smt(). qed.

(* Primitive return values and the byte copy are interpreted at the API
   boundary. The trace is the list of primitive calls actually reached. *)
op f4_mir_derive_with_key exporter_key (o : f4_oracle_call) =
  let suite = o.`f4_oc_suite in
  let h = f4_context_hash suite o.`f4_oc_exporter_context in
  let k = f4_derive_secret suite exporter_key
            (f4_user_exporter_label o.`f4_oc_exporter_label) in
  let out = if f4_expand_length_supported (f4_hash_bytes suite) o.`f4_oc_length
            then f4_kdf_expand_with_label suite (oget k) f4_internal_exported_label
                   (oget h) o.`f4_oc_length else None in
  f4_derive_mir h k out.

op f4_mir_derive_call p o = f4_mir_derive_with_key (f4_stored_exporter_secret p) o.

lemma f4_mir_derive_result p o :
  (f4_mir_derive_call p o).`2 = f4_exporter_derive p o.
proof. rewrite /f4_mir_derive_call /f4_mir_derive_with_key /f4_derive_mir /f4_exporter_derive; smt(). qed.

lemma f4_nested_mir_exporter_result p o static_log runtime_log :
  0 <= o.`f4_oc_length =>
  f4_export_mir o.`f4_oc_length (f4_active_group p) static_log runtime_log
    (f4_mir_derive_call p o).`2 = Some (f4_exporter_result p o).
proof. by rewrite f4_mir_derive_result; apply f4_mir_exporter_result. qed.

lemma f4_mir_primitive_call_order h k out :
  (f4_derive_mir h k out).`1 =
    (if h = None then [ContextHash] else if k = None then [ContextHash; DeriveLabel]
     else [ContextHash; DeriveLabel; ExpandExported]).
proof. rewrite /f4_derive_mir; smt(). qed.

(* Explicit imperative approximation of OpenMLS 0.9 exporter entrypoint.
   Deterministic source-level steps, with no ad hoc cryptographic axioms.
   Distinct Rust error variants are abstracted to None because only the
   successful, accepted-state output is sent to the PCS challenge contract. *)

module F4OpenMLSExporterProgram = {
  proc derive(p : f4_provider, o : f4_oracle_call) : f4_derived_bytes option = {
    var r, exporter_key, context_hash, labeled_key;
    if (o.`f4_oc_length < 0 \/ 65535 < o.`f4_oc_length) {
      r <- None;
    } else {
      if (! f4_active_group p) {
        r <- None;
      } else {
        exporter_key <- f4_stored_exporter_secret p;
        context_hash <- f4_context_hash
          o.`f4_oc_suite o.`f4_oc_exporter_context;
        r <- None;
        if (context_hash <> None) {
          labeled_key <- f4_derive_secret o.`f4_oc_suite exporter_key
            (f4_user_exporter_label o.`f4_oc_exporter_label);
          if (labeled_key <> None /\
              f4_expand_length_supported (f4_hash_bytes o.`f4_oc_suite) o.`f4_oc_length) {
            r <- f4_kdf_expand_with_label o.`f4_oc_suite (oget labeled_key)
              f4_internal_exported_label (oget context_hash) o.`f4_oc_length;
          }
        }
      }
    }
    return r;
  }
}.

module F4OpenMLSExporterReference = {
  proc derive(p : f4_provider, o : f4_oracle_call) : f4_derived_bytes option = {
    var r;
    r <- f4_exporter_result p o;
    return r;
  }
}.

lemma f4_openmls_exporter_program_refines_algorithm :
  equiv [F4OpenMLSExporterProgram.derive ~
         F4OpenMLSExporterReference.derive :
         ={p,o} ==> ={res}].
proof.
  proc.
  wp.
  skip.
  rewrite /f4_exporter_result /f4_exporter_derive.
  by smt().
qed.
