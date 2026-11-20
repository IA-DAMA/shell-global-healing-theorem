require import AllCore.

(* Model-level F4 challenge correspondence. This file deliberately does not
   assert that the real Rust/OpenMLS adapter refines these uninterpreted
   observation functions; that implementation theorem is a separate step. *)

type f4_shell.
type f4_provider.
type f4_candidate.
type f4_domain.
type f4_provider_id.
type f4_provider_version.
type f4_suite.
type f4_group_id.
type f4_head.
type f4_parent.
type f4_membership_digest.
type f4_generator.
type f4_authenticator.
type f4_exporter_label.
type f4_exporter_context.
type f4_purpose.

op f4_s_domain : f4_shell -> f4_domain.
op f4_p_domain : f4_provider -> f4_domain.
op f4_c_domain : f4_candidate -> f4_domain.
op f4_s_provider_id : f4_shell -> f4_provider_id.
op f4_p_provider_id : f4_provider -> f4_provider_id.
op f4_c_provider_id : f4_candidate -> f4_provider_id.
op f4_s_provider_version : f4_shell -> f4_provider_version.
op f4_p_provider_version : f4_provider -> f4_provider_version.
op f4_c_provider_version : f4_candidate -> f4_provider_version.
op f4_s_suite : f4_shell -> f4_suite.
op f4_p_suite : f4_provider -> f4_suite.
op f4_c_suite : f4_candidate -> f4_suite.
op f4_s_group_id : f4_shell -> f4_group_id.
op f4_p_group_id : f4_provider -> f4_group_id.
op f4_c_group_id : f4_candidate -> f4_group_id.
op f4_s_head : f4_shell -> f4_head.
op f4_p_head : f4_provider -> f4_head.
op f4_c_head : f4_candidate -> f4_head.
op f4_s_parent : f4_shell -> f4_parent.
op f4_p_parent : f4_provider -> f4_parent.
op f4_c_parent : f4_candidate -> f4_parent.
op f4_s_epoch : f4_shell -> int.
op f4_p_epoch : f4_provider -> int.
op f4_c_epoch : f4_candidate -> int.
op f4_s_membership_digest : f4_shell -> f4_membership_digest.
op f4_p_membership_digest : f4_provider -> f4_membership_digest.
op f4_c_membership_digest : f4_candidate -> f4_membership_digest.
op f4_s_generator : f4_shell -> f4_generator.
op f4_p_generator : f4_provider -> f4_generator.
op f4_c_generator : f4_candidate -> f4_generator.
op f4_s_authenticator : f4_shell -> f4_authenticator.
op f4_p_authenticator : f4_provider -> f4_authenticator.
op f4_c_authenticator : f4_candidate -> f4_authenticator.
op f4_s_exporter_label : f4_shell -> f4_exporter_label.
op f4_p_exporter_label : f4_provider -> f4_exporter_label.
op f4_c_exporter_label : f4_candidate -> f4_exporter_label.
op f4_s_exporter_context : f4_shell -> f4_exporter_context.
op f4_p_exporter_context : f4_provider -> f4_exporter_context.
op f4_c_exporter_context : f4_candidate -> f4_exporter_context.
op f4_s_purpose : f4_shell -> f4_purpose.
op f4_p_purpose : f4_provider -> f4_purpose.
op f4_c_purpose : f4_candidate -> f4_purpose.
op f4_s_length : f4_shell -> int.
op f4_p_length : f4_provider -> int.
op f4_c_length : f4_candidate -> int.

op f4_shell_accepted : f4_shell -> bool.
op f4_provider_accepted : f4_provider -> bool.
op f4_provider_no_pending : f4_provider -> bool.
op f4_peer_accepted : f4_provider -> bool.
op f4_exporter_peer_equal : f4_provider -> bool.
op f4_candidate_accepted : f4_candidate -> bool.

op f4_shell_matches (s : f4_shell) (c : f4_candidate) : bool =
  f4_s_domain s = f4_c_domain c /\
  f4_s_provider_id s = f4_c_provider_id c /\
  f4_s_provider_version s = f4_c_provider_version c /\
  f4_s_suite s = f4_c_suite c /\
  f4_s_group_id s = f4_c_group_id c /\
  f4_s_head s = f4_c_head c /\
  f4_s_parent s = f4_c_parent c /\
  f4_s_epoch s = f4_c_epoch c /\
  f4_s_membership_digest s = f4_c_membership_digest c /\
  f4_s_generator s = f4_c_generator c /\
  f4_s_authenticator s = f4_c_authenticator c /\
  f4_s_exporter_label s = f4_c_exporter_label c /\
  f4_s_exporter_context s = f4_c_exporter_context c /\
  f4_s_purpose s = f4_c_purpose c /\
  f4_s_length s = f4_c_length c.

op f4_provider_matches (p : f4_provider) (c : f4_candidate) : bool =
  f4_p_domain p = f4_c_domain c /\
  f4_p_provider_id p = f4_c_provider_id c /\
  f4_p_provider_version p = f4_c_provider_version c /\
  f4_p_suite p = f4_c_suite c /\
  f4_p_group_id p = f4_c_group_id c /\
  f4_p_head p = f4_c_head c /\
  f4_p_parent p = f4_c_parent c /\
  f4_p_epoch p = f4_c_epoch c /\
  f4_p_membership_digest p = f4_c_membership_digest c /\
  f4_p_generator p = f4_c_generator c /\
  f4_p_authenticator p = f4_c_authenticator c /\
  f4_p_exporter_label p = f4_c_exporter_label c /\
  f4_p_exporter_context p = f4_c_exporter_context c /\
  f4_p_purpose p = f4_c_purpose c /\
  f4_p_length p = f4_c_length c.

op f4_challenge_same (s : f4_shell) (p : f4_provider) : bool =
  f4_s_domain s = f4_p_domain p /\
  f4_s_provider_id s = f4_p_provider_id p /\
  f4_s_provider_version s = f4_p_provider_version p /\
  f4_s_suite s = f4_p_suite p /\
  f4_s_group_id s = f4_p_group_id p /\
  f4_s_head s = f4_p_head p /\
  f4_s_parent s = f4_p_parent p /\
  f4_s_epoch s = f4_p_epoch p /\
  f4_s_membership_digest s = f4_p_membership_digest p /\
  f4_s_generator s = f4_p_generator p /\
  f4_s_authenticator s = f4_p_authenticator p /\
  f4_s_exporter_label s = f4_p_exporter_label p /\
  f4_s_exporter_context s = f4_p_exporter_context p /\
  f4_s_purpose s = f4_p_purpose p /\
  f4_s_length s = f4_p_length p.

op f4_guard (s : f4_shell) (p : f4_provider) (c : f4_candidate) : bool =
  f4_shell_accepted s /\ f4_provider_accepted p /\
  f4_provider_no_pending p /\ f4_peer_accepted p /\
  f4_exporter_peer_equal p /\ f4_candidate_accepted c /\
  f4_shell_matches s c /\ f4_provider_matches p c.

op f4_bad_challenge (s : f4_shell) (p : f4_provider) (c : f4_candidate) : bool =
  !f4_shell_accepted s \/ !f4_provider_accepted p \/
  !f4_provider_no_pending p \/ !f4_peer_accepted p \/
  !f4_exporter_peer_equal p \/ !f4_candidate_accepted c \/
  !f4_shell_matches s c \/ !f4_provider_matches p c \/
  !f4_challenge_same s p.

(* Independently checked shell and provider selectors agree by transitivity.
   No correspondence assertion is assumed as a premise. *)
lemma f4_candidate_two_sided_refines (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_guard s p c => f4_challenge_same s p.
proof.
  rewrite /f4_guard /f4_shell_matches /f4_provider_matches /f4_challenge_same.
  by smt().
qed.

lemma f4_guard_exactly_excludes_bad_challenge (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_guard s p c <=> !f4_bad_challenge s p c.
proof.
  rewrite /f4_guard /f4_bad_challenge /f4_challenge_same
          /f4_shell_matches /f4_provider_matches.
  by smt().
qed.

lemma f4_accepted_excludes_bad_challenge (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_guard s p c => !f4_bad_challenge s p c.
proof.
  rewrite /f4_guard /f4_bad_challenge /f4_challenge_same
          /f4_shell_matches /f4_provider_matches.
  by smt().
qed.

lemma f4_bad_challenge_rejects (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_bad_challenge s p c => !f4_guard s p c.
proof.
  rewrite /f4_guard /f4_bad_challenge /f4_challenge_same
          /f4_shell_matches /f4_provider_matches.
  by smt().
qed.

lemma f4_mutated_domain_rejected (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_s_domain s <> f4_c_domain c => !f4_guard s p c.
proof.
  rewrite /f4_guard /f4_shell_matches.
  by smt().
qed.

lemma f4_mutated_provider_id_rejected (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_s_provider_id s <> f4_c_provider_id c => !f4_guard s p c.
proof.
  rewrite /f4_guard /f4_shell_matches.
  by smt().
qed.

lemma f4_mutated_provider_version_rejected (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_s_provider_version s <> f4_c_provider_version c => !f4_guard s p c.
proof.
  rewrite /f4_guard /f4_shell_matches.
  by smt().
qed.

lemma f4_mutated_suite_rejected (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_s_suite s <> f4_c_suite c => !f4_guard s p c.
proof.
  rewrite /f4_guard /f4_shell_matches.
  by smt().
qed.

lemma f4_mutated_group_id_rejected (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_s_group_id s <> f4_c_group_id c => !f4_guard s p c.
proof.
  rewrite /f4_guard /f4_shell_matches.
  by smt().
qed.

lemma f4_mutated_head_rejected (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_s_head s <> f4_c_head c => !f4_guard s p c.
proof.
  rewrite /f4_guard /f4_shell_matches.
  by smt().
qed.

lemma f4_mutated_parent_rejected (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_s_parent s <> f4_c_parent c => !f4_guard s p c.
proof.
  rewrite /f4_guard /f4_shell_matches.
  by smt().
qed.

lemma f4_mutated_epoch_rejected (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_s_epoch s <> f4_c_epoch c => !f4_guard s p c.
proof.
  rewrite /f4_guard /f4_shell_matches.
  by smt().
qed.

lemma f4_mutated_membership_digest_rejected (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_s_membership_digest s <> f4_c_membership_digest c => !f4_guard s p c.
proof.
  rewrite /f4_guard /f4_shell_matches.
  by smt().
qed.

lemma f4_mutated_generator_rejected (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_s_generator s <> f4_c_generator c => !f4_guard s p c.
proof.
  rewrite /f4_guard /f4_shell_matches.
  by smt().
qed.

lemma f4_mutated_authenticator_rejected (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_s_authenticator s <> f4_c_authenticator c => !f4_guard s p c.
proof.
  rewrite /f4_guard /f4_shell_matches.
  by smt().
qed.

lemma f4_mutated_exporter_label_rejected (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_s_exporter_label s <> f4_c_exporter_label c => !f4_guard s p c.
proof.
  rewrite /f4_guard /f4_shell_matches.
  by smt().
qed.

lemma f4_mutated_exporter_context_rejected (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_s_exporter_context s <> f4_c_exporter_context c => !f4_guard s p c.
proof.
  rewrite /f4_guard /f4_shell_matches.
  by smt().
qed.

lemma f4_mutated_purpose_rejected (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_s_purpose s <> f4_c_purpose c => !f4_guard s p c.
proof.
  rewrite /f4_guard /f4_shell_matches.
  by smt().
qed.

lemma f4_mutated_length_rejected (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  f4_s_length s <> f4_c_length c => !f4_guard s p c.
proof.
  rewrite /f4_guard /f4_shell_matches.
  by smt().
qed.

lemma f4_unaccepted_candidate_rejected (s : f4_shell) (p : f4_provider) (c : f4_candidate) :
  !f4_candidate_accepted c => !f4_guard s p c.
proof.
  rewrite /f4_guard.
  by smt().
qed.
