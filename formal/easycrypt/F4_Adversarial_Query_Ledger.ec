require import AllCore Int List.

(* F4 query-ledger lemma: preserve corruption/reveal chronology, targets and
   chosen challenge position. This is a finite typed MODELLING obligation:
   it does not assert native Rust/OpenMLS trace completeness, and does NOT
   replace T1's FreshQ or the provider's computational PCS/QPT game. *)

type f4_member_id.
type f4_device_id.
type f4_secret_kind_id.

type f4_query_record = {
  f4_q_index : int;
  f4_q_epoch : int;
  f4_q_member : f4_member_id;
  f4_q_device : f4_device_id;
  f4_q_secret_kind : f4_secret_kind_id;
  f4_q_corrupt : bool;
  f4_q_reveal : bool;
}.

op f4_prior_exposure_for
    (q ch : f4_query_record) : bool =
  (q.`f4_q_corrupt \/ q.`f4_q_reveal) /\
  q.`f4_q_index < ch.`f4_q_index /\
  q.`f4_q_epoch = ch.`f4_q_epoch /\
  q.`f4_q_member = ch.`f4_q_member /\
  q.`f4_q_device = ch.`f4_q_device /\
  q.`f4_q_secret_kind = ch.`f4_q_secret_kind.

op f4_exposed_before_challenge
    (events : f4_query_record list) (ch : f4_query_record) : bool =
  has (fun q => f4_prior_exposure_for q ch) events.

op f4_clear_of_prior_matching_exposure
    (events : f4_query_record list) (ch : f4_query_record) : bool =
  !f4_exposed_before_challenge events ch.

lemma f4_corrupt_or_reveal_preceding_challenge_blocks
    (q ch : f4_query_record) (suffix : f4_query_record list) :
  (q.`f4_q_corrupt \/ q.`f4_q_reveal) =>
  q.`f4_q_index < ch.`f4_q_index =>
  q.`f4_q_epoch = ch.`f4_q_epoch =>
  q.`f4_q_member = ch.`f4_q_member =>
  q.`f4_q_device = ch.`f4_q_device =>
  q.`f4_q_secret_kind = ch.`f4_q_secret_kind =>
  !f4_clear_of_prior_matching_exposure (q :: suffix) ch.
proof.
  rewrite /f4_clear_of_prior_matching_exposure
          /f4_exposed_before_challenge /= /f4_prior_exposure_for.
  by smt().
qed.

lemma f4_prior_exposure_cannot_be_healed_by_appending
    (prefix suffix : f4_query_record list) (ch : f4_query_record) :
  f4_exposed_before_challenge prefix ch =>
  f4_exposed_before_challenge (prefix ++ suffix) ch.
proof.
  rewrite /f4_exposed_before_challenge has_cat.
  by smt().
qed.

lemma f4_prior_exposure_preserves_exact_query_index
    (q ch : f4_query_record) :
  ch.`f4_q_index <= q.`f4_q_index =>
  !f4_prior_exposure_for q ch.
proof.
  rewrite /f4_prior_exposure_for.
  by smt().
qed.

lemma f4_prior_exposure_preserves_member_and_device
    (q ch : f4_query_record) :
  (q.`f4_q_member <> ch.`f4_q_member \/
   q.`f4_q_device <> ch.`f4_q_device) =>
  !f4_prior_exposure_for q ch.
proof.
  rewrite /f4_prior_exposure_for.
  by smt().
qed.

lemma f4_prior_exposure_preserves_secret_kind
    (q ch : f4_query_record) :
  q.`f4_q_secret_kind <> ch.`f4_q_secret_kind =>
  !f4_prior_exposure_for q ch.
proof.
  rewrite /f4_prior_exposure_for.
  by smt().
qed.

lemma f4_public_adversarial_ledger_equality_preserves_bad
    (real ideal : f4_query_record list) (ch : f4_query_record) :
  real = ideal =>
  f4_exposed_before_challenge real ch =
  f4_exposed_before_challenge ideal ch.
proof.
  by move=> ->.
qed.


(* A previous-epoch exposure is deliberately NOT caught by the exact-epoch
   guard. This is a proved counterexample to treating the guard as PCS
   freshness: the actual healing/dependency check MUST come from a separate
   native-backed FreshQ proof, including external operations. *)
lemma f4_cross_epoch_exposure_not_detected_by_exact_epoch_guard
    (q ch : f4_query_record) :
  q.`f4_q_epoch <> ch.`f4_q_epoch =>
  !f4_prior_exposure_for q ch.
proof.
  rewrite /f4_prior_exposure_for.
  by smt().
qed.

lemma f4_cross_epoch_corruption_singleton_guard_is_clear
    (q ch : f4_query_record) :
  q.`f4_q_epoch <> ch.`f4_q_epoch =>
  f4_clear_of_prior_matching_exposure [q] ch.
proof.
  rewrite /f4_clear_of_prior_matching_exposure
          /f4_exposed_before_challenge /= /f4_prior_exposure_for.
  by smt().
qed.
