require import AllCore Int List.

(* F4-E: challenger-owned adaptive-query ledger. This is an executable
   transition specification, NOT a refinement of Rust/OpenMLS and NOT a
   post-quantum PCS hardness theorem. The challenger records corrupt/reveal
   even when the product cannot observe an extraction. *)

type f4_adversarial_query = {
  f4_q_kind : int;
  f4_q_member : int;
  f4_q_device : int;
  f4_q_secret_kind : int;
  f4_q_challenge_id : int;
  f4_q_authenticated : bool;
}.

type f4_adversarial_entry = {
  f4_e_index : int;
  f4_e_query : f4_adversarial_query;
  f4_e_global_epoch_before : int;
}.

type f4_adversarial_state = {
  f4_s_global_epoch : int;
  f4_s_queries : f4_adversarial_entry list;
  f4_s_exposures : f4_adversarial_entry list;
  f4_s_challenges : f4_adversarial_entry list;
}.

(* Query tags: 1 corrupt; 2 reveal; 3 send; 4 accepted Commit;
   5 verified Welcome installation; 6 accepted external Commit;
   7 challenge. These are challenger operations, not runtime telemetry. *)
op f4_is_exposure (q : f4_adversarial_query) : bool =
  q.`f4_q_kind = 1 \/ q.`f4_q_kind = 2.

op f4_is_challenge (q : f4_adversarial_query) : bool =
  q.`f4_q_kind = 7.

op f4_advances_global_epoch (q : f4_adversarial_query) : bool =
  q.`f4_q_authenticated /\
  (q.`f4_q_kind = 4 \/ q.`f4_q_kind = 6).

op f4_before_entry (s : f4_adversarial_state)
                   (q : f4_adversarial_query) : f4_adversarial_entry =
  {| f4_e_index = size s.`f4_s_queries;
     f4_e_query = q;
     f4_e_global_epoch_before = s.`f4_s_global_epoch |}.

(* This operation never infers freshness or security from a local epoch.
   The accepted flag is still an abstract input until a separate verified
   Rust witness binds it to an authenticated commit or Welcome. *)
op f4_adversarial_step (s : f4_adversarial_state)
                       (q : f4_adversarial_query) : f4_adversarial_state =
  {| f4_s_global_epoch =
       s.`f4_s_global_epoch + (if f4_advances_global_epoch q then 1 else 0);
     f4_s_queries = s.`f4_s_queries ++ [f4_before_entry s q];
     f4_s_exposures =
       if f4_is_exposure q
       then s.`f4_s_exposures ++ [f4_before_entry s q]
       else s.`f4_s_exposures;
     f4_s_challenges =
       if f4_is_challenge q
       then s.`f4_s_challenges ++ [f4_before_entry s q]
       else s.`f4_s_challenges |}.

lemma f4_query_index_is_challenger_owned
    (s : f4_adversarial_state) (q : f4_adversarial_query) :
  (f4_before_entry s q).`f4_e_index = size s.`f4_s_queries.
proof.
  by rewrite /f4_before_entry.
qed.

lemma f4_query_records_pre_state_epoch
    (s : f4_adversarial_state) (q : f4_adversarial_query) :
  (f4_before_entry s q).`f4_e_global_epoch_before =
    s.`f4_s_global_epoch.
proof.
  by rewrite /f4_before_entry.
qed.

lemma f4_every_adversarial_query_is_recorded
    (s : f4_adversarial_state) (q : f4_adversarial_query) :
  (f4_adversarial_step s q).`f4_s_queries =
    s.`f4_s_queries ++ [f4_before_entry s q].
proof.
  by rewrite /f4_adversarial_step.
qed.

lemma f4_corrupt_or_reveal_persists
    (s : f4_adversarial_state) (q : f4_adversarial_query) :
  f4_is_exposure q =>
  (f4_adversarial_step s q).`f4_s_exposures =
    s.`f4_s_exposures ++ [f4_before_entry s q].
proof.
  move=> he.
  by rewrite /f4_adversarial_step he.
qed.

lemma f4_other_queries_cannot_erase_exposures
    (s : f4_adversarial_state) (q : f4_adversarial_query) :
  ! f4_is_exposure q =>
  (f4_adversarial_step s q).`f4_s_exposures =
    s.`f4_s_exposures.
proof.
  move=> hn.
  by rewrite /f4_adversarial_step hn.
qed.

lemma f4_challenge_attempt_always_recorded
    (s : f4_adversarial_state) (q : f4_adversarial_query) :
  f4_is_challenge q =>
  (f4_adversarial_step s q).`f4_s_challenges =
    s.`f4_s_challenges ++ [f4_before_entry s q].
proof.
  move=> hc.
  by rewrite /f4_adversarial_step hc.
qed.

lemma f4_nonchallenge_cannot_invent_attempt
    (s : f4_adversarial_state) (q : f4_adversarial_query) :
  ! f4_is_challenge q =>
  (f4_adversarial_step s q).`f4_s_challenges =
    s.`f4_s_challenges.
proof.
  move=> hn.
  by rewrite /f4_adversarial_step hn.
qed.

lemma f4_welcome_does_not_advance_global_epoch
    (s : f4_adversarial_state) (q : f4_adversarial_query) :
  q.`f4_q_kind = 5 =>
  (f4_adversarial_step s q).`f4_s_global_epoch =
    s.`f4_s_global_epoch.
proof.
  move=> hw.
  rewrite /f4_adversarial_step /f4_advances_global_epoch hw.
  by smt().
qed.

lemma f4_send_does_not_advance_global_epoch
    (s : f4_adversarial_state) (q : f4_adversarial_query) :
  q.`f4_q_kind = 3 =>
  (f4_adversarial_step s q).`f4_s_global_epoch =
    s.`f4_s_global_epoch.
proof.
  move=> hs.
  rewrite /f4_adversarial_step /f4_advances_global_epoch hs.
  by smt().
qed.

lemma f4_unverified_commit_does_not_advance_epoch
    (s : f4_adversarial_state) (q : f4_adversarial_query) :
  ! q.`f4_q_authenticated =>
  (f4_adversarial_step s q).`f4_s_global_epoch =
    s.`f4_s_global_epoch.
proof.
  move=> ha.
  rewrite /f4_adversarial_step /f4_advances_global_epoch ha.
  by smt().
qed.

lemma f4_only_verified_commits_advance_epoch
    (s : f4_adversarial_state) (q : f4_adversarial_query) :
  (f4_adversarial_step s q).`f4_s_global_epoch =
  s.`f4_s_global_epoch +
    (if q.`f4_q_authenticated /\
        (q.`f4_q_kind = 4 \/ q.`f4_q_kind = 6)
     then 1 else 0).
proof.
  by rewrite /f4_adversarial_step /f4_advances_global_epoch.
qed.
