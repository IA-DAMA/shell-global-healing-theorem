require import AllCore.

(* Provider-neutral Shell T2: authenticated continuity and history
   classification.

   T2 is deliberately separate from T1.  It supplies no secret entropy and
   makes no global-consensus claim.  Given authenticated histories tied to the
   same Shell anchor, it states exactly which relations may advance local
   continuity and which relations must fail closed with persistent evidence.
*)

type history.

op authenticated : history -> bool.
op same_anchor : history -> history -> bool.
op prefix : history -> history -> bool.

op comparable (current candidate : history) : bool =
  authenticated current /\ authenticated candidate /\
  same_anchor current candidate.

op same_history (current candidate : history) : bool =
  prefix current candidate /\ prefix candidate current.

op forward_extension (current candidate : history) : bool =
  prefix current candidate /\ ! prefix candidate current.

op strict_rollback (current candidate : history) : bool =
  prefix candidate current /\ ! prefix current candidate.

op divergent_fork (current candidate : history) : bool =
  ! prefix current candidate /\ ! prefix candidate current.

op accept_candidate (current candidate : history) : bool =
  comparable current candidate /\
  (same_history current candidate \/ forward_extension current candidate).

op conflict_evidence (current candidate : history) : bool =
  comparable current candidate /\ divergent_fork current candidate.

op rollback_evidence (current candidate : history) : bool =
  comparable current candidate /\ strict_rollback current candidate.

(* Every authenticated same-anchor pair falls into exactly one local
   continuity class: replay/equality, forward extension, strict rollback, or
   divergence. *)
lemma t2_authenticated_history_classification
    (current candidate : history) :
  comparable current candidate =>
  same_history current candidate \/
  forward_extension current candidate \/
  strict_rollback current candidate \/
  divergent_fork current candidate.
proof.
  move=> _.
  rewrite /same_history /forward_extension
          /strict_rollback /divergent_fork.
  case: (prefix current candidate);
  case: (prefix candidate current) => //=.
qed.

(* The four cases are not only exhaustive: their prefix predicates make them
   pairwise disjoint.  This is what licenses a deterministic local decision
   instead of merely listing possible labels. *)
lemma t2_authenticated_history_classes_are_disjoint
    (current candidate : history) :
  comparable current candidate =>
  ! (same_history current candidate /\
     forward_extension current candidate) /\
  ! (same_history current candidate /\
     strict_rollback current candidate) /\
  ! (same_history current candidate /\
     divergent_fork current candidate) /\
  ! (forward_extension current candidate /\
     strict_rollback current candidate) /\
  ! (forward_extension current candidate /\
     divergent_fork current candidate) /\
  ! (strict_rollback current candidate /\
     divergent_fork current candidate).
proof.
  move=> _.
  rewrite /same_history /forward_extension
          /strict_rollback /divergent_fork.
  case: (prefix current candidate);
  case: (prefix candidate current) => //=.
qed.

(* A delayed but authentic observer sees a prefix.  Delay is compatible and
   must not be misreported as a fork. *)
lemma t2_prefix_delay_not_a_fork (older newer : history) :
  comparable older newer =>
  prefix older newer =>
  ! divergent_fork older newer.
proof.
  move=> _ hp.
  rewrite /divergent_fork.
  by rewrite hp.
qed.

lemma t2_forward_extension_is_accepted (current candidate : history) :
  comparable current candidate =>
  forward_extension current candidate =>
  accept_candidate current candidate.
proof.
  move=> hc hf.
  rewrite /accept_candidate.
  split.
  + exact hc.
  + right; exact hf.
qed.

lemma t2_same_history_is_idempotently_accepted
    (current candidate : history) :
  comparable current candidate =>
  same_history current candidate =>
  accept_candidate current candidate.
proof.
  move=> hc hs.
  rewrite /accept_candidate.
  split.
  + exact hc.
  + left; exact hs.
qed.

(* A strict rollback can be authenticated and still be inadmissible.  Valid
   signatures do not grant retroactive authority. *)
lemma t2_strict_rollback_is_rejected (current candidate : history) :
  comparable current candidate =>
  strict_rollback current candidate =>
  rollback_evidence current candidate /\
  ! accept_candidate current candidate.
proof.
  move=> hc hr.
  move: hr; rewrite /strict_rollback.
  move=> [hback hnforward].
  rewrite /rollback_evidence /accept_candidate
          /strict_rollback /same_history /forward_extension.
  by rewrite hback hnforward.
qed.

(* Two authenticated same-anchor histories with no prefix relation constitute
   locally checkable fork evidence and cannot advance local continuity. *)
lemma t2_authenticated_divergence_is_detected
    (current candidate : history) :
  comparable current candidate =>
  divergent_fork current candidate =>
  conflict_evidence current candidate /\
  ! accept_candidate current candidate.
proof.
  move=> hc hf.
  move: hf; rewrite /divergent_fork.
  move=> [hnforward hnback].
  rewrite /conflict_evidence /accept_candidate
          /divergent_fork /same_history /forward_extension.
  by rewrite hnforward hnback.
qed.

(* Without authentication or a common anchor, T2 refuses to classify the pair
   as an admissible transition or as authenticated fork evidence. *)
lemma t2_unverifiable_pair_fails_closed (current candidate : history) :
  ! comparable current candidate =>
  ! accept_candidate current candidate /\
  ! conflict_evidence current candidate /\
  ! rollback_evidence current candidate.
proof.
  move=> hn.
  rewrite /accept_candidate /conflict_evidence /rollback_evidence.
  by rewrite hn.
qed.

(* Scope boundary: these lemmas prove deterministic local classification under
   their authentication/anchor premises.  They do not prove availability,
   universal gossip, Byzantine consensus, prevention of every remote fork, or
   an independent Witness deployment. *)
