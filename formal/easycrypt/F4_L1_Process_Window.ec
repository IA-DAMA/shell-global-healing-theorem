require import AllCore List RealExp.

(* L1 classifies the Product prepare window.  Capabilities denote possession,
   never byte equality.  T4 is split by program counter because one undivided
   error cut has no sound live-value set. *)
type cut = [ T1Pending | T2Merged | T3Rolled | T4Pending |
             T4Merged | T4Rolled | T5UncommittedRestart |
             T5CommittedRestart ].
type capability = [ OldState | SuccessorState | SuccessorExporter |
                    GeneratorState | SignerKey | CustodyKey |
                    PublicCommit | PublicContext | PublicGroupInfo |
                    SecretRemnant ].

op successor_typed_live t =
  with t=T1Pending => true
  with t=T2Merged => true
  with t=T3Rolled => true
  with t=T4Pending => true
  with t=T4Merged => true
  with t=T4Rolled => true
  with t=T5UncommittedRestart => false
  with t=T5CommittedRestart => true.

(* SecretRemnant is included while the process survives because OpenMLS Secret
   has no zeroizing Drop in the pinned source.  It is not asserted observable
   after process termination. *)
op gamma t =
  with t=T1Pending => [OldState;SuccessorState;SuccessorExporter;
    GeneratorState;SignerKey;CustodyKey;PublicCommit;PublicContext]
  with t=T2Merged => [OldState;SuccessorState;SuccessorExporter;
    GeneratorState;SignerKey;CustodyKey;PublicCommit;PublicContext;SecretRemnant]
  with t=T3Rolled => [OldState;SuccessorState;SuccessorExporter;
    GeneratorState;SignerKey;CustodyKey;PublicCommit;PublicContext;
    PublicGroupInfo;SecretRemnant]
  with t=T4Pending => [OldState;SuccessorState;SuccessorExporter;
    GeneratorState;SignerKey;CustodyKey;PublicCommit;PublicContext;SecretRemnant]
  with t=T4Merged => [OldState;SuccessorState;SuccessorExporter;
    GeneratorState;SignerKey;CustodyKey;PublicCommit;PublicContext;SecretRemnant]
  with t=T4Rolled => [OldState;SuccessorState;SuccessorExporter;
    GeneratorState;SignerKey;CustodyKey;PublicCommit;PublicContext;
    PublicGroupInfo;SecretRemnant]
  with t=T5UncommittedRestart => [OldState;GeneratorState;SignerKey;CustodyKey]
  with t=T5CommittedRestart => [OldState;SuccessorState;SuccessorExporter;
    GeneratorState;SignerKey;CustodyKey;PublicCommit;PublicContext;
    PublicGroupInfo].

op exposes_process (asked : bool) t c = asked /\ mem (gamma t) c.
op bad_epoch (asked : bool) t = asked /\ successor_typed_live t.

lemma successor_is_accounted t :
  successor_typed_live t => mem (gamma t) SuccessorState /\
                            mem (gamma t) SuccessorExporter.
proof. by case: t. qed.

lemma process_exposure_blocks_successor t :
  exposes_process true t SuccessorState => bad_epoch true t.
proof. rewrite /exposes_process /bad_epoch; case: t => //=. qed.

(* A later generation is eligible only after the last exposure and only when
   its honest commit input is declared independent of the accumulated cq view.
   This is a gate; independence is not inferred here. *)
op healed (last_bad selected first_fresh : int) independent no_later_exposure =
  last_bad < selected /\ selected = first_fresh /\
  independent /\ no_later_exposure.

lemma first_fresh_after_window (last_bad : int) :
  healed last_bad (last_bad+1) (last_bad+1) true true.
proof. rewrite /healed; smt(). qed.

lemma exposed_epoch_not_healed (e first_fresh : int) independent quiet :
  ! healed e e first_fresh independent quiet.
proof. rewrite /healed; smt(). qed.

(* Conditional composition with the previously established partial 2d+10h
   subcase and a separate real-generator replacement charge g. *)
op healing_budget d h g = 2%r*d + 10%r*h + g.
lemma healing_bound (adv partial d h g : real) :
  0%r <= g => adv <= partial + g => partial <= 2%r*d + 10%r*h =>
  adv <= healing_budget d h g.
proof. rewrite /healing_budget; smt(). qed.

(* Non-vacuity: e+1 is rejected after exposure, while the first independent
   commit after that exposure can select e+2. *)
lemma healing_witness (e : int) :
  bad_epoch true T2Merged /\
  ! healed (e+1) (e+1) (e+2) true true /\
  healed (e+1) (e+2) (e+2) true true.
proof. rewrite /bad_epoch /successor_typed_live /healed /=; smt(). qed.
