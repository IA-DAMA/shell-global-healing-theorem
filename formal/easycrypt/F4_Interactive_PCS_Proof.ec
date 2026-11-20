require import AllCore List.
require import F4_Adversarial_Query_Ledger F4_Interactive_PCS_Game.
require import F4_Epoch_Schedule_Cut.
require import F4_Epoch_Fixture.

(* Replay the source-issued events using two arbitrary caller identities.
   Installs and transitions never become successful disclosures. *)
op f4_fixture_exposures (subject peer : f4_query_record) =
  map (fun e : f4_fixture_kind * int * int * bool =>
    f4_challenger_tag (if e.`4 then subject else peer) e.`2 e.`3
      (e.`1 = Capture) (e.`1 = Reveal))
    (filter (fun (e : f4_fixture_kind * int * int * bool) =>
       e.`1 = Capture \/ e.`1 = Reveal) f4_epoch_fixture).

lemma f4_product_two_members_capture_windows subject peer :
  let exposures = f4_fixture_exposures subject peer in
  f4_group_capture_before exposures (f4_challenger_tag peer 4 1 false false) /\
  !f4_group_capture_before exposures (f4_challenger_tag peer 6 2 false false) /\
  f4_group_capture_before exposures (f4_challenger_tag subject 8 2 false false).
proof.
  by rewrite /f4_fixture_exposures /f4_epoch_fixture /f4_group_capture_before
             /f4_challenger_tag /=.
qed.

op f4_fixture_owner_update_between (subject : bool) (ex ch : int) =
  has (fun (e : f4_fixture_kind * int * int * bool) =>
    e.`1 = Own /\ e.`4 = subject /\ ex < e.`2 < ch) f4_epoch_fixture.

lemma f4_product_update_attribution :
  f4_fixture_owner_update_between true 2 8 /\
  !f4_fixture_owner_update_between false 3 8 /\
  !f4_fixture_owner_update_between false 7 8.
proof. by rewrite /f4_fixture_owner_update_between /f4_epoch_fixture /=. qed.

lemma f4_observed_schedule_derivation_forces_bad (B <: F4ProductPCSBackend) :
  hoare [F4Challenger(B).challenge :
    (exists steps, foldl f4_learn
      (f4_observed_exporter_view F4Challenger.exposures
        (f4_challenger_tag arg.`1 F4Challenger.query_count
          F4Challenger.global_epoch false false)) steps Output)
    ==> F4Challenger.bad_challenge /\ res = None].
proof.
  proc.
  seq 2 : ((f4_exposed_before_challenge F4Challenger.exposures x \/
            f4_group_capture_before F4Challenger.exposures x) /\ out = None).
  + auto; smt(f4_output_route_exact f4_observed_route).
  rcondt 1; first by skip; smt().
  wp; skip; smt().
qed.

(* Concrete HOARE gate: if the challenger has already recorded a matching
   earlier corrupt/reveal event, the challenge procedure must return None
   and set Bad_challenge, regardless of the provider implementation.
   This says NOTHING about quantum PCS advantage on FreshQ challenges. *)

lemma f4_recorded_prior_exposure_forces_bad
    (B <: F4ProductPCSBackend) :
  hoare [F4Challenger(B).challenge :
    f4_exposed_before_challenge F4Challenger.exposures
      (f4_challenger_tag arg.`1 F4Challenger.query_count
                         F4Challenger.global_epoch false false)
    ==>
    F4Challenger.bad_challenge /\ res = None].
proof.
  proc.
  seq 2 : (
    f4_exposed_before_challenge F4Challenger.exposures x /\
    out = None).
  + auto; smt().
  rcondt 1.
  + by skip; smt().
  wp; skip => &hr; smt().
qed.

(* REAL NATIVE TRACE: the Product can be corrupted after a challenge.
   The challenger must NOT silently return None if native corruption/reveal
   would have succeeded. It passes through the native oracle result and
   records Bad_challenge for a successful post-selection disclosure.
   This establishes a necessary trace-shape property, NOT a QPT bound. *)

lemma f4_after_challenge_corrupt_success_forces_bad
    (B <: F4ProductPCSBackend{-F4Challenger}) :
  hoare [F4Challenger(B).corrupt :
    F4Challenger.challenge_selected
    ==>
    F4Challenger.challenge_selected /\
    (res <> None => F4Challenger.bad_challenge)].
proof.
  proc.
  wp.
  call (_: true).
  wp; skip => &hr; smt().
qed.

lemma f4_after_challenge_reveal_success_forces_bad
    (B <: F4ProductPCSBackend{-F4Challenger}) :
  hoare [F4Challenger(B).reveal :
    F4Challenger.challenge_selected
    ==>
    F4Challenger.challenge_selected /\
    (res <> None => F4Challenger.bad_challenge)].
proof.
  proc.
  wp.
  call (_: true).
  wp; skip => &hr; smt().
qed.

lemma f4_second_challenge_is_bad
    (B <: F4ProductPCSBackend) :
  hoare [F4Challenger(B).challenge :
    F4Challenger.challenge_selected
    ==>
    F4Challenger.bad_challenge /\ res = None].
proof.
  proc.
  seq 2 : (F4Challenger.challenge_selected /\ out = None).
  + auto; smt().
  rcondt 1.
  + by skip; smt().
  wp; skip => &hr; smt().
qed.
