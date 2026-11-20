require import AllCore Int List.
require import F4_External_FreshQ_Criterion F4_Groupwide_Taint_Recovery_Criterion.

(* F4-M3 actual gap: the prior group-wide taint criterion compares only
   ff_secret_kind = challenge.ff_secret_kind. That can miss successful
   disclosure of a different secret class whose value is sufficient, via
   publicly computable derivations and retained ciphertext, to derive
   the challenged group epoch secret.

   This file does NOT call a backend-provided FreshQ boolean. It requires a
   typed DERIVATION-ROUTE CERTIFICATE: an accepted/authenticated transition
   strictly between disclosure and challenge, with the specific input and
   output secret kinds, and a complete publicly computable dependency
   (no additional independent hidden input). Importantly, a certificate
   is NOT inferred from kind of Commit or timestamp. The Product Rust/HPKE
   trace must establish the certificate independently; otherwise the final
   PCS proof remains OPEN.

   The model exposes a formal counterexample to the earlier criterion and
   proves a sufficient syntactic guard against this cross-class bad event,
   without assuming PCS, IND-CCA, Dual-PRF or a numerical advantage. *)

type f4_causal_route = {
  fc_group : int;
  fc_event_index : int;
  fc_input_kind : int;
  fc_output_kind : int;
  fc_accepted : bool;
  fc_authenticated : bool;
  fc_public_derivation_complete : bool;
}.

(* Cross-class route: after secret exposure and before challenge, the
   adversary can follow an independently verified deterministic derivation
   to the challenged secret. A transition with an uncompromised independent
   secret MUST NOT receive a 'complete' certificate. *)
op f4_exposed_usable_route
    (ex : f4_fresh_event) (route : f4_causal_route)
    (ch : f4_fresh_event) : bool =
  f4_is_exposure_event ex /\ ex.`ff_member_active /\
  ex.`ff_group = ch.`ff_group /\
  ex.`ff_group = route.`fc_group /\
  ex.`ff_secret_kind = route.`fc_input_kind /\
  ch.`ff_secret_kind = route.`fc_output_kind /\
  ex.`ff_index < route.`fc_event_index /\
  route.`fc_event_index < ch.`ff_index /\
  route.`fc_accepted /\ route.`fc_authenticated /\
  route.`fc_public_derivation_complete.

op f4_cross_class_bad
    (exposures : f4_fresh_event list)
    (routes : f4_causal_route list)
    (ch : f4_fresh_event) : bool =
  has (fun ex => has (fun route =>
    f4_exposed_usable_route ex route ch) routes) exposures.

(* The prior conservative same-class guard is retained, with this extra
   syntactic check. Even this guard is not a full MLS FreshQ theorem:
   missing routes, private retention and quantum-game hops still require
   separate proofs. *)
op f4_causal_cut_candidate
    (exposures : f4_fresh_event list)
    (routes : f4_causal_route list)
    (ch : f4_fresh_event) : bool =
  f4_strict_freshq_candidate exposures ch /\
  !f4_cross_class_bad exposures routes ch.

lemma f4_previous_guard_ignores_other_secret_class
    (ex ch : f4_fresh_event) :
  ex.`ff_secret_kind <> ch.`ff_secret_kind =>
  ch.`ff_kind = f4_kind_challenge =>
  f4_strict_freshq_candidate [ex] ch.
proof.
  move=> hdiff hch.
  apply (f4_strict_freshq_without_prior_exposure [ex] ch hch).
  rewrite /f4_exposure_before_challenge /=.
  exact (f4_exposure_in_other_secret_class_is_irrelevant ex ch hdiff).
qed.

lemma f4_cross_class_cut_rejects_certified_route
    (ex ch : f4_fresh_event) (route : f4_causal_route) :
  f4_exposed_usable_route ex route ch =>
  ! f4_causal_cut_candidate [ex] [route] ch.
proof.
  move=> hroute.
  rewrite /f4_causal_cut_candidate /f4_cross_class_bad /=.
  by smt().
qed.

lemma f4_causal_cut_refines_previous_guard
    (exposures : f4_fresh_event list)
    (routes : f4_causal_route list) (ch : f4_fresh_event) :
  f4_causal_cut_candidate exposures routes ch =>
  f4_strict_freshq_candidate exposures ch.
proof.
  rewrite /f4_causal_cut_candidate.
  by smt().
qed.

lemma f4_cross_class_rejects_without_same_kind_exposure
    (ex ch : f4_fresh_event) (route : f4_causal_route) :
  ex.`ff_secret_kind <> ch.`ff_secret_kind =>
  ch.`ff_kind = f4_kind_challenge =>
  f4_exposed_usable_route ex route ch =>
  f4_strict_freshq_candidate [ex] ch /\
  ! f4_causal_cut_candidate [ex] [route] ch.
proof.
  move=> hdiff hch hroute.
  have hprev := f4_previous_guard_ignores_other_secret_class ex ch hdiff hch.
  have hnew := f4_cross_class_cut_rejects_certified_route ex ch route hroute.
  by smt().
qed.

lemma f4_noncausal_future_route_not_counted
    (ex ch : f4_fresh_event) (route : f4_causal_route) :
  ch.`ff_index <= route.`fc_event_index =>
  ! f4_exposed_usable_route ex route ch.
proof.
  rewrite /f4_exposed_usable_route.
  by smt().
qed.

lemma f4_unaccepted_route_not_counted
    (ex ch : f4_fresh_event) (route : f4_causal_route) :
  !route.`fc_accepted =>
  ! f4_exposed_usable_route ex route ch.
proof.
  rewrite /f4_exposed_usable_route.
  by smt().
qed.

lemma f4_route_with_hidden_independent_input_not_counted
    (ex ch : f4_fresh_event) (route : f4_causal_route) :
  !route.`fc_public_derivation_complete =>
  ! f4_exposed_usable_route ex route ch.
proof.
  rewrite /f4_exposed_usable_route.
  by smt().
qed.

(* A future native/PQ security proof must discharge, not assert,
     (1) event/secret inventory completeness;
     (2) correctness of route certificates, including X-Wing/HPKE
         decapsulation and the MLS key schedule;
     (3) QPT indistinguishability for all non-openable routes;
     (4) challenge selection and history preservation.
   A stale or missing certificate may make this candidate TOO PERMISSIVE. *)
