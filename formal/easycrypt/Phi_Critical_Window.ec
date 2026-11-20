require import AllCore Int List.
require import Phi_Refinement Phi_Trace_Model.

(* Canonical projection used by both Shell-side classification and the provider
   view passed to the imported TTKEM theorem. The point is to remove separate
   uninterpreted Shell/provider functions for the critical-window data. *)

type canonical_trace.

op canonicalize_shell : shell_trace -> challenge_binding -> canonical_trace.
op canonicalize_provider : provider_view -> canonical_trace.

op key_source : canonical_trace -> member -> position.
op exposed_between :
  canonical_trace -> member -> position -> position -> bool.

(* Phi correctness for the critical-window projection.  This is narrower than
   the final theorem: it says only that Phi is the canonical projection, not
   that the resulting challenge is safe. *)
op critical_projection_ok
  (tr : shell_trace) (ch : challenge_binding) : bool =
  canonicalize_shell tr ch = canonicalize_provider (phi tr ch).

lemma key_source_preserved
    (tr : shell_trace) (ch : challenge_binding) (u : member) :
  critical_projection_ok tr ch =>
  key_source (canonicalize_shell tr ch) u =
  key_source (canonicalize_provider (phi tr ch)) u.
proof.
  move=> h.
  by rewrite /critical_projection_ok in h; rewrite h.
qed.

lemma corruption_window_preserved
    (tr : shell_trace) (ch : challenge_binding)
    (u : member) (lo hi : position) :
  critical_projection_ok tr ch =>
  exposed_between (canonicalize_shell tr ch) u lo hi =
  exposed_between (canonicalize_provider (phi tr ch)) u lo hi.
proof.
  move=> h.
  by rewrite /critical_projection_ok in h; rewrite h.
qed.

(* The two facts above are consequences of one projection equality.  Thus a
   concrete Phi implementation has one refinement obligation for L2/L3 instead
   of two independent assumptions that could disagree. *)

op shell_current_key_source
  (tr : shell_trace) (ch : challenge_binding) (u : member) : position =
  key_source (canonicalize_shell tr ch) u.

op provider_current_key_source
  (pv : provider_view) (u : member) : position =
  key_source (canonicalize_provider pv) u.

op shell_exposed
  (tr : shell_trace) (ch : challenge_binding)
  (u : member) (lo hi : position) : bool =
  exposed_between (canonicalize_shell tr ch) u lo hi.

op provider_exposed
  (pv : provider_view) (u : member) (lo hi : position) : bool =
  exposed_between (canonicalize_provider pv) u lo hi.

lemma L2_from_canonical_projection
    (tr : shell_trace) (ch : challenge_binding) (u : member) :
  critical_projection_ok tr ch =>
  shell_current_key_source tr ch u =
  provider_current_key_source (phi tr ch) u.
proof.
  move=> h.
  rewrite /shell_current_key_source /provider_current_key_source.
  exact (key_source_preserved tr ch u h).
qed.

lemma L3_from_canonical_projection
    (tr : shell_trace) (ch : challenge_binding)
    (u : member) (lo hi : position) :
  critical_projection_ok tr ch =>
  shell_exposed tr ch u lo hi =
  provider_exposed (phi tr ch) u lo hi.
proof.
  move=> h.
  rewrite /shell_exposed /provider_exposed.
  exact (corruption_window_preserved tr ch u lo hi h).
qed.
