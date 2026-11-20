# Shell T1/T2 EasyCrypt composition

This directory contains the machine-checkable Shell T1 composition layer and
the separate T2 local continuity classifier.

Current machine-checked target:
- explicit G0 -> G1 reduction to the imported QPCS real/ideal game;
- explicit G1 -> G2 reduction to the exporter real/ideal game;
- explicit G2 -> G3 reduction to the split-PRF real/ideal game;
- program equivalence for all three reduction wrappers;
- the conditional G0 -> G3 advantage bound obtained by two applications of
  the triangle inequality.

Current provider-transport front:
- `QPCS` challenges are indexed by the Shell context instead of being
  context-free;
- `ProviderPCS_Adapter.ec` defines the zero-loss wrapper from a
  provider-specific challenge view into `QPCS`;
- this adapter does not prove freshness refinement, oracle inclusion or
  challenge-state correspondence.  Those are the open P2b obligations.

Conditional T1 closure front:
- `Phi_Canonical_Events.ec`, `Phi_Window_Fold.ec`,
  `Phi_Safe_TTKEM.ec`, and `Phi_Membership_Fold.ec` derive provider safety
  from a single canonical accepted-event projection;
- `ShellPCS_T1_Conditional.ec` connects that derived safety predicate, the
  explicit correspondence/authentication/session/composition gates, and the
  imported provider/exporter/MSS26 assumptions to the G0 -> G3 bound;
- this is a provider-neutral conditional theorem.  It is not a concrete
  OpenMLS, TTKEM, or QPT instantiation.

T2 continuity front:
- `ShellContinuity_T2.ec` proves exhaustive local history classification under
  authenticated same-anchor premises;
- forward extensions and idempotent replays are admitted, strict rollback and
  divergent histories are rejected with distinct evidence, and unverifiable
  pairs fail closed;
- the theorem proves local detectability/classification, not global fork
  prevention, consensus, universal gossip, or an independent Witness.

The workflow pins EasyCrypt at
`884dad7a44f72e358900ad15c38edbf1760a73e8` and checks every file in this
directory in dependency order.  A run URL and commit are recorded in the
research milestone only after the expanded workflow actually passes.

Hard rule: do not add a circular axiom such as ShellSecure or axiomatize the
G0/G1, G1/G2, or G2/G3 hops. Quantitative hops must be discharged against the
named imported security game/assumption.

The upstream QPCS theorem and concrete provider correspondence are not
re-proved here.  The exact RFC/OpenMLS correspondence, a concrete split-PRF
profile, quantitative bad-event games, and a QPT lifting remain open.  This
directory therefore proves the stated provider-neutral conditional theorems;
it does not prove collective post-quantum PCS for a deployed Linka profile.
