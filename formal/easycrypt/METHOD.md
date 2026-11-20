# EasyCrypt method note — studied before further T1 edits

## Tool semantics confirmed from current upstream sources

1. EasyCrypt is an interactive theorem prover for code-based, game-playing
   cryptographic proofs. Batch compilation is not the same interface as the
   interactive proof shell.

2. The `print` command is a proof-shell command that expects an object/procedure
   argument; inserting bare `print.` inside a batch proof was invalid. The
   diagnostic run #17 therefore taught us nothing about the residual goal.

3. Upstream cryptographic examples prove relational game equivalences using
   `byequiv`/equiv, `proc`, `seq`, `if`, `inline`, `wp`, repeated
   `call`, and `auto`. A current PKE theory contains an example with
   `do 4! call (_: true); auto` after program alignment.

4. `call` has side-condition/noninterference requirements. The restrictions
   discovered in runs #9-#12 are therefore part of EasyCrypt's module-state
   discipline, not dynamically invented cryptographic assumptions.

5. Current EasyCrypt releases have changed/strengthened call/proc tactics and
   diagnostics. We are pinned to ~dev, so proofs must follow the current
   semantics rather than older snippets blindly.

## Method change

No further speculative tactic edits.

For each red run:
- classify PARSER / TOOLING / MODULE-NONINTERFERENCE / PROGRAM-ALIGNMENT /
  CRYPTOGRAPHIC-REDUCTION;
- use upstream current examples/documentation for the relevant tactic;
- make one justified proof change;
- record whether it changes the adversary model.

## Current diagnosis of G0/G1

The four-call script was structurally guessed before program alignment was
known. Upstream examples show repeated `call` only after aligning statements
with tactics such as inline/wp/seq/swap/if as appropriate.

Therefore the next proof attempt must first align G0 and RealHop after inlining
Continue, then apply call rules only to the calls actually remaining in the
aligned relational program.

No new {-X} restriction will be added unless EasyCrypt reports a concrete
module-state interference and it is justified against T1-BASE.

Status:
EASYCRYPT_METHOD = STUDIED_CURRENT_UPSTREAM
BARE_PRINT_DIAGNOSTIC = INVALID_BATCH_USAGE
G0_G1_NEXT_STEP = GENERIC_QPCS_REDUCTION

## Resolved abstract-call state obligation

The current EasyCrypt implementation used by this branch is pinned to
`884dad7a44f72e358900ad15c38edbf1760a73e8`.  In
`src/phl/ecPhlCall.ml`, `mk_inv_spec` builds the inferred contract for an
abstract relational call from three components:

- equality of call parameters;
- equality of the abstract module globals;
- the user-supplied invariant.

It also preserves result equality and module-global equality.  Consequently,
two syntactically identical calls to a stateful abstract module are not
reflexive from input equality alone: the two memories must initially relate
that module's global state.

`continue_is_explicit` now states equality of `glob E`, `glob M`, and `glob A`
in addition to its public inputs.  This is program-state alignment, not a new
cryptographic hypothesis and not a restriction on the adversary's behavior.
The corresponding EasyCrypt workflow run #23, commit `211041f`, completed
successfully.

Evidence status:

CONTINUATION_STATE_ALIGNMENT = teste isolado passou
ADVERSARY_MODEL_CHANGE = NONE
UPSTREAM_QPCS_SECURITY = NOT_DISCHARGED_BY_THIS_LEMMA

## Conditional cryptographic core closed

The three reductions are now explicit EasyCrypt modules rather than
axiomatized Shell hops:

- `QPCS_Hop.ec`: G0 -> G1;
- `Exporter_Hop.ec`: G1 -> G2;
- `SplitPRF_Hop.ec`: G2 -> G3.

`ShellPCS_T1.ec` composes their three imported advantage premises with two
explicit triangle-inequality steps. Workflow run #28, commit `bfd9283d`,
accepted every formal file under pinned EasyCrypt
`884dad7a44f72e358900ad15c38edbf1760a73e8`.

Evidence status:

T1_CRYPTO_CORE_COMPOSITION = teste isolado passou
PRIMITIVE_SECURITY_PREMISES = NOT_DISCHARGED
RFC_OPENMLS_CORRESPONDENCE = OPEN
EXACT_SPLIT_PRF_INSTANTIATION = OPEN
HISTORY_AUTH_BAD_EVENT_GAMES = OPEN
PQ_PCS_QPT = NOT_PROVEN
