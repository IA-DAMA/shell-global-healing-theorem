#!/usr/bin/env python3
"""Fail-closed F4 proof-boundary audit. Not a cryptographic proof."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
REQUIRED = {
    "formal/easycrypt/ShellPCS_T1_Conditional.ec": (
        "op challenge_context_binding", "op oracle_correspondence",
        "t1_shell_pcs_conditional_bound",
    ),
    "formal/easycrypt/ProviderPCS_Adapter.ec": (
        "type provider_view", "op phi", "module type ProviderPCS",
        "provider_pcs_to_qpcs_zero_loss",
    ),
    "formal/easycrypt/F4_Provider_Oracle_Games_Conditional.ec": (
        "op f4_encode_context", "f4_provider_pcs_bound_preserves_exact_advantage",
    ),
}
FORBIDDEN = ("admit.", "sorry.", "axiom ")
def main():
    failures = []
    for name, tokens in REQUIRED.items():
        path = ROOT / name
        if not path.is_file():
            failures.append(f"missing: {name}")
            continue
        data = path.read_text(encoding="utf-8")
        failures.extend(f"{name}: missing {token}" for token in tokens if token not in data)
    # These are *uninterpreted* boundaries. Presence is a failure for F4 closure,
    # not evidence that a concrete bridge has been proved.
    unresolved = [
        "T1 challenge_context_binding is uninterpreted",
        "ProviderPCS phi maps to an uninterpreted provider_view",
        "F4 f4_encode_context is uninterpreted",
        "No checked OpenMLS Rust transition-system refinement",
        "No instantiated QPT PCS bound for the Product hybrid ciphersuite",
        "No proven corrupt/reveal/send/join/resync trace simulation",
    ]
    for x in failures:
        print("ERROR:", x)
    for x in unresolved:
        print("UNRESOLVED:", x)
    print("F4_CONCRETE_CLOSED=false")
    return 1
if __name__ == "__main__":
    sys.exit(main())
