"""Pin the Product observer that supplies L4's public refinement events."""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path


PIN = "476bd8f1f4755ae2f6a689d23a937ba2573434a4"


def main(native: Path) -> None:
    source = native / "research/protocol_shell/pq_group_chat_lab/src/offline_product_f4_semantic_audit.rs"
    text = source.read_text(encoding="utf-8")
    body = text[text.index("pub(super) fn audit_real_android_command(") :]
    body = body[: body.index("/// A real Product accepted-state witness")]
    if body.count("super::execute_android(") != 1:
        raise ValueError("L4 observer must execute the Product dispatcher exactly once")
    before = body.index("let before =")
    execute = body.index("super::execute_android(")
    after = body.index("let after =")
    classify = body.index("let classification =")
    if not before < execute < after < classify:
        raise ValueError("L4 pre/execute/post/classify chronology changed")
    required = (
        "F4SemanticStepClass::VerifiedPublicRead",
        "F4SemanticStepClass::VerifiedSingleAcceptedCommit",
        "F4SemanticStepClass::RejectedWithPossiblePrivateOrAcceptedMutation",
        "F4SemanticStepClass::UnprovedSideEffectOrInstallation",
        "F4SemanticStepClass::UnprovedTransition",
        "pub(super) fn proves_freshq(&self) -> bool { false }",
    )
    for fragment in required:
        if fragment not in text:
            raise ValueError(("L4 fail-closed classifier changed", fragment))
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    print(f"L4_NATIVE_PIN={PIN}")
    print("L4_DISPATCH_EXECUTIONS=1;CHRONOLOGY=pre,execute,post,classify")
    print(f"L4_SEMANTIC_AUDIT_SHA256={digest}")
    print("L4_EPS_REF=0|ADMITTED_SOURCE_TRACE;DIVERGENCE=Bad_CC")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("native", type=Path)
    args = parser.parse_args()
    main(args.native.resolve())
