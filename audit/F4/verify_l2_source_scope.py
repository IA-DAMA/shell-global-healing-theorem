"""Pin L2's exhaustive Product request boundary and fail-closed classifier."""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re


PIN = "476bd8f1f4755ae2f6a689d23a937ba2573434a4"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def block(text: str, start: str, end: str) -> str:
    begin = text.index(start)
    finish = text.index(end, begin)
    return text[begin:finish]


def variants(enum: str) -> set[str]:
    return set(re.findall(r"(?m)^\s{4}([A-Z][A-Za-z0-9_]*)\s*(?:\{|,)", enum))


def main(native: Path) -> None:
    source = native / "research/protocol_shell/pq_group_chat_lab/src/offline_product.rs"
    scope = native / "research/protocol_shell/pq_group_chat_lab/src/offline_product_f4_request_scope.rs"
    audit = native / "research/protocol_shell/pq_group_chat_lab/src/offline_product_f4_semantic_audit.rs"
    texts = {p: p.read_text(encoding="utf-8") for p in (source, scope, audit)}

    enum = block(texts[source], "pub enum ProductRequest {", "/// The service observes")
    declared = variants(enum)
    if len(declared) != 34:
        raise ValueError(("ProductRequest variant count changed", sorted(declared)))

    classify = block(
        texts[scope],
        "pub(super) fn f4_native_request_obligation(",
        "impl F4NativeProofObligation",
    )
    classified = set(re.findall(r"ProductRequest::([A-Za-z0-9_]+)", classify))
    if classified != declared:
        raise ValueError(("classifier is not exhaustive", sorted(declared-classified), sorted(classified-declared)))
    if re.search(r"(?m)^\s*_\s*=>", classify):
        raise ValueError("wildcard classifier arm is forbidden")

    dispatcher = texts[source][texts[source].index("pub fn execute_android("):]
    dispatched = set(re.findall(r"ProductRequest::([A-Za-z0-9_]+)", dispatcher))
    if not declared <= dispatched:
        raise ValueError(("dispatcher variant absent", sorted(declared-dispatched)))

    required = (
        "RejectedSameAcceptedPublicView",
        "RejectedWithPossiblePrivateOrAcceptedMutation",
        "UnprovedSideEffectOrInstallation",
        "UnprovedTransition",
        "pub(super) fn proves_freshq(&self) -> bool { false }",
        "_ => F4SemanticStepClass::UnprovedSideEffectOrInstallation",
    )
    for fragment in required:
        if fragment not in texts[audit]:
            raise ValueError(("semantic fail-closed boundary changed", fragment))

    print(f"L2_NATIVE_PIN={PIN}")
    print(f"L2_PRODUCT_REQUEST_VARIANTS={len(declared)};CLASSIFIED={len(classified)};DISPATCHED={len(declared & dispatched)}")
    print(f"L2_PRODUCT_SOURCE_SHA256={digest(source)}")
    print(f"L2_REQUEST_SCOPE_SHA256={digest(scope)}")
    print(f"L2_SEMANTIC_AUDIT_SHA256={digest(audit)}")
    print("L2_UNSUPPORTED_POLICY=irreversible_coverage_gap;PROVES_FRESHQ=false")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("native", type=Path)
    args = parser.parse_args()
    main(args.native.resolve())
