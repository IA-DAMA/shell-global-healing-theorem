"""Pin the L1 source boundary and check typed MIR storage intervals."""
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
import re


PIN = "476bd8f1f4755ae2f6a689d23a937ba2573434a4"
DEBUG = {
    "group": (112, 325),
    "signer": (123, 326),
    "b": (134, 327),
    "commit": (202, 354),
    "probe": (328, 397),
    "request": (358, 409),
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require_once(text: str, fragment: str, label: str) -> None:
    if text.count(fragment) != 1:
        raise ValueError(f"{label}: source boundary absent or ambiguous")


def require_count(text: str, fragment: str, count: int, label: str) -> None:
    if text.count(fragment) != count:
        raise ValueError(f"{label}: expected {count} exact occurrences")


def main(native: Path, mir_dir: Path) -> None:
    lifecycle = native / "research/protocol_shell/pq_group_chat_lab/src/offline_product_lifecycle.rs"
    store = native / "research/protocol_shell/pq_group_chat_lab/src/store.rs"
    custody = native / "research/protocol_shell/pq_group_chat_lab/src/android_storage.rs"
    openmls = native / "third_party/openmls-0.9.0"
    group = openmls / "src/group/mls_group/mod.rs"
    staged = openmls / "src/group/mls_group/staged_commit.rs"
    exporting = openmls / "src/group/mls_group/exporting.rs"
    secret = openmls / "src/ciphersuite/secret.rs"
    signer = Path.home() / ".cargo/registry/src/index.crates.io-1949cf8c6b5b557f/openmls_basic_credential-0.6.0/src/lib.rs"
    crypto = Path.home() / ".cargo/registry/src/index.crates.io-1949cf8c6b5b557f/openmls_rust_crypto-0.6.0/src/provider.rs"

    sources = {p.name: p.read_text(encoding="utf-8") for p in
               (lifecycle, store, custody, group, staged, exporting, secret, signer, crypto)}
    for fragment, label in (
        ('let mut group = match_native_snapshot(c, &current)?;', "group load"),
        ('let commit = if kind == "CLOSE"', "commit creation"),
        ('let probe = (|| {\n            checked(\n                group.merge_pending_commit(&provider)', "temporary merge"),
        ('ROLLBACK TO product_lifecycle_probe; RELEASE product_lifecycle_probe', "rollback"),
        ('b.successor_group_info = Binary(probe?);', "post-rollback buffer"),
        ('local.pending = Some(canonical::digest(&request.body.commit.0));', "durable pending selector"),
        ('crate::save(c, &local)?;\n        schema(c)?;\n        checked(c.execute("INSERT INTO product_lifecycle_v1', "persist pending group and outbox"),
        ('pub(super) fn require_pending(c: &rusqlite::Connection, request: &ProductLifecycleRequest) -> Result<()> {\n    public_checked(request)?;\n    let local = crate::state(c)?;\n    let group = crate::load(&Provider::new(c), &local)?;', "restart pending reload"),
    ):
        require_once(sources[lifecycle.name], fragment, label)
    require_count(
        sources[lifecycle.name],
        'group\n                .pending_commit()\n                .ok_or("product_lifecycle_pending")?',
        2,
        "successor context and restart pending validation",
    )
    require_once(
        sources[staged.name],
        """pub(crate) struct MemberStagedCommitState {
    group_epoch_secrets: GroupEpochSecrets,
    message_secrets: MessageSecrets,
    staged_diff: StagedPublicGroupDiff,
    new_keypairs: Vec<EncryptionKeyPair>,""",
        "staged successor secrets and keypairs",
    )
    require_once(sources[exporting.name], '.group_epoch_secrets\n                .exporter_secret()',
                 "exporter from installed epoch secret")
    require_once(sources[secret.name], 'pub(crate) struct Secret {', "OpenMLS Secret")
    if "impl Drop for Secret" in sources[secret.name] or "ZeroizeOnDrop for Secret" in sources[secret.name]:
        raise ValueError("Secret zeroization boundary changed; reassess L1")
    require_once(sources[signer.name], 'private: SecretVLBytes,', "live signing key")
    if "impl Drop for SignatureKeyPair" in sources[signer.name]:
        raise ValueError("signer destruction boundary changed; reassess L1")
    require_once(sources[custody.name], 'material: Zeroizing::new(*material),', "custody copy")
    require_once(sources[crypto.name], 'rng: RwLock<rand_chacha::ChaCha20Rng>,', "generator state")
    require_once(sources[crypto.name], 'rand_chacha::ChaCha20Rng::from_entropy()', "generator seed")
    require_count(
        sources[store.name],
        'connection.execute_batch("ROLLBACK")',
        2,
        "rollback on precommit or operation error",
    )

    matches = list(mir_dir.glob("*prepare-{closure#0}.1-1-000.built.after.mir"))
    if len(matches) != 1:
        raise ValueError("expected one built MIR for lifecycle::prepare closure")
    mir = matches[0]
    text = mir.read_text(encoding="utf-8")
    for name, (local, source_line) in DEBUG.items():
        debug = rf"debug {name} => _{local};"
        if debug not in text:
            raise ValueError(f"MIR local changed for {name}")
        live = re.findall(rf"StorageLive\(_{local}\);.*lifecycle\.rs:(\d+):", text)
        dead = re.findall(rf"StorageDead\(_{local}\);.*lifecycle\.rs:(\d+):", text)
        if live != [str(source_line)] or not dead or set(dead) != {"425"}:
            raise ValueError((name, live, dead))

    print(f"L1_NATIVE_PIN={PIN}")
    print(f"L1_PREPARE_SOURCE_SHA256={digest(lifecycle)}")
    print(f"L1_OPENMLS_STAGED_SHA256={digest(staged)}")
    print(f"L1_OPENMLS_SECRET_SHA256={digest(secret)}")
    print(f"L1_PREPARE_MIR_SHA256={digest(mir)}")
    print("L1_TYPED_LIFETIMES=group,signer,body,commit,probe,request:verified")
    print("L1_SECRET_DROP_ZEROIZE=absent;CUSTODY_SCOPE_ZEROIZE=present")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("native", type=Path)
    parser.add_argument("mir_dir", type=Path)
    args = parser.parse_args()
    main(args.native.resolve(), args.mir_dir.resolve())
