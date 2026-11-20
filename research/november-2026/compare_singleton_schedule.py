"""Compare synthetic byte vectors with the vendored OpenMLS methods, on a temporary source copy."""
import argparse
import hashlib
import hmac
import io
import json
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile

PIN = "476bd8f1f4755ae2f6a689d23a937ba2573434a4"
CRATE = "research/protocol_shell/pq_group_chat_lab"
OPENMLS = "third_party/openmls-0.9.0"
LENGTHS = (0, 17, 63, 64, 300)
FORMAL = Path(__file__).resolve().parents[2] / "formal/easycrypt"


def literal(source, pattern):
    match = re.search(pattern, source)
    if match is None:
        raise ValueError("missing byte literal in formal definition: " + pattern)
    return bytes(int(octet) for octet in match[1].split(";"))


def model_labels():
    exporter = (FORMAL / "F4_M5_Epoch_Exporter_Hops.ec").read_text()
    schedule = (FORMAL / "F4_M5_Singleton_Schedule.ec").read_text()
    octets = r"\[([\d;]+)\]"
    return {
        "prefix": literal(exporter, "op prefix = " + octets),
        "exporter": literal(exporter, "op epoch_slot = short_input 48 " + octets),
        "application": literal(exporter, "op label_slot = short_input 48 " + octets),
        "final": literal(exporter, "op final_slot ctx = short_input 32 " + octets),
        "welcome": literal(schedule, "op welcome_slot = short_input 48 " + octets),
    }

# Everything entering this test-only method is derived from public constants.
BRIDGE = r"""
#[doc(hidden)]
pub fn f4_public_vector(crypto: &impl OpenMlsCrypto, n: usize) -> (Vec<u8>, Vec<u8>) {
    let suite = Ciphersuite::MLS_128_MLKEM768X25519_CHACHA20POLY1305_SHA384_MLDSA44;
    let g: Vec<u8> = (0..n).map(|i| (i % 251) as u8).collect();
    let ctx = [b"synthetic/".as_slice(), &g].concat();
    let old = InitSecret::from(Secret::from_slice(&[17; 48]));
    let commit = CommitSecret { secret: Secret::from_slice(&[34; 48]) };
    let j = JoinerSecret::new(crypto, suite, commit, &old, &g).unwrap();
    let psk = PskSecret::new(crypto, suite, Vec::<(PreSharedKeyId, Secret)>::new()).unwrap();
    let mut ks = KeySchedule::init(suite, crypto, &j, psk).unwrap();
    let w = ks.welcome(crypto, suite).unwrap();
    ks.add_context(crypto, &g).unwrap();
    let e = ks.epoch_secrets(crypto, suite).unwrap().epoch_secrets;
    let y = e.exporter_secret.derive_exported_secret(suite, crypto,
            F4_VECTOR_LABEL, &ctx, F4_VECTOR_LENGTH).unwrap();
    (w.secret.as_slice().to_vec(), y)
}
"""
MAIN = r"""
fn main() {
    let crypto = openmls_rust_crypto::RustCrypto::default();
    for n in [0, 17, 63, 64, 300] {
        let (w, y) = openmls::schedule::f4_public_vector(&crypto, n);
        println!("{}", serde_json::to_string(&(n, w, y)).unwrap());
    }
}
"""


def vl(value):
    n = len(value)
    if n < 64:
        return bytes([n]) + value
    if n < 16384:
        return (16384 + n).to_bytes(2, "big") + value
    raise ValueError("outside the fixture")


def mac(key, data):
    return hmac.digest(key, data, "sha384")


def expand(prefix, key, label, ctx=b"", n=48):
    info = n.to_bytes(2, "big") + vl(prefix + label) + vl(ctx)
    return mac(key, info + b"\x01")[:n]


def expected(n):
    g = bytes(i % 251 for i in range(n))
    t = mac(bytes([17]) * 48, bytes([34]) * 48)
    labels = model_labels()
    prefix = labels["prefix"]
    j = expand(prefix, t, b"joiner", g)
    mid = mac(j, bytes(48))
    e = expand(prefix, mid, b"epoch", g)
    app = expand(prefix, expand(prefix, e, labels["exporter"]), labels["application"])
    y = expand(prefix, app, labels["final"], hashlib.sha384(b"synthetic/" + g).digest(), 32)
    return [n, list(expand(prefix, mid, labels["welcome"])), list(y)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("native", type=Path)
    parser.add_argument("--git", default="git")
    args = parser.parse_args()
    archive = subprocess.check_output(
        [args.git, "archive", "--format=tar", PIN, CRATE, OPENMLS, "research/ghost_manifest_protocol/payload_schemas"],
        cwd=args.native,
    )
    with tempfile.TemporaryDirectory(prefix="f4-public-vectors-") as folder:
        root = Path(folder)
        with tarfile.open(fileobj=io.BytesIO(archive)) as tree:
            tree.extractall(root, filter="data")
        schedule = root / OPENMLS / "src/schedule/mod.rs"
        with schedule.open("a", encoding="utf-8") as src:
            probe = (root / CRATE / "src/offline_product_f4_probe.rs").read_text()
            label = re.search(r'^const F4_EXPORTER_LABEL: &str = ("[^"]+");$', probe, re.M)
            length = re.search(r'^const F4_OUTPUT_LEN: usize = ([0-9]+);$', probe, re.M)
            if label is None or length is None:
                raise ValueError("missing pinned Product challenge parameters")
            src.write(BRIDGE.replace("F4_VECTOR_LABEL", label[1]).replace("F4_VECTOR_LENGTH", length[1]))
        examples = root / CRATE / "examples"
        examples.mkdir(exist_ok=True)
        (examples / "f4_public_schedule.rs").write_text(MAIN, encoding="utf-8")
        output = subprocess.check_output(["cargo", "run", "--offline", "--locked",
                                         "--example", "f4_public_schedule"], cwd=root / CRATE)
        if [json.loads(line) for line in output.splitlines()] != [expected(n) for n in LENGTHS]:
            raise ValueError("OpenMLS and the independent byte calculation disagree")
    print(f"{len(LENGTHS)} synthetic cases matched both outputs at {PIN}")


if __name__ == "__main__":
    main()
