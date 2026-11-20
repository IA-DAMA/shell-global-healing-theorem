//! Execution-level trace of the exact OpenMLS 0.9.0 public exporter API.
 //!
 //! Test-only, synthetic groups. Intercepts public HKDF label metadata and
 //! context length. Never prints, serializes or logs PRKs, keys or raw outputs.
 //! An observed crypto-call trace is NOT a PCS game-security proof.
use super::*;
use openmls::prelude::tls_codec::SecretVLBytes;
use openmls_rust_crypto::RustCrypto;
use openmls_traits::types::{
    AeadType, CryptoError, ExporterSecret as HpkeExporterSecret, HashType,
    HpkeCiphertext, HpkeConfig, HpkeKeyPair, KemOutput, SignatureScheme,
};
use std::{fs, sync::Mutex, time::{SystemTime, UNIX_EPOCH}};

#[derive(Clone, Debug, PartialEq, Eq)]
struct CryptoCall {
    kind: &'static str,
    input_len: usize,
    output_len: usize,
    public_info: Vec<u8>,
}

#[derive(Default)]
struct TraceCrypto {
    inner: RustCrypto,
    seen: Mutex<Vec<CryptoCall>>,
}
impl TraceCrypto {
    fn log(&self, kind: &'static str, input_len: usize, output_len: usize, info: &[u8]) {
        self.seen.lock().expect("trace mutex").push(CryptoCall {
            kind,
            input_len,
            output_len,
            public_info: info.to_vec(),
        });
    }
    fn calls(&self) -> Vec<CryptoCall> {
        self.seen.lock().expect("trace mutex").clone()
    }
}
impl OpenMlsCrypto for TraceCrypto {
    fn supports(&self, suite: Ciphersuite) -> std::result::Result<(), CryptoError> {
        self.inner.supports(suite)
    }
    fn supported_ciphersuites(&self) -> Vec<Ciphersuite> {
        self.inner.supported_ciphersuites()
    }
    fn hkdf_extract(
        &self, typ: HashType, salt: &[u8], ikm: &[u8]
    ) -> std::result::Result<SecretVLBytes, CryptoError> {
        // No raw key material is recorded.
        self.log("extract", 0, 0, &[]);
        self.inner.hkdf_extract(typ, salt, ikm)
    }
    fn hmac(
        &self, typ: HashType, key: &[u8], message: &[u8]
    ) -> std::result::Result<SecretVLBytes, CryptoError> {
        self.log("hmac", 0, 0, &[]);
        self.inner.hmac(typ, key, message)
    }
    fn hkdf_expand(
        &self, typ: HashType, prk: &[u8], info: &[u8], len: usize
    ) -> std::result::Result<SecretVLBytes, CryptoError> {
        // HKDF info is public: TLS-encoded domain/label/context hash.
        self.log("expand", info.len(), len, info);
        self.inner.hkdf_expand(typ, prk, info, len)
    }
    fn hash(
        &self, typ: HashType, data: &[u8]
    ) -> std::result::Result<Vec<u8>, CryptoError> {
        self.log("hash", data.len(), 0, &[]);
        self.inner.hash(typ, data)
    }
    fn aead_encrypt(
        &self, alg: AeadType, key: &[u8], data: &[u8], nonce: &[u8], aad: &[u8]
    ) -> std::result::Result<Vec<u8>, CryptoError> {
        self.log("aead_encrypt", 0, 0, &[]);
        self.inner.aead_encrypt(alg, key, data, nonce, aad)
    }
    fn aead_decrypt(
        &self, alg: AeadType, key: &[u8], ct: &[u8], nonce: &[u8], aad: &[u8]
    ) -> std::result::Result<Vec<u8>, CryptoError> {
        self.log("aead_decrypt", 0, 0, &[]);
        self.inner.aead_decrypt(alg, key, ct, nonce, aad)
    }
    fn signature_key_gen(
        &self, alg: SignatureScheme
    ) -> std::result::Result<(Vec<u8>, Vec<u8>), CryptoError> {
        self.inner.signature_key_gen(alg)
    }
    fn verify_signature(
        &self, alg: SignatureScheme, data: &[u8], pk: &[u8], sig: &[u8]
    ) -> std::result::Result<(), CryptoError> {
        self.inner.verify_signature(alg, data, pk, sig)
    }
    fn sign(
        &self, alg: SignatureScheme, data: &[u8], key: &[u8]
    ) -> std::result::Result<Vec<u8>, CryptoError> {
        self.inner.sign(alg, data, key)
    }
    fn hpke_seal(
        &self, config: HpkeConfig, pk: &[u8], info: &[u8], aad: &[u8], msg: &[u8]
    ) -> std::result::Result<HpkeCiphertext, CryptoError> {
        self.inner.hpke_seal(config, pk, info, aad, msg)
    }
    fn hpke_open(
        &self, config: HpkeConfig, input: &HpkeCiphertext, sk: &[u8],
        info: &[u8], aad: &[u8]
    ) -> std::result::Result<Vec<u8>, CryptoError> {
        self.inner.hpke_open(config, input, sk, info, aad)
    }
    fn hpke_setup_sender_and_export(
        &self, config: HpkeConfig, pk: &[u8], info: &[u8],
        context: &[u8], len: usize
    ) -> std::result::Result<(KemOutput, HpkeExporterSecret), CryptoError> {
        self.inner.hpke_setup_sender_and_export(config, pk, info, context, len)
    }
    fn hpke_setup_receiver_and_export(
        &self, config: HpkeConfig, enc: &[u8], sk: &[u8],
        info: &[u8], context: &[u8], len: usize
    ) -> std::result::Result<HpkeExporterSecret, CryptoError> {
        self.inner.hpke_setup_receiver_and_export(config, enc, sk, info, context, len)
    }
    fn derive_hpke_keypair(
        &self, config: HpkeConfig, ikm: &[u8]
    ) -> std::result::Result<HpkeKeyPair, CryptoError> {
        self.inner.derive_hpke_keypair(config, ikm)
    }
}
fn includes(info: &[u8], public_label: &[u8]) -> bool {
    info.windows(public_label.len()).any(|x| x == public_label)
}

#[test]
fn actual_openmls_exporter_api_uses_context_hash_then_two_labeled_expands() {
    let stamp = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
    let path = std::env::temp_dir().join(format!(
        "shell-f4-cryptographic-call-{}-{stamp}.sqlite", std::process::id()
    ));
    initialize(&path).expect("synthetic MLS setup");

    let connection = store::open(&path).expect("open lab state");
    let state = read_state(&connection).expect("read accepted checkpoint");
    let provider = Provider::new(&connection);
    for (idx, leg) in [ChallengeLeg::Classical, ChallengeLeg::PostQuantum]
        .iter().copied().enumerate()
    {
        let challenge = accepted_challenge(&path, leg).expect("accepted challenge");
        let group = load_group(&provider, &state.legs[idx].group_id)
            .expect("accepted OpenMLS group");
        let tracer = TraceCrypto::default();
        let observed = group.export_secret(
            &tracer,
            &challenge.exporter_label,
            &challenge.exporter_context,
            challenge.output_length,
        ).expect("OpenMLS exporter");
        let canonical = group.export_secret(
            provider.crypto(),
            &challenge.exporter_label,
            &challenge.exporter_context,
            challenge.output_length,
        ).expect("baseline exporter");
        assert!(observed == canonical, "traced crypto differs from OpenMLS backend");
        assert!(observed.len() == 32, "exporter output length incorrect");
        let calls = tracer.calls();
        assert!(calls.len() == 3, "unexpected exporter cryptographic call sequence");
        assert!(calls[0].kind == "hash", "first step is context Hash");
        assert!(calls[0].input_len == challenge.exporter_context.len(),
            "hashed context length differs from typed binding");
        assert!(calls[1].kind == "expand", "second step is DeriveSecret(label)");
        assert!(includes(&calls[1].public_info, b"MLS 1.0 shell.f4.accepted/1"),
            "DeriveSecret used an unexpected public exporter label");
        assert!(calls[2].kind == "expand", "third step is ExpandWithLabel(exported)");
        assert!(includes(&calls[2].public_info, b"MLS 1.0 exported"),
            "final expansion used an unexpected public exporter label");
        assert!(calls[2].output_len == 32, "final HKDF output length mismatch");
    }
    drop(connection);
    let _ = fs::remove_file(&path);
}
