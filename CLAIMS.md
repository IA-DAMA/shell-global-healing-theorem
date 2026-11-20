# SGH claim ledger

## Kernel-checked result

The five-term conditional bound is accepted in the formal model:

```text
Adv_SGH(A) <= eps_PQ + eps_ref + Pr[Bad_CC] + eps_svc + eps_env
```

The model accounts for retained copies, process exposure, Welcome,
resynchronization, retry, crash/restart and multiple installations within the
admitted operational trace. A challenge epoch whose live successor secret is
exposed is not fresh; healing is claimed only after a later independent,
unexposed contribution satisfying the named premises.

## Named hypotheses and residual terms

- `eps_gen`: real-to-ideal generator replacement in the exact game domain.
- `eps_hmac`: compatible QPT HMAC/HKDF advantage.
- `eps_exporter`: compatible QPT exporter real/ideal advantage.
- `eps_ref`: Product behavior outside the admitted source-typed trace.
- `Bad_CC`: an unrepresented physical observation or coverage failure.
- `eps_svc`: service/authentication boundary, including Ed25519.
- `eps_env`: operating-system, device and environmental capabilities outside
  the game.

## Not claimed

- numerical instantiation making every term negligible;
- active-QPT authentication from Ed25519;
- coherent superposition access to Product oracles;
- total extraction of Rust/Android binary semantics;
- independent audit, certification or production invulnerability.

## Evidence classes

- `PROVADO_KERNEL`: accepted EasyCrypt/Lean theorem or equivalence.
- `MODELO_TESTADO`: executable model or negative control.
- `AUDITADO_NA_FONTE`: source correspondence inspected at the pinned commit.
- `OBSERVADO_NA_IMPLANTACAO`: physical deployment observation; not supplied by
  this capsule.

