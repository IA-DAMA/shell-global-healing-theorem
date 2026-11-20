# Shell Global Post-Compromise Healing Theorem (SGH)

**Machine-checkable conditional theorem and public audit capsule**  
**Author:** Raphael M. Franco  
**Version:** 1.0.0 · 20 November 2026

The Shell Global Post-Compromise Healing Theorem is the public name of the
result historically tracked inside the project as milestone F4. F4 is not the
name of a product or protocol.

## Claim

For every admissible QPT adversary with auxiliary quantum memory and classical
queries to the Product, the checked composition proves:

```text
Adv_SGH(A) <= eps_PQ + eps_ref + Pr[Bad_CC] + eps_svc + eps_env
eps_PQ     =  eps_gen + eps_hmac + eps_exporter
```

Status: **kernel-checked under named hypotheses**. This is not an unconditional
certificate for the deployed Android application and not an independent audit.

## Start here

1. `CLAIMS.md` — exact theorem, hypotheses and non-claims.
2. `audit/F4/F4_GLOBAL_RESULT_20261120.md` — frozen result.
3. `REPRODUCE.md` — public checks and the controlled Product review boundary.
4. `SOURCE_BOUNDARY.json` — what is public, hash-bound or private.
5. `MANIFEST.sha256` — digest of every file in this capsule.

The proof modules, negative controls and public research lab are included. The
Linka monorepository, production configuration, user data, credentials and
unpublished research are not.

## Product relationship

Shell/R8 over OpenMLS is the runtime profile. This capsule checks the theorem
and the admitted source-typed projection. It does not publish the complete
Product source merely to make a stronger-sounding claim. An external reviewer
can inspect AGPL Corresponding Source for a distributed client release and may
request controlled access to additional non-distributed correspondence source.
Hashes establish byte identity; they do not replace source inspection.

## Rights

Copyright © 2025–2026 Raphael M. Franco.

Original verification software in this capsule is offered under
`AGPL-3.0-only`, except files carrying another SPDX/license. Editorial text and
the future paper are separately licensed as stated in `LICENSES.md`. Linka and
Shell marks and visual identity are not licensed by this capsule.

