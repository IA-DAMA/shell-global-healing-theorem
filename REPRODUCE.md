# Reproduction boundary

## Public capsule

The public capsule contains the 83 EasyCrypt modules, Lean possession proof,
contract tests, negative controls and the public Rust/OpenMLS research lab used
by the frozen result. Tool versions are recorded in the machine receipt.

On a Windows host with the pinned WSL toolchain:

```powershell
powershell -ExecutionPolicy Bypass -File audit/F4/reproduce_public_windows.ps1
```

The command verifies the manifest before running public formal and executable
checks. Cargo downloads only dependencies pinned by the included `Cargo.lock`;
use a network-isolated mirror or vendor directory if the review requires a
fully offline build. A result must not be reported as reproduced if any module
or negative control is skipped.

## Controlled Product correspondence

The historical full command `audit/F4/reproduce_global_windows.ps1` additionally
requires a checkout containing native Product commit
`476bd8f1f4755ae2f6a689d23a937ba2573434a4`. That source is not silently copied
into this research capsule. Depending on the reviewed release, it is available
as AGPL Corresponding Source or through controlled review.

Therefore:

- the public capsule can reproduce the theorem and public model checks;
- the exact Product correspondence cannot be called independently reproduced
  unless the reviewer also obtained and inspected the pinned native source;
- a matching hash alone is provenance evidence, not a semantic audit.

