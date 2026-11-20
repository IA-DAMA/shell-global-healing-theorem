#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "$0")/../.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT

cd "$root"
python3 -B -m unittest discover -s formal/tools -p 'test_f4*contract*.py'
python3 -B audit/F4/check_cc_prefix.py

mkdir -p "$out/ec"
cp formal/easycrypt/*.ec "$out/ec/"
F4_EC_DIR="$out/ec" bash research/november-2026/verify_easycrypt.sh \
  >"$out/easycrypt.log" 2>&1 || {
    tail -c 2500 "$out/easycrypt.log"
    exit 1
  }
grep -Fx 'EASYCRYPT_ALL_83_ACCEPTED=true' "$out/easycrypt.log"

lean audit/F4/SelectedPossession.lean

cargo test \
  --manifest-path research/november-2026/openmls-lab/Cargo.toml \
  --locked --all-targets -- --test-threads=1

python3 -B audit/F4/check_cc_prefix.py --negative "$out/ec"

printf 'SGH_PUBLIC_FORMAL_CHECKS_PASSED=true\n'
printf 'SGH_PRODUCT_CORRESPONDENCE_REQUIRES_PINNED_NATIVE_SOURCE=true\n'
