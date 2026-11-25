#!/usr/bin/env bash
# Provision public dependencies before entering the network-isolated proof build.
set -euo pipefail
runner=$(cd -- "$(dirname -- "$0")" && pwd)
inputs="$runner/../inputs"
work=$(realpath -m "${1:?Pass a new working directory}")
mkdir "$work"
cd "$work"
(cd "$inputs" && sha256sum -c --strict SHA256SUMS)
rev=a0e8ac417cddc6ffa88e43cfd68d2b58ea339517
git init -q upstream
git -C upstream fetch -q --depth=1 https://github.com/RamanujanMachine/zeta2_four_trajectory_matrices.git "$rev"
git -C upstream checkout -q --detach FETCH_HEAD
for file in lake-manifest.json lakefile.toml lean-toolchain; do cmp "$inputs/$file" "upstream/$file"; done
release=lean-4.35.0-rc4-linux
curl -fLsS --retry 3 "https://github.com/leanprover/lean4/releases/download/v4.35.0-rc4/$release.tar.zst" -o lean.tar.zst
echo 'e78e14c54c39a145945833cfcdb219458d650c210847a90dcef8fa8ff05ab51a  lean.tar.zst' | sha256sum --check --strict -
tar -xf lean.tar.zst
rm -- lean.tar.zst
export PATH="$work/$release/bin:$PATH"
unset LEAN_PATH LEAN_SRC_PATH
mkdir deps
cp "$inputs"/{lakefile.toml,lake-manifest.json,lean-toolchain} deps/
(cd deps && lake exe cache get Mathlib)
cmp deps/lake-manifest.json "$inputs/lake-manifest.json"
python3 -I -B "$runner/verify.py" --toolchain "$work/$release" --bwrap "$(command -v bwrap)" \
  --upstream "$work/upstream" --packages "$work/deps/.lake/packages" --work "$work/run"
