# Replay the two-case pi formalization

These draft instructions reconstruct the source environment for
the November 26, 2026 replay of PiTwoCaseBridge.main. The
November 26 run used already compiled inherited modules. The
fresh-checkout steps below have yet to be tested end to end.

Use a Linux shell with Git, Elan, Rust and Cargo, unzip, and
space for the Lean dependencies and the 1.26 GB uncompressed export.
Copy this directory's stock-reader/ and nanoda.json to an empty Linux work
directory. Put the [companion ZIP](../../preprints/The-irrationality-exponent-of-pi-through-a-two-case-determinant-argument-October-11-2026/build/PiTwoCaseBridge-2026-11-26.zip)
in that directory and run both blocks in the same Bash session.

## Build the inherited modules and the overlay

```bash
set -euo pipefail
root=$PWD
tools=$root/tools
bundle=$root/bridge
mkdir -p "$tools" "$bundle"
unzip -q PiTwoCaseBridge-2026-11-26.zip -d "$bundle"
inherited=$bundle/formalizations/AffineLogarithms
bridge=$bundle/formalizations/PiTwoCaseBridge
overlay=$root/overlay

elan toolchain install leanprover/lean4:v4.34.1
git init -q "$tools/openai-math"
git -C "$tools/openai-math" fetch --depth=1 https://github.com/openai/math.git \
  fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
git -C "$tools/openai-math" sparse-checkout set lean
git -C "$tools/openai-math" checkout --detach FETCH_HEAD
test "$(git -C "$tools/openai-math" rev-parse HEAD:lean/OAI/NumberTheory/PiExponent)" = \
  8a202af08bf5a2b708abfc07248834e4bd2a88fd
cp -R "$tools/openai-math/lean/OAI" "$inherited/"
cp "$tools/openai-math/lean/OAI.lean" "$inherited/"
cp "$bridge/lean-toolchain" "$inherited/"
cat > "$inherited/lakefile.lean" <<'EOF'
import Lake
open Lake DSL
package QuadraticPeriods where
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean_lib OAI
EOF
cd "$inherited"
lake exe cache get
mapfile -t targets < <(
  awk '$1 == "import" && $2 ~ /^OAI\./ { sub(/\r$/, "", $2); print "+" $2 }' \
    "$bridge"/PiTwoCaseBridge/*.lean | sort -u
)
test "${#targets[@]}" -gt 0
lake build "${targets[@]}"
lake env bash "$bridge/build-overlay.sh" "$overlay"
```

The import scan removes any CR from the target names. It leaves the frozen Lean files byte for byte intact.

The overlay script elaborates Audit.lean. The recorded axiom audit
for Theorem 5.1 and both pi endpoints lists propext, Classical.choice,
and Quot.sound.

## Export and replay

```bash
cd "$root"
git init -q "$tools/lean4export"
git -C "$tools/lean4export" fetch --depth=1 https://github.com/leanprover/lean4export.git \
  05d43a2bc773b40ecfdebb32294192a5ef756951
git -C "$tools/lean4export" checkout --detach FETCH_HEAD
(cd "$tools/lean4export" && lake +leanprover/lean4:v4.34.1 --keep-toolchain build lean4export)
(cd "$root/stock-reader" && lake +leanprover/lean4:v4.34.1 --keep-toolchain build kernel)
git init -q "$tools/nanoda"
git -C "$tools/nanoda" fetch --depth=1 https://github.com/ammkrn/nanoda_lib.git \
  0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929
git -C "$tools/nanoda" checkout --detach FETCH_HEAD
cargo build --release --locked --manifest-path "$tools/nanoda/Cargo.toml"

cd "$inherited"
lake env bash -c '
  export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
  "$2" PiTwoCaseBridge.Main -- PiTwoCaseBridge.main
' _ "$overlay" "$tools/lean4export/.lake/build/bin/lean4export" > "$root/closure.ndjson"

cd "$root"
sha256sum closure.ndjson
./stock-reader/.lake/build/bin/kernel closure.ndjson
"$tools/nanoda/target/release/nanoda_bin" nanoda.json
```

The recorded export had 1,255,233,780 bytes and SHA-256
9c8013cd869e49790892ca6224624cafed2a7b9df6a6461b3c463716d0133b31.
Stock Lean printed Accepted 117238 declarations.
Nanoda printed Checked 117241 declarations with no errors.
The stock reader removes three quotient declarations added by the kernel.
Both commands exited successfully. Compare the size, hash, and checker
results before describing a fresh run as a replay of the recorded bytes.
The export command above provides a reconstruction route. The historical
export and full checker logs are separate from this source package.
