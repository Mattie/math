#!/usr/bin/env bash
# Rebuild the two independent-verification tools from unmodified pinned source.
# Requires git, curl, a C toolchain, and the bundle's Lean 4.34.1 toolchain.
set -euo pipefail
export ELAN_TOOLCHAIN=leanprover/lean4:v4.34.1
lean --version
tools_dir=${1:-$(mktemp -d)}
mkdir -p "$tools_dir"
tools_dir=$(cd "$tools_dir" && pwd)
export CARGO_HOME="$tools_dir/cargo-home"
export RUSTUP_HOME="$tools_dir/rustup-home"
export CARGO_TARGET_DIR="$tools_dir/nanoda-target"
if [ ! -d "$tools_dir/nanoda/.git" ]; then
  git clone https://github.com/ammkrn/nanoda_lib "$tools_dir/nanoda"
fi
git -C "$tools_dir/nanoda" checkout --detach 3a2407216ee84a75f9e1aead6803d0578be06ae7
if [ ! -d "$tools_dir/lean4export/.git" ]; then
  git clone https://github.com/leanprover/lean4export "$tools_dir/lean4export"
fi
git -C "$tools_dir/lean4export" checkout --detach 076e8e57707e813375e8f9da8bf989799ace9680
if [ ! -x "$CARGO_HOME/bin/rustup" ]; then
  curl --proto '=https' --tlsv1.2 -fsSL \
    https://static.rust-lang.org/rustup/dist/x86_64-unknown-linux-gnu/rustup-init \
    -o "$tools_dir/rustup-init"
  chmod +x "$tools_dir/rustup-init"
  "$tools_dir/rustup-init" -y --no-modify-path --profile minimal --default-toolchain 1.99.0
fi
export PATH="$CARGO_HOME/bin:$PATH"
rustc --version
cd "$tools_dir/nanoda"
cargo build --release --locked
cd "$tools_dir/lean4export"
lake build
printf 'LEAN4EXPORT=%s\n' "$tools_dir/lean4export/.lake/build/bin/lean4export"
printf 'NANODA=%s\n' "$tools_dir/nanoda-target/release/nanoda_bin"
sha256sum "$tools_dir/lean4export/.lake/build/bin/lean4export" \
  "$tools_dir/nanoda-target/release/nanoda_bin"
