# Verification and reproduction

The frozen proof export passed fifteen literal statement comparisons, Rust
Nanoda, and Lean 4.34.1. A separately built Lean 4.34.0 reader accepted the same
bytes, reporting 118,382 declarations. Only the three foundational axioms
`propext`, `Classical.choice`, and `Quot.sound` occur. The complete original
execution used identified inherited caches, a fresh affine/required-overlay
build, and independent proof-body replay. It was not a clean compilation of
every upstream source. The package build test is recorded separately in
[the packaging check](evidence/package-check.json).

## Check the package and retained artifact

```sh
python3 scripts/check.py
python3 scripts/check.py --export release-assets/affine-proof-export.ndjson.gz
```

The first command requires every manifest-listed file. The second additionally
requires the export asset and hashes its **uncompressed** bytes. An absent export
is an error when `--export` is supplied. It is 1,280,383,670 bytes before gzip,
with SHA-256
`5f242493d0a285caaf5db6d0fa20eda5bd773f51fbd2c843544ac3b442abe5aa`.
The gzip asset and source ZIP have separate transport hashes in
`release-assets/SHA256SUMS.txt` beside the archives. These are prepared local
files; no public download has been published or tested.

Hash checking establishes file identity, not mathematical acceptance. The
manifest is an integrity aid, not a digital signature or independent trust root.

## Build the source

With Python 3.11+, Git, and elan installed, run:

```sh
python3 scripts/build.py
```

This invokes the actual solution and audit targets; the inherited project does
not have useful implicit default targets. It retrieves the Mathlib cache and
compiles the bundled inherited proofs and local extensions as needed. It checks
the locked upstream Git revisions and tracked-file cleanliness, then checks the
source digests again and rejects axiom reports outside the permitted set.
All twelve public endpoints report exactly those three axioms in the recorded
result. The output goes to `.work/` and `.lake/`.

The actual audit policy has imported-admission and extra-axiom rejection
controls. Run them independently with:

```sh
python3 scripts/audit_controls.py
```

Their fixtures are compiled only under `.work/`, outside the solution's imports.
See [CHECKERS.md](CHECKERS.md) for the exact policy and version limitations.

`--skip-cache-download` skips only the Mathlib cache retrieval step. It is useful
when caches and locked checkouts are already present. It does not turn a cached
build into a clean bootstrap. The package was tested this way on Linux with
identified inherited `OAI`/`Logarithm` and Mathlib caches, while the required
`AlgebraicLog` and `PairedAffine` objects started absent. A network-only bootstrap
from an empty machine and the Windows build route have not been tested here.

## Replay the exact export

Build Nanoda from the documented source pin with Rust/Cargo:

```sh
git clone https://github.com/ammkrn/nanoda_lib .work/nanoda
git -C .work/nanoda checkout --detach 3a2407216ee84a75f9e1aead6803d0578be06ae7
cargo build --release --locked --manifest-path .work/nanoda/Cargo.toml
```

Build the supplemental reader with the separate Lean 4.34.0 toolchain selected
by `replay-reader/lean-toolchain`:

This reproduces the **historical supplemental** route. That release lacks the
runtime fixes in 4.34.1; use the primary 4.34.1 Comparator result for current Lean
assurance and read [the checker caveats](CHECKERS.md) before using the older reader.

```sh
cd replay-reader
lake build
cd ..
python3 scripts/replay.py \
  --nanoda .work/nanoda/target/release/nanoda_bin \
  --lean-reader replay-reader/.lake/build/bin/kernel \
  --export release-assets/affine-proof-export.ndjson.gz
```

On Windows, executable paths end in `.exe` and line continuation differs; use
one line or PowerShell backticks. Replay needs several GB of RAM, roughly 1.3 GB
for the decompressed export, and substantial CPU time. Logs and a new receipt
are kept in a unique `.work/replay-*` directory. Add `--controls-only` and omit
`--export` to test the binaries against the tiny controls alone.

The replay script first requires a valid proof to pass both checkers. It then
requires Nanoda to reject an ill-typed proof at its type-equality check, and the
Lean reader to parse that fixture successfully but reject it with a declaration
type mismatch. An arbitrary crash or missing executable is not a passed negative
control. It verifies the retained export identity before checking its proof
bodies. The script records binary hashes, but relies on the operator to build
the documented pins; it does not certify a supplied executable's implementation.

The supplemental reader supplies only body replay. It does not independently
compare statements, enforce the permitted-axiom policy, or perform the current
Comparator's quotient post-check. The earlier maintained Comparator run supplies
those checks. Its current Lean 4.34.1 result and Nanoda result are preserved in
[the checker receipt](evidence/checker-receipt.json) and
[comparison log](evidence/comparator.log). The older reader is in the same Lean
kernel family and is not a second independently implemented kernel.

## Reproduce the literal statement comparison

The root `config.json`, `Challenge.lean`, `Solution.lean`, and `StandardBridge.lean`
are exactly the earlier verified comparison inputs. With the compatible pinned
Comparator, lean4export, Nanoda, and Landrun installed and configured, run:

```sh
lake env comparator config.json
```

Tool source pins and binary identities are in
[checker-receipt.json](evidence/checker-receipt.json). Set
`COMPARATOR_LEAN4EXPORT`, `COMPARATOR_NANODA`, and `COMPARATOR_LANDRUN` to the
respective compatible executables. Consult the pinned
[Comparator instructions](https://github.com/leanprover/comparator/tree/ca04cfc72b550331658ec314bf47685281bfd4bf)
for building the tools and its Linux isolation requirements. This package does
not automate installation of the full isolation environment. The earlier run
also exercised valid-proof, statement-mismatch, forbidden-axiom, and write/socket
boundary controls. Its success does not certify containment against arbitrary
hostile submissions.

The solution never imports `Challenge`; its intentional `sorry` placeholders
belong only to the trusted statement side. The exported inventory records all
twelve original theorem bodies, fifteen wrapper bodies, and exactly the three
structured axiom names. Its count of 112,870 recognized declaration records is
not the reader's total of 118,382, which includes additional declaration kinds.

Source compilation, statement comparison, export identity, axiom inventory, and
kernel replay are distinct checks. Packaging reuses the earlier proof replays
because every proof/specification byte is unchanged; it does not relabel the
portable build or control test as a new full replay.

## Fresh GitHub verification

The containing repository's `verification/isolated-affine/` runner and manual
`.github/workflows/isolated-affine.yml` workflow prepare a fresh hosted verification
of all fifteen final wrappers. They are repository infrastructure, separate from
this standalone source archive. [WORKFLOW.md](WORKFLOW.md) tracks setup, actual
execution, and evidence audit as separate milestones. No hosted success is claimed
by the local evidence above.

The intended run prepares pinned tools and official upstream dependency caches in
a trusted project, then copies the frozen candidate source into fresh build state.
It uses the maintained Comparator with Landrun and the tested systemd restrictions,
exercises acceptance, rejection, and boundary controls, and requires full-target
comparison plus acceptance by Lean and Nanoda. Official dependency caches remain a
declared trust input; this is not a from-source rebuild of every dependency.

The ordinary CI integrity check and audit of the retained build log do not execute
this verifier. A completed hosted run must have its exact commit, run/attempt,
receipt, logs, protected-input checks, and target coverage audited before its
checklist entries can be marked complete.
