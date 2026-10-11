# Affine isolated source verifier setup

Status: RUN authorized; branch publication and dispatch are being prepared. No
hosted affine result is claimed. See the package's [workflow checklist](../../formalizations/AffineLogarithms/WORKFLOW.md)
for proof position and the separate execution and evidence-audit milestones.

The manual [workflow](../../.github/workflows/isolated-affine.yml) checks all 15
frozen `PairedAffineVerification` declarations from `Solution`, including the
three standard Mathlib exponent bridges. Its exact target list and conventional
axiom policy come from the frozen package's `config.json`. It validates all 969
manifest entries (968 Lean source/specification files and the configuration),
the original Lake configuration, dependency lock, toolchain and earlier receipt.
No mathematical file or earlier evidence is rewritten.
The auxiliary `replay-reader` program and local `.work`/`.lake` trees are outside
the candidate source inventory and are never copied into the checking project.

The runner reuses the reviewed `isolated-preflight` machinery and the
`isolated-6942` resource/boundary helpers. Its dedicated pins retain the affine
receipt's Comparator `ca04cfc72b550331658ec314bf47685281bfd4bf` and exporter
`05d43a2bc773b40ecfdebb32294192a5ef756951`; these differ from the older FC 6942
configuration. This process explicitly selects those pins for preflight setup
without changing the shared runner. Lean remains 4.34.1. The package's dated
[checker assessment](../../formalizations/AffineLogarithms/CHECKERS.md) is reused;
no new upstream safety assessment was performed for this setup. Its stated
Nanoda and descendant-process limitations still apply.

Execution first installs pinned tools and runs valid, mismatched-statement,
forbidden-axiom, write/socket-boundary and imported-admission controls. The last
control imports a theorem proved with `sorry` and must reach Comparator's
specific `sorryAx` rejection through the same isolated frontend. An unrelated
failure, timeout or crash does not count as a passing rejection control.

Dependencies are prepared in a separate trusted project using a generated Lake
configuration and the official Mathlib cache. Dependency revisions, source and
compiled bytes are inventoried. This trusts the official cache; it is not a
from-source rebuild of upstream dependencies. Only afterward are all frozen
candidate sources copied byte for byte into fresh scratch state. No inherited
candidate `.olean`, `.ilean`, build traces, submitted Lake code or other compiled
artifacts are copied. The generated Lake configuration is used by the outer
`lake env`; trusted dependency artifacts stay outside writable candidate `.lake`.
The complete source inventory is preserved, while Lake builds the dependency
closure of the requested `Solution` module.

Stock Comparator builds/exports the challenge before building/exporting the
candidate under Landrun and the outer systemd AF_UNIX restriction. Success
requires both exports to name all 15 targets, both kernels to accept, every
control to pass, and protected source, dependency and tool identities to remain
unchanged. These tests establish only their exercised boundary operations, not
universal hostile-code containment. This route does not retain a new standalone
export or claim byte-for-byte replay of the historical export.

The initial disk/memory budget follows FC 6942: 35 GiB free before setup, 10 GiB
before the proof, and 12 GiB memory with four CPUs and four Lean threads. The
proof service gets five hours within a six-hour job because this route rebuilds
the inherited candidate closure too. These are unvalidated limits, not measured
affine hosted requirements; the job cap can terminate a long setup/proof earlier.
Disk cleanup runs only on the disposable GitHub-hosted VM before Go installation.
No workstation cleanup or proof build is part of the preparation tests.

Run local preparation tests from the repository root:

```console
python -B -m unittest discover -s verification/isolated-affine -p test_*.py
```

The workflow has read-only repository permissions, no persisted checkout
credentials, no automatic triggers, and serialized execution. Evidence upload
runs even after failure and contains the receipt, command logs, generated control
inputs, frozen checking inputs, dependency inventory and early setup diagnostics.
The final evidence index hashes the completed console log and receipt after the
verifier exits. Candidate build trees, tool caches and historical exports are
excluded. Artifacts expire after 90 days; dispatch, audit, durable retention and
publication remain separate authorized actions. A green badge alone is not the
final evidence audit.

For the first branch run, the already registered `isolated-irrationality.yml`
workflow also accepts `case=affine` and invokes this same runner with the same
resource limits and final evidence index. This avoids needing to merge a new
workflow onto the default branch before dispatch. The receipt records the actual
workflow ref. No other case is dispatched as part of the affine run.
