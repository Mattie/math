# Verification and reproduction

This record applies to the five new `lean/Degree/` files, whose exact SHA-256
identities are in [checker metadata](evidence/checker-metadata.json). It is
separate from the four earlier papers' verification records.

## Native checking

Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, freshly compiled
all five modules with `autoImplicit=false`. The documented overlay command also
rebuilt them. The build reused compiled dependencies after matching all 924
`OAI/` and `Logarithm/` source files. This was not a fresh rebuild of the entire
inherited Mathlib and π library. The packaged command is tested separately from
the earlier checking runs; its result is in [the preparation receipt](evidence/preparation.json).

The audit prints the principal concrete statements, checks an explicit `1,x`
projective-line example for every natural power, and prints the axiom closures.
The six principal declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`. None of the five new files contains a proof hole, new axiom,
`native_decide`, or unsafe declaration.

## Selected proof export and replay

The selected export contains the following declarations and their proof dependencies:

- `Degree.supportBound_of_pow`
- `Degree.monomial_all_supportBound`
- `Degree.logarithm_all_supportBound`
- `Degree.admissible_all_supportBound`
- `Degree.Audit.projective_line_example`

The positive-power and zero-power lemmas are in this dependency closure. Unused
helper declarations are covered by the native build, rather than by this export.
The exporter was lean4export 3.1.0, pinned to
[`076e8e57707e813375e8f9da8bf989799ace9680`](https://github.com/leanprover/lean4export/tree/076e8e57707e813375e8f9da8bf989799ace9680).
The uncompressed export is 730,631,418 bytes, with SHA-256
`e0d80c6854703682a764bc601cd35b971bf383ea2715b3997323174e3f16dd89`.

[Nanoda](https://github.com/ammkrn/nanoda_lib/tree/3a2407216ee84a75f9e1aead6803d0578be06ae7)
0.4.19, commit `3a2407216ee84a75f9e1aead6803d0578be06ae7`, accepted all 73,054
declarations with zero errors and exit status 0. The configuration allowed only
the three standard axioms above, hard-failed on any other axiom, and disabled the
option to permit all axioms.

Lean 4.34.0, commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, replayed 73,051
declarations with exit status 0. The retained reader removes `Quot.mk`,
`Quot.lift`, and `Quot.ind` because registering `Quot` regenerates them, covering
the same 73,054 declarations. It invokes kernel replay, not its parse-only mode.
The [reader source and build files](lean/reference-reader) and
[reader provenance](evidence/second-lean-reader.json) are retained. `Main.lean`
is byte-identical to Lean Kernel Arena's official reader at commit
`b83254de5146ef34147ab82a48edbe1856b0edcc`; its parser is pinned to the exporter
revision above. The standalone reader directory itself was not a Git checkout.

These two routes share the exporter and its artifact. Lean 4.34.0 is a related
kernel implementation; Nanoda supplies implementation diversity. Recorded binary
digests identify the checking runs, rather than promising reproducible binary
hashes on every platform. The [concise checking receipt](evidence/checker-results.json)
records the outcomes. Private execution logs are not distributed here.

## Independent automated review

A separate Astra Max reviewer freshly compiled the five immutable modules and
boundary diagnostics, checked nonvacuity and the concrete specializations, and
recomputed the export identity. It audited the recorded replay outcomes without
rerunning Nanoda or the second Lean kernel. The review found no remaining
mathematical or specification defect after clarifying the scheme-theoretic
closure and retaining the reader provenance. The five Lean files were unchanged.

This was model review, not independent human mathematical review. No new
negative-control experiment, specification comparator run, novelty certification,
or peer-reviewed acceptance is claimed for this extension.

## Rebuild the overlay

Use Bash, Python 3.11 or later, Git, and Lean 4.34.1 with Lake. From this package's
`lean/` directory, run:

```bash
bash verify.sh
```

From the package root, the equivalent command is `bash lean/verify.sh`. The first
Lean invocation selects `lean/lean-toolchain` even when elan has no default
toolchain. Caller-relative dependency paths retain their usual meaning.

With no `LEAN_DEPENDENCY_ROOT` set, the command fetches the public dependency
project at commit `0cfe10002ea95c45721b93d18bffbe2c3bbbcbbd`, obtains the pinned
Mathlib cache, and builds that project. Its source and configuration identities
are checked before the overlay is compiled. The download and build require network
access; all outputs go under ignored `.verification/` directories.

To reuse an already built matching dependency project:

```bash
LEAN_DEPENDENCY_ROOT=/path/to/pinned-project/lean bash verify.sh
```

The [dependency pin](evidence/dependency-pin.json),
[924-file manifest](evidence/dependency-source-sha256.json), and
[configuration manifest](evidence/dependency-config-sha256.json) fix the input.
The initial public dependency commit was compared with all 924 frozen source
digests during preparation. Reusing a cache does not make this a clean rebuild
of all inherited dependencies.

## Regenerate or replay the export

Build lean4export at the pinned revision using Lean 4.34.1. Set `LEAN4EXPORT` to
its executable and `LEAN_DEPENDENCY_ROOT` to the built dependency project, then
run `bash scripts/export.sh`. It checks the export against the recorded identity.
Different export bytes require a new audit and verification record.

Build Nanoda at its pinned revision, set `NANODA_BIN` to its executable, and run:

```bash
bash scripts/replay.sh nanoda /path/to/degree-main.ndjson
```

For the other route, build `lean/reference-reader/` with Lean 4.34.0 using
`lake build kernel`. Set `LEAN340_READER` to the resulting executable and run:

```bash
bash scripts/replay.sh lean340 /path/to/degree-main.ndjson
```

The replay script validates the artifact first. It generates the restricted
Nanoda configuration in `.verification/replay/` or invokes the full retained
reader. Ensure the executables were built from the stated revisions; the script
does not certify arbitrary caller-supplied checker binaries.

## Manuscript and preservation

`bash scripts/build-paper.sh` builds the standalone LaTeX source using Tectonic.
The published PDF was built with Tectonic 0.17.0 and visually inspected page by
page. Its author metadata is Ryan Matthew Casper.

The four earlier preprints' 3,758 Lean and TeX source files matched the retained
local baseline during review and preparation. They are not modified by this
package. Their previous manuscripts, exports, and checking claims remain separate.

## Verification and distribution update

Verification scripts enforce the three-axiom allowlist on fresh output and reject
missing reports. Frozen dependency style warnings remain visible; catalogue
wrappers are compiled separately with warnings treated as errors. Publication
checks exclude generated dependency/build directories. Historical receipts and
all proof sources retain their original identities.

The [repository verification guide](https://github.com/Mattie/math/blob/main/verification/publication/README.md)
records the six-package build run, resource observations, and the distinction
between publication checks and full Lean builds. The build run's live status,
not a publication-only green check, determines whether reproduction succeeded.

The retained export is listed in the [distribution inventory](https://github.com/Mattie/math/blob/main/verification/publication/release-assets.json).
The [release location](https://github.com/Mattie/math/releases/tag/proof-exports-2026-10-08)
is planned; publication awaits the repair PR's merge and successful verification.
After publication, use the existing replay commands with the downloaded export.
Publishing a retained export does not claim a new kernel-check run.
