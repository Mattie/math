# Publication verification

The six preprint packages keep their reviewed Lean sources, toolchain/dependency
pins, manuscripts, exports, and historical receipts unchanged. Repairs affect
verification tooling and documentation. New build logs are separate evidence.

## Checks

Run `python3 verification/publication/test_verification.py` for script regression
tests and `python3 verification/publication/check-upstream.py` for the pinned
OpenAI comparison. The upstream check requires network access and Git history
containing the recorded dependency revision. It checks the complete 869-module
inventory, including the two packages that fetch a pinned dependency project.

Each package retains its documented verification entrypoint. Frozen dependency
style warnings remain visible; catalogue wrappers are checked separately with
warnings treated as errors. Fresh axiom output must include every expected
declaration and only `propext`, `Classical.choice`, and `Quot.sound` (or a subset).
Missing or malformed reports and imported `sorryAx` fail verification.

CI runs publication checks and script regressions automatically. Full Lean builds
are explicitly dispatched with `rebuild_proof=true`; their logs are retained as
Actions artifacts. A green publication-only run is not a proof build.
The [successful six-package reproduction](https://github.com/Mattie/math/actions/runs/37872740986)
checked commit `a1fdf2f3c6941d95dbce9f16b540856dbcd3899b`: all six builds,
fresh axiom audits, post-build publication checks, and log uploads passed.
Six log artifacts were retained. The [earlier run](https://github.com/Mattie/math/actions/runs/37868135214)
also passed its proof steps, but failed to upload logs; it remains a distinct historical result.
The separate [PR run](https://github.com/Mattie/math/actions/runs/37872739030)
hit an anonymous GitHub API rate limit. Authenticated provenance checks passed in
[the subsequent PR run](https://github.com/Mattie/math/actions/runs/37925371633)
at `324b8388f658d97714a7d4172823e91a57ce67d0`. Later evidence/documentation additions
do not change the proof inputs or six package verification entrypoints.

## Independent catalogue-statement evidence

The existing [portable four-statement workflow](../irrationality-exponents/README.md)
and its [retained validation](../irrationality-exponents/validation/README.md)
are included separately from the six-package Lean builds. Comparator compared
compiled statements and definition closures; Nanoda checked the same solution
exports. The [coverage note](../irrationality-exponents/COVERAGE.md) explains the
exact normalized-logarithm wrapper and its correspondence with FC #6942.
Run `python3 verification/publication/check-wrapper-evidence.py` to check pinned
inputs and retained log identities. This command does not rerun either checker.

## Resources

Packages retain separate Lake workspaces. One observed native workspace used
about 7.25 GiB for Mathlib and 5.50 GiB for project build output, excluding the
toolchain and exports. Allow additional space for downloads and each retained
export (up to about 1.28 GB uncompressed). Building all packages simultaneously
multiplies storage and memory requirements. Put WSL builds on a native Linux
filesystem where practical. Cache reuse and hardware affect time substantially;
the full CI logs record elapsed time and peak memory for each actual run.

## Retained exports

The [distribution inventory](release-assets.json) records six transport archives
and their original uncompressed identities. Five transports are unchanged;
the quadratic-logarithm transport wraps its unchanged export in deterministic gzip.

Publication is planned at [Recorded proof exports — October 8, 2026](https://github.com/Mattie/math/releases/tag/proof-exports-2026-10-08).
Until the repair PR is merged and verification passes, this is a planned release
location, not an available download. Existing historical receipts retain their
original dates and scope; preparing or publishing these files does not constitute
a new independent kernel replay.

After publication, download all six attachments to one directory and run:

```sh
python3 verification/publication/check-release-assets.py /path/to/downloads
```

This checks both compressed bytes and streamed uncompressed bytes against the
inventory. Applicable upstream licenses and notices remain in each preprint.

The [additional wrapper inventory](wrapper-release-assets.json) separately records
`realnorm-catalogue-20261008T144533Z.ndjson.gz`, prepared from the retained portable
validation run. Its original export identity is preserved. This seventh archive
is planned for the same release; it does not replace `realnorm-main.ndjson.gz`.
Use `--inventory verification/publication/wrapper-release-assets.json` with the
same download checker to validate it separately.

For a fresh public run of the independent checking route, use the optional
[`independent_proofs` CI job](../irrationality-exponents/CI.md). It retains new
complete receipts and logs for the four selected final statements, separately
from the historical evidence and the six-package Lean build matrix.
