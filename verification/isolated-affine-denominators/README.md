# Denominator affine verification

The October 12 local run **passed** its six-target comparison, both primary
kernels, exact body/axiom inventory, and direct Nanoda and separately built
Lean 4.34.1 replays of the same retained bytes. See the
[final summary](results/local-replay-2026-10-12.json),
[export inventory](results/export-inventory-2026-10-12.json), and
[evidence index](results/evidence-index-2026-10-12.json).
This used identified inherited/upstream caches; hosted source verification has
not been performed. Nanoda's reproduced projection defect makes the successful
same-byte Lean replay essential.

The independent specification covers the general degree-four paired-embedding
theorem and all five `log(3/2) + sqrt(2)` endpoints. [Challenge.lean](Challenge.lean)
uses only standard Mathlib definitions and literal approximation quantifiers.
[Solution.lean](Solution.lean) binds those statements directly to the six public
declarations. The general wrapper is a separate target because the pilot invokes
the fixed-denominator theorem and would not by itself cover denominator existence.

The [source manifest](source-manifest.json) freezes the ten new proof modules,
966 inherited Lean sources, and the independent specification/configuration.
It was created after the author reported strict compilation and the seven-target
axiom audit. The [policy summary](results/axiom-policy-2026-10-12.json) binds the
unchanged maintained policy's acceptance to that exact author manifest, target
array and diagnostic log. Fresh imported-proof and malformed-log controls are
identified in [axiom-controls](results/axiom-controls-2026-10-12.json).

The [pins](pins.json) and [scoped checker assessment](CHECKERS.md) preserve the
existing compatible Comparator/exporter/Nanoda revisions. A new separately built
Lean 4.34.1 reader passed the actual positive, parseable-invalid, and typed-rejection
controls, alongside Nanoda on the same tiny exports. Its
[summary](results/stock-controls-2026-10-12.json) identifies the reader binary,
source, dependency, compiler, logs and link provenance.

Portable [positive](controls/positive.ndjson) and
[ill-typed](controls/ill-typed.ndjson) exports retain the exact one-body mutation
used in those controls. Run the built `stock-reader/.lake/build/bin/kernel` on
each file: the positive must exit zero, the negative must reject with a declaration
type mismatch, while `--parse-only` on the negative must exit zero.
`stock_controls.py --root /absolute/reader-and-controls --tools /absolute/tools`
records these results when the root contains `stock-reader`, `controls`, and
`stock-build.log`; the tools directory contains `lean/bin` and `nanoda_bin`.

The tiny [invalid projection export](controls/projection-invalid.ndjson) retains
the exact selected-pin limitation fixture. The stock reader must reject it with
`invalid projection`; the selected Nanoda binary unexpectedly accepts it.
The [reproduction driver](projection_control.py) constructs and classifies it
afresh. These fixtures are diagnostic inputs and are never candidate imports.

## Preparation and fresh hosted source route

From the repository root:

```console
python -B -m unittest discover -s verification/isolated-affine-denominators -p test_*.py
python -I verification/isolated-affine-denominators/verify.py --check
```

These are preparation checks, not theorem execution. `--freeze` refuses to replace
an existing manifest. Investigate changes rather than refreshing hashes to make a
check pass.

The adapter authenticates and reuses the maintained `isolated-affine` runner. The
fresh hosted route retains its trusted upstream setup, fresh candidate sources,
actual imported-admission control, exact target inventory, valid/mismatch/axiom
controls, and write/socket probes. It adds the `DenominatorAffine` library and the
new independent challenge. No candidate `.olean` or candidate Lake configuration
is copied. A manual workflow should invoke:

```bash
python3 -I -B verification/isolated-affine-denominators/verify.py --run \
  --work-dir "$RUNNER_TEMP/isolated-affine-denominators"
```

The registered generic workflow contains the new `affine-denominators` case.
After publication and separate dispatch authorization, the intended command is:

```console
gh workflow run isolated-irrationality.yml --ref feat/affine-denominators -f case=affine-denominators
```

The dedicated `isolated-affine-denominators.yml` workflow is also prepared; GitHub
requires default-branch registration before that new workflow can be dispatched.
Both workflows retain manual dispatch, read-only permissions, no checkout
credentials, hash-guarded cleanup before tool setup, indexing and failure uploads.
The hosted adapter records and protects both workflow file hashes.
The five-hour service/six-hour job budget is an inherited starting budget, not a
measured guarantee for the new clean build. This preparation does not authorize
push, workflow dispatch or diagnostic publication. No hosted result is claimed.

The October 12 local primary comparison completed in 24 minutes 48 seconds; its
systemd service reported 11.9 GB peak memory and 709.3 MB swap under the 12 GB cap.
These are service-scoped observations, not a universal or complete-host peak.
GitHub documents 16 GB RAM and four CPUs for its public-repository Ubuntu runners
([runner reference](https://docs.github.com/en/actions/reference/runners/github-hosted-runners)).
The shared preparation reserves disk but does not configure swap. The hosted
adapter records host memory and swap totals/availability before setup and proof.
Available
memory/swap and the full source rebuild's resource needs remain hosted-run
conditions to measure; local success is not a capacity guarantee.

## Local cached route and retained-byte replay

`run_local.py` accepts explicit paths for a fresh work directory, inherited-cache
identity receipt, prior tool receipt and separately built stock-reader root:

```bash
python3 -I verification/isolated-affine-denominators/run_local.py \
  --work-dir /absolute/fresh-work \
  --cache-receipt /absolute/cache-identity.json \
  --tool-receipt /absolute/accepted-tool-receipt.json \
  --stock-root /absolute/reader-and-controls
```

The source is this frozen repository checkout. `audit_cache.py` constructs the
cache identity from a source checkout and the
[canonical inherited inventory](inherited-source-sha256.json). It identifies
compiled objects; it does not authenticate them as compiled from those sources.
The local runner copies only the four inherited libraries' build directories.
The new denominator modules, `Challenge`, `Solution`, and `StandardBridge` start
without inherited compiled artifacts. Mathlib dependencies use the existing
resolved package cache; revisions and tracked-source cleanliness are checked.
This is not a clean source rebuild of all inherited/upstream code.

The actual Comparator frontend rebuilds the new modules, compares six targets,
and checks both primary kernels. The retention helper copies the actual regular
export observed in the configured Nanoda process. The structured inventory then
requires all six public and six comparison theorem bodies and exactly the three
permitted structured axiom names. It rejects flattened-name collisions.

Direct Nanoda and separately built Lean 4.34.1 replays consume the retained file,
with its SHA-256 checked around each run. Those direct replays certify the retained
artifact's bodies. Its relationship to the temporary file consumed during the
Comparator run assumes no concurrent modification; the helper alone does not
establish adversarial byte stability. The new stock reader is in the same Lean
kernel family; Nanoda supplies implementation diversity.

The [executed adapter snapshot](results/executed-adapter-2026-10-12.py) preserves
the exact adapter used by the October 12 local run. Later preparation added
hosted workflow identity and memory diagnostics to the current adapter; those
later changes were not part of that local execution. The snapshot is retained
for source inspection and identity comparison.

Raw local receipts contain operational host paths and are not automatically a
public upload inventory. The final local result and clean hosted result are
separate milestones. Public source/artifact retention, publication and hosted
dispatch remain separate actions.

The full export is 1,281,194,270 bytes, SHA-256
`fd0f5d689cc5f04f723d4c105a8da84e0d1f8a4c7356cf01c9db3afeac9f5dd6`.
Its 112,854 serialized declaration records contain all twelve required theorem
bodies and exactly the permitted axioms. Nanoda reported 118,369 checked
declarations; the stock reader accepted 118,366 after regenerating three quotient
primitives. These are distinct counting conventions. The complete private index
covers 121 files; all 120 fetched small evidence files were checked against it,
with the full export retained in the private execution archive.
