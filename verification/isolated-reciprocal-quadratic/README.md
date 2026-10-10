# Isolated reciprocal-quadratic verification

This is the dedicated `reciprocal-quadratic` case in the manual **Isolated
irrationality verification** workflow. It checks the packaged integral
classification using the established hosted sandbox and checking tools. Local
preparation tests do not establish a successful hosted proof check.

## Statements and source

The runner retains the two independently written specifications and their
existing comparison configurations:

| Group | Challenge / solution | Statements |
| --- | --- | --- |
| Positive and nonzero discriminant | `PositiveChallenge` / `PositiveSolution` | Literal eventual bounds and conventional exponent-two statements for each case: four targets |
| Classification | `ClassificationChallenge` / `ClassificationSolution` | Repeated-root evaluation, rationality iff discriminant zero, irrationality iff discriminant nonzero: three targets |

Both specifications import only Mathlib. Their proof placeholders are trusted
comparison inputs and are excluded from the proof-module sweep. Candidate proofs
do not import them. The exact seven names, configurations, source manifest,
toolchain and dependency lock are checked before setup and again before success.

Each comparison starts in a separate directory with no compiled candidate
modules. Dependencies are prepared first in a trusted generated Lake project and
remain outside both candidates' writable build directories. Official Mathlib
cache objects are allowed. Candidate Lake configuration is never executed:
the runner generates the small reviewed configuration it needs.

## Acceptance requirements

The runner reuses the pinned preflight and helper code from the existing hosted
verification. Helper hashes are checked before import or execution. The workflow
checks the disk-preparation helper before running it.

A successful result requires all of the following:

- Actual allowed-write, protected-write, symlink-escape and Unix-socket controls,
  with successful unrestricted baselines; valid-proof acceptance and intended
  statement-mismatch and forbidden-axiom rejections.
- Two stock Comparator executions, each building its challenge before its
  candidate, matching all named statements and referenced definitions, enforcing
  the three permitted axioms, and receiving explicit acceptance from Nanoda and
  Lean's default kernel.
- A supplemental isolated build of every one of the 984 packaged proof modules,
  with nonempty compiled objects and their hashes recorded. Both fresh strict
  audits must pass the named-declaration axiom gate.
- Unchanged protected candidate, dependency, helper and input identities, and
  complete retained diagnostics and input records before a receipt may pass.

The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
Each comparison allows two hours; the full-module sweep allows one hour. The job
has a six-hour ceiling, four-CPU quota and 12 GiB service memory cap. Capacity
checks require 35 GiB before setup and 10 GiB before proof execution. These are
initial bounds informed by the earlier quadratic-period run, not a guarantee
that this case fits them. Capacity, boundary, timeout, kernel or retention
failures leave a failed or incomplete run. There is no unisolated fallback.

## Local preparation

The [October 10 preparation record](preparation-2026-10-10.json) records 48
passing preparation and regression tests, package integrity checks, and an
independent source review. It does not record a hosted proof run.

On Linux with Python 3.11 or later, run the preparation tests from the repository
root:

```sh
python3 -B verification/isolated-reciprocal-quadratic/test_reciprocal.py
```

To prepare both real candidate trees without fetching tools, compiling Lean or
executing a sandbox:

```sh
export RUNNER_TEMP="$(mktemp -d)"
python3 -B verification/isolated-reciprocal-quadratic/reciprocal.py \
  --prepare-only --work-dir "$RUNNER_TEMP/reciprocal-preparation"
```

This validates frozen inputs and generates candidate projects with empty external
dependency directories. Its receipt reports preparation only. It cannot pass a
proof check and is not a substitute for running on a compatible hosted VM.

## Hosted evidence

After the branch is published and a run is authorized, select
`reciprocal-quadratic` on the reviewed commit. The workflow retains evidence on
success or failure for 90 days. Audit the exact run, attempt and commit, retained
file hashes, both comparison results, the complete build inventory and boundary
diagnostics before recording a hosted pass.

The stock Comparator route retains no standalone proof export here. The earlier
integral exports and receipts remain unchanged historical evidence. This new
workflow does not create a downloadable export or replace their checks. Lean,
Mathlib and upstream cache artifacts remain trusted inputs; both kernels share
the exporter and comparator frontend. No hosted result is claimed by the local
preparation work.
