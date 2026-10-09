# Isolated verification of FC #6942

This is a separately prepared, manual source-verification pilot for
[`OAI.RealNorm.normalized_log_sqrt_two_irrationality_and_bound`](../../preprints/The-irrationality-exponent-of-log-3-plus-2-sqrt2-over-sqrt2-is-2-October-7-2026/lean/RealNorm/FormalConjectures.lean),
the final wrapper supporting [FormalConjectures #6942](https://github.com/google-deepmind/formal-conjectures/pull/6942).
Preparation is not a verification result or authorization to publish or execute it.

## Preservation and scope

The runner reads the existing `realnorm` entry in
[`pins.json`](../irrationality-exponents/pins.json). It requires the complete frozen
Lean source inventory and every recorded input hash before setup and after checking.
Existing proof files, dependency/toolchain pins, expected hashes, exports, and
historical receipts are never updated. New run files stay under `RUNNER_TEMP`.

The trusted statement is the existing Mathlib-only
[`challenges/realnorm.lean`](../irrationality-exponents/challenges/realnorm.lean).
It asserts irrationality of `log(3 + 2*sqrt(2))/sqrt(2)` and the eventual lower
bound for every real exponent greater than two. Its `sorry` is a placeholder in
the specification; the solution must use only `propext`, `Quot.sound`, and
`Classical.choice`, enforced by Comparator and Nanoda.

The runner records the exact target, input identities, commands, tool binaries,
dependency inventory, controls, and final outcome. It checks only #6942; it has no
selector for other proofs and never calls the existing four-proof runner.

## Execution order

1. Verify the frozen inputs and the unchanged preflight implementation.
2. Reuse that implementation to build the pinned tools in fresh scratch space and
   repeat its three tiny controls and filesystem/socket probes on this runner.
   The earlier [successful preflight](https://github.com/Mattie/math/actions/runs/37975682035)
   is a reference, not a substitute for these fresh checks.
3. Create a trusted dependency project containing only reviewed Lake configuration
   and the Mathlib-only challenge. Fetch the official Mathlib cache and build the
   pinned `Mathlib` target there. Check the unchanged dependency lock and every Git
   revision, then inventory source and compiled dependency bytes.
4. Create a fresh candidate project. Copy the frozen `.lean` sources byte for byte,
   excluding the submitted Lake configuration. Generate the reviewed configuration
   separately, copy the original lock/toolchain, and expose the prepared dependencies
   through `.lake/packages`, pointing outside the candidate's writable directory.
   No candidate code has been compiled or loaded during trusted setup.
5. Run the stock pinned Comparator using the successful preflight's systemd and
   Landrun route. It builds and exports the challenge first, then builds and exports
   `RealNorm.FormalConjectures`, compares the exact statement and definitions, enforces
   the axiom policy, and checks with Nanoda and Lean's built-in kernel replay.
6. Require explicit acceptance, unchanged protected input/dependency hashes, complete
   controls, and retained diagnostics before recording success.

The outer `lake env` loads our generated configuration and trusted dependencies;
candidate build/export happens inside Comparator's sandbox. Prepared dependencies
are outside its writable `.lake` tree. A missing dependency artifact or attempted
dependency write fails the job; there is no fallback that broadens access or edits
pins. The dependency setup trusts the pinned upstream sources and official cache,
as permitted by the [Comparator documentation](https://github.com/leanprover/comparator/blob/d03acab154d269c06e60e4de7e4cc85deebff94b/README.md).

## Resources and retained evidence

The prepared [workflow](../../.github/workflows/isolated-6942.yml) uses the ordinary
unprivileged account on GitHub-hosted `ubuntu-24.04`. It is manual only, has read-only
repository permissions, does not persist checkout credentials, and reuses no prior
candidate build or Actions cache. Runs are serialized.

Before installing Go, the workflow reuses the existing hosted-only
[`prepare-independent-runner.sh`](../publication/prepare-independent-runner.sh)
to reclaim unused SDKs when needed and require 35 GiB free on the build filesystem.
That cleanup uses `sudo` only on the disposable hosted VM; proof verification runs
under its ordinary unprivileged account. The runner checks for 35 GiB again before
tool setup or dependency downloads, then requires 10 GiB before the proof build.
The latter leaves headroom above the observed 5.50 GiB project output. Cleanup
diagnostics and both runner measurements are retained, including on failure.

The proof service has a two-hour limit, a 12 GiB memory cap, and a four-CPU quota.
The job allows four hours including trusted setup and evidence upload. These are
initial pilot budgets, not a claim that the full target fits. Timeout, disk or
memory exhaustion, or a sandbox failure leaves verification incomplete rather
than proving the mathematical statement false.

The `evidence` artifact contains the receipt, exact generated checking configuration,
trusted challenge, selected frozen manifest entry, dependency/file identities, and
command logs, including failed attempts. It excludes candidate build trees. The stock
Comparator keeps its checked exports in memory; this pilot does not claim to retain
new downloadable proof exports or reproduce the bytes of historical exports.

Artifacts are retained for 90 days. Public dispatch makes run diagnostics available
on GitHub. A successful pilot would add a new verification record alongside the
existing evidence; it would not rewrite historical records or automatically post a
FormalConjectures response. Durable publication of that evidence is a later decision.

## Local preparation checks

```sh
python3 -B verification/isolated-6942/test_verify.py
```

These tests validate input preservation and preparation logic without downloading
dependencies, building tools, compiling proofs, or starting a sandbox. The full
source run, read-only Mathlib compatibility, and resource budgets remain untested
until a separately authorized dispatch.
