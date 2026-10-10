# Isolated irrationality verification

This manual workflow prepares one frozen theorem for isolated source verification.
Preparation and local tests are not proof-verification results. A hosted run still
requires separate authorization, including publication of its diagnostics.

| Selector | Mathematical target | Final declaration |
| --- | --- | --- |
| `log` | Logarithms of positive rational numbers other than one | `log_rational_challenge` |
| `arctan` | Arctangents of nonzero rational numbers | `OAI.Arctangent.rational_arctan_irrationality_and_bound` |
| `imaginary` | `arctan(sqrt(2))/sqrt(2)` | `OAI.Imaginary.normalized_arctan_sqrt_two_irrationality_and_bound` |

Each target includes irrationality and the eventual rational-approximation lower
bound expressing irrationality exponent two. The exact statements are the existing
Mathlib-only files in [`challenges`](../irrationality-exponents/challenges).
The workflow requires a case selection and has no all-cases option.

## Frozen inputs and isolation

The runner reads the existing [`pins.json`](../irrationality-exponents/pins.json)
and validates the selected package's complete Lean inventory and recorded hashes.
It copies the logarithm bridge from the frozen
`review/blind-statement/CertifiedBridge.lean` to `CertifiedBridge.lean` without
changing its bytes. Existing proofs, manifests, expected hashes, exports, and
historical verification records remain unchanged.

This runner carries forward the established isolated source-checking sequence,
while keeping the earlier runner and its recorded identity intact:

1. Validate frozen inputs and the pinned preflight implementation.
2. Build the pinned checking tools in fresh scratch space. Repeat the preflight's
   filesystem/socket probes and valid, mismatched-statement, and forbidden-axiom
   controls on the current runner.
3. Prepare trusted dependencies using generated Lake configuration, the frozen
   lock/toolchain, and the independent challenge. Fetch the official Mathlib cache
   and build Mathlib before introducing candidate sources. Check dependency Git
   revisions and inventory source and compiled bytes.
4. Copy the selected frozen candidate into a fresh project with generated Lake
   configuration. Expose dependencies through a symlink outside the candidate's
   writable `.lake` directory. No candidate code runs during trusted setup.
5. Run stock Comparator through systemd and Landrun, with Unix-domain sockets
   denied. Comparator builds and exports the challenge before the candidate,
   compares the statement and definitions, enforces `propext`, `Quot.sound`, and
   `Classical.choice`, and performs Nanoda and Lean kernel replay.
6. Require explicit acceptance, complete controls, retained evidence, and unchanged
   candidate inputs, frozen sources, and dependency bytes before recording success.

Trusted setup relies on the pinned upstream sources and official dependency cache.
Missing artifacts, unexpected writes, or isolation failures stop verification;
the runner does not broaden access or update pins to recover.

## Manual execution and evidence

The [workflow](../../.github/workflows/isolated-irrationality.yml) runs only through
`workflow_dispatch` on a fresh hosted `ubuntu-24.04` runner. Select exactly one case
and the reviewed revision. Repository permissions are read-only; checkout
credentials are not persisted; prior candidate builds and Actions caches are not
reused. Runs of this workflow are serialized.

Capacity cleanup runs before Go installation and restores ownership of the tool
cache directory. The Python runner requires 35 GiB free before setup and 10 GiB
before checking the proof. The proof service has a two-hour limit, a 12 GiB memory
cap, and a four-CPU quota; the full job allows four hours. All three recorded runs
completed within these budgets. Resource exhaustion in a future run leaves the
verification incomplete.

The always-uploaded artifact includes the receipt, commands and logs, exact target,
tool identities, generated checking inputs, frozen manifest entry, and dependency
inventory. Artifacts expire after 90 days. Inspect the exact run revision, complete
checks, both kernel acceptances, and retained-file/log hashes before adding a new
durable result record. Failed attempts remain distinct from successful evidence.
Reuse valid evidence for unchanged inputs; a documentation or upload change alone
does not require another proof run.

The stock Comparator holds its exports in memory. This workflow does not create
downloadable proof exports or claim byte identity with historical exports. Public
diagnostics need privacy review; durable publication and any external communication
remain separate authorized actions. Results can be retained as evidence in reserve.

## Local preparation checks

```sh
python3 -B verification/isolated-irrationality/test_verify.py
```

These checks exercise selection, frozen input validation, bridge handling,
byte-preserving preparation, scratch boundaries, capacity gates, and checking
configuration without downloading tools, compiling proofs, or starting a sandbox.
All three hosted source-verification runs passed, and their evidence was audited:
[rational logarithms](results/2026-10-10-log.md),
[rational arctangents](results/2026-10-10-arctan.md), and
[normalized quadratic arctangent](results/2026-10-10-imaginary.md).
Reuse these records for unchanged inputs; they do not contain standalone proof exports.
