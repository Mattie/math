# Reproduce the four final statements

This optional workflow compares the compiled propositions and supporting definitions of four final irrationality/approximation statements against independently written Mathlib-only specifications. Nanoda checks the **same solution exports** with only `propext`, `Quot.sound`, and `Classical.choice` permitted.

The selected statements are the original logarithm natural-denominator/epsilon bridge and the rational-arctangent, imaginary-quadratic, and real-quadratic `FormalConjectures` conjunctions. The tool pins, exact declaration names, and frozen input hashes are in [pins.json](pins.json). Proof-source inputs remain pinned to the reviewed revision `3f4e514444214e562eababb4eecc5b6ffb818002`; this does not pin the surrounding documentation to that historical state.

## Run

Use x86_64 Linux or WSL with Bash, Python 3.9 or newer, Git, curl, unzip, a C compiler, and make. Network access is needed for the pinned Lean distribution, tool sources, Rust toolchain, and Mathlib dependencies/cache. Put the working directory on a native Linux filesystem, outside the source checkout.

From the repository root:

```sh
bash verification/irrationality-exponents/run.sh \
  --case all \
  --work-dir "$HOME/lean-four-proof-verification"
```

Individual case names are `log`, `arctan`, `imaginary`, and `realnorm`. The first invocation downloads and builds tools in the selected directory; it does not install a global toolchain or change shell configuration. Subsequent invocations may reuse pinned tools and dependency download caches, but **never reuse a previous acceptance result**. Each invocation creates a fresh `runs/<timestamp>-<unique-id>/` directory.

Expect substantial computation, downloads, and many gigabytes of build and export data. A first source build can take considerably longer than replaying existing exports. The large outputs remain in the caller's working directory, outside Git. Keep that directory if another reviewer needs the complete generated artifacts.

## What counts as a pass?

The command exits zero only after all selected statements pass and all controls behave as expected. Its `receipt.json` records hashes, tool identities, frozen sources, dependency revisions, commands, exit statuses, export inventories, cache provenance, and individual outcomes. After a run directory is created, any failure leaves a non-success receipt and diagnostic logs; earlier prerequisite and argument errors print diagnostics and exit nonzero. Missing files and unrelated crashes do not count as successful rejection controls.

The runner checks input hashes before tool setup, compiles copied solution sources outside the checkout, and compiles each challenge in a separate project without importing OAI proof modules. It uses the maintained [Comparator](https://github.com/leanprover/comparator) implementation without definition holes. Challenge placeholders and deliberately invalid controls are isolated from the mathematical solution sources. Positive controls must pass; changed propositions, changed definitions, forbidden axioms, and an ill-typed proof must fail with the expected diagnostics.

Mathlib's official cache is permitted and disclosed. This is **not** a complete dependency-from-source bootstrap or the comparator's hardened hostile-code build protocol. It does not certify novelty, human understanding, or every manuscript sentence. Standard-definition bounds are checked directly; historical custom-supremum exponent declarations retain their separate evidence.

If a proof source changes, the frozen-source check deliberately fails. Review the changed specification and source, then intentionally refresh the relevant pins and evidence; do not bypass the check or relabel old receipts. The existing package quick checks and older export workflows retain their own scope.

## Evidence and development checks

[Historical audit records](historical/README.md) document the earlier local audit. They are not results of this portable command. New results are created only by running it.

The [8 October portable validation run](validation/README.md) passed all four cases and all controls. Its compact record preserves export identities and checker logs separately from the historical audit.

Small failure-boundary tests do not need Lean or network access:

```sh
python3 verification/irrationality-exponents/test_verify.py
```

They check source mutation/missing input rejection, frozen configuration snapshots under concurrent edits, modified tool-cache rejection, fresh run identity, incomplete success prevention, expected rejection diagnostics, and exact export targets/axioms. Full acceptance additionally requires an actual all-case run.
