# Hosted quadratic-period verification

Select `quadratic-periods` in the existing **Isolated irrationality verification**
manual workflow, on the reviewed branch or commit. This case checks the published
six-target package. A prepared workflow is not a completed proof run.

The runner reuses the established hosted preflight, pinned tools, generated Lake
configuration, dependency inventory, and sandbox invocation. The original `log`,
`arctan`, and `imaginary` cases and their recorded results remain unchanged. The
hosted pins come from `verification/irrationality-exponents/pins.json`; they are
recorded as this run's tools, separately from the earlier local verification.

The complete case requires:

1. Fresh tools on an unprivileged GitHub-hosted Ubuntu 24.04 runner. Actual compiler
   controls must permit the intended build write, deny protected and symlink writes,
   and deny Unix stream/datagram sockets, with successful unrestricted baselines.
   A valid theorem must pass both kernels; statement and forbidden-axiom controls
   must fail for their intended reasons. The strict axiom-output checker also
   receives actual Lean positive, extra-axiom, and imported-admission controls.
2. Trusted upstream dependency preparation before copying candidate sources.
   Official Mathlib caches are allowed; candidate build caches are not. Dependencies
   remain outside the candidate's writable `.lake` directory.
3. Stock Comparator builds and exports the independent `Challenge` before `Solution`,
   compares all six published theorem statements and their referenced definitions,
   enforces the three-axiom policy, and runs Nanoda and Lean's default kernel.
4. A supplemental sandboxed build explicitly selects every one of the 1,028 packaged
   proof modules. Selecting library names alone is insufficient for these directory
   libraries. A strict fresh `Audit.lean` run and enforced six-target axiom gate follow.
5. Protected source/configuration, dependency and tool identities must remain
   unchanged. All required logs, inputs and module/object identities must be retained
   before the receipt becomes `passed`.

The whole job has a six-hour deadline. The comparison has four hours, and the
supplemental build has one hour, within that overall deadline. Proof services retain
the established four-CPU quota, 12 GiB memory cap, Landrun write restrictions, and
systemd Unix-socket denial. Existing capacity gates require 35 GiB before tool setup
and 10 GiB before the proof. A capacity, timeout, or boundary failure is a failed or
incomplete run, with no nonisolated fallback.

The workflow retains its new evidence on success or failure for 90 days. It does
not retain a new standalone export or replace the already published export. The
published export's verification and download receipts remain valid historical
evidence from their recorded run. Only a completed hosted result can establish
that this new route passed; routine publication CI does not run it automatically.

Local preparation checks do not compile proofs or repeat existing release audits:

```sh
python3 -B verification/isolated-quadratic-periods/test_quadratic.py
```

Lean and upstream Mathlib artifacts remain trusted inputs. Both kernels share the
exporter and comparator frontend. Boundary controls establish the observed cases,
not universal sandbox or checker soundness.
