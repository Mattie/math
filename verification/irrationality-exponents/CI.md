# Public independent-checker runs

The `Verify publication` workflow has an opt-in `independent_proofs` input.
It runs the existing [portable command](README.md) with `--case all` on a fresh
Ubuntu 24.04 hosted runner. The four targets are the original logarithm bridge
and the rational-arctangent, imaginary-quadratic, and real-quadratic catalogue
statements. This does not extend independent-checker coverage to the two other
preprints.

From GitHub Actions, select **Verify publication**, choose the branch or commit,
and enable **Rebuild four final statements and check with Comparator and Nanoda**.
The separate `rebuild_proof` input controls the six-package Lean build matrix.
An equivalent CLI invocation is:

```sh
gh workflow run verify.yml -R Mattie/math --ref <branch> -f independent_proofs=true
```

This job builds pinned tools, compiles the frozen solution sources and independent
Mathlib-only challenges, exercises the seven acceptance/rejection controls, and
runs Comparator and Nanoda against the same solution exports. It uses a new
working directory without a persistent CI cache; the portable runner still uses
the official Mathlib dependency cache. No dependency-from-source bootstrap or
hostile-code sandbox is claimed. Before tool setup, the job requires at least 35 GiB free on the build filesystem.
The retained successful local run used about 20 GiB for its builds/exports plus
about 5.5 GiB for tools and caches. The threshold leaves room for transient build
files. If necessary, the job removes only unused Android, .NET, GHC, and hosted
tool-cache directories on the disposable GitHub-hosted Ubuntu 24.04 VM. It refuses
that cleanup elsewhere, never deletes proof exports, and fails before expensive
setup if capacity remains insufficient. `capacity.log` records the before/after
measurements; an early capacity failure has this diagnostic log rather than a
portable-runner receipt because that runner has not started.

The job has a four-hour timeout; the earlier
local four-case run took about 53 minutes on its particular machine.

Each invocation creates a new receipt. The artifact named
`independent-proof-evidence-<commit>-<attempt>` retains the complete `receipt.json`,
all command/checker logs, the outer console log, configuration snapshots, and
Nanoda configurations, including diagnostics when a run fails. Receipt export
identities identify the exact bytes checked; large proof exports and build
folders are not included in this CI artifact. Artifacts have 90-day retention
subject to repository policy; download them before expiration for long-term use.

A green publication-only run does not imply that this optional job ran. Check
that `independent-proof` succeeded, that the receipt reports all four cases and
seven controls passed, and that the run commit is the intended revision.
The October 8 records and their runtime hashes remain historical evidence.
A new successful run validates the current runner separately, including its
configuration-snapshot guard; it never replaces or relabels those old records.

## Verified public replays

Both public replays completed successfully on October 9, 2026. Their downloaded
receipts and all 55 command logs per run were inspected: all four cases and seven
controls passed, each Comparator target was accepted, and Nanoda checked each
corresponding export. The recorded case inputs match the committed pins, and the
runtime hash matches the current portable runner.

| Run | Commit | Receipt SHA-256 |
| --- | --- | --- |
| [First replay](https://github.com/Mattie/math/actions/runs/37931856963) | `d77a7a262e004953ddc2850be6f61d138afd4525` | `9548a8a42fbd6b9db862367074fd51208f2a694e76bf79cd354dd5efa00a85e6` |
| [Replay with capacity gate](https://github.com/Mattie/math/actions/runs/37936794898) | `c1395ef07adb11b83b0a3019dfdf072e10eac246` | `d698d3ee2e2d71bf583dbbf2f9218cb47021522d91ae487440c768ad48da2f48` |

The second run took about 64 minutes. Its capacity gate recorded 92,290,232,320
free bytes before setup, above the 35 GiB requirement; no SDK cleanup was needed.
Its artifact is `independent-proof-evidence-c1395ef07adb11b83b0a3019dfdf072e10eac246-1`,
and its receipt is `runs/20261009T132608Z-omoycypu/receipt.json` within that artifact.
The first artifact uses the first commit in the same naming convention, with
receipt `runs/20261009T124304Z-j50o6l8b/receipt.json`.
These new receipts supplement the unchanged October 8 historical records.
