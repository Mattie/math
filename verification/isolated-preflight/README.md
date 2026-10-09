# Isolated verification preflight

Prepared for a separately authorized manual run of
[`isolated-proof-preflight.yml`](../../.github/workflows/isolated-proof-preflight.yml).
Preparation does not establish that this preflight passes. Dispatch in this public
repository generally exposes its logs and artifacts; it requires separate authorization.

The job uses GitHub's temporary `ubuntu-24.04` VM and its normal unprivileged runner
account. It creates no account, uses no self-hosted infrastructure, and needs no
Docker layer. It does not build any of our mathematical proofs, import Mathlib,
or invoke the existing four-proof runner.

## Inputs and invocation

Lean 4.34.1, Comparator, exporter, Nanoda, and Rust are read from the existing
[`pins.json`](../irrationality-exponents/pins.json), without changing it. Tool
scratch checkouts use that Lean version; the full Comparator frontend's patch-version
compatibility is one of the things this job tests. Landrun is pinned to
`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`, with Go 1.25.12. Tools and download/build
caches are fresh under `RUNNER_TEMP`, outside the source checkout.

Each stdlib-only fixture runs the stock Comparator executable through:

```text
systemd-run --user --wait --pipe --collect
  --property=RestrictAddressFamilies=~AF_UNIX
  --property=RuntimeMaxSec=300
  --working-directory=<fixture> <explicit environment>
  <pinned lake> env <pinned comparator> config.json
```

`--pipe --wait` adapts upstream's interactive `--pty` invocation for CI. The actual
command and explicit tool paths are retained. No solution is built before this
command. Comparator builds/exports the trusted challenge first, then builds/exports
the solution under Landrun and runs Lean and Nanoda. The controlled `lake update`
only prepares the stdlib fixture's dependency metadata.

## Required results

- A trusted tiny C helper is compiled into the disposable Lean prefix so the
  solution can execute it under Comparator's existing executable-path rule.
  No sandbox permission is widened. A `#eval` in the valid fixture invokes it
  during the real solution build, without executing again during export.
- Outside isolation, the same helper must successfully append to all six probe
  files and create UNIX stream/datagram sockets. The tiny fixture files are then
  restored to their original bytes. This rules out ordinary ownership, missing
  paths, or unavailable sockets masquerading as isolation.
- During the isolated build, appending to the challenge, configuration, a tool-area
  sentinel, an outside sentinel, and that sentinel through a `.lake` symlink must
  fail with permission errors. The permitted `.lake` write must succeed and persist.
  Protected file hashes must remain unchanged.
- UNIX stream and datagram socket creation must fail with policy-related errors,
  exercising the inherited systemd restriction from inside the solution build.
- The valid theorem must pass Comparator, Lean, and Nanoda. Separate mismatched
  and forbidden-axiom fixtures must fail with the intended Comparator diagnostics.
  A crash, missing probe, unexpected error, missing kernel success, or disabled
  isolation fails the job. There is no skip or nonisolated fallback.

This checks the specified paths and operations, not the absence of every possible
sandbox escape. Host kernel/session incompatibility is a preflight failure to
investigate, not permission to weaken the invocation or switch accounts.

`evidence/receipt.json` starts as `running` and becomes `passed` only after every
required check and evidence collection completes. It retains pins, binary and
script hashes, commands, results, and log hashes. Small generated fixture files,
probe results, and diagnostic logs are uploaded on success or failure, with 90-day
retention. Tool build trees and proof exports are not uploaded. Failures before
the script starts retain a started marker and the Actions step's own diagnostics.

Local preparation checks, requiring no Lean or tool builds:

```sh
python3 -B verification/isolated-preflight/test_preflight.py
```

After an actual successful preflight, review its retained results and propose a
separately authorized isolated run for FC #6942 alone. Do not automatically launch
that run, change proof sources, replace historical receipts, or claim the preflight
verified any mathematical endpoint. A later source run must retain the tested
invocation and protection boundaries.

## References

- [Comparator at our pin](https://github.com/leanprover/comparator/blob/d03acab154d269c06e60e4de7e4cc85deebff94b/README.md)
- [Lean-eval workflow](https://github.com/leanprover/lean-eval/blob/38361be884302c7edce1908c4aef8296eb2cb27e/.github/workflows/ci.yml)
  and [filesystem probe](https://github.com/leanprover/lean-eval/blob/38361be884302c7edce1908c4aef8296eb2cb27e/scripts/sandbox_engaged_probe.py),
  used as implementation references. Their run is not evidence for this job's
  exact tool combination or added systemd guard.
- [Hosted-runner issue #14649](https://github.com/actions/runner-images/issues/14649):
  session problems when switching users; this job keeps the normal runner account.
