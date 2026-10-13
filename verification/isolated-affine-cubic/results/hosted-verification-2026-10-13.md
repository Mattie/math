# Affine cubic hosted verification — October 13, 2026

**Passed.** A fresh GitHub-hosted execution built the frozen candidate source
under the tested isolation boundary. Comparator matched all four statements
against the independent challenge, and both Nanoda and Lean's default kernel
accepted the solution. A subsequent audit of the downloaded archive passed.

| Identity | Value |
|---|---|
| Run | [38434422471](https://github.com/Mattie/math/actions/runs/38434422471), attempt 1 |
| Job | `115424606730` |
| Checked commit | [`1ee3266da6bd7f6ecafd063caab2cfe7a6defbd2`](https://github.com/Mattie/math/tree/1ee3266da6bd7f6ecafd063caab2cfe7a6defbd2) |
| Workflow | `.github/workflows/isolated-irrationality.yml`, `case=affine-cubic` |
| Verifier interval | 2026-10-13 16:55:29–17:51:46 UTC (56 minutes 17 seconds) |
| Machine-readable audit | [hosted-audit-2026-10-13.json](hosted-audit-2026-10-13.json) |

## Checked statements

The [challenge at the checked commit](https://github.com/Mattie/math/blob/1ee3266da6bd7f6ecafd063caab2cfe7a6defbd2/verification/isolated-affine-cubic/Challenge.lean)
uses standard Mathlib definitions for `Real.log 2 + (2 : Real) ^ (1 / 3 : Real)`.
The exact wrappers, exported from both `Challenge` and `Solution`, are:

- `AffineCubicVerification.eventual_lower_bound`
- `AffineCubicVerification.irrational`
- `AffineCubicVerification.irrationality_exponent_le_six`
- `AffineCubicVerification.not_liouvilleWith`

The permitted axioms are `propext`, `Quot.sound`, and `Classical.choice`.
The source manifest binds 966 inherited Lean files and nine cubic Lean files.
The candidate inventory has 981 entries, including the independently specified
wrappers, checking configuration, generated Lake configuration, lock and toolchain.

## Observed checks

All nine required checks passed: tools, isolation, valid theorem, mismatched
statement, forbidden axiom, imported admission, dependencies, all four cubic
wrappers (the receipt key is `affine`), and protected inputs.

The three negative controls failed for their intended reasons: a statement
mismatch, `preflight_forbidden`, and imported `sorryAx`. The valid control and
full candidate each received explicit acceptance from both kernels.
`logs/57-cubic-affine-comparator.log` records the fresh `Challenge` and `Solution`
builds, both exact wrapper export lists, and final acceptance.

The valid fixture's actual isolated build could write within its permitted
`.lake` area. Writes to the challenge, configuration, tool marker, outside
marker and symlink escape were denied with error 13. UNIX stream and datagram
socket creation were denied with error 97. All corresponding unrestricted
baseline probes succeeded. Protected inputs, tool identities and the prepared
dependency inventory remained unchanged according to the executed runner.

The run used Lean 4.34.1, pinned Comparator, Nanoda and Landrun, and the pinned
Mathlib sources and official cache. Exact revisions and binary hashes appear
in the audit JSON and [checker assessment](../CHECKERS.md). Dependencies were
prepared before candidate source was introduced and exposed read-only outside
the candidate's writable build directory. The recorded dependency inventory
contains 143,949 entries.

The proof service used a five-hour limit, 12 GiB memory cap, four-CPU quota and
four Lean threads. Free disk was 90,733,993,984 bytes before setup and
76,589,305,856 bytes before proof execution, above the 35 GiB and 10 GiB gates.
These are configured limits and disk observations, not a measured peak-memory claim.

## Evidence and retrieval

The downloaded archive matched GitHub's digest and size. Every ZIP member
matched the extracted inventory; all 101 indexed files, 99 receipt-retained
files and 58 command logs matched their recorded hashes. The audit also matched
the runner, actual dispatcher, source and specification identities against the
checked commit, and inspected the raw control and kernel diagnostics.

| Artifact | Value |
|---|---|
| ID | `11836246558` |
| Name | `isolated-irrationality-affine-cubic-1ee3266da6bd7f6ecafd063caab2cfe7a6defbd2-1` |
| ZIP size | 6,447,231 bytes |
| ZIP SHA-256 | `4a3eaf9ebaf3ea0d247274dd38a737744f312fb2a83aa49e558f88383b8ff83c` |
| Evidence-index SHA-256 | `f2b4394ef6ee00f5ac8b6e6e096e059a35edfb7b7f43d8967e0fc314a2f70bfc` |
| Receipt SHA-256 | `a16564ec8421f6b963bd99476bf8ec580df37d9ed2bbf97e28cf7f99ea3bb235` |
| Reported expiry | 2027-01-11 16:55:15 UTC |

Download the named artifact from the run page, or use an authenticated GitHub CLI:

```sh
gh run download 38434422471 --repo Mattie/math \
  --name isolated-irrationality-affine-cubic-1ee3266da6bd7f6ecafd063caab2cfe7a6defbd2-1 \
  --dir cubic-hosted-evidence
```

Authenticated archive retrieval was tested. GitHub may require sign-in, and the
artifact expires at the date above. A complete local archive copy is retained;
the committed audit JSON does not replace the original evidence or provide a
durable public copy of that archive.

## Scope

This is fresh isolated source verification, followed by an audit of its evidence.
It trusts the identified official dependency cache; it is not a from-source
rebuild of every dependency. Remote scratch files are no longer available for
an independent second hash, so preservation claims rely on the hashed runner
and receipt. The boundary probes cover their specified operations, not every
possible escape.

The selected Nanoda baseline predates later projection-name consistency checking;
the checker assessment explains that choice and its limits. Earlier local replay
with a newer Nanoda revision is separate historical evidence, not a second hosted
execution. This route retained no standalone proof export and does not establish
byte-for-byte replay of the historical local export. No manuscript release,
catalogue submission or merge is part of this result.
