# Portable workflow validation — 8 October 2026

The [compact validation record](2026-10-08.json) records a successful `--case all`
invocation of the portable runner. All four exact final statements passed the
maintained comparator and Nanoda, using the same solution exports. All seven
positive/rejection controls passed. The run took about 53 minutes, including a
fresh solution-source build; this is an observed duration, not a runtime guarantee.

| Case | Independently checked declarations | Result |
| --- | ---: | --- |
| Original logarithm epsilon formulation | 117,722 | Passed |
| Rational arctangent | 118,479 | Passed |
| Normalized imaginary-quadratic value | 117,879 | Passed |
| Normalized real-quadratic value | 117,787 | Passed |

The record contains runtime/source-manifest hashes, tool and dependency pins,
export identities, cache provenance, and hashes of the retained checker logs.
The full machine receipt, builds, and large exports remain under the caller's
working directory in `runs/20261008T144533Z-0_9xwobs/`. Its receipt digest is
recorded here; this compact record is an extract, not a replacement for that
complete evidence directory.

The working directory was created for this task. The successful invocation
reused tools and official Mathlib cache acquired during two earlier attempts,
whose failed receipts remain preserved. One was interrupted to apply review
fixes; the other exposed a missing Nanoda axiom-printing destination. The
corrected runner exercises that success-report setting in its small positive
control before rebuilding proofs. No previous proof export or acceptance
result was reused by the successful invocation.

Six failure-boundary tests and all four package quick checks also passed.
All 3,755 frozen source/configuration hashes and the consolidated manuscript
hash remained unchanged. These checks do not establish novelty or replace
human review of the mathematical statements and manuscript.

After that run, review found a configuration race: a changed checkout manifest
could be copied and later used as its own expected value. The runner now captures
and hash-checks configuration before tool setup, reuses that snapshot for every
project, and compares dependencies against its verified lock. All nine focused
tests pass, including three regressions for this race; snapshot creation was also
checked with the real configuration for each case and the all-case selection.
The full proof build and checker run were not repeated for this guard. The record
above and its runtime hashes remain unchanged and describe the earlier version.
