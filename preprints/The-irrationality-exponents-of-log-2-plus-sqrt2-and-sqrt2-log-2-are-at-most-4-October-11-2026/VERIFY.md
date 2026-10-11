# Verification and reproduction

The mathematical sources are the unchanged
[AffineLogarithms package](../../formalizations/AffineLogarithms/README.md).
Its [frozen inventory](../../formalizations/AffineLogarithms/evidence/source-sha256.json)
covers 969 inputs. The paper adds exposition and publication files; it does not
introduce new Lean declarations or change the checked targets.

## Proof evidence

[GitHub run 38139172013](https://github.com/Mattie/math/actions/runs/38139172013),
attempt 1, verified commit `b15a6431eca8632a48c1cd84e5200edd30f0670c`.
The requested candidate dependency closure was compiled in fresh isolated build
state. All fifteen final wrappers passed exact statement comparison and checking
by Lean 4.34.1 and Rust Nanoda. Valid, mismatched-statement, forbidden-axiom,
imported-admission, and write/socket-boundary controls passed.

The downloaded archive matched GitHub's SHA-256. The
[immutable audit result](../../verification/isolated-affine/results/2026-10-11.json)
records 95 indexed files, 58 command logs, 93 retained-file hashes, 13 protected
repository inputs, and 969 frozen inputs checked. The
[artifact](https://github.com/Mattie/math/actions/runs/38139172013/artifacts/11703935710)
expires January 9, 2027. Authenticated retrieval was tested; anonymous artifact
retrieval was not. The complete archive is retained locally.

This reuses the dated hosted result for unchanged proof inputs. It is not a new
proof run performed while typesetting. The official Mathlib dependency cache
remains a trust input, and the boundary tests do not establish universal
containment. The hosted route did not retain a new standalone export.

The earlier [proof-body replay record](../../formalizations/AffineLogarithms/evidence/verification-summary.json)
and [checker assessment](../../formalizations/AffineLogarithms/CHECKERS.md)
describe the historical export and its additional Lean-family replay. The exact
export remains locally retained and has no tested public download. Its absence
does not make the source build or hosted result a replay of those historical bytes.

## Paper evidence

The [theorem map](theorem-map.json) identifies all three main results and their
standard-definition bridges. Two independent model reviews assessed the written
argument and the specification/evidence chain, then inspected the final source
diff. Their [sanitized record](evidence/reviews.json) identifies the exact inputs,
resolved wording corrections, and limits. No new proof run is attributed to them.

The [build record](evidence/build.json) identifies the 19-page PDF, manuscript,
compiler, and warning-free Tectonic build. The [reader review](evidence/reader-review.json)
records PDF inspection, actual GitHub rendering, and retrieval status separately.
See the [workflow checklist](../../formalizations/AffineLogarithms/WORKFLOW.md)
for the current publication status.

Run `python3 scripts/check-publication.py` to check the listed paper files, the
shared proof package, and the exact target mapping. This establishes file
integrity and consistency, not independent mathematical acceptance.

The manuscript discloses substantive AI assistance. Model reviews are not human
peer review, and neither a successful checker run nor an incomplete literature
search establishes mathematical priority.
