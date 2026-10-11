# Affine logarithms workflow checklist

Updated: October 11, 2026 (America/Chicago).

**Current phase:** ✅ Verifier setup complete; 🔄 Hosted verification running; ⏳ Evidence audit pending. Local proof checking,
independent model reviews, and distribution checks are complete within their
recorded scopes. Hosted execution and its evidence audit remain pending.

**Target:** irrationality and exponent at most four for the three expressions in
[README.md](README.md), with the twelve public declarations and fifteen comparison
wrappers in [the target map](evidence/target-map.json). The
[frozen source inventory](evidence/source-sha256.json) covers 969 inputs; its SHA-256
is `88516799eccd19825089e8e71ef84ebacb87d8a16174c0069b4cabe114089cb1`.
The retained export identity is recorded in [export-asset.json](evidence/export-asset.json).

**Current assignment:** the user authorized RUN: publish the scoped verifier
changes, dispatch fresh GitHub verification, and audit the resulting evidence.
The intended assurance includes fresh isolated candidate compilation, exact final
statement comparison, and Lean/Nanoda checking. A later GitHub approval gate, if
one appears, still requires its own explicit authorization.

**Next action:** monitor [GitHub run 38139172013](https://github.com/Mattie/math/actions/runs/38139172013),
started from commit `b15a643` through `isolated-irrationality.yml` with `case=affine`.
Audit the actual run receipts and artifacts before marking hosted verification complete.

Legend: ✅ Complete · 🔄 In progress · ⏳ Pending · ⛔ Blocked · ⏸️ Deferred ·
➖ Not applicable · 🟡 Partial · 🔍 Needs review.

| Milestone | Status | Evidence or remaining action |
| --- | --- | --- |
| Assignment and completion criteria | ✅ Complete | Three scoped upper bounds; local setup requested; hosted success tracked separately below |
| Environment and provenance | ✅ Complete for local evidence | [VERIFY](VERIFY.md) records Lean 4.34.1, pinned dependencies, Linux build, and identified cache reuse; hosted resources are part of verifier setup |
| Feasibility and decision to proceed | ✅ Complete | Concrete field constructions and deduction in [ARGUMENT](ARGUMENT.md) |
| Exhaustive prior-art/priority assessment | ⏸️ Deferred by user | [PRIOR-ART](PRIOR-ART.md) retains the checked benchmark; no novelty claim |
| Independent specification and standard definitions | ✅ Complete | [REVIEW](REVIEW.md), literal [Challenge](Challenge.lean), [Solution](Solution.lean), and [StandardBridge](StandardBridge.lean) |
| Claim-to-declaration map, examples and boundaries | ✅ Complete | [Target map](evidence/target-map.json); the memo states all three instances and limits at exponent four |
| Ordinary argument and Lean development | ✅ Complete | [ARGUMENT](ARGUMENT.md); hypotheses, constants, parameter order and common witness inspected in the correspondence review |
| Frozen sources, dependencies and final wrappers | ✅ Complete | [Source inventory](evidence/source-sha256.json), [inherited pin](evidence/inherited-source-pin.json), original archives retained |
| Source build and transitive axiom audit | ✅ Complete, local Linux | [Fresh build receipt](evidence/pre-pr/build-receipt.json): twelve public reports; identified inherited caches, not a full clean dependency rebuild |
| Actual audit rejection controls | ✅ Complete, local Linux | [Policy controls](evidence/pre-pr/axiom-controls/receipt.json): valid, imported admission, extra axiom, and malformed/missing reports |
| Trusted statement comparison | ✅ Complete, earlier unchanged artifact | [Checker receipt](evidence/checker-receipt.json): fifteen literal wrappers |
| Export inventory and proof-body checks | ✅ Complete, earlier unchanged artifact | [Verification summary](evidence/verification-summary.json), [inventory](evidence/export-inventory.json); same accepted export, no new full replay during packaging |
| Comparator admission and boundary controls | ✅ Complete for recorded local route | [New admission controls](evidence/pre-pr/comparator-controls/receipt.json) and original [checker receipt](evidence/checker-receipt.json); hosted boundary must be exercised anew |
| Pinned checker assessment and trust limits | ✅ Complete for dated assessment | [CHECKERS](CHECKERS.md); supplemental older Lean is distinguished from primary Lean and Rust Nanoda |
| GitHub verifier preparation | ✅ Complete, local setup | Repository workflow `.github/workflows/isolated-affine.yml` and runner `verification/isolated-affine/`; [setup receipt](evidence/hosted-setup.json) records eleven passing tests, fixed inputs and limits |
| GitHub verifier execution | 🔄 In progress — run 38139172013 | Dispatched at `b15a643`; record commit, run and attempt plus full-target comparison and both-kernel acceptance |
| GitHub evidence audit | ⏳ Pending | Download artifacts; verify receipts, log hashes, controls, input/tool/dependency identities, scope and retention; write immutable result record |
| Independent mathematical/specification reviews | ✅ Complete | [REVIEW](REVIEW.md), with independent initial judgments and scope limits |
| Blind prose-first and correspondence review | ✅ Complete | Separately authored [ARGUMENT](ARGUMENT.md), reviewed before source inspection; [review identities](evidence/pre-pr/review.json) |
| Reconciliation | ✅ Complete for local preparation | Prior review gaps resolved; omitted verifier setup added and tested; actual hosted execution/audit remain explicit pending gates |
| Catalogue integration | ➖ Not applicable to this assignment | Standalone package; no target-catalogue submission requested |
| Provenance, licensing, authorship and disclosure | ✅ Complete | [PROVENANCE](PROVENANCE.md), [LICENSES](LICENSES.md), [README](README.md) |
| Distribution identity, privacy, links and archive checks | ✅ Complete through revision three | Revision-three documentation and checklist inventory, archive round trip, source-tamper/wrong-export rejection, private-path scan and relative links checked; earlier archives and receipts retained |
| Narrow PR scope and staged-byte review | ✅ Complete for published branch | Package, focused CI checks, and new hosted verifier; unrelated working-tree changes must remain outside the PR |
| Branch publication and verifier dispatch | ✅ Complete | Branch `codex/affine-logarithms-verifier` published; run 38139172013 dispatched. No PR or release created |
| PR, release and review follow-up | ⏳ Pending | No PR or release created by this run; prepare reviewable evidence first |
| Public evidence retrieval | ⏳ Pending | Local archives exist; no public download has been published or tested |
| Human peer review | ➖ Not applicable to current assignment | Model review is disclosed; no human-review claim |

Update this file after each material phase transition, changed proof/checker input,
new run, or scope decision. Link new immutable records rather than replacing old
results. A green integrity check or retained-log policy check is not a hosted proof
verification. Official upstream dependency caches, if used on the hosted runner,
must remain explicit even though candidate compilation starts fresh.
