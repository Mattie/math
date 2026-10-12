# Affine logarithms workflow checklist

Updated: October 11, 2026 (America/Chicago).

**Current phase:** ✅ Hosted verification complete; ✅ Evidence audit passed;
✅ Full manuscript drafted, reviewed and compiled; ✅ PDF/GitHub rendering,
public downloads and source-archive integrity checked. The 19-page preprint,
editable source and reproduction records are available in the existing PR.
All fifteen comparison targets passed Lean and Rust Nanoda on fresh candidate
compilation. The official Mathlib dependency cache remains trusted. See the
[immutable hosted result](evidence/hosted-result-2026-10-11.json).
The later [complete source sweep](evidence/full-module-sweep-2026-10-11/summary.json)
compiled all 967 proof modules from empty candidate build output and passed all
fifteen endpoint axiom reports. The shared manual rebuild now includes affine.
Proof-export and hosted-evidence release assets are prepared and hash checked;
publication and anonymous retrieval remain pending.

**Target:** irrationality and exponent at most four for the three expressions in
[README.md](README.md), with the twelve public declarations and fifteen comparison
wrappers in [the target map](evidence/target-map.json). The
[frozen source inventory](evidence/source-sha256.json) covers 969 inputs; its SHA-256
is `88516799eccd19825089e8e71ef84ebacb87d8a16174c0069b4cabe114089cb1`.
The retained export identity is recorded in [export-asset.json](evidence/export-asset.json).

**Final deliverable and completion criterion:** a preprint matching the existing
`preprints/` layout, with manuscript source, reproducible build, compiled
`paper.pdf`, accompanying formalization and verification evidence. Paper claims
must match checked declarations, receive independent manuscript/correspondence
review, and pass reader-facing PDF/Markdown/link checks. Deliver direct links to
the PDF, manuscript, proofs and verification result. No alternative deliverable
has been agreed; [ARGUMENT](ARGUMENT.md) is supporting material, not the preprint.

**Contribution and publication scope:** three formalized irrationality and
exponent-at-most-four results, with a common proof mechanism. The user prefers
the result-focused working title **The irrationality exponents of log(2) + √2
and √2 log(2) are at most 4**. The third result remains a main theorem:
`mu(log(3 + 2*sqrt(2))/sqrt(2) + sqrt(3)) <= 4`, together with irrationality.
It is omitted from the title, not from the paper's mathematical scope.
Existing preprint titles and layout were inspected on October 11. Mathematical
priority remains unestablished; this limits claims, not preprint preparation.

**Permissions and current assignment:** RUN authorized scoped branch publication,
hosted verification and evidence audit; PR authorized [PR 22](https://github.com/Mattie/math/pull/22).
The user authorized PAPER: prepare the complete preprint under the explicit
title, using the supplied Mbang handoff and the unreleased combined paper as
style references. Private voice references and the unreleased combined paper
remain outside the publication package. No merge, release or external submission is authorized.
A later GitHub approval gate requires separate explicit authorization.
The subsequent ALIGN/SWEEP assignment authorizes shared rebuild integration,
a complete module compilation, refreshed verification records, and preparation
of reviewable proof-export and hosted-evidence release assets.

**Evidence reused:** [GitHub run 38139172013](https://github.com/Mattie/math/actions/runs/38139172013)
verified commit `b15a6431eca8632a48c1cd84e5200edd30f0670c`; the proof run took
56 minutes 54 seconds. All 969 frozen inputs and final targets remain unchanged;
later commits change documentation, records and verification tooling. This is reuse of the dated
hosted result, not a fresh run. The complete evidence archive was downloaded and
its GitHub SHA-256 verified. Hosted artifacts expire January 9, 2027; anonymous
artifact retrieval and durable public distribution remain unverified.

The [editorial revision](../../preprints/The-irrationality-exponents-of-log-2-plus-sqrt2-and-sqrt2-log-2-are-at-most-4-October-11-2026/evidence/editorial-revision.json) records the corrected title and prose cleanup.

**Next action:** review [PR 22](https://github.com/Mattie/math/pull/22) and the
[prepared distribution identities](evidence/release-distribution.json), then
authorize publication of the retained export and hosted evidence if desired.
No merge, release, external submission, or exhaustive priority claim follows from
completion of the preparation and verification work.

Legend: ✅ Complete · 🔄 In progress · ⏳ Pending · ⛔ Blocked · ⏸️ Deferred ·
➖ Not applicable · 🟡 Partial · 🔍 Needs review.

| Milestone | Status | Evidence or remaining action |
| --- | --- | --- |
| Assignment and completion criteria | ✅ Complete | Three scoped upper bounds; required preprint and concrete completion criterion recorded above; no memo-only exception |
| Environment and provenance | ✅ Complete for local evidence | [VERIFY](VERIFY.md) records Lean 4.34.1, pinned dependencies, Linux build, and identified cache reuse; hosted resources are part of verifier setup |
| Feasibility and decision to proceed | ✅ Complete | Concrete field constructions and deduction in [ARGUMENT](ARGUMENT.md) |
| Exhaustive prior-art/priority assessment | ⏸️ Deferred by user | [PRIOR-ART](PRIOR-ART.md) retains the checked benchmark; no novelty claim |
| Independent specification and standard definitions | ✅ Complete | [REVIEW](REVIEW.md), literal [Challenge](Challenge.lean), [Solution](Solution.lean), and [StandardBridge](StandardBridge.lean) |
| Claim-to-declaration map, examples and boundaries | ✅ Complete | [Target map](evidence/target-map.json); the memo states all three instances and limits at exponent four |
| Ordinary argument and Lean development | ✅ Complete | [ARGUMENT](ARGUMENT.md); hypotheses, constants, parameter order and common witness inspected in the correspondence review |
| Frozen sources, dependencies and final wrappers | ✅ Complete | [Source inventory](evidence/source-sha256.json), [inherited pin](evidence/inherited-source-pin.json), original archives retained |
| Source build and transitive axiom audit | ✅ Complete, local Linux | [Complete module sweep](evidence/full-module-sweep-2026-10-11/summary.json): all 967 proof modules built from empty candidate output, then twelve public and three standard endpoint reports passed; pinned upstream dependency caches remain trusted. Earlier receipts remain historical evidence |
| Shared manual rebuild coverage | ✅ Configured and locally validated | `Verify publication` with `rebuild_proof=true` now includes the affine all-module builder and axiom controls alongside the eight earlier packages. The new job has not been dispatched as a hosted proof run |
| Actual audit rejection controls | ✅ Complete, local Linux | [Policy controls](evidence/pre-pr/axiom-controls/receipt.json): valid, imported admission, extra axiom, and malformed/missing reports |
| Trusted statement comparison | ✅ Complete, earlier unchanged artifact | [Checker receipt](evidence/checker-receipt.json): fifteen literal wrappers |
| Export inventory and proof-body checks | ✅ Complete, earlier unchanged artifact | [Verification summary](evidence/verification-summary.json), [inventory](evidence/export-inventory.json); same accepted export, no new full replay during packaging |
| Comparator admission and boundary controls | ✅ Complete for recorded local route | [New admission controls](evidence/pre-pr/comparator-controls/receipt.json) and original [checker receipt](evidence/checker-receipt.json); hosted boundary also passed in the immutable hosted result |
| Pinned checker assessment and trust limits | ✅ Complete for dated assessment | [CHECKERS](CHECKERS.md); supplemental older Lean is distinguished from primary Lean and Rust Nanoda |
| GitHub verifier preparation | ✅ Complete, local setup | Repository workflow `.github/workflows/isolated-affine.yml` and runner `verification/isolated-affine/`; [setup receipt](evidence/hosted-setup.json) records eleven passing tests, fixed inputs and limits |
| GitHub verifier execution | ✅ Complete — run 38139172013, attempt 1 | Exact commit `b15a643`; all fifteen targets accepted by Lean and Rust Nanoda; valid and rejection controls passed |
| GitHub evidence audit | ✅ Complete | [Immutable result](evidence/hosted-result-2026-10-11.json): 95 indexed files, 58 command logs, 93 retained-file hashes, 13 protected repository inputs and 969 frozen inputs checked |
| Independent mathematical/specification reviews | ✅ Complete | [REVIEW](REVIEW.md), with independent initial judgments and scope limits |
| Proof-memo blind prose-first and correspondence review | ✅ Complete for the reviewed memo | Separately authored [ARGUMENT](ARGUMENT.md), reviewed before source inspection; [review identities](evidence/pre-pr/review.json). Does not cover a future manuscript; later memo edits corrected the truncation explanation and GitHub math markup without changing proof sources |
| Reconciliation | ✅ Complete | [Review record](../../preprints/The-irrationality-exponents-of-log-2-plus-sqrt2-and-sqrt2-log-2-are-at-most-4-October-11-2026/evidence/reviews.json): both manuscript reviewers checked the final hash and corrections; mathematical source bytes remain unchanged |
| Publication scope and title | ✅ Complete | Result-focused title used consistently; all three results remain main theorems; no priority or exact-exponent claim |
| Paper drafted | ✅ Complete | Full manuscript with all three main results, mathematical argument, limitations, references, and formalization appendix |
| Independent manuscript review | ✅ Complete, model review | [Review record](../../preprints/The-irrationality-exponents-of-log-2-plus-sqrt2-and-sqrt2-log-2-are-at-most-4-October-11-2026/evidence/reviews.json): fresh mathematical prose-first assessment, separate specification/evidence review, and both final-diff checks; no human-review claim |
| Paper–formalization correspondence | ✅ Complete within recorded scope | [Review record](../../preprints/The-irrationality-exponents-of-log-2-plus-sqrt2-and-sqrt2-log-2-are-at-most-4-October-11-2026/evidence/reviews.json) and theorem map cover three main results, twelve public declarations and fifteen comparison targets; wrapper wording corrected; no proof changes |
| Preprint built | ✅ Complete | Editable single-file LaTeX and retained 19-page PDF; desktop compiler succeeds; reproducible Tectonic build has no layout warnings |
| Reader-facing review | ✅ Complete for recorded files | [Reader record](../../preprints/The-irrationality-exponents-of-log-2-plus-sqrt2-and-sqrt2-log-2-are-at-most-4-October-11-2026/evidence/reader-review.json): 19-page PDF inspected, actual GitHub README/VERIFY and memo checked, seven anonymous downloads matched, public source archive passed integrity checks |
| Publication package reconciled | ✅ Complete | [Preprint](../../preprints/The-irrationality-exponents-of-log-2-plus-sqrt2-and-sqrt2-log-2-are-at-most-4-October-11-2026/README.md), citation metadata, three-result theorem map, build/review identities and verification limits agree |
| Final delivery | ✅ Ready | [PDF](../../preprints/The-irrationality-exponents-of-log-2-plus-sqrt2-and-sqrt2-log-2-are-at-most-4-October-11-2026/paper.pdf), [manuscript](../../preprints/The-irrationality-exponents-of-log-2-plus-sqrt2-and-sqrt2-log-2-are-at-most-4-October-11-2026/build/main.tex), [proofs](README.md), and [verification](../../preprints/The-irrationality-exponents-of-log-2-plus-sqrt2-and-sqrt2-log-2-are-at-most-4-October-11-2026/VERIFY.md) available in PR 22 |
| Catalogue integration | ➖ Not applicable to this assignment | Standalone package; no target-catalogue submission requested |
| Provenance, licensing, authorship and disclosure | ✅ Complete | [PROVENANCE](PROVENANCE.md), [LICENSES](LICENSES.md), [README](README.md) |
| Distribution identity, privacy, links and archive checks | ✅ Complete for source publication | [Reader record](../../preprints/The-irrationality-exponents-of-log-2-plus-sqrt2-and-sqrt2-log-2-are-at-most-4-October-11-2026/evidence/reader-review.json): actual public files and repository archive retrieved; privacy/metadata/URI/attachment and package checks passed; historical proof-export availability remains separate |
| Narrow PR scope and staged-byte review | ✅ Complete for published branch | Package, focused CI checks, and new hosted verifier; unrelated working-tree changes must remain outside the PR |
| Branch publication and verifier dispatch | ✅ Complete | Branch `codex/affine-logarithms-verifier` published; run 38139172013 dispatched. [PR 22](https://github.com/Mattie/math/pull/22) created; no release |
| PR creation | ✅ Complete | [PR 22](https://github.com/Mattie/math/pull/22) includes the full preprint, formalization and audited verifier |
| PR review follow-up | ✅ Seven review comments addressed | Verification tooling hardened and all seven threads resolved at b03f478; publication CI [38188475786](https://github.com/Mattie/math/actions/runs/38188475786) passed. Later ALIGN/SWEEP validation is recorded separately. Author review and merge remain separate |
| Public release or external submission | ⏳ Pending, not authorized | Separate from preprint preparation; no merge, GitHub release or external submission performed |
| Public evidence retrieval | 🟡 Release assets prepared | [Distribution inventory](evidence/release-distribution.json): the retained export's compressed/uncompressed identities and the complete hosted archive were checked; all 95 archive-index entries match. Anonymous retrieval and durable public distribution remain pending |
| Human peer review | ➖ Not applicable to current assignment | Model review is disclosed; no human-review claim |

Update this file after each material phase transition, changed proof/checker input,
new run, or scope decision. Link new immutable records rather than replacing old
results. A green integrity check or retained-log policy check is not a hosted proof
verification. Official upstream dependency caches, if used on the hosted runner,
must remain explicit even though candidate compilation starts fresh.
