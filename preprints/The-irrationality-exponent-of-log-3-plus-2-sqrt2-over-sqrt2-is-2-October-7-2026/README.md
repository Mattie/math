# The irrationality exponent of log(3 + 2 sqrt(2))/sqrt(2) is 2

Ryan Matthew Casper · October 7, 2026

This preprint proves that log(3 + 2√2)/√2 has rational irrationality exponent 2. The generic theorem treats compatible norm-one periods in Q(√2). It does not establish the result for every real quadratic field or for the unnormalized logarithm.

- [Paper](paper.pdf) and [editable manuscript](build/manuscript.md)
- [Lean proof](lean/RealNorm/Main.lean), [catalogue statement](lean/RealNorm/FormalConjectures.lean), [verification summary](lean/VERIFICATION.md), and [reproduction](VERIFY.md)
- Explanations: [PhD](explainers/ELIPHD.md), [master's](explainers/ELIMS.md), [bachelor's](explainers/ELIBS.md), and [high school](explainers/ELIHS.md)
- [Licenses and attribution](LICENSES.md), [NOTICE](NOTICE), and [citation metadata](CITATION.cff)

Lean 4.34.1 compiled the proof and its 29 declaration audits. Nanoda and a separate stock Lean 4.34.0 replay checked the frozen export's 117,830 declarations. The verification summary records the exact statements, hashes, and checker results. Formal checks are not external human peer review.

The work builds on OpenAI's released weighted interpolation library, Mathlib, and Casper's preceding logarithm and quadratic-period adaptations. OpenAI coding agents contributed substantially to the research, mathematical adaptation, formalization, checking, and exposition under Casper's direction. The paper includes the full disclosure and makes no exhaustive priority claim.

[Verification status and retained-export downloads](VERIFY.md#verification-and-distribution-update).
