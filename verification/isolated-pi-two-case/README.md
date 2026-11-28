# Isolated verification of the two-case pi companion

This manual workflow checks three exact declarations.
It has been prepared locally. A GitHub-hosted run and its evidence audit remain pending.

| Declaration | Trusted statement |
| --- | --- |
| PiTwoCaseBridge.main | The eventual integer-denominator bound and the supremum for rational approximations to pi. |
| PiTwoCaseBridge.pi_irrationalityExponent_eq_two | The irrationality exponent of pi in the pinned OpenAI definition. |
| PiTwoCaseBridge.theorem_5_1 | The strict curve-degree hypothesis and jet interpolation with one affine budget for every positive real cutoff. |

[Challenge.lean](Challenge.lean) states these targets without importing the candidate.
The interpolation statement spells out the local coefficient condition and the weighted source bound. Its geometric hypothesis uses the pinned definitions of branch contact and pole degree. The challenge uses admitted propositions for comparison. The candidate may use only the three listed standard axioms.

[verify.py](verify.py) reuses the existing Comparator, Landrun, and systemd preflight.
It checks the input freeze, builds the pinned OpenAI dependencies in a trusted project, and stages the candidate into fresh build space. The workflow requires intended diagnostics for the mismatch, forbidden axiom, and imported admission controls, and acceptance by both kernels. It records tool, input, dependency, and log hashes. [Workflow](../../.github/workflows/isolated-pi-two-case.yml)

For local, offline preparation checks, run:

~~~sh
python3 -I -B verification/isolated-pi-two-case/verify.py
python3 -I -B verification/isolated-pi-two-case/verify.py --stage /path/to/new/directory
~~~

Local preparation passed the three staging tests and the 14 tests for the reused verifier. On Linux, the generated workspace resolved both trusted libraries and kept the dependency lock intact. Lean also accepted each challenge type when supplied with the corresponding frozen theorem. The GitHub workflow will exercise the actual isolation boundary and the two checker implementations.

The historical exported-proof replay and the hosted build are separate checks. See the [paper verification record](../../preprints/The-irrationality-exponent-of-pi-through-a-two-case-determinant-argument-October-11-2026/VERIFY.md) and the [source replay instructions](REPLAY.md).
