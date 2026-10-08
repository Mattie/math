# Verification summary

The following checks were completed on October 7, 2026. These are recorded
verification results; the scripts let readers repeat them independently.

## Statement and source identity

For every rational `a > 0` with `a ≠ 1`, the theorem
`OAI.Logarithm.rational_log_irrationalityExponent_eq_two` proves
`OAI.PiExponent.irrationalityExponent (Real.log (a : ℝ)) = 2`.
The endpoint file also proves the cases log 2 and log 3 and an explicit
uniform approximation bound. No separate irrationality or interpolation
assumption is required. See [Main.lean](Logarithm/Main.lean).

The source manifest covers 55 extension modules and 869 unchanged modules
from OpenAI/math commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Mathlib is pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`.
All 924 source hashes match the checked sources.

## Completed checks

| Check | Result |
| --- | --- |
| Lean 4.34.1 build and endpoint/intermediate axiom audits | Accepted; all 42 audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`. |
| Nanoda 0.4.19 on the exported dependency closure | Accepted 117,774 declarations, exit 0. |
| Official Lean 4.34.0 kernel replay of the same export | Accepted 117,771 declarations and regenerated the three quotient declarations, exit 0. |
| Forbidden-axiom negative control | Rejected by Nanoda. |
| Ill-typed-proof negative control | Rejected by the Lean 4.34.0 replay checker. |
| Independently expressed statement bridge | Compiled; only the three foundational axioms above. |

The second Lean pass consumed the portable text export in a fresh kernel
environment at trust level zero. It did not load Lean 4.34.1 binary objects.
Nanoda used strict axiom checking, allowing only the three axioms above.
The export audit found no unsafe or partial declarations.

## Tool and artifact pins

- Lean 4.34.1: `5045d0056413266e57c625dcd7c365b10e377c52`.
- Lean 4.34.0: `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.
- Nanoda: `3a2407216ee84a75f9e1aead6803d0578be06ae7`.
- lean4export: `076e8e57707e813375e8f9da8bf989799ace9680`.
- Lean Kernel Arena: `b83254de5146ef34147ab82a48edbe1856b0edcc`.

The compressed export is 251,779,698 bytes, with SHA-256
`fdb74704ed1bc0fa9bf3a142eb3ae676d65da86832eed51bb91be8870e052206`.
The uncompressed export is 1,270,835,163 bytes, with SHA-256
`031249e63ebd33862c73b090a60faefeb1131ead9e07c32d0952cb45b80d71b3`.

See [reproduction instructions](../VERIFY.md) for builds, kernel replay,
and negative controls. Raw execution records are retained separately from
the publication; they are not needed to run the supplied scripts.

## Scope and limitations

The exponent uses infinitely many distinct reduced rational approximations
with positive error. The proof establishes membership of 2 and boundedness
above by 2 before taking the real supremum. The uniform approximation bound
also excludes exact rational representations of the target.

The [statement bridge](../review/blind-statement/CertifiedBridge.lean)
proves the exact type of an independently frozen Mathlib-only statement.
The [frozen specification](../review/blind-statement/Challenge.lean) contains
an intentional placeholder and is not imported by the proved bridge.
Its elaboration alone is not proof evidence. The independent reviewer was
an AI agent with a separate task context, not an external human referee.

Kernel checks validate formal declarations relative to their definitions
and foundational axioms. They do not establish priority or replace human
mathematical scrutiny of the exposition and its connection to the theorem.
