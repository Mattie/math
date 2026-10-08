# Verification scope

The published `SmallDivisors/Main.lean` has SHA256 `9a6604aebf7eb7ed284f89b2841cffcac8dc45493b7b6958b6578877987467ad`.

It passed a fresh Lean 4.34.1 compilation with `autoImplicit=false` and warnings treated as errors, using the existing pinned dependency build. Its two convergence endpoints and cosine-nonvanishing theorem report only `propext`, `Classical.choice`, and `Quot.sound`. The receipt is in `evidence/lean-build.log`.

The underlying mathematical argument and exact series statements underwent two automated specification/adversarial reviews. These are not external human peer review. A preceding source revision was also checked through Nanoda and a separate Lean kernel replay; it differed by a one-word tactic cleanup (`simpa` to `simp`). Those earlier export checks are **not claimed for the source bytes published here**. This revision has the fresh strict source build and axiom audit described above; a new independent export replay was not performed.

The source checker verifies this module's hash and all 869 inherited OAI source hashes. Hash checks establish artifact identity, not mathematical correctness. The dependency cache, Lean implementation, and Mathlib remain trust dependencies. The documented Lake configuration points to the inherited sources within this repository. Rebuilding all inherited modules from a clean machine was not repeated for the small tactic cleanup.
