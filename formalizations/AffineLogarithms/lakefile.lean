import Lake
open Lake DSL
package QuadraticPeriods where
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean_lib OAI
lean_lib Logarithm
lean_lib AlgebraicLog
lean_lib PairedAffine
lean_lib StandardBridge
lean_lib Challenge
@[default_target] lean_lib Solution
