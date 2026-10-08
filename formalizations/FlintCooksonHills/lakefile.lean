import Lake
open Lake DSL
package SmallDivisorsPort where
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean_lib OAI where
  srcDir := "../../preprints/The-irrationality-exponent-of-positive-rational-logarithms-is-2-October-7-2026/lean"
lean_lib SmallDivisors
