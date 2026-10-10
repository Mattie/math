import Lake
open Lake DSL
package QuadraticPeriods where
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean_lib OAI
lean_lib Logarithm
lean_lib Imaginary
lean_lib Periodic
lean_lib PeriodicGeometry
lean_lib PeriodicFamily
lean_lib Quadratic
lean_lib QuadraticReal3
lean_lib QuadraticImag5
lean_lib QuadraticAudit
lean_lib QuadraticFamilyAudit
lean_lib Combined
lean_lib StandardBridge
lean_lib Challenge
lean_lib Solution
lean_lib Audit
