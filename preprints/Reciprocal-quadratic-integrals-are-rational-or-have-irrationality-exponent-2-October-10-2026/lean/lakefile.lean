import Lake
open Lake DSL
package ReciprocalQuadratic where
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean_lib Classification
lean_lib ClassificationAudit
lean_lib ClassificationChallenge
lean_lib ClassificationSolution
lean_lib Coefficients
lean_lib Combined
lean_lib Imaginary
lean_lib Logarithm
lean_lib Main
lean_lib Negative
lean_lib OAI
lean_lib PeriodicFamily
lean_lib PeriodicGeometry
lean_lib Positive
lean_lib PositiveAudit
lean_lib PositiveChallenge
lean_lib PositiveControls
lean_lib PositiveCrossRatio
lean_lib PositiveLogBridge
lean_lib PositiveMain
lean_lib PositiveNormCoefficients
lean_lib PositiveScaling
lean_lib PositiveSolution
lean_lib PositiveSquareclass
lean_lib Quadratic
lean_lib RepeatedRoot
lean_lib StandardBridge
