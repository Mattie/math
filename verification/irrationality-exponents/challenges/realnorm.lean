import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational
set_option autoImplicit false
theorem OAI.RealNorm.normalized_log_sqrt_two_irrationality_and_bound  :
  Irrational (Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2) ∧ ∀ nu : ℝ, 2 < nu →
    ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
      (q : ℝ)^(-nu) ≤ |(Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2) - (p : ℝ)/(q : ℝ)| := by sorry
