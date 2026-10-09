import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational
set_option autoImplicit false
theorem OAI.Arctangent.rational_arctan_irrationality_and_bound (r : ℚ) (hr : r ≠ 0) :
  Irrational (Real.arctan (r : ℝ)) ∧ ∀ nu : ℝ, 2 < nu →
    ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
      (q : ℝ)^(-nu) ≤ |(Real.arctan (r : ℝ)) - (p : ℝ)/(q : ℝ)| := by sorry
