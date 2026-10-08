import Arctangent.Main

/-!
# Statement for Formal Conjectures

The catalogue statement uses only standard Mathlib definitions. This module
proves that exact statement from the arctangent approximation theorem.
-/

namespace OAI.Arctangent

/-- Every nonzero rational arctangent is irrational and satisfies the eventual
approximation lower bound for every real exponent greater than two. -/
theorem rational_arctan_irrationality_and_bound (r : ℚ) (hr : r ≠ 0) :
    Irrational (Real.arctan (r : ℝ)) ∧
      ∀ nu : ℝ, 2 < nu →
        ∃ Q : ℤ, 2 ≤ Q ∧
          ∀ p q : ℤ, Q ≤ q →
            (q : ℝ) ^ (-nu) ≤ |Real.arctan (r : ℝ) - (p : ℝ) / (q : ℝ)| := by
  exact ⟨OAI.LogarithmExtension.irrational_of_eventualLowerBound
    (rational_arctan_eventualLowerBound r hr),
    rational_arctan_integer_eventualLowerBound r hr⟩

end OAI.Arctangent
