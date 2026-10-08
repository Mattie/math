import Imaginary.Main

/-!
# Statement for Formal Conjectures

This module states the result for the normalized value arctan(sqrt(2))/sqrt(2)
using only standard Mathlib definitions.
-/

namespace OAI.Imaginary

/-- The normalized value arctan(sqrt(2))/sqrt(2) is irrational and satisfies
the eventual approximation lower bound for every real exponent greater than two. -/
theorem normalized_arctan_sqrt_two_irrationality_and_bound :
    Irrational (Real.arctan (Real.sqrt 2) / Real.sqrt 2) ∧
      ∀ nu : ℝ, 2 < nu →
        ∃ Q : ℤ, 2 ≤ Q ∧
          ∀ p q : ℤ, Q ≤ q →
            (q : ℝ) ^ (-nu) ≤
              |Real.arctan (Real.sqrt 2) / Real.sqrt 2 - (p : ℝ) / (q : ℝ)| := by
  exact ⟨OAI.LogarithmExtension.irrational_of_eventualLowerBound
    normalized_arctan_sqrt_two_eventualLowerBound,
    normalized_arctan_sqrt_two_integer_eventualLowerBound⟩

end OAI.Imaginary
