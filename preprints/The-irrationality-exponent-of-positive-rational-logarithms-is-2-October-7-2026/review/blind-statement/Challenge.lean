import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational

/-- Specification only: the `sorry` is intentional and supplies no proof. -/
theorem log_rational_challenge (a : ℚ) (ha : 0 < a) (ha_ne_one : a ≠ 1) :
    Irrational (Real.log (a : ℝ)) ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ Q : ℕ, 2 ≤ Q ∧
          ∀ (p : ℤ) (q : ℕ), Q ≤ q →
            Real.rpow (q : ℝ) (-(2 + ε)) ≤
              |Real.log (a : ℝ) - (p : ℝ) / (q : ℝ)| := by
  sorry
