import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

/- Independent specification. The cube root is positive real exponentiation;
the threshold precedes both approximation variables and is uniform in them.
Only this trusted challenge contains placeholders. -/
set_option autoImplicit false
namespace AffineCubicVerification

theorem eventual_lower_bound :
    ∀ nu : ℝ, 6 < nu → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (q : ℝ) ^ (-nu) ≤
          |Real.log 2 + (2 : ℝ) ^ (1 / 3 : ℝ) - (p : ℝ) / (q : ℝ)| := by
  sorry

theorem irrational : Irrational (Real.log 2 + (2 : ℝ) ^ (1 / 3 : ℝ)) := by
  sorry

theorem irrationality_exponent_le_six :
    sSup {nu : ℝ | 0 < nu ∧
      ({r : ℚ | 2 ≤ r.den ∧
        0 < |Real.log 2 + (2 : ℝ) ^ (1 / 3 : ℝ) - (r : ℝ)| ∧
        |Real.log 2 + (2 : ℝ) ^ (1 / 3 : ℝ) - (r : ℝ)| <
          (r.den : ℝ) ^ (-nu)} : Set ℚ).Infinite} ≤ 6 := by
  sorry

theorem not_liouvilleWith :
    ∀ nu : ℝ, 6 < nu →
      ¬ LiouvilleWith nu (Real.log 2 + (2 : ℝ) ^ (1 / 3 : ℝ)) := by
  sorry

end AffineCubicVerification
