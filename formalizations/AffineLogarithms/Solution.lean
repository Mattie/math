import PairedAffine.Main
import PairedAffine.AffineExamples
import StandardBridge

set_option autoImplicit false
namespace PairedAffineVerification

theorem shifted_period_eventualLowerBound :
    ∀ nu : ℝ, 4 < nu → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (q : ℝ) ^ (-nu) ≤ |(Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2 + Real.sqrt 3) - (p : ℝ) / (q : ℝ)| :=
  OAI.PairedAffine.shifted_period_eventualLowerBound

theorem shifted_period_explicit_bound :
    ∀ nu : ℝ, 4 < nu → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (q : ℝ) ^ (-nu) ≤ |(Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2 + Real.sqrt 3) - (p : ℝ) / (q : ℝ)| :=
  OAI.PairedAffine.shifted_period_explicit_bound

theorem shifted_period_irrational :
    Irrational (Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2 + Real.sqrt 3) :=
  OAI.PairedAffine.shifted_period_irrational

theorem shifted_period_irrationalityExponent_le_four :
    sSup {nu : ℝ | 0 < nu ∧
      ({r : ℚ | 2 ≤ r.den ∧ 0 < |(Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2 + Real.sqrt 3) - (r : ℝ)| ∧
        |(Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2 + Real.sqrt 3) - (r : ℝ)| < (r.den : ℝ) ^ (-nu)} : Set ℚ).Infinite} ≤ 4 :=
  OAI.PairedAffine.shifted_period_irrationalityExponent_le_four

theorem shifted_period_standard_exponent_le_four :
    Irrational (Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2 + Real.sqrt 3) ∧
      ∀ nu : ℝ, 4 < nu → ¬ LiouvilleWith nu (Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2 + Real.sqrt 3) :=
  ⟨OAI.PairedAffine.shifted_period_irrational,
    not_liouvilleWith_of_eventual_bound (Real.log (3 + 2 * Real.sqrt 2) / Real.sqrt 2 + Real.sqrt 3)
      OAI.PairedAffine.shifted_period_explicit_bound⟩

theorem log_two_add_sqrt_two_eventualLowerBound :
    ∀ nu : ℝ, 4 < nu → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (q : ℝ) ^ (-nu) ≤ |(Real.log 2 + Real.sqrt 2) - (p : ℝ) / (q : ℝ)| :=
  OAI.PairedAffine.log_two_add_sqrt_two_eventualLowerBound

theorem log_two_add_sqrt_two_explicit_bound :
    ∀ nu : ℝ, 4 < nu → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (q : ℝ) ^ (-nu) ≤ |(Real.log 2 + Real.sqrt 2) - (p : ℝ) / (q : ℝ)| :=
  OAI.PairedAffine.log_two_add_sqrt_two_explicit_bound

theorem log_two_add_sqrt_two_irrational :
    Irrational (Real.log 2 + Real.sqrt 2) :=
  OAI.PairedAffine.log_two_add_sqrt_two_irrational

theorem log_two_add_sqrt_two_irrationalityExponent_le_four :
    sSup {nu : ℝ | 0 < nu ∧
      ({r : ℚ | 2 ≤ r.den ∧ 0 < |(Real.log 2 + Real.sqrt 2) - (r : ℝ)| ∧
        |(Real.log 2 + Real.sqrt 2) - (r : ℝ)| < (r.den : ℝ) ^ (-nu)} : Set ℚ).Infinite} ≤ 4 :=
  OAI.PairedAffine.log_two_add_sqrt_two_irrationalityExponent_le_four

theorem log_two_add_sqrt_two_standard_exponent_le_four :
    Irrational (Real.log 2 + Real.sqrt 2) ∧
      ∀ nu : ℝ, 4 < nu → ¬ LiouvilleWith nu (Real.log 2 + Real.sqrt 2) :=
  ⟨OAI.PairedAffine.log_two_add_sqrt_two_irrational,
    not_liouvilleWith_of_eventual_bound (Real.log 2 + Real.sqrt 2)
      OAI.PairedAffine.log_two_add_sqrt_two_explicit_bound⟩

theorem sqrt_two_mul_log_two_eventualLowerBound :
    ∀ nu : ℝ, 4 < nu → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (q : ℝ) ^ (-nu) ≤ |(Real.sqrt 2 * Real.log 2) - (p : ℝ) / (q : ℝ)| :=
  OAI.PairedAffine.sqrt_two_mul_log_two_eventualLowerBound

theorem sqrt_two_mul_log_two_explicit_bound :
    ∀ nu : ℝ, 4 < nu → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (q : ℝ) ^ (-nu) ≤ |(Real.sqrt 2 * Real.log 2) - (p : ℝ) / (q : ℝ)| :=
  OAI.PairedAffine.sqrt_two_mul_log_two_explicit_bound

theorem sqrt_two_mul_log_two_irrational :
    Irrational (Real.sqrt 2 * Real.log 2) :=
  OAI.PairedAffine.sqrt_two_mul_log_two_irrational

theorem sqrt_two_mul_log_two_irrationalityExponent_le_four :
    sSup {nu : ℝ | 0 < nu ∧
      ({r : ℚ | 2 ≤ r.den ∧ 0 < |(Real.sqrt 2 * Real.log 2) - (r : ℝ)| ∧
        |(Real.sqrt 2 * Real.log 2) - (r : ℝ)| < (r.den : ℝ) ^ (-nu)} : Set ℚ).Infinite} ≤ 4 :=
  OAI.PairedAffine.sqrt_two_mul_log_two_irrationalityExponent_le_four

theorem sqrt_two_mul_log_two_standard_exponent_le_four :
    Irrational (Real.sqrt 2 * Real.log 2) ∧
      ∀ nu : ℝ, 4 < nu → ¬ LiouvilleWith nu (Real.sqrt 2 * Real.log 2) :=
  ⟨OAI.PairedAffine.sqrt_two_mul_log_two_irrational,
    not_liouvilleWith_of_eventual_bound (Real.sqrt 2 * Real.log 2)
      OAI.PairedAffine.sqrt_two_mul_log_two_explicit_bound⟩

end PairedAffineVerification

