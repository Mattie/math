import Mathlib

set_option autoImplicit false

namespace PositiveIntegralCheck

theorem positive_bound
    (A B C a b : ℚ)
    (hA : A ≠ 0)
    (hab : a < b)
    (hDelta : 0 < B ^ 2 - 4 * A * C)
    (hpoles : ∀ t : ℝ, t ∈ Set.Icc (a : ℝ) (b : ℝ) →
      (A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ) ≠ 0) :
    ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ (p : ℤ) (q : ℕ), Q ≤ q →
        1 / (q : ℝ) ^ ν ≤
          |(∫ t in (a : ℝ)..(b : ℝ),
              1 / ((A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ))) -
            (p : ℝ) / (q : ℝ)| := by
  sorry

theorem positive_exponent_two
    (A B C a b : ℚ)
    (hA : A ≠ 0)
    (hab : a < b)
    (hDelta : 0 < B ^ 2 - 4 * A * C)
    (hpoles : ∀ t : ℝ, t ∈ Set.Icc (a : ℝ) (b : ℝ) →
      (A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ) ≠ 0) :
    Irrational (∫ t in (a : ℝ)..(b : ℝ),
      1 / ((A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ))) ∧
    ∀ ν : ℝ, 2 < ν →
      ¬LiouvilleWith ν (∫ t in (a : ℝ)..(b : ℝ),
        1 / ((A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ))) := by
  sorry

theorem nonzero_discriminant_bound
    (A B C a b : ℚ)
    (hA : A ≠ 0)
    (hab : a < b)
    (hDelta : B ^ 2 - 4 * A * C ≠ 0)
    (hpoles : ∀ t : ℝ, t ∈ Set.Icc (a : ℝ) (b : ℝ) →
      (A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ) ≠ 0) :
    ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ (p : ℤ) (q : ℕ), Q ≤ q →
        1 / (q : ℝ) ^ ν ≤
          |(∫ t in (a : ℝ)..(b : ℝ),
              1 / ((A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ))) -
            (p : ℝ) / (q : ℝ)| := by
  sorry

theorem nonzero_discriminant_exponent_two
    (A B C a b : ℚ)
    (hA : A ≠ 0)
    (hab : a < b)
    (hDelta : B ^ 2 - 4 * A * C ≠ 0)
    (hpoles : ∀ t : ℝ, t ∈ Set.Icc (a : ℝ) (b : ℝ) →
      (A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ) ≠ 0) :
    Irrational (∫ t in (a : ℝ)..(b : ℝ),
      1 / ((A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ))) ∧
    ∀ ν : ℝ, 2 < ν →
      ¬LiouvilleWith ν (∫ t in (a : ℝ)..(b : ℝ),
        1 / ((A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ))) := by
  sorry

end PositiveIntegralCheck
