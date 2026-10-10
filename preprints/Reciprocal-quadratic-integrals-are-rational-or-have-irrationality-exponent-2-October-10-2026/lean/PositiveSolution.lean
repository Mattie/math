import PositiveMain
import StandardBridge
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

set_option autoImplicit false

namespace PositiveIntegralCheck

private theorem literal_bound {x : ℝ} (h : OAI.PiExponent.EventualLowerBound x) :
    ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ (p : ℤ) (q : ℕ), Q ≤ q →
        1 / (q : ℝ) ^ ν ≤ |x - (p : ℝ) / (q : ℝ)| := by
  intro ν hν
  obtain ⟨Q, hQ, hb⟩ := h ν hν
  refine ⟨Q, hQ, fun p q hq => ?_⟩
  simpa only [Real.rpow_eq_pow, Real.rpow_neg (Nat.cast_nonneg q), one_div] using hb p q hq


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
  exact literal_bound (OAI.Integrals.positive_discriminant_bound A B C a b hA hDelta hab hpoles)

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
  exact CompareChallenge.standard_exponent_two_of_eventual_bound _ (positive_bound A B C a b hA hab hDelta hpoles)

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
  exact literal_bound (OAI.Integrals.nonzero_discriminant_bound A B C a b hA hDelta hab hpoles)

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
  exact CompareChallenge.standard_exponent_two_of_eventual_bound _ (nonzero_discriminant_bound A B C a b hA hab hDelta hpoles)

end PositiveIntegralCheck
#print axioms PositiveIntegralCheck.positive_bound
#print axioms PositiveIntegralCheck.positive_exponent_two
#print axioms PositiveIntegralCheck.nonzero_discriminant_bound
#print axioms PositiveIntegralCheck.nonzero_discriminant_exponent_two
