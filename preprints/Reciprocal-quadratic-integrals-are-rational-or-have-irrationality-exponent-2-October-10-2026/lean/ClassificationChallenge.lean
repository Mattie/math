import Mathlib

/- Independent trusted statement. The three sorry proofs are intentional challenge
   placeholders; this file is not a claimed proof of the classification. -/
namespace ClassificationChallenge

theorem repeated_root_evaluation
    (A B C a b : ℚ)
    (hA : A ≠ 0)
    (hab : a < b)
    (hpole : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ),
      (A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ) ≠ 0)
    (hdisc : B ^ 2 - 4 * A * C = 0) :
    (∫ t in (a : ℝ)..(b : ℝ),
      1 / ((A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ))) =
      2 / (2 * (A : ℝ) * (a : ℝ) + (B : ℝ)) -
        2 / (2 * (A : ℝ) * (b : ℝ) + (B : ℝ)) := by
  sorry

theorem rational_iff_discriminant_zero
    (A B C a b : ℚ)
    (hA : A ≠ 0)
    (hab : a < b)
    (hpole : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ),
      (A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ) ≠ 0) :
    (∃ r : ℚ, (∫ t in (a : ℝ)..(b : ℝ),
      1 / ((A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ))) = (r : ℝ)) ↔
      B ^ 2 - 4 * A * C = 0 := by
  sorry

theorem irrational_iff_discriminant_ne_zero
    (A B C a b : ℚ)
    (hA : A ≠ 0)
    (hab : a < b)
    (hpole : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ),
      (A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ) ≠ 0) :
    Irrational (∫ t in (a : ℝ)..(b : ℝ),
      1 / ((A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ))) ↔
      B ^ 2 - 4 * A * C ≠ 0 := by
  sorry

end ClassificationChallenge
