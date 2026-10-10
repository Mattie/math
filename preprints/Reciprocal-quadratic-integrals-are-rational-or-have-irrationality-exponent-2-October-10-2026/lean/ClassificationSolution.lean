import Classification

set_option autoImplicit false
namespace ClassificationChallenge

/-- Repeated-root evaluation on the full pole-free real interval. -/
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
  exact OAI.IntegralClassification.repeated_root_evaluation_real (A:ℝ) B C a b
    (by exact_mod_cast hA) (by exact_mod_cast hdisc) (by exact_mod_cast hab.le) hpole

/-- Rationality is equivalent to vanishing discriminant. -/
theorem rational_iff_discriminant_zero
    (A B C a b : ℚ)
    (hA : A ≠ 0)
    (hab : a < b)
    (hpole : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ),
      (A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ) ≠ 0) :
    (∃ r : ℚ, (∫ t in (a : ℝ)..(b : ℝ),
      1 / ((A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ))) = (r : ℝ)) ↔
      B ^ 2 - 4 * A * C = 0 :=
  OAI.IntegralClassification.rational_iff_discriminant_zero A B C a b hA hab hpole

/-- Irrationality is equivalent to nonvanishing discriminant. -/
theorem irrational_iff_discriminant_ne_zero
    (A B C a b : ℚ)
    (hA : A ≠ 0)
    (hab : a < b)
    (hpole : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ),
      (A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ) ≠ 0) :
    Irrational (∫ t in (a : ℝ)..(b : ℝ),
      1 / ((A : ℝ) * t ^ 2 + (B : ℝ) * t + (C : ℝ))) ↔
      B ^ 2 - 4 * A * C ≠ 0 :=
  OAI.IntegralClassification.irrational_iff_discriminant_ne_zero A B C a b hA hab hpole

end ClassificationChallenge
