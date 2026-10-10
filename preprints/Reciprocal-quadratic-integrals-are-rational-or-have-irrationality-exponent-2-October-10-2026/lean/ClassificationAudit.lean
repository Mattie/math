import ClassificationSolution

noncomputable section
open intervalIntegral Set
namespace OAI.IntegralClassification.Controls

/-- The positive-leading repeated-root example fixes the factor of two. -/
theorem repeated_positive : (∫ x : ℝ in 1..2, 1/x^2) = 1/2 := by
  have h := repeated_root_evaluation_real 1 0 0 1 2
    (by norm_num) (by norm_num) (by norm_num) (by
      intro x hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      simpa using pow_ne_zero 2 hx0)
  norm_num at h
  simpa only [one_div] using h

/-- Negative leading coefficients retain the negative integral sign. -/
theorem repeated_negative : (∫ x : ℝ in 1..2, 1/(-x^2)) = -1/2 := by
  have h := repeated_root_evaluation_real (-1) 0 0 1 2
    (by norm_num) (by norm_num) (by norm_num) (by
      intro x hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      simpa using pow_ne_zero 2 hx0)
  norm_num at h
  simpa only [one_div, inv_neg, integral_neg, neg_div] using congrArg Neg.neg h

end OAI.IntegralClassification.Controls

#check @OAI.IntegralClassification.repeated_root_evaluation_real
#check @OAI.IntegralClassification.repeated_root_rational
#check @OAI.IntegralClassification.rational_iff_discriminant_zero
#check @OAI.IntegralClassification.irrational_iff_discriminant_ne_zero
#check @OAI.IntegralClassification.reciprocal_quadratic_dichotomy
#check @ClassificationChallenge.repeated_root_evaluation
#check @ClassificationChallenge.rational_iff_discriminant_zero
#check @ClassificationChallenge.irrational_iff_discriminant_ne_zero

#print axioms OAI.IntegralClassification.repeated_root_evaluation_real
#print axioms OAI.IntegralClassification.repeated_root_rational
#print axioms OAI.IntegralClassification.rational_iff_discriminant_zero
#print axioms OAI.IntegralClassification.irrational_iff_discriminant_ne_zero
#print axioms OAI.IntegralClassification.reciprocal_quadratic_dichotomy
#print axioms ClassificationChallenge.repeated_root_evaluation
#print axioms ClassificationChallenge.rational_iff_discriminant_zero
#print axioms ClassificationChallenge.irrational_iff_discriminant_ne_zero
#print axioms OAI.IntegralClassification.Controls.repeated_positive
#print axioms OAI.IntegralClassification.Controls.repeated_negative
