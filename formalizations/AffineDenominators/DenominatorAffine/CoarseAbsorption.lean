import PairedAffine.AnalyticCoarse

namespace OAI.DenominatorAffine

open AlgebraicLog.DeterminantData AlgebraicLog.ConjugateAggregate

noncomputable section

/-- Enlarging the fixed coarse centre bound pays both the good-embedding
multiplier and twice the transverse denominator cost. The enlargement is
chosen before the approximation parameters and does not depend on height. -/
theorem conjugateCost_add_denominator_le {proxy nu rho : ℝ}
    (d : FixedData proxy nu rho) (kappa : ℝ) (dn : ℕ) (hdn : 0 < dn)
    {R : ℝ} (hR : 0 ≤ R) :
    conjugateCost d kappa R + (Real.log 2 + 2 * Real.log (dn : ℝ)) / d.wstar ≤
      conjugateCost d kappa (2 * (dn : ℝ) ^ 2 * (R + 2)) := by
  have hK : (1 : ℝ) ≤ d.K := by exact_mod_cast d.K_pos
  have hd : (0 : ℝ) < dn := by exact_mod_cast hdn
  have hpos : 0 < 2 * ((d.K : ℝ) * R + 2) := by positivity
  have hbound : (2 * ((d.K : ℝ) * R + 2)) * (2 * (dn : ℝ) ^ 2) ≤
      2 * ((d.K : ℝ) * (2 * (dn : ℝ) ^ 2 * (R + 2)) + 2) := by
    nlinarith only [mul_nonneg (sq_nonneg (dn : ℝ)) (sub_nonneg.mpr hK)]
  have heq : Real.log ((2 * ((d.K : ℝ) * R + 2)) * (2 * (dn : ℝ) ^ 2)) =
      Real.log (2 * ((d.K : ℝ) * R + 2)) +
        (Real.log 2 + 2 * Real.log (dn : ℝ)) := by
    rw [Real.log_mul hpos.ne' (by positivity),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 2 hd.ne'),
      Real.log_pow]
    norm_num
  have hlog := Real.log_le_log (by positivity :
    0 < (2 * ((d.K : ℝ) * R + 2)) * (2 * (dn : ℝ) ^ 2)) hbound
  rw [heq] at hlog
  have hdiv := div_le_div_of_nonneg_right hlog d.wstar_pos.le
  rw [add_div] at hdiv
  unfold conjugateCost
  linarith

end
end OAI.DenominatorAffine
