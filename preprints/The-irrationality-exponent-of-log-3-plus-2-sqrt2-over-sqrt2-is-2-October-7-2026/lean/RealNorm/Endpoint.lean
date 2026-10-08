import RealNorm.PeriodData

namespace OAI.RealNorm
noncomputable section

def fundamentalUnit : RealInt := ⟨3, 2⟩
def unitValue : ℝ := 3 + 2 * Real.sqrt 2
def normalizedLog : ℝ := Real.log unitValue / Real.sqrt 2

theorem unitValue_gt_one : 1 < unitValue := by
  unfold unitValue
  nlinarith [Real.sqrt_nonneg 2]

theorem normalizedLog_ne_zero : normalizedLog ≠ 0 := by
  unfold normalizedLog
  exact (div_pos (Real.log_pos unitValue_gt_one)
    (Real.sqrt_pos.mpr (by norm_num))).ne'

theorem unit_embeddings_product :
    RealInt.embedding false fundamentalUnit * RealInt.embedding true fundamentalUnit = 1 := by
  change RealInt.embedding false fundamentalUnit * RealInt.embedding (!false) fundamentalUnit = 1
  rw [← RealInt.norm_eq_product false fundamentalUnit]
  norm_num [fundamentalUnit, Zsqrtd.norm_def]

theorem exp_normalizedLog_pos :
    Complex.exp (rotation false * (normalizedLog : ℂ)) =
      RealInt.embedding false fundamentalUnit := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have he : rotation false * (normalizedLog : ℂ) = (Real.log unitValue : ℂ) := by
    simp only [rotation, Bool.false_eq_true, ite_false, normalizedLog, Complex.ofReal_div]
    field_simp
  rw [he, ← Complex.ofReal_exp, Real.exp_log (zero_lt_one.trans unitValue_gt_one)]
  simp [unitValue, fundamentalUnit, RealInt.embedding_def, rotation]

theorem exp_normalizedLog (s : Bool) :
    Complex.exp (rotation s * (normalizedLog : ℂ)) =
      RealInt.embedding s fundamentalUnit := by
  cases s
  · exact exp_normalizedLog_pos
  · have he : rotation true * (normalizedLog : ℂ) =
        -(rotation false * (normalizedLog : ℂ)) := by simp [rotation]
    rw [he, Complex.exp_neg, exp_normalizedLog_pos]
    have hn : RealInt.embedding false fundamentalUnit ≠ 0 := by
      rw [← exp_normalizedLog_pos]
      exact Complex.exp_ne_zero _
    apply (mul_left_cancel₀ hn)
    rw [mul_inv_cancel₀ hn]
    exact unit_embeddings_product.symm

theorem real_exp_powers_injective {y : ℝ} (hy : y ≠ 0) :
    Function.Injective (fun n : ℕ => (Complex.exp (y : ℂ)) ^ n) := by
  intro j k h
  have he : Real.exp ((j : ℝ) * y) = Real.exp ((k : ℝ) * y) := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_natCast,
      Complex.exp_nat_mul] using h
  have hn : (j : ℝ) = k := mul_right_cancel₀ hy (Real.exp_injective he)
  exact_mod_cast hn

theorem unit_powers_injective (s : Bool) :
    Function.Injective (fun n : ℕ => (RealInt.embedding s fundamentalUnit) ^ n) := by
  rw [← exp_normalizedLog s]
  cases s
  · have he : rotation false * (normalizedLog : ℂ) =
        ((Real.sqrt 2 * normalizedLog : ℝ) : ℂ) := by simp [rotation]
    rw [he]
    exact real_exp_powers_injective (mul_ne_zero
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne' normalizedLog_ne_zero)
  · have he : rotation true * (normalizedLog : ℂ) =
        ((-Real.sqrt 2 * normalizedLog : ℝ) : ℂ) := by simp [rotation]
    rw [he]
    exact real_exp_powers_injective (mul_ne_zero
      (neg_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne') normalizedLog_ne_zero)

def sqrtTwoPeriod : PeriodData where
  num := fundamentalUnit
  den := 1
  den_pos := by norm_num
  angle := normalizedLog
  angle_ne_zero := normalizedLog_ne_zero
  exp_angles := by simpa using exp_normalizedLog
  powers_injective := by simpa using unit_powers_injective
  sign := false

end
end OAI.RealNorm
