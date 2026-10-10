import Imaginary.PeriodData
import Mathlib.NumberTheory.Niven
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace OAI.Imaginary
noncomputable section

def alpha : ℂ := (-1 + 2 * rotation) / 3
def normalizedAngle : ℝ := 2 * Real.arctan (Real.sqrt 2) / Real.sqrt 2

theorem normalizedAngle_ne_zero : normalizedAngle ≠ 0 := by
  unfold normalizedAngle
  positivity

theorem cos_two_arctan (x : ℝ) :
    Real.cos (2 * Real.arctan x) = (1 - x ^ 2) / (1 + x ^ 2) := by
  rw [Real.cos_two_mul, Real.cos_sq_arctan]
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem sin_two_arctan (x : ℝ) :
    Real.sin (2 * Real.arctan x) = (2 * x) / (1 + x ^ 2) := by
  have ht := Real.tan_arctan x
  rw [Real.tan_eq_sin_div_cos] at ht
  have hs : Real.sin (Real.arctan x) = x * Real.cos (Real.arctan x) :=
    (div_eq_iff (Real.cos_arctan_pos x).ne').mp ht
  calc
    _ = 2 * x * Real.cos (Real.arctan x) ^ 2 := by rw [Real.sin_two_mul, hs]; ring
    _ = _ := by rw [Real.cos_sq_arctan]; ring

theorem exp_normalizedAngle : Complex.exp (rotation * (normalizedAngle : ℂ)) = alpha := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have he : rotation * (normalizedAngle : ℂ) =
      Complex.I * ((2 * Real.arctan (Real.sqrt 2) : ℝ) : ℂ) := by
    unfold rotation normalizedAngle
    push_cast
    field_simp
  rw [he, mul_comm Complex.I, Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, cos_two_arctan, sin_two_arctan]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp [alpha, rotation]
  ring

theorem alpha_ne_zero : alpha ≠ 0 := by
  rw [← exp_normalizedAngle]
  exact Complex.exp_ne_zero _

/-- A root of unity has integral trace; here the trace is -2/3. -/
theorem alpha_no_root (n : ℕ) (hn : 0 < n) : alpha ^ n ≠ 1 := by
  intro hroot
  have hz : IsIntegral ℤ alpha := IsIntegral.of_pow hn (hroot ▸ isIntegral_one)
  have hconjpow : (starRingEnd ℂ alpha) ^ n = 1 := by
    rw [← map_pow, hroot, map_one]
  have hconj : IsIntegral ℤ (starRingEnd ℂ alpha) :=
    IsIntegral.of_pow hn (hconjpow ▸ isIntegral_one)
  have htrace : IsIntegral ℤ (((-2 / 3 : ℚ) : ℂ)) := by
    convert hz.add hconj using 1
    norm_num [alpha, rotation, map_add, map_mul, map_ofNat]
    ring
  obtain ⟨k, hk⟩ := htrace.exists_int_iff_exists_rat.mp ⟨-2 / 3, rfl⟩
  have heq : (-2 / 3 : ℚ) = (k : ℚ) := by exact_mod_cast hk
  have hklo : -1 < k := by
    have : (-1 : ℚ) < k := by linarith
    exact_mod_cast this
  have hkhi : k < 0 := by
    have : (k : ℚ) < 0 := by linarith
    exact_mod_cast this
  omega

theorem alpha_powers_injective : Function.Injective (fun n : ℕ => alpha ^ n) := by
  intro j k h
  change alpha ^ j = alpha ^ k at h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · apply alpha_no_root (k-j) (Nat.sub_pos_of_lt hjk)
    rw [pow_sub₀ alpha alpha_ne_zero hjk.le, h, mul_inv_cancel₀ (pow_ne_zero _ alpha_ne_zero)]
  · apply alpha_no_root (j-k) (Nat.sub_pos_of_lt hkj)
    rw [pow_sub₀ alpha alpha_ne_zero hkj.le, h, mul_inv_cancel₀ (pow_ne_zero _ alpha_ne_zero)]

def sqrtTwoPeriod : PeriodData where
  num := ⟨-1, 2⟩
  den := 3
  den_pos := by norm_num
  angle := normalizedAngle
  angle_ne_zero := normalizedAngle_ne_zero
  exp_angle := by
    rw [exp_normalizedAngle]
    simp [alpha, ImaginaryInt.toComplex_def']
  powers_injective := by
    simpa [alpha, ImaginaryInt.toComplex_def'] using alpha_powers_injective

end
end OAI.Imaginary
