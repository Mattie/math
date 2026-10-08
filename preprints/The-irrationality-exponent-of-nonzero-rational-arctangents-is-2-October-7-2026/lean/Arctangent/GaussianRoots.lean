import Mathlib.NumberTheory.Niven
import Arctangent.PeriodData

namespace OAI.Arctangent
noncomputable section

/-- The only roots of unity with rational real and imaginary parts are the four
Gaussian units. The norm-one hypothesis is supplied by the exponential identity. -/
theorem gaussian_rational_root_coordinates (a b : ℚ)
    (hnorm : a ^ 2 + b ^ 2 = 1) (n : ℕ) (hn : 0 < n)
    (hroot : ((a : ℂ) + (b : ℂ) * Complex.I) ^ n = 1) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨
      (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) := by
  let z : ℂ := (a : ℂ) + (b : ℂ) * Complex.I
  have hz : IsIntegral ℤ z := IsIntegral.of_pow hn (hroot ▸ isIntegral_one)
  have hconjpow : (starRingEnd ℂ z) ^ n = 1 := by
    rw [← map_pow, show z ^ n = 1 from hroot, map_one]
  have hconj : IsIntegral ℤ (starRingEnd ℂ z) :=
    IsIntegral.of_pow hn (hconjpow ▸ isIntegral_one)
  have hreal : IsIntegral ℤ (((2 * a : ℚ) : ℂ)) := by
    convert hz.add hconj using 1
    simp [z, map_add, map_mul]
    ring
  have himag : IsIntegral ℤ (((2 * b : ℚ) : ℂ)) := by
    convert (hz.sub hconj).mul (Complex.isIntegral_I ℤ).neg using 1
    simp [z, map_add, map_mul]
    ring_nf
    simp
  obtain ⟨ka, hka⟩ := hreal.exists_int_iff_exists_rat.mp ⟨2 * a, rfl⟩
  obtain ⟨kb, hkb⟩ := himag.exists_int_iff_exists_rat.mp ⟨2 * b, rfl⟩
  have ha : 2 * a = (ka : ℚ) := by exact_mod_cast hka
  have hb : 2 * b = (kb : ℚ) := by exact_mod_cast hkb
  have hka_low : -2 ≤ ka := by
    have : (-2 : ℚ) ≤ ka := by nlinarith [sq_nonneg (a + 1), sq_nonneg b]
    exact_mod_cast this
  have hka_high : ka ≤ 2 := by
    have : (ka : ℚ) ≤ 2 := by nlinarith [sq_nonneg (a - 1), sq_nonneg b]
    exact_mod_cast this
  have hkb_low : -2 ≤ kb := by
    have : (-2 : ℚ) ≤ kb := by nlinarith [sq_nonneg (b + 1), sq_nonneg a]
    exact_mod_cast this
  have hkb_high : kb ≤ 2 := by
    have : (kb : ℚ) ≤ 2 := by nlinarith [sq_nonneg (b - 1), sq_nonneg a]
    exact_mod_cast this
  interval_cases ka <;> interval_cases kb <;> norm_num at ha hb <;>
    first
    | (left; constructor <;> linarith)
    | (right; left; constructor <;> linarith)
    | (right; right; left; constructor <;> linarith)
    | (right; right; right; constructor <;> linarith)
    | nlinarith

/-- Non-torsion in a field gives pairwise distinct nonnegative powers. -/
theorem powers_injective_of_no_root {z : ℂ} (hz : z ≠ 0)
    (hroot : ∀ n : ℕ, 0 < n → z ^ n ≠ 1) :
    Function.Injective (fun n : ℕ => z ^ n) := by
  intro j k h
  change z ^ j = z ^ k at h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · apply hroot (k - j) (Nat.sub_pos_of_lt hjk)
    rw [pow_sub₀ z hz hjk.le, h, mul_inv_cancel₀ (pow_ne_zero _ hz)]
  · apply hroot (j - k) (Nat.sub_pos_of_lt hkj)
    rw [pow_sub₀ z hz hkj.le, h, mul_inv_cancel₀ (pow_ne_zero _ hz)]

end
end OAI.Arctangent
