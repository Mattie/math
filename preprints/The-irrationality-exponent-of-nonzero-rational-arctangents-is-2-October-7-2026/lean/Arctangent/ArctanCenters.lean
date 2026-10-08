import Arctangent.GaussianRoots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace OAI.Arctangent
noncomputable section

def realPart (r : ℚ) : ℚ := (1 - r ^ 2) / (1 + r ^ 2)
def imagPart (r : ℚ) : ℚ := (2 * r) / (1 + r ^ 2)
def alpha (r : ℚ) : ℂ := (realPart r : ℂ) + (imagPart r : ℂ) * Complex.I

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

/-- The angle is specified directly; no global logarithm branch is selected. -/
theorem exp_two_arctan (r : ℚ) :
    Complex.exp (Complex.I * ((2 * Real.arctan (r : ℝ) : ℝ) : ℂ)) = alpha r := by
  rw [mul_comm Complex.I, Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, cos_two_arctan, sin_two_arctan]
  simp [alpha, realPart, imagPart]

theorem alpha_ne_zero (r : ℚ) : alpha r ≠ 0 := by
  rw [← exp_two_arctan]
  exact Complex.exp_ne_zero _

theorem coordinates_norm_one (r : ℚ) : realPart r ^ 2 + imagPart r ^ 2 = 1 := by
  have hd : 1 + r ^ 2 ≠ 0 := by positivity
  unfold realPart imagPart
  field_simp
  ring

theorem alpha_no_root (r : ℚ) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hrm1 : r ≠ -1)
    (n : ℕ) (hn : 0 < n) : alpha r ^ n ≠ 1 := by
  intro hroot
  have hd : 1 + r ^ 2 ≠ 0 := by positivity
  rcases gaussian_rational_root_coordinates (realPart r) (imagPart r)
    (coordinates_norm_one r) n hn hroot with h | h | h | h
  · have hh := (div_eq_iff hd).mp h.1
    have hz : r ^ 2 = 0 := by nlinarith
    exact hr0 (sq_eq_zero_iff.mp hz)
  · have hh := (div_eq_iff hd).mp h.1
    linarith
  · have hh := (div_eq_zero_iff).mp h.1
    have hs : r ^ 2 = 1 := by rcases hh with hh | hh; linarith; exact (hd hh).elim
    rcases sq_eq_one_iff.mp hs with hh | hh
    · exact hr1 hh
    · exact hrm1 hh
  · have hh := (div_eq_zero_iff).mp h.1
    have hs : r ^ 2 = 1 := by rcases hh with hh | hh; linarith; exact (hd hh).elim
    rcases sq_eq_one_iff.mp hs with hh | hh
    · exact hr1 hh
    · exact hrm1 hh

theorem alpha_powers_injective (r : ℚ) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hrm1 : r ≠ -1) :
    Function.Injective (fun n : ℕ => alpha r ^ n) :=
  powers_injective_of_no_root (alpha_ne_zero r) (alpha_no_root r hr0 hr1 hrm1)

def numerator (r : ℚ) : GaussianInt :=
  ⟨(realPart r).num * ((imagPart r).den : ℤ),
    (imagPart r).num * ((realPart r).den : ℤ)⟩

def denominator (r : ℚ) : ℕ := (realPart r).den * (imagPart r).den

theorem denominator_pos (r : ℚ) : 0 < denominator r :=
  Nat.mul_pos (realPart r).pos (imagPart r).pos

theorem numerator_div_denominator (r : ℚ) :
    (numerator r : ℂ) / (denominator r : ℂ) = alpha r := by
  have ha : ((realPart r).den : ℂ) ≠ 0 := by exact_mod_cast (realPart r).pos.ne'
  have hb : ((imagPart r).den : ℂ) ≠ 0 := by exact_mod_cast (imagPart r).pos.ne'
  simp only [numerator, denominator, alpha, GaussianInt.toComplex_def',
    Int.cast_mul, Int.cast_natCast, Nat.cast_mul, Rat.cast_def]
  field_simp

def arctanPeriod (r : ℚ) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hrm1 : r ≠ -1) : PeriodData where
  num := numerator r
  den := denominator r
  den_pos := denominator_pos r
  angle := 2 * Real.arctan (r : ℝ)
  angle_ne_zero := by
    apply mul_ne_zero (by norm_num)
    simpa using (show (r : ℝ) ≠ 0 by exact_mod_cast hr0)
  exp_angle := by rw [numerator_div_denominator, exp_two_arctan]
  powers_injective := by
    simp only [numerator_div_denominator]
    exact alpha_powers_injective r hr0 hr1 hrm1

end
end OAI.Arctangent
