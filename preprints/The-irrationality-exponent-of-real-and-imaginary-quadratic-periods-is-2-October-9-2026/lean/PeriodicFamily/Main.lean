import PeriodicFamily.DeterminantContradiction
import Imaginary.Scaling

namespace OAI.PeriodicFamily
noncomputable section
open PiExponent

def natAngle (rad : ℕ) : ℝ := 2 * Real.pi / Real.sqrt rad

theorem natAngle_ne_zero (rad : ℕ) (hrad : 0 < rad) : natAngle rad ≠ 0 := by
  have hr : (0 : ℝ) < rad := by exact_mod_cast hrad
  exact (div_pos (mul_pos (by norm_num) Real.pi_pos) (Real.sqrt_pos.mpr hr)).ne'

theorem exp_natAngle (rad : ℕ) (hrad : 0 < rad) :
    Complex.exp (rotation rad * (natAngle rad : ℂ)) = 1 := by
  have hr : (0 : ℝ) < rad := by exact_mod_cast hrad
  have hs : (Real.sqrt rad : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hr).ne'
  have he : rotation rad * (natAngle rad : ℂ) = 2 * Real.pi * Complex.I := by
    unfold rotation natAngle
    push_cast
    field_simp <;> ring
  rw [he, Complex.exp_two_pi_mul_I]

def natPeriod (rad : ℕ) (hrad : 0 < rad) : PeriodData rad where
  num := 1
  den := 1
  den_pos := by norm_num
  angle := natAngle rad
  angle_ne_zero := natAngle_ne_zero rad hrad
  exp_angle := by simpa using exp_natAngle rad hrad
  value_eq_one := by simp

theorem nat_scaled_pi_eventualLowerBound (rad : ℕ) (hrad : 0 < rad) :
    EventualLowerBound (Real.pi / Real.sqrt rad) := by
  letI : Fact (0 < rad) := ⟨hrad⟩
  have hh := Imaginary.eventualLowerBound_div_nat
    (DeterminantContradiction.period_eventualLowerBound (natPeriod rad hrad)) 2 (by norm_num)
  convert hh using 1
  simp only [natPeriod, natAngle, Nat.cast_ofNat]
  ring

theorem nat_scaled_pi_irrationalityExponent_eq_two (rad : ℕ) (hrad : 0 < rad) :
    irrationalityExponent (Real.pi / Real.sqrt rad) = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    (nat_scaled_pi_eventualLowerBound rad hrad)

def rationalRadicand (r : ℚ) : ℕ := r.num.natAbs * r.den
def rationalAngle (r : ℚ) : ℝ := 2 * Real.pi / Real.sqrt (r : ℝ)

theorem rationalRadicand_pos (r : ℚ) (hr : 0 < r) : 0 < rationalRadicand r := by
  unfold rationalRadicand
  have hn : 0 < r.num := Rat.num_pos.mpr hr
  exact Nat.mul_pos (Int.natAbs_pos.mpr hn.ne') r.den_pos

theorem rationalRadicand_sqrt (r : ℚ) (hr : 0 < r) :
    Real.sqrt (rationalRadicand r : ℝ) = (r.den : ℝ) * Real.sqrt (r : ℝ) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hn : (r.num.natAbs : ℝ) = (r.num : ℝ) := by
    simpa only [Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ℝ)) (Int.natAbs_of_nonneg (Rat.num_pos.mpr hr).le)
  have hd : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hs : ((r.den : ℝ) * Real.sqrt (r : ℝ)) ^ 2 = (rationalRadicand r : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hrR.le]
    unfold rationalRadicand
    push_cast
    rw [hn, Rat.cast_def]
    field_simp <;> ring
  rw [← hs, Real.sqrt_sq_eq_abs, abs_of_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))]

theorem rationalAngle_ne_zero (r : ℚ) (hr : 0 < r) : rationalAngle r ≠ 0 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  exact (div_pos (mul_pos (by norm_num) Real.pi_pos) (Real.sqrt_pos.mpr hrR)).ne'

theorem exp_rationalAngle (r : ℚ) (hr : 0 < r) :
    Complex.exp (rotation (rationalRadicand r) * (rationalAngle r : ℂ)) = 1 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hn : (Real.sqrt (r : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hrR).ne'
  have hs : (Real.sqrt (rationalRadicand r : ℝ) : ℂ) =
      (r.den : ℂ) * (Real.sqrt (r : ℝ) : ℂ) := by
    exact_mod_cast rationalRadicand_sqrt r hr
  have he : rotation (rationalRadicand r) * (rationalAngle r : ℂ) =
      (r.den : ℂ) * (2 * Real.pi * Complex.I) := by
    unfold rotation rationalAngle
    push_cast
    rw [hs]
    field_simp <;> ring
  rw [he, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]

def rationalPeriod (r : ℚ) (hr : 0 < r) : PeriodData (rationalRadicand r) where
  num := 1
  den := 1
  den_pos := by norm_num
  angle := rationalAngle r
  angle_ne_zero := rationalAngle_ne_zero r hr
  exp_angle := by simpa using exp_rationalAngle r hr
  value_eq_one := by simp

/-- Every positive rational radicand, through its literal integer-order period. -/
theorem rational_scaled_pi_eventualLowerBound (r : ℚ) (hr : 0 < r) :
    EventualLowerBound (Real.pi / Real.sqrt (r : ℝ)) := by
  letI : Fact (0 < rationalRadicand r) := ⟨rationalRadicand_pos r hr⟩
  have hh := Imaginary.eventualLowerBound_div_nat
    (DeterminantContradiction.period_eventualLowerBound (rationalPeriod r hr)) 2 (by norm_num)
  convert hh using 1
  simp only [rationalPeriod, rationalAngle, Nat.cast_ofNat]
  ring

theorem rational_scaled_pi_irrationalityExponent_eq_two (r : ℚ) (hr : 0 < r) :
    irrationalityExponent (Real.pi / Real.sqrt (r : ℝ)) = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    (rational_scaled_pi_eventualLowerBound r hr)

theorem rational_scaled_pi_explicit_bound (r : ℚ) (hr : 0 < r)
    (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤ |Real.pi / Real.sqrt (r : ℝ) - (p : ℝ) / q| :=
  rational_scaled_pi_eventualLowerBound r hr nu hnu

theorem rational_scaled_pi_integer_explicit_bound (r : ℚ) (hr : 0 < r)
    (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤ |Real.pi / Real.sqrt (r : ℝ) - (p : ℝ) / (q : ℝ)| :=
  (eventualLowerBound_iff_integer _).mp (rational_scaled_pi_eventualLowerBound r hr) nu hnu

end
end OAI.PeriodicFamily
