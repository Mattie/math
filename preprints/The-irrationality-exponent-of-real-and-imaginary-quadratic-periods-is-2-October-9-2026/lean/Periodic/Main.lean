import Periodic.DeterminantContradiction
import Imaginary.Scaling

namespace OAI.Periodic
noncomputable section
open PiExponent

def scaledPiAngle : ℝ := 2 * Real.pi / Real.sqrt 2

theorem scaledPiAngle_ne_zero : scaledPiAngle ≠ 0 := by
  unfold scaledPiAngle
  positivity

theorem exp_scaledPiAngle :
    Complex.exp (Imaginary.rotation * (scaledPiAngle : ℂ)) = 1 := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have he : Imaginary.rotation * (scaledPiAngle : ℂ) = 2 * Real.pi * Complex.I := by
    unfold Imaginary.rotation scaledPiAngle
    push_cast
    field_simp
  rw [he, Complex.exp_two_pi_mul_I]

def scaledPiPeriod : PeriodData where
  num := 1
  den := 1
  den_pos := by norm_num
  angle := scaledPiAngle
  angle_ne_zero := scaledPiAngle_ne_zero
  exp_angle := by simpa using exp_scaledPiAngle
  value_eq_one := by simp

theorem scaled_pi_eventualLowerBound : EventualLowerBound (Real.pi / Real.sqrt 2) := by
  have hh := Imaginary.eventualLowerBound_div_nat
    (DeterminantContradiction.period_eventualLowerBound scaledPiPeriod) 2 (by norm_num)
  convert hh using 1
  simp only [scaledPiPeriod, scaledPiAngle, Nat.cast_ofNat]
  ring

/-- The exact target, with no arithmetic or interpolation premise. -/
theorem scaled_pi_irrationalityExponent_eq_two :
    irrationalityExponent (Real.pi / Real.sqrt 2) = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound scaled_pi_eventualLowerBound

theorem scaled_pi_explicit_bound (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤ |Real.pi / Real.sqrt 2 - (p : ℝ) / q| :=
  scaled_pi_eventualLowerBound nu hnu

theorem scaled_pi_integer_explicit_bound (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤ |Real.pi / Real.sqrt 2 - (p : ℝ) / (q : ℝ)| :=
  (eventualLowerBound_iff_integer _).mp scaled_pi_eventualLowerBound nu hnu

end
end OAI.Periodic
