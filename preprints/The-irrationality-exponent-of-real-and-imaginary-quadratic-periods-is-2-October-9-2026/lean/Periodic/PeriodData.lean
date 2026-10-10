import Logarithm.ScaledArithmetic
import Logarithm.ApproximationGeometry
import Imaginary.Arithmetic

open OAI.Imaginary

namespace OAI.Periodic
noncomputable section

/-- A nonzero unwrapped real angle whose imaginary quadratic exponential is one.
The concrete period is discharged in `Periodic.Main`. -/
structure PeriodData where
  num : ImaginaryInt
  den : ℕ
  den_pos : 0 < den
  angle : ℝ
  angle_ne_zero : angle ≠ 0
  exp_angle : Complex.exp (Imaginary.rotation * (angle : ℂ)) = (num : ℂ) / (den : ℂ)
  value_eq_one : (num : ℂ) / (den : ℂ) = 1

namespace PeriodData

def value (b : PeriodData) : ℂ := (b.num : ℂ) / (b.den : ℂ)
def omega (b : PeriodData) : ℂ := Imaginary.rotation * (b.angle : ℂ)
def radius (b : PeriodData) : ℝ := 100 * max 1 (2 * |b.angle|)

theorem value_ne_zero (b : PeriodData) : b.value ≠ 0 := by
  rw [value, ← b.exp_angle]
  exact Complex.exp_ne_zero _

theorem norm_omega (b : PeriodData) : ‖b.omega‖ = Real.sqrt 2 * |b.angle| := by
  simp [omega, Imaginary.rotation, Complex.norm_real, Real.norm_eq_abs, Real.sqrt_nonneg]

theorem exp_nat_mul (b : PeriodData) (j : ℕ) :
    Complex.exp ((j : ℂ) * b.omega) = b.value ^ j := by
  rw [Complex.exp_nat_mul, omega, b.exp_angle]
  rfl

theorem radius_large (b : PeriodData) : 100 ≤ b.radius := by
  unfold radius
  nlinarith [le_max_left (1 : ℝ) (2 * |b.angle|)]

theorem radius_covers_target (b : PeriodData) : 100 * |b.angle| ≤ b.radius := by
  unfold radius
  nlinarith [le_max_right (1 : ℝ) (2 * |b.angle|), abs_nonneg b.angle]

theorem radius_covers_omega (b : PeriodData) : 100 * ‖b.omega‖ ≤ b.radius := by
  rw [norm_omega]
  have hs : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  unfold radius
  nlinarith [le_max_right (1 : ℝ) (2 * |b.angle|),
    mul_le_mul_of_nonneg_right hs (abs_nonneg b.angle)]

end PeriodData
end
end OAI.Periodic
