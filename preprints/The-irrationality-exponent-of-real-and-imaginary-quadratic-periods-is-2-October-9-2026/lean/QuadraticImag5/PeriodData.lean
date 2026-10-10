import Logarithm.ScaledArithmetic
import Logarithm.ApproximationGeometry
import QuadraticImag5.Arithmetic

namespace OAI.QuadraticImag5
noncomputable section

/-- An imaginary quadratic rational exponential with a specified normalized real angle.
The hypotheses are discharged for the arctangent endpoints below. -/
structure PeriodData where
  num : QuadraticImag5Int
  den : ℕ
  den_pos : 0 < den
  angle : ℝ
  angle_ne_zero : angle ≠ 0
  exp_angle : Complex.exp (rotation * (angle : ℂ)) = (num : ℂ) / (den : ℂ)
  powers_injective : Function.Injective (fun n : ℕ => ((num : ℂ) / (den : ℂ)) ^ n)

namespace PeriodData

def value (b : PeriodData) : ℂ := (b.num : ℂ) / (b.den : ℂ)
def omega (b : PeriodData) : ℂ := rotation * (b.angle : ℂ)
def radius (b : PeriodData) : ℝ := 100 * max 1 (3 * |b.angle|)

theorem value_ne_zero (b : PeriodData) : b.value ≠ 0 := by
  rw [value, ← b.exp_angle]
  exact Complex.exp_ne_zero _

theorem norm_omega (b : PeriodData) : ‖b.omega‖ = Real.sqrt 5 * |b.angle| := by
  simp [omega, rotation, Complex.norm_real, Real.norm_eq_abs, Real.sqrt_nonneg]

theorem exp_nat_mul (b : PeriodData) (j : ℕ) :
    Complex.exp ((j : ℂ) * b.omega) = b.value ^ j := by
  rw [Complex.exp_nat_mul, omega, b.exp_angle]
  rfl

theorem radius_large (b : PeriodData) : 100 ≤ b.radius := by
  unfold radius
  nlinarith [le_max_left (1 : ℝ) (3 * |b.angle|)]

theorem radius_covers_target (b : PeriodData) : 100 * |b.angle| ≤ b.radius := by
  unfold radius
  nlinarith [le_max_right (1 : ℝ) (3 * |b.angle|), abs_nonneg b.angle]

theorem radius_covers_omega (b : PeriodData) : 100 * ‖b.omega‖ ≤ b.radius := by
  rw [norm_omega]
  have hs : Real.sqrt 5 ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 2]
  unfold radius
  nlinarith [le_max_right (1 : ℝ) (3 * |b.angle|),
    mul_le_mul_of_nonneg_right hs (abs_nonneg b.angle)]

end PeriodData
end
end OAI.QuadraticImag5
