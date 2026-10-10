import Logarithm.ScaledArithmetic
import Logarithm.ApproximationGeometry
import PeriodicFamily.Arithmetic

namespace OAI.PeriodicFamily
noncomputable section
variable (rad : ℕ)

/-- A literal, nonzero unwrapped period of the integral imaginary generator. -/
structure PeriodData where
  num : Integral rad
  den : ℕ
  den_pos : 0 < den
  angle : ℝ
  angle_ne_zero : angle ≠ 0
  exp_angle : Complex.exp (rotation rad * (angle : ℂ)) = (num : ℂ) / (den : ℂ)
  value_eq_one : (num : ℂ) / (den : ℂ) = 1

namespace PeriodData
variable {rad}

def value (b : PeriodData rad) : ℂ := (b.num : ℂ) / (b.den : ℂ)
def omega (b : PeriodData rad) : ℂ := rotation rad * (b.angle : ℂ)
def radius (b : PeriodData rad) : ℝ := 100 * max 1 (slopeBound rad * |b.angle|)

theorem value_ne_zero (b : PeriodData rad) : b.value ≠ 0 := by
  rw [value, ← b.exp_angle]
  exact Complex.exp_ne_zero _

theorem norm_omega (b : PeriodData rad) : ‖b.omega‖ = Real.sqrt rad * |b.angle| := by
  simp [omega, norm_mul, norm_rotation, Complex.norm_real, Real.norm_eq_abs]

theorem exp_nat_mul (b : PeriodData rad) (j : ℕ) :
    Complex.exp ((j : ℂ) * b.omega) = b.value ^ j := by
  rw [Complex.exp_nat_mul, omega, b.exp_angle]
  rfl

theorem radius_large (b : PeriodData rad) : 100 ≤ b.radius := by
  unfold radius
  nlinarith [le_max_left (1 : ℝ) (slopeBound rad * |b.angle|)]

theorem radius_covers_target (b : PeriodData rad) : 100 * |b.angle| ≤ b.radius := by
  have hs := mul_le_mul_of_nonneg_right (slopeBound_two_le rad) (abs_nonneg b.angle)
  unfold radius
  nlinarith [le_max_right (1 : ℝ) (slopeBound rad * |b.angle|), abs_nonneg b.angle]

theorem radius_covers_omega (b : PeriodData rad) : 100 * ‖b.omega‖ ≤ b.radius := by
  rw [norm_omega]
  have hs := mul_le_mul_of_nonneg_right (sqrt_le_slopeBound rad) (abs_nonneg b.angle)
  unfold radius
  nlinarith [le_max_right (1 : ℝ) (slopeBound rad * |b.angle|)]

end PeriodData
end
end OAI.PeriodicFamily
