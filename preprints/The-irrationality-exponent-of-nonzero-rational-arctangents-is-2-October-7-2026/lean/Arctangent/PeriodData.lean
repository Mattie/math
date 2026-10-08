import Logarithm.ScaledArithmetic
import Logarithm.ApproximationGeometry

namespace OAI.Arctangent
noncomputable section

/-- A Gaussian rational exponential with a specified nonzero real angle.
The hypotheses are discharged for the arctangent endpoints below. -/
structure PeriodData where
  num : GaussianInt
  den : ℕ
  den_pos : 0 < den
  angle : ℝ
  angle_ne_zero : angle ≠ 0
  exp_angle : Complex.exp (Complex.I * (angle : ℂ)) = (num : ℂ) / (den : ℂ)
  powers_injective : Function.Injective (fun n : ℕ => ((num : ℂ) / (den : ℂ)) ^ n)

namespace PeriodData

def value (b : PeriodData) : ℂ := (b.num : ℂ) / (b.den : ℂ)
def omega (b : PeriodData) : ℂ := Complex.I * (b.angle : ℂ)
def radius (b : PeriodData) : ℝ := 100 * max 1 |b.angle|

theorem value_ne_zero (b : PeriodData) : b.value ≠ 0 := by
  rw [value, ← b.exp_angle]
  exact Complex.exp_ne_zero _

theorem norm_omega (b : PeriodData) : ‖b.omega‖ = |b.angle| := by
  simp [omega, Complex.norm_real, Real.norm_eq_abs]

theorem exp_nat_mul (b : PeriodData) (j : ℕ) :
    Complex.exp ((j : ℂ) * b.omega) = b.value ^ j := by
  rw [Complex.exp_nat_mul, omega, b.exp_angle]
  rfl

theorem radius_large (b : PeriodData) : 100 ≤ b.radius := by
  unfold radius
  nlinarith [le_max_left (1 : ℝ) |b.angle|]

theorem radius_covers_target (b : PeriodData) : 100 * |b.angle| ≤ b.radius := by
  unfold radius
  nlinarith [le_max_right (1 : ℝ) |b.angle|]

end PeriodData
end
end OAI.Arctangent
