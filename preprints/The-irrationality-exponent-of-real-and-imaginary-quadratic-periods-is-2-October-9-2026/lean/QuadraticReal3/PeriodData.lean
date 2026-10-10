import Logarithm.ScaledArithmetic
import Logarithm.ApproximationGeometry
import QuadraticReal3.Order

namespace OAI.QuadraticReal3
noncomputable section

/-- The two exponential identities specify compatible logarithms at both real
embeddings. They are arithmetic input conditions, not determinant hypotheses. -/
structure PeriodData where
  num : RealInt
  den : ℕ
  den_pos : 0 < den
  angle : ℝ
  angle_ne_zero : angle ≠ 0
  exp_angles : ∀ s : Bool,
    Complex.exp (rotation s * (angle : ℂ)) = RealInt.embedding s num / (den : ℂ)
  powers_injective : ∀ s : Bool,
    Function.Injective (fun n : ℕ => (RealInt.embedding s num / (den : ℂ)) ^ n)
  sign : Bool

namespace PeriodData

def slope (b : PeriodData) : ℂ := rotation b.sign
def value (b : PeriodData) : ℂ := RealInt.embedding b.sign b.num / (b.den : ℂ)
def omega (b : PeriodData) : ℂ := b.slope * (b.angle : ℂ)
def radius (b : PeriodData) : ℝ := 100 * max 1 (2 * |b.angle|)
def flip (b : PeriodData) : PeriodData := { b with sign := !b.sign }

@[simp] theorem flip_flip (b : PeriodData) : b.flip.flip = b := by
  cases b
  simp [flip]

theorem value_ne_zero (b : PeriodData) : b.value ≠ 0 := by
  rw [value, ← b.exp_angles]
  exact Complex.exp_ne_zero _

theorem norm_omega (b : PeriodData) : ‖b.omega‖ = Real.sqrt 3 * |b.angle| := by
  simp [omega, slope, norm_rotation, Complex.norm_real, Real.norm_eq_abs]

theorem exp_nat_mul (b : PeriodData) (j : ℕ) :
    Complex.exp ((j : ℂ) * b.omega) = b.value ^ j := by
  rw [Complex.exp_nat_mul, omega, slope, b.exp_angles]
  rfl

theorem radius_large (b : PeriodData) : 100 ≤ b.radius := by
  unfold radius
  nlinarith [le_max_left (1 : ℝ) (2 * |b.angle|)]

theorem radius_covers_target (b : PeriodData) : 100 * |b.angle| ≤ b.radius := by
  unfold radius
  nlinarith [le_max_right (1 : ℝ) (2 * |b.angle|), abs_nonneg b.angle]

theorem radius_covers_omega (b : PeriodData) : 100 * ‖b.omega‖ ≤ b.radius := by
  rw [norm_omega]
  have hs : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 2]
  unfold radius
  nlinarith [le_max_right (1 : ℝ) (2 * |b.angle|),
    mul_le_mul_of_nonneg_right hs (abs_nonneg b.angle)]

end PeriodData
end
end OAI.QuadraticReal3
