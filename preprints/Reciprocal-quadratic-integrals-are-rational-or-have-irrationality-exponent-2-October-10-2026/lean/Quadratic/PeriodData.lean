import Logarithm.ScaledArithmetic
import Logarithm.ApproximationGeometry
import Quadratic.Order

namespace OAI.Quadratic
variable {f : Context}
noncomputable section

/-- The two exponential identities specify compatible logarithms at both real
embeddings. They are arithmetic input conditions, not determinant hypotheses. -/
structure PeriodData (f : Context) where
  num : (RealInt f)
  den : ℕ
  den_pos : 0 < den
  angle : ℝ
  angle_ne_zero : angle ≠ 0
  exp_angles : ∀ s : Bool,
    Complex.exp ((rotation f) s * (angle : ℂ)) = RealInt.embedding s num / (den : ℂ)
  powers_injective : ∀ s : Bool,
    Function.Injective (fun n : ℕ => (RealInt.embedding s num / (den : ℂ)) ^ n)
  sign : Bool

namespace PeriodData

def slope (b : (PeriodData f)) : ℂ := (rotation f) b.sign
def value (b : (PeriodData f)) : ℂ := RealInt.embedding b.sign b.num / (b.den : ℂ)
def omega (b : (PeriodData f)) : ℂ := b.slope * (b.angle : ℂ)
def radius (b : (PeriodData f)) : ℝ := 100 * max 1 (f.bound * |b.angle|)
def flip (b : (PeriodData f)) : (PeriodData f) := { b with sign := !b.sign }

@[simp] theorem flip_flip (b : (PeriodData f)) : b.flip.flip = b := by
  cases b
  simp [flip]

theorem value_ne_zero (b : (PeriodData f)) : b.value ≠ 0 := by
  rw [value, ← b.exp_angles]
  exact Complex.exp_ne_zero _

theorem norm_omega (b : (PeriodData f)) : ‖b.omega‖ = ‖f.generator‖ * |b.angle| := by
  simp [omega, slope, norm_rotation, Complex.norm_real, Real.norm_eq_abs]

theorem exp_nat_mul (b : (PeriodData f)) (j : ℕ) :
    Complex.exp ((j : ℂ) * b.omega) = b.value ^ j := by
  rw [Complex.exp_nat_mul, omega, slope, b.exp_angles]
  rfl

theorem radius_large (b : (PeriodData f)) : 100 ≤ b.radius := by
  unfold radius
  nlinarith [le_max_left (1 : ℝ) (f.bound * |b.angle|)]

theorem radius_covers_target (b : (PeriodData f)) : 100 * |b.angle| ≤ b.radius := by
  unfold radius
  nlinarith [le_max_right (1 : ℝ) (f.bound * |b.angle|), abs_nonneg b.angle, mul_le_mul_of_nonneg_right f.one_le_bound (abs_nonneg b.angle)]

theorem radius_covers_omega (b : (PeriodData f)) : 100 * ‖b.omega‖ ≤ b.radius := by
  rw [norm_omega]
  have hs : ‖f.generator‖ ≤ f.bound := f.norm_generator_le
  unfold radius
  nlinarith [le_max_right (1 : ℝ) (f.bound * |b.angle|),
    mul_le_mul_of_nonneg_right hs (abs_nonneg b.angle)]

end PeriodData
end
end OAI.Quadratic
