import OAI.NumberTheory.PiExponent.Approximation.Arithmetic

namespace OAI.PeriodicFamily
noncomputable section

abbrev Integral (rad : ℕ) := Zsqrtd (-(rad : ℤ))

def rotation (rad : ℕ) : ℂ := Complex.I * (Real.sqrt rad : ℂ)
def slopeBound (rad : ℕ) : ℝ := max 2 (Real.sqrt rad)
def slopeCost (rad : ℕ) : ℝ := Real.log (slopeBound rad)

theorem slopeBound_two_le (rad : ℕ) : 2 ≤ slopeBound rad := le_max_left _ _
theorem sqrt_le_slopeBound (rad : ℕ) : Real.sqrt rad ≤ slopeBound rad := le_max_right _ _
theorem slopeBound_pos (rad : ℕ) : 0 < slopeBound rad :=
  lt_of_lt_of_le (by norm_num) (slopeBound_two_le rad)
theorem slopeCost_nonneg (rad : ℕ) : 0 ≤ slopeCost rad :=
  Real.log_nonneg ((by norm_num : (1 : ℝ) ≤ 2).trans (slopeBound_two_le rad))

theorem norm_rotation (rad : ℕ) : ‖rotation rad‖ = Real.sqrt rad := by
  simp [rotation, Complex.norm_real, Real.norm_eq_abs, Real.sqrt_nonneg]

theorem norm_rotation_le (rad : ℕ) : ‖rotation rad‖ ≤ slopeBound rad := by
  rw [norm_rotation]
  exact sqrt_le_slopeBound rad

theorem rotation_sq (rad : ℕ) : rotation rad * rotation rad = (-(rad : ℤ) : ℤ) := by
  have hs : (Real.sqrt rad : ℂ) * (Real.sqrt rad : ℂ) = rad := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg rad : (0 : ℝ) ≤ rad)
  calc
    _ = (Complex.I * Complex.I) * ((Real.sqrt rad : ℂ) * (Real.sqrt rad : ℂ)) := by
      unfold rotation
      ring
    _ = _ := by rw [Complex.I_mul_I, hs]; simp

theorem rotation_ne_zero {rad : ℕ} [Fact (0 < rad)] : rotation rad ≠ 0 := by
  have hp : (0 : ℝ) < rad := by exact_mod_cast (Fact.out : 0 < rad)
  unfold rotation
  exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr hp).ne')

namespace Integral
variable {rad : ℕ}

def toComplex : Integral rad →+* ℂ := Zsqrtd.lift ⟨rotation rad, rotation_sq rad⟩
instance : CoeOut (Integral rad) ℂ := ⟨toComplex (rad := rad)⟩

theorem toComplex_def' (z : Integral rad) :
    (z : ℂ) = (z.re : ℂ) + (z.im : ℂ) * rotation rad := rfl

@[simp] theorem coe_natCast (n : ℕ) : ((n : Integral rad) : ℂ) = n :=
  map_natCast (toComplex (rad := rad)) n
@[simp] theorem coe_intCast (n : ℤ) : ((n : Integral rad) : ℂ) = n :=
  map_intCast (toComplex (rad := rad)) n
@[simp] theorem coe_mul (a b : Integral rad) : ((a * b : Integral rad) : ℂ) = (a : ℂ) * b :=
  (toComplex (rad := rad)).map_mul a b
@[simp] theorem coe_pow (a : Integral rad) (n : ℕ) : ((a ^ n : Integral rad) : ℂ) = (a : ℂ) ^ n :=
  (toComplex (rad := rad)).map_pow a n

theorem intCast_real_norm (z : Integral rad) :
    (z.norm : ℝ) = Complex.normSq (z : ℂ) := by
  have hs := Real.mul_self_sqrt (Nat.cast_nonneg rad : (0 : ℝ) ≤ rad)
  have hh := congrArg (fun t : ℝ => (z.im : ℝ) * (z.im : ℝ) * t) hs
  simp [Zsqrtd.norm_def, toComplex_def', rotation, Complex.normSq_apply]
  nlinarith only [hh]

theorem norm_pos [Fact (0 < rad)] {z : Integral rad} (hz : z ≠ 0) : 0 < z.norm := by
  have hn : (-(rad : ℤ)) ≤ 0 := neg_nonpos.mpr (Int.natCast_nonneg rad)
  have hp : (-(rad : ℤ)) < 0 := neg_neg_of_pos (by exact_mod_cast (Fact.out : 0 < rad))
  have hnonneg := Zsqrtd.norm_nonneg hn z
  have he := Zsqrtd.norm_eq_zero_iff hp z
  exact lt_of_le_of_ne hnonneg (Ne.symm (fun h => hz (he.mp h)))

theorem toComplex_injective [Fact (0 < rad)] : Function.Injective (toComplex (rad := rad)) := by
  apply Zsqrtd.lift_injective
  intro n hn
  have hp : (0 : ℤ) < rad := by exact_mod_cast (Fact.out : 0 < rad)
  nlinarith [sq_nonneg n]

end Integral
end
end OAI.PeriodicFamily
