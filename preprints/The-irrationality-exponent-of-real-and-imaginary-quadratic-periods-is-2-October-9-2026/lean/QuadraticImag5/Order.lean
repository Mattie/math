import OAI.NumberTheory.PiExponent.Approximation.Arithmetic

namespace OAI.QuadraticImag5
noncomputable section

abbrev QuadraticImag5Int := Zsqrtd (-5)

def rotation : ℂ := Complex.I * (Real.sqrt 5 : ℂ)

theorem rotation_sq : rotation * rotation = (-5 : ℤ) := by
  have hs : (Real.sqrt 5 : ℂ) * (Real.sqrt 5 : ℂ) = 5 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  calc
    _ = (Complex.I * Complex.I) * ((Real.sqrt 5 : ℂ) * (Real.sqrt 5 : ℂ)) := by
      unfold rotation; ring
    _ = _ := by rw [Complex.I_mul_I, hs]; norm_num

namespace QuadraticImag5Int

def toComplex : QuadraticImag5Int →+* ℂ := Zsqrtd.lift ⟨rotation, rotation_sq⟩

instance : Coe QuadraticImag5Int ℂ := ⟨toComplex⟩

theorem toComplex_def' (z : QuadraticImag5Int) :
    (z : ℂ) = (z.re : ℂ) + (z.im : ℂ) * rotation := rfl

@[simp] theorem coe_natCast (n : ℕ) : ((n : QuadraticImag5Int) : ℂ) = n :=
  map_natCast toComplex n
@[simp] theorem coe_intCast (n : ℤ) : ((n : QuadraticImag5Int) : ℂ) = n :=
  map_intCast toComplex n
@[simp] theorem coe_mul (a b : QuadraticImag5Int) : ((a*b : QuadraticImag5Int) : ℂ) = (a : ℂ)*b :=
  toComplex.map_mul a b
@[simp] theorem coe_pow (a : QuadraticImag5Int) (n : ℕ) : ((a^n : QuadraticImag5Int) : ℂ) = (a : ℂ)^n :=
  toComplex.map_pow a n

theorem intCast_real_norm (z : QuadraticImag5Int) :
    (z.norm : ℝ) = Complex.normSq (z : ℂ) := by
  have hs := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  simp [Zsqrtd.norm_def, toComplex_def', rotation, Complex.normSq_apply]
  nlinarith

theorem norm_pos {z : QuadraticImag5Int} (hz : z ≠ 0) : 0 < z.norm := by
  have hn := Zsqrtd.norm_nonneg (by norm_num : (-5 : ℤ) ≤ 0) z
  have he := Zsqrtd.norm_eq_zero_iff (by norm_num : (-5 : ℤ) < 0) z
  exact lt_of_le_of_ne hn (Ne.symm (fun h => hz (he.mp h)))

theorem toComplex_injective : Function.Injective toComplex := by
  apply Zsqrtd.lift_injective
  intro n hn
  nlinarith [sq_nonneg n]

end QuadraticImag5Int
end
end OAI.QuadraticImag5
