import OAI.NumberTheory.PiExponent.Approximation.Arithmetic

namespace OAI.Imaginary
noncomputable section

abbrev ImaginaryInt := Zsqrtd (-2)

def rotation : ℂ := Complex.I * (Real.sqrt 2 : ℂ)

theorem rotation_sq : rotation * rotation = (-2 : ℤ) := by
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ = (Complex.I * Complex.I) * ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) := by
      unfold rotation; ring
    _ = _ := by rw [Complex.I_mul_I, hs]; norm_num

namespace ImaginaryInt

def toComplex : ImaginaryInt →+* ℂ := Zsqrtd.lift ⟨rotation, rotation_sq⟩

instance : Coe ImaginaryInt ℂ := ⟨toComplex⟩

theorem toComplex_def' (z : ImaginaryInt) :
    (z : ℂ) = (z.re : ℂ) + (z.im : ℂ) * rotation := rfl

@[simp] theorem coe_natCast (n : ℕ) : ((n : ImaginaryInt) : ℂ) = n :=
  map_natCast toComplex n
@[simp] theorem coe_intCast (n : ℤ) : ((n : ImaginaryInt) : ℂ) = n :=
  map_intCast toComplex n
@[simp] theorem coe_mul (a b : ImaginaryInt) : ((a*b : ImaginaryInt) : ℂ) = (a : ℂ)*b :=
  toComplex.map_mul a b
@[simp] theorem coe_pow (a : ImaginaryInt) (n : ℕ) : ((a^n : ImaginaryInt) : ℂ) = (a : ℂ)^n :=
  toComplex.map_pow a n

theorem intCast_real_norm (z : ImaginaryInt) :
    (z.norm : ℝ) = Complex.normSq (z : ℂ) := by
  have hs := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp [Zsqrtd.norm_def, toComplex_def', rotation, Complex.normSq_apply]
  nlinarith

theorem norm_pos {z : ImaginaryInt} (hz : z ≠ 0) : 0 < z.norm := by
  have hn := Zsqrtd.norm_nonneg (by norm_num : (-2 : ℤ) ≤ 0) z
  have he := Zsqrtd.norm_eq_zero_iff (by norm_num : (-2 : ℤ) < 0) z
  exact lt_of_le_of_ne hn (Ne.symm (fun h => hz (he.mp h)))

theorem toComplex_injective : Function.Injective toComplex := by
  apply Zsqrtd.lift_injective
  intro n hn
  nlinarith [sq_nonneg n]

end ImaginaryInt
end
end OAI.Imaginary
