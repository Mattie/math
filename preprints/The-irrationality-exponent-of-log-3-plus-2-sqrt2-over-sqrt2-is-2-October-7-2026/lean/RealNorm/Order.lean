import OAI.NumberTheory.PiExponent.Approximation.Arithmetic

namespace OAI.RealNorm
noncomputable section

abbrev RealInt := Zsqrtd 2

def rotation (s : Bool) : ℂ := if s then -(Real.sqrt 2 : ℂ) else (Real.sqrt 2 : ℂ)

theorem rotation_sq (s : Bool) : rotation s * rotation s = (2 : ℤ) := by
  have h : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  cases s <;> simp [rotation, h]

@[simp] theorem rotation_not (s : Bool) : rotation (!s) = -rotation s := by
  cases s <;> simp [rotation]

theorem norm_rotation (s : Bool) : ‖rotation s‖ = Real.sqrt 2 := by
  cases s <;> simp [rotation, Complex.norm_real, Real.norm_eq_abs, Real.sqrt_nonneg]

namespace RealInt

def embedding (s : Bool) : RealInt →+* ℂ := Zsqrtd.lift ⟨rotation s, rotation_sq s⟩

theorem embedding_def (s : Bool) (z : RealInt) :
    embedding s z = (z.re : ℂ) + (z.im : ℂ) * rotation s := rfl

theorem embedding_injective (s : Bool) : Function.Injective (embedding s) := by
  apply Zsqrtd.lift_injective
  intro n hn
  have hlo : -1 ≤ n := by nlinarith [sq_nonneg (n + 1)]
  have hhi : n ≤ 1 := by nlinarith [sq_nonneg (n - 1)]
  interval_cases n <;> norm_num at hn

theorem norm_eq_product (s : Bool) (z : RealInt) :
    (z.norm : ℂ) = embedding s z * embedding (!s) z := by
  simp only [Zsqrtd.norm_def, Int.cast_sub, Int.cast_mul, Int.cast_ofNat,
    embedding_def, rotation_not]
  calc
    _ = (z.re : ℂ) * z.re - (z.im : ℂ) * z.im * (rotation s * rotation s) := by
      rw [rotation_sq]
      push_cast
      ring
    _ = _ := by ring

theorem norm_ne_zero {z : RealInt} (hz : z ≠ 0) : z.norm ≠ 0 := by
  intro h
  have hp := norm_eq_product false z
  rw [h, Int.cast_zero] at hp
  rcases mul_eq_zero.mp hp.symm with h | h
  · exact hz (embedding_injective false (by simpa using h))
  · exact hz (embedding_injective true (by simpa using h))

theorem one_le_norm_product (s : Bool) {z : RealInt} (hz : z ≠ 0) :
    1 ≤ ‖embedding s z‖ * ‖embedding (!s) z‖ := by
  have hi : (1 : ℤ) ≤ |z.norm| := Int.one_le_abs (norm_ne_zero hz)
  have hr : (1 : ℝ) ≤ |(z.norm : ℝ)| := by exact_mod_cast hi
  have h := congrArg norm (norm_eq_product s z)
  simp only [norm_mul, Complex.norm_intCast] at h
  exact hr.trans_eq h

end RealInt
end
end OAI.RealNorm
