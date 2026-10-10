import OAI.NumberTheory.PiExponent.Approximation.Arithmetic

namespace OAI.Quadratic
noncomputable section

/-- Arithmetic and bounded-slope data only; no determinant or approximation premise. -/
structure Context where
  radicand : ℤ
  generator : ℂ
  generator_sq : generator * generator = (radicand : ℂ)
  no_int_square : ∀ n : ℤ, n * n ≠ radicand
  bound : ℝ
  one_le_bound : 1 ≤ bound
  norm_generator_le : ‖generator‖ ≤ bound

theorem Context.bound_pos (f : Context) : 0 < f.bound := zero_lt_one.trans_le f.one_le_bound

abbrev RealInt (f : Context) := Zsqrtd f.radicand
def rotation (f : Context) (s : Bool) : ℂ := if s then -f.generator else f.generator

theorem rotation_sq (f : Context) (s : Bool) : rotation f s * rotation f s = (f.radicand : ℂ) := by
  cases s <;> simp [rotation, f.generator_sq]

@[simp] theorem rotation_not (f : Context) (s : Bool) : rotation f (!s) = -rotation f s := by
  cases s <;> simp [rotation]

theorem norm_rotation (f : Context) (s : Bool) : ‖rotation f s‖ = ‖f.generator‖ := by
  cases s <;> simp [rotation]

variable {f : Context}
namespace RealInt

def embedding (s : Bool) : RealInt f →+* ℂ := Zsqrtd.lift ⟨rotation f s, rotation_sq f s⟩

theorem embedding_def (s : Bool) (z : RealInt f) :
    embedding s z = (z.re : ℂ) + (z.im : ℂ) * rotation f s := rfl

theorem embedding_injective (s : Bool) : Function.Injective (embedding (f := f) s) := by
  apply Zsqrtd.lift_injective
  exact fun n hn => f.no_int_square n hn.symm

theorem norm_eq_product (s : Bool) (z : RealInt f) :
    (z.norm : ℂ) = embedding s z * embedding (!s) z := by
  simp only [Zsqrtd.norm_def, Int.cast_sub, Int.cast_mul, embedding_def, rotation_not]
  calc
    _ = (z.re : ℂ) * z.re - (z.im : ℂ) * z.im * (rotation f s * rotation f s) := by
      rw [rotation_sq]
      ring
    _ = _ := by ring

theorem norm_ne_zero {z : RealInt f} (hz : z ≠ 0) : z.norm ≠ 0 := by
  intro h
  have hp := norm_eq_product false z
  rw [h, Int.cast_zero] at hp
  rcases mul_eq_zero.mp hp.symm with h | h
  · exact hz (embedding_injective false (by simpa using h))
  · exact hz (embedding_injective true (by simpa using h))

theorem one_le_norm_product (s : Bool) {z : RealInt f} (hz : z ≠ 0) :
    1 ≤ ‖embedding s z‖ * ‖embedding (!s) z‖ := by
  have hi : (1 : ℤ) ≤ |z.norm| := Int.one_le_abs (norm_ne_zero hz)
  have hr : (1 : ℝ) ≤ |(z.norm : ℝ)| := by exact_mod_cast hi
  have h := congrArg norm (norm_eq_product s z)
  simp only [norm_mul, Complex.norm_intCast] at h
  exact hr.trans_eq h

end RealInt
end
end OAI.Quadratic
