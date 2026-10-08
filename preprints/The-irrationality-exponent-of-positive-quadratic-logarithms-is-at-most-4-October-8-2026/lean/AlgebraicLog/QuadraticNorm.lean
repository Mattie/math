import Mathlib.NumberTheory.NumberField.House
import Mathlib.Tactic

/-!+# A norm lower bound for one fixed algebraic determinant

These lemmas use the genuine number-field norm of an algebraic integer.
The quadratic specialization records the exact coefficient two on the
logarithm of a rational clearing factor. The distinguished embedding and
the other embeddings always evaluate the same element.
-/

namespace OAI.AlgebraicLog.QuadraticNorm

noncomputable section
open scoped BigOperators NumberField

variable {K : Type*} [Field K] [NumberField K]

local instance : DecidableEq (K →ₐ[ℚ] ℂ) := Classical.decEq _

/-- The product runs over all embeddings, with complex conjugates counted
separately. Integrality is in `K`, so no auxiliary field degree is introduced. -/
theorem one_le_prod_norm_embeddings {z : K} (hz : z ≠ 0)
    (hint : IsIntegral ℤ z) :
    1 ≤ ∏ σ : K →ₐ[ℚ] ℂ, ‖σ z‖ := by
  classical
  let zi : 𝓞 K := ⟨z, hint⟩
  have hzi : zi ≠ 0 := by
    intro he
    apply hz
    exact congrArg (fun x : 𝓞 K => (x : K)) he
  have hn : (1 : ℝ) ≤ |(Algebra.norm ℚ z : ℝ)| := by
    rw [show z = (zi : K) from rfl, ← Algebra.coe_norm_int]
    rw [Rat.cast_intCast, ← Int.cast_abs, ← Int.cast_one, Int.cast_le]
    exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr hzi)
  have he := congrArg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ z)
  rw [norm_prod] at he
  have hncast : ‖algebraMap ℚ ℂ (Algebra.norm ℚ z)‖ =
      |(Algebra.norm ℚ z : ℝ)| := by
    rw [eq_ratCast, Complex.norm_ratCast]
  rw [hncast] at he
  exact he ▸ hn

/-- A positive rational scalar clearing `delta` is repeated once per field
embedding. In particular inverse rational row factors are retained. -/
theorem clearing_norm_product_bound (C : ℚ) (hC : 0 < C) {delta : K}
    (hdelta : delta ≠ 0)
    (hint : IsIntegral ℤ ((C : K) * delta)) :
    1 ≤ (C : ℝ) ^ Module.finrank ℚ K *
      ∏ σ : K →ₐ[ℚ] ℂ, ‖σ delta‖ := by
  classical
  have hCK : (C : K) ≠ 0 := by exact_mod_cast hC.ne'
  have h := one_le_prod_norm_embeddings (mul_ne_zero hCK hdelta) hint
  have hnormC : ‖(C : ℂ)‖ = (C : ℝ) := by
    rw [Complex.norm_ratCast,
      abs_of_pos (show (0 : ℝ) < C by exact_mod_cast hC)]
  simp only [map_mul, map_ratCast, norm_mul, hnormC,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at h
  simpa using h

/-- Logarithmic form with the distinguished embedding separated explicitly. -/
theorem clearing_log_bound (C : ℚ) (hC : 0 < C) {delta : K}
    (hdelta : delta ≠ 0)
    (hint : IsIntegral ℤ ((C : K) * delta)) (σ₀ : K →ₐ[ℚ] ℂ) :
    -(Module.finrank ℚ K : ℝ) * Real.log (C : ℝ) -
      ∑ σ ∈ Finset.univ.erase σ₀, Real.log ‖σ delta‖ ≤
        Real.log ‖σ₀ delta‖ := by
  classical
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hemb (σ : K →ₐ[ℚ] ℂ) : 0 < ‖σ delta‖ :=
    norm_pos_iff.mpr ((map_ne_zero σ).mpr hdelta)
  have hp : 0 < ∏ σ : K →ₐ[ℚ] ℂ, ‖σ delta‖ :=
    Finset.prod_pos (fun σ _ => hemb σ)
  have h := Real.log_nonneg (clearing_norm_product_bound C hC hdelta hint)
  rw [Real.log_mul (pow_pos hCpos _).ne' hp.ne', Real.log_pow,
    Real.log_prod (fun σ _ => (hemb σ).ne')] at h
  have hs := Finset.sum_erase_add (s := (Finset.univ : Finset (K →ₐ[ℚ] ℂ)))
    (f := fun σ => Real.log ‖σ delta‖) (Finset.mem_univ σ₀)
  linarith

/-- Actual degree-two norm inequality; there is no supplied norm-bound premise. -/
theorem quadratic_clearing_log_bound (hdegree : Module.finrank ℚ K = 2)
    (C : ℚ) (hC : 0 < C) {delta : K} (hdelta : delta ≠ 0)
    (hint : IsIntegral ℤ ((C : K) * delta)) (σ₀ : K →ₐ[ℚ] ℂ) :
    -2 * Real.log (C : ℝ) -
      ∑ σ ∈ Finset.univ.erase σ₀, Real.log ‖σ delta‖ ≤
        Real.log ‖σ₀ delta‖ := by
  simpa only [hdegree, Nat.cast_ofNat] using clearing_log_bound C hC hdelta hint σ₀

/-- This explicit matrix corollary guarantees the same minor is evaluated at
every embedding: mapping the determinant commutes with taking the determinant. -/
theorem quadratic_cleared_minor_log_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hdegree : Module.finrank ℚ K = 2) (A : Matrix ι ι K)
    (C : ℚ) (hC : 0 < C) (hdet : A.det ≠ 0)
    (hint : IsIntegral ℤ ((C : K) * A.det)) (σ₀ : K →ₐ[ℚ] ℂ) :
    -2 * Real.log (C : ℝ) -
      ∑ σ ∈ Finset.univ.erase σ₀, Real.log ‖(A.map σ.toRingHom).det‖ ≤
        Real.log ‖(A.map σ₀.toRingHom).det‖ := by
  have h := quadratic_clearing_log_bound hdegree C hC hdet hint σ₀
  have hmap (σ : K →ₐ[ℚ] ℂ) : (A.map σ.toRingHom).det = σ A.det :=
    (RingHom.map_det σ.toRingHom A).symm
  simp_rw [hmap]
  exact h

/-- Version for literal complex minors identified as the images of one integral
matrix after a common positive rational scaling. The image relation is an
equality, not a supplied lower-bound assumption. -/
theorem quadratic_literal_minor_log_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hdegree : Module.finrank ℚ K = 2) (B : Matrix ι ι K)
    (hB : IsIntegral ℤ B.det) (hdet : B.det ≠ 0)
    (A : (K →ₐ[ℚ] ℂ) → Matrix ι ι ℂ) (C : ℚ) (hC : 0 < C)
    (himage : ∀ σ : K →ₐ[ℚ] ℂ, σ B.det = (C : ℂ) * (A σ).det)
    (σ₀ : K →ₐ[ℚ] ℂ) :
    -2 * Real.log (C : ℝ) -
      ∑ σ ∈ Finset.univ.erase σ₀, Real.log ‖(A σ).det‖ ≤
        Real.log ‖(A σ₀).det‖ := by
  classical
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hnormC : ‖(C : ℂ)‖ = (C : ℝ) := by
    rw [Complex.norm_ratCast, abs_of_pos hCpos]
  have hnonzero (σ : K →ₐ[ℚ] ℂ) : (A σ).det ≠ 0 := by
    have hn : σ B.det ≠ 0 := (map_ne_zero σ).mpr hdet
    rw [himage σ] at hn
    exact (mul_ne_zero_iff.mp hn).2
  have hemb (σ : K →ₐ[ℚ] ℂ) : 0 < ‖σ B.det‖ :=
    norm_pos_iff.mpr ((map_ne_zero σ).mpr hdet)
  have hn := Real.log_nonneg (one_le_prod_norm_embeddings hdet hB)
  rw [Real.log_prod (fun σ _ => (hemb σ).ne')] at hn
  simp_rw [himage, norm_mul, hnormC,
    Real.log_mul hCpos.ne' (norm_ne_zero_iff.mpr (hnonzero _))] at hn
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hn
  have hcard : Fintype.card (K →ₐ[ℚ] ℂ) = 2 := by simpa using hdegree
  rw [hcard] at hn
  have hs := Finset.sum_erase_add (s := (Finset.univ : Finset (K →ₐ[ℚ] ℂ)))
    (f := fun σ => Real.log ‖(A σ).det‖) (Finset.mem_univ σ₀)
  norm_num only [Nat.cast_ofNat] at hn
  linarith

end
end OAI.AlgebraicLog.QuadraticNorm
