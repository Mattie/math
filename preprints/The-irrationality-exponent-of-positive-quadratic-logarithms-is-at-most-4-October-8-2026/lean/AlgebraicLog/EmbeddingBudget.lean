import Mathlib.NumberTheory.NumberField.House
import Mathlib.Tactic

namespace OAI.AlgebraicLog.EmbeddingBudget
noncomputable section
open scoped BigOperators NumberField
variable {F : Type*} [Field F] [NumberField F]
local instance : DecidableEq (F →ₐ[ℚ] ℂ) := Classical.decEq _

/-- A deliberately coarse fixed cost bounds every embedding, so no choice of
the other quadratic conjugate is needed in the parameter construction. -/
def embeddingCost (a : F) : ℝ :=
  ∑ σ : F →ₐ[ℚ] ℂ, Real.log (max 1 ‖σ a‖)

theorem embeddingCost_nonneg (a : F) : 0 ≤ embeddingCost a :=
  Finset.sum_nonneg (fun _ _ => Real.log_nonneg (le_max_left _ _))

theorem log_norm_le_embeddingCost (a : F) (σ : F →ₐ[ℚ] ℂ) :
    Real.log (max 1 ‖σ a‖) ≤ embeddingCost a := by
  unfold embeddingCost
  exact Finset.single_le_sum (f := fun τ : F →ₐ[ℚ] ℂ => Real.log (max 1 ‖τ a‖))
    (fun _ _ => Real.log_nonneg (le_max_left _ _))
    (Finset.mem_univ σ)

theorem quadratic_other_card (hdegree : Module.finrank ℚ F = 2) (σ₀ : F →ₐ[ℚ] ℂ) :
    (Finset.univ.erase σ₀ : Finset (F →ₐ[ℚ] ℂ)).card = 1 := by
  have hcard : Fintype.card (F →ₐ[ℚ] ℂ) = 2 := by simpa using hdegree
  simp [Finset.card_erase_of_mem (Finset.mem_univ σ₀), hcard]

/-- In degree two the sum over all embeddings except the distinguished one
contains exactly one term, so a uniform bound incurs its cost only once. -/
theorem quadratic_other_sum_le (hdegree : Module.finrank ℚ F = 2)
    (σ₀ : F →ₐ[ℚ] ℂ) (f : (F →ₐ[ℚ] ℂ) → ℝ) (B : ℝ)
    (h : ∀ σ ∈ Finset.univ.erase σ₀, f σ ≤ B) :
    ∑ σ ∈ Finset.univ.erase σ₀, f σ ≤ B := by
  have hh := Finset.sum_le_sum h
  simpa [Finset.sum_const, quadratic_other_card hdegree σ₀] using hh

end
end OAI.AlgebraicLog.EmbeddingBudget
