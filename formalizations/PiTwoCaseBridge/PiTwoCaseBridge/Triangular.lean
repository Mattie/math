import OAI.NumberTheory.PiExponent.Jets.FilteredLength

/-!
# Finite triangular interpolation

If each coordinate has a lift correct through its weight, successive
corrections solve the whole finite packet in the same source module.
-/

namespace PiTwoCaseBridge

open scoped Classical

section

variable {K M Row : Type*} [Field K] [AddCommGroup M] [Module K M] [Fintype Row]

/-- The packet vanishes in every coordinate strictly below the given weight. -/
def packetFiltration (weight : Row → ℕ) (n : ℕ) : Submodule K (Row → K) where
  carrier := {v | ∀ r, weight r < n → v r = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy r hr
    change x r + y r = 0
    rw [hx r hr, hy r hr, add_zero]
  smul_mem' := by
    intro a x hx r hr
    change a * x r = 0
    rw [hx r hr, mul_zero]

/-- A basis lift correct through its own weight gives packet surjectivity.
The source module can already impose a single degree bound for all lifts. -/
theorem surjective_of_weight_triangular_lifts (weight : Row → ℕ)
    (f : M →ₗ[K] (Row → K)) (N : ℕ) (hN : ∀ r, weight r < N)
    (lift : Row → M)
    (hlift : ∀ r s, weight s ≤ weight r →
      f (lift r) s = if s = r then 1 else 0) :
    Function.Surjective f := by
  classical
  apply OAI.PiExponentJets.W24.surjective_of_finite_corrections f
    (packetFiltration weight) N
  · ext v
    simp [packetFiltration]
  · ext v
    simpa [packetFiltration, funext_iff] using
      (show (∀ r, weight r < N → v r = 0) ↔ ∀ r, v r = 0 from
        ⟨fun h r => h r (hN r), fun h r _ => h r⟩)
  · intro n _ v hv
    let layer := Finset.univ.filter fun r => weight r = n
    refine ⟨∑ r ∈ layer, v r • lift r, ?_⟩
    intro s hs
    have hsn : weight s ≤ n := by omega
    have term (r : Row) (hr : r ∈ layer) :
        f (v r • lift r) s = if s = r then v s else 0 := by
      have hrn : weight r = n := (Finset.mem_filter.mp hr).2
      rw [map_smul, Pi.smul_apply, hlift r s (hrn.symm ▸ hsn)]
      by_cases he : s = r <;> simp [he]
    change v s - f (∑ r ∈ layer, v r • lift r) s = 0
    rw [map_sum, Finset.sum_apply, Finset.sum_congr rfl term, Finset.sum_ite_eq]
    by_cases hm : s ∈ layer
    · simp [hm]
    · have hlt : weight s < n := by
        have hne : weight s ≠ n := by simpa [layer] using hm
        omega
      simp [hm, hv s hlt]

end

end PiTwoCaseBridge
