import KernelEndToEnd
import WindowGeometry

/-!
# Counting each translated prime once

Summing log primes window by window gives a lower bound on the logarithm
of the common divisor. The two facts needed here are that each window lies
in the divisor's prime set and that different windows are disjoint.
-/

namespace PrimeNumerator.WindowAggregate

open Finset Zeta2Blueprint Zeta2NextTwo

/-- Disjoint windows count each member of the product at most once. -/
theorem sum_log_le {ι : Type*} (S : Finset ι) (W : ι → Finset ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hsub : ∀ i ∈ S, W i ⊆ P)
    (hdisj : (S : Set ι).PairwiseDisjoint W) :
    (∑ i ∈ S, ∑ p ∈ W i, Real.log (p : ℝ)) ≤ Real.log ((∏ p ∈ P, p : ℕ) : ℝ) := by
  classical
  have hUnion : S.biUnion W ⊆ P := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := mem_biUnion.mp hp
    exact hsub i hi hpi
  rw [← sum_biUnion hdisj, Nat.cast_prod, Real.log_prod]
  · exact sum_le_sum_of_subset_of_nonneg hUnion fun p hp _ =>
      Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt (hP p hp))
  · intro p hp
    exact_mod_cast (hP p hp).ne'

private theorem sum_grid_le {α β : Type*} (I : Finset α) (J : Finset β)
    (W : α → β → Finset ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (hsub : ∀ i ∈ I, ∀ j ∈ J, W i j ⊆ P)
    (hdisj : ∀ a b : α × β, a ≠ b → Disjoint (W a.1 a.2) (W b.1 b.2)) :
    (∑ i ∈ I, ∑ j ∈ J, ∑ p ∈ W i j, Real.log (p : ℝ)) ≤
      Real.log ((∏ p ∈ P, p : ℕ) : ℝ) := by
  classical
  rw [← sum_product']
  apply sum_log_le (I ×ˢ J) (fun ij => W ij.1 ij.2) P hP
  · intro ij hij
    exact hsub ij.1 (mem_product.mp hij).1 ij.2 (mem_product.mp hij).2
  · intro a _ b _ hab
    exact hdisj a b hab

/-- All primes counted by the six windows over the first million translates
contribute distinct factors to the simultaneous divisor. -/
theorem sum_windows_le {N : ℕ} (hN : 50*1000001^2 ≤ N) :
    (∑ i ∈ range 1000000, ∑ j : Fin 6, ∑ p ∈ WindowGeometry.window N (i+1) j,
      Real.log (p : ℝ)) ≤ Real.log (KernelEndToEnd.translatedProduct N : ℝ) := by
  classical
  unfold KernelEndToEnd.translatedProduct
  apply sum_grid_le
  · intro p hp
    exact (mem_filter.mp hp).2.1.pos
  · intro i hi j _
    exact WindowGeometry.window_subset hN (mem_range.mp hi) j
  · intro a b hab
    exact WindowGeometry.window_disjoint N (i := a.1) (j := a.2) (k := b.1) (l := b.2) hab

#print axioms sum_windows_le

end PrimeNumerator.WindowAggregate
