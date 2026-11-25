import KernelEndToEnd

/-!
# Size and independence after division

Dividing by the common prime product reduces both the coefficient and the
linear-form error. The product is positive at each level, so division also
preserves the nonzero determinant needed in the three-level independence argument.
-/

open Finset Filter
namespace PrimeNumerator.KernelReduction
open KernelEndToEnd

theorem translatedProduct_pos (N : ℕ) : 0 < translatedProduct N := by
  unfold translatedProduct
  exact Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.1.pos

/-- The same positive divisor improves the coefficient height and the error. -/
theorem reduced_size {N : ℕ} {z : Fin 2 → ℤ} (hz : KernelContent.PublishedColumn N z) :
    ∃ w : Fin 2 → ℤ, (∀ i, z i = (translatedProduct N : ℤ) * w i) ∧
      |(w 1 : ℝ)| = |(z 1 : ℝ)| / translatedProduct N ∧
      ∀ α : ℝ, |(w 1 : ℝ)*α - w 0| = |(z 1 : ℝ)*α - z 0| / translatedProduct N := by
  obtain ⟨w, hw⟩ := published_column_factor hz
  have hp : (0 : ℝ) < translatedProduct N := by exact_mod_cast translatedProduct_pos N
  have cast (i : Fin 2) : (z i : ℝ) = (translatedProduct N : ℝ) * w i := by
    exact_mod_cast hw i
  refine ⟨w, hw, ?_, ?_⟩
  · rw [cast 1, abs_mul, abs_of_pos hp, mul_div_cancel_left₀ _ hp.ne']
  · intro α
    rw [cast 1, cast 0, mul_assoc, ← mul_sub, abs_mul, abs_of_pos hp,
      mul_div_cancel_left₀ _ hp.ne']

/-- Dividing each level separately preserves the same witness in the
three-consecutive-level independence hypothesis of the irrationality criterion. -/
theorem preserve_three_level_gap (z w : ℕ → Fin 2 → ℤ)
    (hw : ∀ n ≥ 1, ∀ i, z n i = (translatedProduct n : ℤ) * w n i)
    (old : ∀ᶠ N : ℕ in atTop, ∀ (a : ℤ) (b : ℕ), 0 < b →
      ∃ i : Fin 3, (b : ℤ)*z (N+i) 0-a*z (N+i) 1 ≠ 0) :
    ∀ᶠ N : ℕ in atTop, ∀ (a : ℤ) (b : ℕ), 0 < b →
      ∃ i : Fin 3, (b : ℤ)*w (N+i) 0-a*w (N+i) 1 ≠ 0 := by
  filter_upwards [old, eventually_ge_atTop 1] with N hold hN
  intro a b hb
  obtain ⟨i, hi⟩ := hold a b hb
  refine ⟨i, fun bad => hi ?_⟩
  rw [hw (N+i) (by omega) 0, hw (N+i) (by omega) 1]
  linear_combination (translatedProduct (N+i) : ℤ)*bad

#print axioms reduced_size
#print axioms preserve_three_level_gap
end PrimeNumerator.KernelReduction
