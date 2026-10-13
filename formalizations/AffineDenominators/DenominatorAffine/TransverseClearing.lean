import DenominatorAffine.ArithmeticClearing

namespace OAI.DenominatorAffine.Arithmetic
noncomputable section
open scoped BigOperators NumberField
open PiExponent PiExponent.InterpolationMatrix
variable {F : Type*} [Field F] [NumberField F]

/-- Fixed denominators for both the base and centre numerators, with the original centres. -/
theorem exists_denominator_entry_lift {m : ℕ}
    (a : F) (D N K : ℕ) (hN : 0 < N) (ha : IsIntegral ℤ ((D : F) * a))
    (T q e : Fin m → ℕ) (z : Fin m → F)
    (hz : ∀ i, IsIntegral ℤ ((N : F) * z i))
    (hq : ∀ i, q i ≠ 0) (j s h : ℕ) (β γ : Fin m → ℕ)
    (hj : j ≤ K) (hγ : ∀ i, γ i ≤ e i) :
    ∃ b : F, IsIntegral ℤ b ∧ ∀ σ : F →ₐ[ℚ] ℂ,
      σ b =
        ((∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) /
          (∏ i, (q i : ℂ) ^ β i)) *
        ((D : ℂ) ^ (K * h) * ((N : ℂ) ^ (∑ i, γ i) * ∏ i, (q i : ℂ) ^ γ i)) *
        ((σ a) ^ (j * h) * entry (fun i => σ (z i) / (q i : ℂ))
          (fun i => truncatedLog (T i)) j s β h γ) := by
  obtain ⟨b, hb, hmap⟩ := exists_integral_entry_lift a D K ha T
    (fun i => N * q i) e (fun i => (N : F) * z i) hz
    (fun i => mul_ne_zero hN.ne' (hq i)) j s h β γ hj hγ
  refine ⟨(N : F) ^ (∑ i, β i) * b,
    ((isIntegral_natCast N).pow _).mul hb, ?_⟩
  intro σ
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcentres (i : Fin m) : σ ((N : F) * z i) / (N * q i : ℕ) =
      σ (z i) / (q i : ℂ) := by
    simp only [map_mul, map_natCast, Nat.cast_mul]
    exact mul_div_mul_left _ _ hNC
  rw [map_mul, map_pow, map_natCast, hmap σ]
  simp_rw [hcentres, Nat.cast_mul, mul_pow, Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum]
  have hqprod : (∏ i, (q i : ℂ) ^ β i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (by exact_mod_cast hq i))
  have hNprod : (∏ i : Fin m, (N : ℂ) ^ β i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun _ _ => pow_ne_zero _ hNC)
  field_simp


end
end OAI.DenominatorAffine.Arithmetic
