import PairedAffine.ArithmeticClearing

namespace OAI.DenominatorAffine.Arithmetic
noncomputable section
open scoped BigOperators NumberField
open PiExponent PiExponent.InterpolationMatrix
variable {F : Type*} [Field F] [NumberField F]

/-- A fixed denominator clears the base without changing the analytic entry. -/
theorem exists_integral_entry_lift {m : ℕ}
    (a : F) (D K : ℕ) (ha : IsIntegral ℤ ((D : F) * a))
    (T q e : Fin m → ℕ) (z : Fin m → F) (hz : ∀ i, IsIntegral ℤ (z i))
    (hq : ∀ i, q i ≠ 0) (j s h : ℕ) (β γ : Fin m → ℕ)
    (hj : j ≤ K) (hγ : ∀ i, γ i ≤ e i) :
    ∃ b : F, IsIntegral ℤ b ∧ ∀ σ : F →ₐ[ℚ] ℂ,
      σ b =
        ((∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) /
          (∏ i, (q i : ℂ) ^ β i)) *
        ((D : ℂ) ^ (K * h) * ∏ i, (q i : ℂ) ^ γ i) *
        ((σ a) ^ (j * h) * entry (fun i => σ (z i) / (q i : ℂ))
          (fun i => truncatedLog (T i)) j s β h γ) := by
  obtain ⟨n, hn, hmap⟩ := PairedAffine.Arithmetic.exists_integral_entry_lift
    (1 : F) isIntegral_one T q e z hz hq j s h β γ hγ
  refine ⟨((D : F) * a) ^ (j * h) * (D : F) ^ ((K - j) * h) * n,
    ((ha.pow _).mul ((isIntegral_natCast D).pow _)).mul hn, ?_⟩
  intro σ
  rw [map_mul, AlgebraicLog.MatrixArithmetic.map_cleared_base_power a D K j h hj σ,
    hmap σ]
  simp only [map_one, one_pow, one_mul]
  ring

end
end OAI.DenominatorAffine.Arithmetic
