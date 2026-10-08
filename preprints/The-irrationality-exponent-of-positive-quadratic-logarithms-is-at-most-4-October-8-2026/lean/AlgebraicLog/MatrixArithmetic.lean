import AlgebraicLog.IntegerClearing
import AlgebraicLog.QuadraticNorm

/-! Integral matrices whose images are the literal logarithmic jet minors.

The integer witnesses below come from rational-centre coefficient clearing.
The base belongs to the original number field throughout; every embedding
therefore evaluates the same integral matrix, including at negative conjugates.
-/

namespace OAI.AlgebraicLog.MatrixArithmetic

noncomputable section
open scoped BigOperators
open PiExponent

variable {F : Type*} [Field F] [NumberField F]

/-- Multiplying the base by one integer suffices to clear every power in a
column. The remaining exponent is nonnegative because `j ≤ K`. -/
theorem map_cleared_base_power (a : F) (d K j h : ℕ) (hj : j ≤ K)
    (σ : F →ₐ[ℚ] ℂ) :
    σ (((d : F) * a) ^ (j * h) * (d : F) ^ ((K - j) * h)) =
      (d : ℂ) ^ (K * h) * (σ a) ^ (j * h) := by
  have he : j * h + (K - j) * h = K * h := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hj]
  simp only [map_mul, map_pow, map_natCast, mul_pow]
  rw [mul_right_comm, ← pow_add, he]

/-- Entry-level identification of an integral lift at every embedding. -/
theorem exists_integral_entry_lift {m : ℕ}
    (a : F) (d K : ℕ) (ha : IsIntegral ℤ ((d : F) * a))
    (T q e : Fin m → ℕ) (p : Fin m → ℤ) (hq : ∀ i, q i ≠ 0)
    (j s h : ℕ) (β γ : Fin m → ℕ) (hj : j ≤ K) (hγ : ∀ i, γ i ≤ e i) :
    ∃ b : F, IsIntegral ℤ b ∧ ∀ σ : F →ₐ[ℚ] ℂ,
      σ b =
        ((∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) /
          (∏ i, (q i : ℂ) ^ β i)) *
        ((d : ℂ) ^ (K * h) * (∏ i, (q i : ℂ) ^ γ i)) *
        ((σ a) ^ (j * h) *
          InterpolationMatrix.entry (fun i => (p i : ℂ) / (q i : ℂ))
            (fun i => InterpolationMatrix.truncatedLog (T i)) j s β h γ) := by
  obtain ⟨n, hn⟩ := IntegerClearing.entry_truncatedLog_cleared_int
    T q e p hq j s h β γ hγ
  refine ⟨((d : F) * a) ^ (j * h) * (d : F) ^ ((K - j) * h) * (n : F), ?_, ?_⟩
  · exact ((ha.pow _).mul ((isIntegral_natCast d).pow _)).mul (isIntegral_intCast n)
  · intro σ
    rw [map_mul, map_intCast, map_cleared_base_power a d K j h hj σ]
    change (n : ℂ) = _ at hn
    rw [hn]
    ring

/-- An arbitrary fixed square minor has one integral lift. No new minor is
chosen when the embedding changes. -/
theorem exists_integral_minor_lift {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : F) (d K : ℕ) (ha : IsIntegral ℤ ((d : F) * a))
    (T q e : Fin m → ℕ) (p : Fin m → ℤ) (hq : ∀ i, q i ≠ 0)
    (j s : ι → ℕ) (β : ι → Fin m → ℕ)
    (h : ι → ℕ) (γ : ι → Fin m → ℕ)
    (hj : ∀ r, j r ≤ K) (hγ : ∀ c i, γ c i ≤ e i) :
    ∃ B : Matrix ι ι F, (∀ r c, IsIntegral ℤ (B r c)) ∧
      IsIntegral ℤ B.det ∧ ∀ σ : F →ₐ[ℚ] ℂ,
      B.map σ.toRingHom = fun r c =>
        ((∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) /
          (∏ i, (q i : ℂ) ^ β r i)) *
        ((d : ℂ) ^ (K * h c) * (∏ i, (q i : ℂ) ^ γ c i)) *
        ((σ a) ^ (j r * h c) *
          InterpolationMatrix.entry (fun i => (p i : ℂ) / (q i : ℂ))
            (fun i => InterpolationMatrix.truncatedLog (T i))
            (j r) (s r) (β r) (h c) (γ c)) := by
  choose B hB hmap using fun r c => exists_integral_entry_lift
    a d K ha T q e p hq (j r) (s r) (h c) (β r) (γ c) (hj r) (hγ c)
  exact ⟨B, hB, IsIntegral.det hB, fun σ => by ext r c; exact hmap r c σ⟩

/-- Determinant scaling retains the inverse denominator factor for every row.
This is a general identity, valid also when the matrix is singular. -/
theorem det_row_column_scale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (u v : ι → ℂ) :
    (Matrix.of (fun r c => u r * v c * A r c)).det =
      (∏ r, u r) * (∏ c, v c) * A.det := by
  have he : Matrix.of (fun r c => u r * v c * A r c) =
      Matrix.of (fun r c => u r * (v c * A r c)) := by
    ext r c
    simp only [Matrix.of_apply]
    ring
  rw [he]
  calc
    _ = (∏ r, u r) * (Matrix.of (fun r c => v c * A r c)).det := by
      exact Matrix.det_mul_column u (fun r c => v c * A r c)
    _ = _ := by rw [Matrix.det_mul_row v A]; ring

/-- The scalar in the determinant identity is explicitly rational and contains
all row denominator savings. This is the image relation used by the norm bound. -/
theorem exists_integral_minor_det_lift {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : F) (d K : ℕ) (ha : IsIntegral ℤ ((d : F) * a))
    (T q e : Fin m → ℕ) (p : Fin m → ℤ) (hq : ∀ i, q i ≠ 0)
    (j s : ι → ℕ) (β : ι → Fin m → ℕ)
    (h : ι → ℕ) (γ : ι → Fin m → ℕ)
    (hj : ∀ r, j r ≤ K) (hγ : ∀ c i, γ c i ≤ e i) :
    ∃ B : Matrix ι ι F, IsIntegral ℤ B.det ∧ ∀ σ : F →ₐ[ℚ] ℂ,
      σ B.det =
        (((∏ r, ((∏ i, (Nat.lcmUpto (T i) : ℚ) ^ e i) /
          (∏ i, (q i : ℚ) ^ β r i))) *
          (∏ c, (d : ℚ) ^ (K * h c) * (∏ i, (q i : ℚ) ^ γ c i)) : ℚ) : ℂ) *
        (Matrix.of (fun r c => (σ a) ^ (j r * h c) *
          InterpolationMatrix.entry (fun i => (p i : ℂ) / (q i : ℂ))
            (fun i => InterpolationMatrix.truncatedLog (T i))
            (j r) (s r) (β r) (h c) (γ c))).det := by
  obtain ⟨B, _, hB, hmap⟩ := exists_integral_minor_lift
    a d K ha T q e p hq j s β h γ hj hγ
  refine ⟨B, hB, fun σ => ?_⟩
  have hm : σ B.det = (B.map σ.toRingHom).det := RingHom.map_det σ.toRingHom B
  rw [hm, hmap σ]
  have hh := det_row_column_scale
    (fun r c => (σ a) ^ (j r * h c) *
      InterpolationMatrix.entry (fun i => (p i : ℂ) / (q i : ℂ))
        (fun i => InterpolationMatrix.truncatedLog (T i)) (j r) (s r) (β r) (h c) (γ c))
    (fun r => (∏ i, (Nat.lcmUpto (T i) : ℂ) ^ e i) / (∏ i, (q i : ℂ) ^ β r i))
    (fun c => (d : ℂ) ^ (K * h c) * (∏ i, (q i : ℂ) ^ γ c i))
  convert hh using 1 <;> push_cast <;> rfl

end
end OAI.AlgebraicLog.MatrixArithmetic
