import AlgebraicLog.ConjugateBound

namespace OAI.AlgebraicLog.ConjugateDeterminant

noncomputable section
open scoped BigOperators
open PiExponent

/-- The bound is uniform over all complex conjugate base values, including
negative real values. No logarithm of the conjugate is used. -/
theorem norm_base_entry_le {m : ℕ} (z : ℂ)
    (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j s h : ℕ) (β γ : Fin m → ℕ) {K : ℕ} {R : ℝ}
    (hR : 0 ≤ R) (hr : ∀ i, ‖r i‖ ≤ R) (hj : j ≤ K) :
    ‖z ^ (j * h) *
      InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i))
        j s β h γ‖ ≤
      (max 1 ‖z‖) ^ (K * h) *
        ((2 : ℝ) ^ s * (3 / 2 : ℝ) ^ h *
          (2 * ((K : ℝ) * R + 2)) ^ (∑ i, γ i)) := by
  rw [norm_mul, norm_pow]
  apply mul_le_mul _ (ConjugateBound.norm_entry_truncatedLog_le r T j s h β γ hR hr hj)
    (norm_nonneg _) (by positivity)
  exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
    (pow_le_pow_right₀ (le_max_left _ _) (Nat.mul_le_mul_right h hj))

/-- The exponential form exposes precisely the three entry costs that tend
to zero after division by the geometric weights. -/
theorem norm_base_entry_le_exp {m : ℕ} (z : ℂ)
    (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j s h : ℕ) (β γ : Fin m → ℕ) {K : ℕ} {R : ℝ}
    (hR : 0 ≤ R) (hr : ∀ i, ‖r i‖ ≤ R) (hj : j ≤ K) :
    ‖z ^ (j * h) *
      InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i))
        j s β h γ‖ ≤
      Real.exp ((s : ℝ) * Real.log 2 +
        (h : ℝ) * ((K : ℝ) * Real.log (max 1 ‖z‖) + Real.log (3 / 2)) +
        (∑ i, (γ i : ℝ)) * Real.log (2 * ((K : ℝ) * R + 2))) := by
  have hz : 0 < max 1 ‖z‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hc : 0 < 2 * ((K : ℝ) * R + 2) := by positivity
  have he : (s : ℝ) * Real.log 2 +
      (h : ℝ) * ((K : ℝ) * Real.log (max 1 ‖z‖) + Real.log (3 / 2)) +
      (∑ i, (γ i : ℝ)) * Real.log (2 * ((K : ℝ) * R + 2)) =
      ((K * h : ℕ) : ℝ) * Real.log (max 1 ‖z‖) +
      ((s : ℝ) * Real.log 2 + (h : ℝ) * Real.log (3 / 2) +
        ((∑ i, γ i : ℕ) : ℝ) * Real.log (2 * ((K : ℝ) * R + 2))) := by
    push_cast
    ring
  rw [he, Real.exp_add, Real.exp_add, Real.exp_add]
  simp only [Real.exp_nat_mul, Real.exp_log hz, Real.exp_log hc,
    Real.exp_log (by norm_num : (0 : ℝ) < 2),
    Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]
  exact norm_base_entry_le z r T j s h β γ hR hr hj

/-- Every selected square minor obeys the same conjugate bound. Its row and
column indices remain fixed while `z` varies between embeddings. -/
theorem norm_minor_le {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ℂ) (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j s : ι → ℕ) (β : ι → Fin m → ℕ)
    (h : ι → ℕ) (γ : ι → Fin m → ℕ) {K : ℕ} {R U H : ℝ}
    (hR : 0 ≤ R) (hr : ∀ i, ‖r i‖ ≤ R) (hj : ∀ row, j row ≤ K)
    (hcost : ∀ row col,
      (s row : ℝ) * Real.log 2 +
        (h col : ℝ) * ((K : ℝ) * Real.log (max 1 ‖z‖) + Real.log (3 / 2)) +
        (∑ i, (γ col i : ℝ)) * Real.log (2 * ((K : ℝ) * R + 2)) ≤ U * H) :
    ‖(Matrix.of (fun row col => z ^ (j row * h col) *
      InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i))
        (j row) (s row) (β row) (h col) (γ col))).det‖ ≤
      (Fintype.card ι).factorial * Real.exp (U * H * (Fintype.card ι : ℝ)) := by
  have he := AnalyticCollision.norm_det_le_factorial_mul_pow
    (Matrix.of (fun row col => z ^ (j row * h col) *
      InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i))
        (j row) (s row) (β row) (h col) (γ col)))
    (Real.exp_pos (U * H)).le (fun row col =>
      (norm_base_entry_le_exp z r T (j row) (s row) (h col) (β row) (γ col)
        hR hr (hj row)).trans (Real.exp_le_exp.mpr (hcost row col)))
  rw [← Real.exp_nat_mul] at he
  simpa only [mul_comm (Fintype.card ι : ℝ)] using he

end
end OAI.AlgebraicLog.ConjugateDeterminant
