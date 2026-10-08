import AlgebraicLog.MatrixArithmetic

namespace OAI.AlgebraicLog.ArithmeticBounds

noncomputable section
open scoped BigOperators

def rowScale {m : ℕ} (T q e β : Fin m → ℕ) : ℚ :=
  (∏ i, (Nat.lcmUpto (T i) : ℚ) ^ e i) / (∏ i, (q i : ℚ) ^ β i)

def columnScale {m : ℕ} (d K h : ℕ) (q γ : Fin m → ℕ) : ℚ :=
  (d : ℚ) ^ (K * h) * ∏ i, (q i : ℚ) ^ γ i

def clearingScalar {m : ℕ} {ι : Type*} [Fintype ι]
    (d K : ℕ) (T q e : Fin m → ℕ) (β : ι → Fin m → ℕ)
    (h : ι → ℕ) (γ : ι → Fin m → ℕ) : ℚ :=
  (∏ r, rowScale T q e (β r)) * ∏ c, columnScale d K (h c) q (γ c)

theorem rowScale_pos {m : ℕ} (T q e β : Fin m → ℕ) (hq : ∀ i, 0 < q i) :
    0 < rowScale T q e β := by
  apply div_pos
  · exact Finset.prod_pos (fun i _ => pow_pos
      (by exact_mod_cast Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero (T i))) _)
  · exact Finset.prod_pos (fun i _ => pow_pos (by exact_mod_cast hq i) _)

theorem columnScale_pos {m : ℕ} (d K h : ℕ) (q γ : Fin m → ℕ)
    (hd : 0 < d) (hq : ∀ i, 0 < q i) : 0 < columnScale d K h q γ := by
  exact mul_pos (pow_pos (by exact_mod_cast hd) _)
    (Finset.prod_pos (fun i _ => pow_pos (by exact_mod_cast hq i) _))

theorem clearingScalar_pos {m : ℕ} {ι : Type*} [Fintype ι]
    (d K : ℕ) (T q e : Fin m → ℕ) (β : ι → Fin m → ℕ)
    (h : ι → ℕ) (γ : ι → Fin m → ℕ) (hd : 0 < d) (hq : ∀ i, 0 < q i) :
    0 < clearingScalar d K T q e β h γ :=
  mul_pos (Finset.prod_pos (fun r _ => rowScale_pos T q e (β r) hq))
    (Finset.prod_pos (fun c _ => columnScale_pos d K (h c) q (γ c) hd hq))

theorem log_clearingScalar {m : ℕ} {ι : Type*} [Fintype ι]
    (d K : ℕ) (T q e : Fin m → ℕ) (β : ι → Fin m → ℕ)
    (h : ι → ℕ) (γ : ι → Fin m → ℕ) (hd : 0 < d) (hq : ∀ i, 0 < q i) :
    Real.log (clearingScalar d K T q e β h γ : ℝ) =
      (Fintype.card ι : ℝ) * Real.log (∏ i, (Nat.lcmUpto (T i) : ℝ) ^ e i) +
      (∑ c, ((K : ℝ) * (h c : ℝ) * Real.log d + ∑ i, (γ c i : ℝ) * Real.log (q i))) -
      ∑ r, ∑ i, (β r i : ℝ) * Real.log (q i) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hqR : ∀ i, (0 : ℝ) < q i := fun i => by exact_mod_cast hq i
  have hL : ∀ i, (0 : ℝ) < Nat.lcmUpto (T i) := fun i => by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero (T i))
  have hr (r : ι) : (0 : ℝ) < rowScale T q e (β r) := by
    exact_mod_cast rowScale_pos T q e (β r) hq
  have hc (c : ι) : (0 : ℝ) < columnScale d K (h c) q (γ c) := by
    exact_mod_cast columnScale_pos d K (h c) q (γ c) hd hq
  rw [clearingScalar, Rat.cast_mul, Rat.cast_prod, Rat.cast_prod,
    Real.log_mul (Finset.prod_pos (fun r _ => hr r)).ne'
      (Finset.prod_pos (fun c _ => hc c)).ne',
    Real.log_prod (fun r _ => (hr r).ne'), Real.log_prod (fun c _ => (hc c).ne')]
  simp only [rowScale, columnScale, Rat.cast_div, Rat.cast_prod, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_mul]
  simp_rw [Real.log_div (Finset.prod_pos (fun i _ => pow_pos (hL i) _)).ne'
      (Finset.prod_pos (fun i _ => pow_pos (hqR i) _)).ne',
    Real.log_mul (pow_pos hdR _).ne'
      (Finset.prod_pos (fun i _ => pow_pos (hqR i) _)).ne',
    Real.log_prod (fun i _ => (pow_pos (hqR i) _).ne'), Real.log_pow]
  simp only [Nat.cast_mul, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

/-- Numerical normalization of the exact quadratic norm inequality. Both the
main denominator cost and the inverse row saving are multiplied by two. -/
theorem normalized_quadratic_bound
    (M H b E delta gamma logD column row conjugate logAbsDet U remainder : ℝ)
    (hM : 0 < M) (hH : 0 < H)
    (hclear : -2 * (M * logD + column - row) - conjugate ≤ logAbsDet)
    (hden : logD ≤ H * E)
    (hcol : column ≤ M * H * (1 + gamma))
    (hrow : M * H * b - M * H * delta ≤ row)
    (hconj : conjugate ≤ M * H * (U + remainder)) :
    -2 * (1 - b) - 2 * (E + delta + gamma) - U - remainder ≤
      logAbsDet / (M * H) := by
  apply (le_div_iff₀ (mul_pos hM hH)).mpr
  have hd := mul_le_mul_of_nonneg_left hden hM.le
  nlinarith only [hclear, hd, hcol, hrow, hconj]

end
end OAI.AlgebraicLog.ArithmeticBounds
