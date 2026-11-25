import Zeta2FourTrajectoryMatrices.IrrationalityMeasure.blueprint_irr_criterion

/-!
# Transferring an irrationality bound from ζ(2) to π²

Euler's identity gives π² = 6ζ(2). Dividing a reduced rational approximation
by six increases its denominator by at most a factor of six. For each
exponent strictly above the bound, a small margin in the exponent absorbs
this constant for all sufficiently large denominators. This transfers the
unrestricted bound to π².
-/

open Zeta2Blueprint Filter

namespace PrimeNumerator.WindowPi

private theorem bounded_den_finite (x : ℝ) (B : ℕ) :
    {q : ℚ | q.den ≤ B ∧ |x - q| < 1}.Finite := by
  let S := {v : ℤ × ℕ | 0 < v.2 ∧ v.2 ≤ B ∧ |x - v.1 / v.2| < 1}
  have hs : S.Finite := Zeta2IrrCriterion.finite_of_bounds x S B (fun _ h ↦ h)
  refine (hs.image (fun v : ℤ × ℕ ↦ (v.1 : ℚ) / v.2)).subset ?_
  intro q hq
  refine ⟨(q.num, q.den), ⟨q.den_pos, hq.1, ?_⟩, Rat.num_div_den q⟩
  simpa only [← Rat.cast_def] using hq.2

private theorem scaled_den (q : ℚ) : (q / 6).den ≤ 6 * q.den := by
  rw [div_eq_mul_inv, Rat.mul_den]
  simpa only [show ((6 : ℚ)⁻¹).den = 6 from Rat.inv_ofNat_den 6, Nat.mul_comm q.den 6] using
    Nat.div_le_self (q.den * ((6 : ℚ)⁻¹).den) _

/-- Multiplication by six preserves the upper bound on the irrationality measure.
Dividing a reduced approximant by six increases its denominator by at most six.
The slack in the exponent absorbs that fixed factor at large denominators. -/
theorem six_mul_bound {α μ : ℝ} (hμ : 0 ≤ μ) (h : IrrMeasureLE α μ) :
    IrrMeasureLE (6 * α) μ := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨B, hB⟩ := Filter.tendsto_atTop_atTop.mp
    ((tendsto_rpow_atTop hhalf).comp tendsto_natCast_atTop_atTop)
    ((6 : ℝ) ^ (μ + ε / 2))
  have small := bounded_den_finite (6 * α) B
  have large := (h (ε / 2) hhalf).image (fun r : ℚ ↦ 6*r)
  refine (small.union large).subset ?_
  intro q hq
  have hqpos : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hqone : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
  change |6 * α - (q : ℝ)| < (q.den : ℝ) ^ (-(μ + ε)) at hq
  by_cases hsmall : q.den ≤ B
  · exact Or.inl ⟨hsmall, hq.trans_le (Real.rpow_le_one_of_one_le_of_nonpos hqone (by linarith))⟩
  · refine Or.inr ⟨q/6, ?_, by ring⟩
    have hc : (6 : ℝ) ^ (μ + ε / 2) ≤ (q.den : ℝ) ^ (ε / 2) := hB q.den (by omega)
    have hd : (((q / 6).den : ℕ) : ℝ) ≤ 6 * q.den := by exact_mod_cast scaled_den q
    have hpow : (((q / 6).den : ℕ) : ℝ) ^ (μ + ε / 2) ≤ (q.den : ℝ) ^ (μ + ε) := calc
      _ ≤ (6 * (q.den : ℝ)) ^ (μ + ε / 2) :=
        Real.rpow_le_rpow (by positivity) hd (by linarith)
      _ = (6 : ℝ) ^ (μ + ε / 2) * (q.den : ℝ) ^ (μ + ε / 2) :=
        Real.mul_rpow (by norm_num) hqpos.le
      _ ≤ (q.den : ℝ) ^ (ε / 2) * (q.den : ℝ) ^ (μ + ε / 2) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by rw [← Real.rpow_add hqpos]; congr 1; ring
    change |α - ((q / 6 : ℚ) : ℝ)| < (((q / 6).den : ℕ) : ℝ) ^ (-(μ + ε / 2))
    calc
      _ = |6 * α - (q : ℝ)| / 6 := by
        push_cast
        rw [show α - (q : ℝ) / 6 = (6 * α - q) / 6 by ring, abs_div]
        norm_num
      _ ≤ |6 * α - (q : ℝ)| := by linarith [abs_nonneg (6 * α - (q : ℝ))]
      _ < (q.den : ℝ) ^ (-(μ + ε)) := hq
      _ ≤ _ := by
        rw [Real.rpow_neg hqpos.le, Real.rpow_neg (by positivity)]
        exact inv_anti₀ (by positivity) hpow

theorem pi_sq_eq_six_zeta2 : Real.pi ^ 2 = 6 * zeta2 := by
  unfold zeta2
  rw [riemannZeta_two]
  norm_num [← Complex.ofReal_pow, ← Complex.ofReal_div]
  ring

theorem pi_sq_bound {μ : ℝ} (hμ : 0 ≤ μ) (h : IrrMeasureLE zeta2 μ) :
    IrrMeasureLE (Real.pi ^ 2) μ :=
  by rw [pi_sq_eq_six_zeta2]; exact six_mul_bound hμ h

theorem measure_lt {α μ b : ℝ} (h : IrrMeasureLE α μ) (hb : μ < b) :
    irrationalityMeasure α < (b : EReal) := by
  have hle : irrationalityMeasure α ≤ (μ : EReal) :=
    iInf_le_of_le μ (iInf_le_of_le h le_rfl)
  exact hle.trans_lt (EReal.coe_lt_coe_iff.mpr hb)

theorem finite_lt {α μ b : ℝ} (h : IrrMeasureLE α μ) (hb : μ < b) :
    {q : ℚ | |α - q| < (q.den : ℝ) ^ (-b)}.Finite := by
  simpa only [show μ + (b - μ) = b by ring] using h (b - μ) (sub_pos.mpr hb)

#print axioms pi_sq_bound
#print axioms measure_lt
#print axioms finite_lt
end PrimeNumerator.WindowPi
