import Logarithm.ScaledMatrix
import OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic
import OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic

/-! Coarse coefficient bounds for the same minor at another embedding.

The estimates below require only a bound on the rational additive centres.
No exponential relation at the second embedding is assumed.
-/

namespace OAI.AlgebraicLog.ConjugateBound

noncomputable section
open scoped BigOperators Topology
open PiExponent PiExponent.AnalyticCollision

theorem hasSum_polynomial_coeff (P : Polynomial ℂ) (z : ℂ) :
    HasSum (fun n => P.coeff n * z ^ n) (P.eval z) := by
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (s := P.support) (f := fun n => P.coeff n * z ^ n) (by
      intro n hn
      simp only [Polynomial.mem_support_iff, not_not] at hn
      simp [hn])
  simpa only [Polynomial.eval_eq_sum, Polynomial.sum] using h

theorem hasFPowerSeriesAt_polynomial_coeff (P : Polynomial ℂ) :
    HasFPowerSeriesAt (fun z => P.eval z)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => P.coeff n)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  exact Filter.Eventually.of_forall (fun z => by
    simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul, mul_comm]
      using hasSum_polynomial_coeff P z)

theorem rowTest_polynomial_eq_coeff (P : Polynomial ℂ) (s : ℕ) :
    rowTest s (fun z => P.eval z) = P.coeff s := by
  have hd : DifferentiableOn ℂ (fun z => P.eval z) (Metric.closedBall 0 (1 / 2)) :=
    P.differentiable.differentiableOn
  have hp := hd.hasFPowerSeriesOnBall (R := (1 / 2 : NNReal)) (by norm_num)
  have he := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries
    (hasFPowerSeriesAt_polynomial_coeff P)
  have hh := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p s (fun _ => 1)) he
  simpa only [rowTest, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    Finset.prod_const_one, one_smul, FormalMultilinearSeries.coeff_ofScalars,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hh

theorem norm_polynomial_coeff_le {P : Polynomial ℂ} {B : ℝ}
    (hB : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2), ‖P.eval z‖ ≤ B) (s : ℕ) :
    ‖P.coeff s‖ ≤ (2 : ℝ) ^ s * B := by
  rw [← rowTest_polynomial_eq_coeff]
  exact norm_rowTest_le hB s

/-- A conservative bound uniform in the truncation order. The final parameter
selection absorbs its fixed constant, so no sharp logarithm estimate is needed. -/
theorem norm_truncatedLog_eval_le_two (T : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖(InterpolationMatrix.truncatedLog T).eval z‖ ≤ 2 := by
  change ‖(PowerSeries.trunc T (PowerSeries.log ℂ)).eval z‖ ≤ 2
  rw [LogTailAnalytic.eval_trunc_log]
  by_cases hT : T = 0
  · simp [hT, Complex.logTaylor_zero]
  have htail := LogTailAnalytic.norm_logTail_le_one T (Nat.one_le_iff_ne_zero.mpr hT) hz
  have hlog := Complex.norm_log_one_add_half_le_self hz
  have he : Complex.logTaylor T z =
      LogTailAnalytic.logTail T z + Complex.log (1 + z) := by
    unfold LogTailAnalytic.logTail
    ring
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

/-- Entry-level coarse bound. It is intentionally a little weaker than the
unit-polydisc estimate in the human proof, with `2*(K*R+2)` in place of `K*R+2`.
The only resulting change is a fixed logarithmic cost divided by `wstar`. -/
theorem norm_entry_truncatedLog_le {m : ℕ} (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j s h : ℕ) (β γ : Fin m → ℕ) {K : ℕ} {R : ℝ}
    (hR : 0 ≤ R) (hr : ∀ i, ‖r i‖ ≤ R) (hj : j ≤ K) :
    ‖InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i))
      j s β h γ‖ ≤
      (2 : ℝ) ^ s * (3 / 2 : ℝ) ^ h *
        (2 * ((K : ℝ) * R + 2)) ^ (∑ i, γ i) := by
  classical
  let B : ℝ := (K : ℝ) * R + 2
  have hB : 1 ≤ B := by
    have hKR : 0 ≤ (K : ℝ) * R := mul_nonneg (Nat.cast_nonneg _) hR
    dsimp [B]
    linarith
  let P : Polynomial ℂ := (1 + Polynomial.X) ^ h *
    ∏ i, (Polynomial.C ((j : ℂ) * r i) +
      InterpolationMatrix.truncatedLog (T i)) ^ (γ i - β i)
  have hP : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2),
      ‖P.eval z‖ ≤ (3 / 2 : ℝ) ^ h * B ^ (∑ i, γ i) := by
    intro z hz
    have hnz : ‖z‖ = (1 / 2 : ℝ) := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz
    have hf (i : Fin m) :
        ‖(Polynomial.C ((j : ℂ) * r i) +
          InterpolationMatrix.truncatedLog (T i)).eval z‖ ≤ B := by
      rw [Polynomial.eval_add, Polynomial.eval_C]
      apply (norm_add_le _ _).trans
      have hg := norm_truncatedLog_eval_le_two (T i) hnz.le
      have hjR : (j : ℝ) * R ≤ (K : ℝ) * R :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hR
      have hrr : ‖(j : ℂ) * r i‖ ≤ (j : ℝ) * R := by
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left (hr i) (Nat.cast_nonneg _)
      dsimp [B]
      linarith
    have hone : ‖(1 : ℂ) + z‖ ≤ (3 / 2 : ℝ) := by
      have ht := norm_add_le (1 : ℂ) z
      norm_num only [norm_one, hnz] at ht
      exact ht
    simp only [P, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_prod, norm_mul, norm_pow,
      norm_prod]
    apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hone h) ?_ (by positivity) (by positivity)
    calc
      _ ≤ ∏ i, B ^ (γ i - β i) :=
        Finset.prod_le_prod₀ (fun i _ => by positivity)
          (fun i _ => pow_le_pow_left₀ (norm_nonneg _)
            (by simpa only [Polynomial.eval_add] using hf i) _)
      _ = B ^ (∑ i, (γ i - β i)) := Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ B ^ (∑ i, γ i) :=
        pow_le_pow_right₀ hB (Finset.sum_le_sum (fun i _ => Nat.sub_le _ _))
  have hcoeff := norm_polynomial_coeff_le hP s
  have hchoose : ‖(∏ i, ((γ i).choose (β i) : ℂ))‖ ≤
      (2 : ℝ) ^ (∑ i, γ i) := by
    rw [norm_prod]
    calc
      _ ≤ ∏ i, (2 : ℝ) ^ γ i := by
        apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
        rw [Complex.norm_natCast]
        exact_mod_cast Nat.choose_le_two_pow (γ i) (β i)
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  rw [InterpolationMatrix.entry_eq_binomial_product, norm_mul]
  calc
    _ ≤ (2 : ℝ) ^ (∑ i, γ i) *
        ((2 : ℝ) ^ s * ((3 / 2 : ℝ) ^ h * B ^ (∑ i, γ i))) :=
      mul_le_mul hchoose hcoeff (norm_nonneg _) (by positivity)
    _ = _ := by dsimp [B]; rw [mul_pow]; ring

end
end OAI.AlgebraicLog.ConjugateBound
