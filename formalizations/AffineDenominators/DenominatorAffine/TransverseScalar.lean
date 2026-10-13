import DenominatorAffine.Arithmetic
import AlgebraicLog.ConjugateAggregate

namespace OAI.DenominatorAffine.Arithmetic
noncomputable section
open scoped BigOperators NumberField
open AlgebraicLog.LiteralAnalytic PairedAffine PiExponent Logarithm AlgebraicLog.DeterminantData
variable {proxy nu rho : ℝ} (d : FixedData proxy nu rho)

/-- The transverse clearing factor charges total degree, not dimension times total degree. -/
def transverseScalar (N : ℕ) (H : ℝ) (selection : Row d H → Column d H) : ℚ :=
  ∏ c, (N : ℚ) ^ (∑ i : Fin d.m, (selection c).val i.succ)

def denominatorScalar (D N : ℕ) (H : ℝ) (selection : Row d H → Column d H) : ℚ :=
  AlgebraicLog.SelectedArithmetic.selectedScalar d D H selection *
    transverseScalar d N H selection

theorem transverseScalar_pos (N : ℕ) (hN : 0 < N) (H : ℝ)
    (selection : Row d H → Column d H) : 0 < transverseScalar d N H selection := by
  exact Finset.prod_pos (fun _ _ => pow_pos (by exact_mod_cast hN) _)

theorem denominatorScalar_pos (D N : ℕ) (hD : 0 < D) (hN : 0 < N) (H : ℝ)
    (selection : Row d H → Column d H) : 0 < denominatorScalar d D N H selection :=
  mul_pos (AlgebraicLog.SelectedArithmetic.selectedScalar_pos d D hD H selection)
    (transverseScalar_pos d N hN H selection)

theorem log_transverseScalar_le (N : ℕ) (hN : 0 < N) (H : ℝ)
    (selection : Row d H → Column d H) :
    Real.log (transverseScalar d N H selection : ℝ) ≤
      (actualRowCount d H : ℝ) * H * (Real.log N / d.wstar) := by
  classical
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcol (c : Row d H) :
      (∑ i : Fin d.m, ((selection c).val i.succ : ℝ)) ≤ H / d.wstar := by
    have hc := InterpolationMatrix.column_weight_le d.w0_pos (fixedWeights_pos d) (selection c)
    have hw : 0 ≤ (d.w0 : ℝ) * ((selection c).val 0 : ℝ) := mul_nonneg d.w0_pos.le (Nat.cast_nonneg _)
    apply (le_div_iff₀ d.wstar_pos).mpr
    have hbound := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_right (fixedWeights_lower d i)
        (Nat.cast_nonneg ((selection c).val i.succ)))
    rw [← Finset.mul_sum] at hbound
    nlinarith
  simp only [transverseScalar, Rat.cast_prod, Rat.cast_pow, Rat.cast_natCast]
  rw [Real.log_prod (fun c _ => pow_ne_zero _ hNR)]
  simp only [Real.log_pow, Nat.cast_sum]
  calc
    _ ≤ ∑ _c : Row d H, (H / d.wstar) * Real.log N :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_right (hcol c)
        (Real.log_natCast_nonneg N))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, actualRowCount]
      ring

theorem log_denominatorScalar_le (D N : ℕ) (hD : 0 < D) (hN : 0 < N)
    (H : ℝ) (hH : 0 < H) (selection : Row d H → Column d H) :
    Real.log (denominatorScalar d D N H selection : ℝ) ≤
      (actualRowCount d H : ℝ) * H *
        (1 - actualMean d H +
          (AlgebraicLog.SelectedArithmetic.arithmeticError d D + Real.log N / d.wstar)) := by
  have hbase := log_selectedScalar_le d D hD H hH selection
  have htrans := log_transverseScalar_le d N hN H selection
  have hp : (0 : ℝ) < AlgebraicLog.SelectedArithmetic.selectedScalar d D H selection := by
    exact_mod_cast AlgebraicLog.SelectedArithmetic.selectedScalar_pos d D hD H selection
  have hq : (0 : ℝ) < transverseScalar d N H selection := by
    exact_mod_cast transverseScalar_pos d N hN H selection
  rw [denominatorScalar, Rat.cast_mul, Real.log_mul hp.ne' hq.ne']
  nlinarith

end
end OAI.DenominatorAffine.Arithmetic
