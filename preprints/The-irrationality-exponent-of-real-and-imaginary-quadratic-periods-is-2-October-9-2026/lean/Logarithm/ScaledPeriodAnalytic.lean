import OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic
import Logarithm.RationalCenters

namespace OAI
noncomputable section
namespace Logarithm.ScaledPeriodAnalytic
open scoped BigOperators
open PiExponent PiExponent.PeriodAnalytic PiExponent.AnalyticCollision

/-- Multiplying the local Y monomial by its center value removes the period-one
restriction in the exponential-column identity. -/
theorem scaled_periodFunction_eq_exponentialMonomial (b center : ℂ) (h d : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    periodFunction (b * Complex.exp center ^ h) center h d z =
      exponentialMonomial b (h : ℂ) d (center + Complex.log (1 + z)) := by
  have hz0 : 1 + z ≠ 0 := by
    intro heq
    have heq' : z = -1 := by linear_combination heq
    simp [heq'] at hz
  unfold periodFunction exponentialMonomial
  rw [Complex.exp_nat_mul, Complex.exp_add, Complex.exp_log hz0, mul_pow]
  ring

theorem scaled_periodSeries (b center : ℂ) (h d : ℕ) :
    periodSeries (b * Complex.exp center ^ h) center h d =
      PowerSeries.C (Complex.exp center ^ h) * periodSeries b center h d := by
  unfold periodSeries
  rw [map_mul]
  ring

theorem rowTest_exponentialMonomial_eq_scaled_coeff
    (b center : ℂ) (h d ell : ℕ) :
    rowTest ell (fun t => exponentialMonomial b (h : ℂ) d
      (center + Complex.log (1 + t))) =
      Complex.exp center ^ h * PowerSeries.coeff ell (periodSeries b center h d) := by
  calc
    _ = rowTest ell (periodFunction (b * Complex.exp center ^ h) center h d) := by
      apply rowTest_congr_sphere
      intro t ht
      symm
      apply scaled_periodFunction_eq_exponentialMonomial
      have hn : ‖t‖ = (1 / 2 : ℝ) := by
        simpa only [Metric.mem_sphere, dist_zero_right] using ht
      rw [hn]
      norm_num
    _ = _ := by
      rw [rowTest_periodFunction_eq_coeff, scaled_periodSeries, PowerSeries.coeff_C_mul]

theorem scaled_periodMonomial_coeff_eq_rowTest {m : ℕ}
    (omega : ℂ) (j h ell : ℕ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    Complex.exp ((j : ℂ) * omega) ^ h *
      PowerSeries.coeff ell ((MatrixTranslation.periodMonomial j omega h a).coeff A) =
      rowTest ell (fun t => columnFunction h a A
        ((j : ℂ) * omega + Complex.log (1 + t))) := by
  rw [columnFunction, rowTest_exponentialMonomial_eq_scaled_coeff,
    MatrixTranslation.periodMonomial_coeff]
  simp only [periodSeries, MatrixTranslation.periodCoordinate, map_natCast]

/-- At the logarithm of a positive rational base the new matrix factor is a^(j*h). -/
theorem rational_scaled_periodMonomial_coeff_eq_rowTest {m : ℕ}
    (base : ℚ) (hbase : 0 < base) (j h ell : ℕ)
    (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    (base : ℂ) ^ (j * h) *
      PowerSeries.coeff ell ((MatrixTranslation.periodMonomial j
        (Real.log (base : ℝ) : ℂ) h a).coeff A) =
      rowTest ell (fun t => columnFunction h a A
        ((j : ℂ) * (Real.log (base : ℝ) : ℂ) + Complex.log (1 + t))) := by
  simpa only [exp_log_rational_center base hbase j, ← pow_mul] using
    scaled_periodMonomial_coeff_eq_rowTest (Real.log (base : ℝ) : ℂ) j h ell a A

end Logarithm.ScaledPeriodAnalytic
end
end OAI
