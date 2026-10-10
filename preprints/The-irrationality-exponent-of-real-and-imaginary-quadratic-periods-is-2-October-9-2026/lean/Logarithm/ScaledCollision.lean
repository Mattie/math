import Logarithm.ScaledPeriodAnalytic
import OAI.NumberTheory.PiExponent.Analysis.Collision

namespace OAI
noncomputable section
namespace Logarithm.ScaledCollision
open scoped BigOperators
open PiExponent

theorem center_radius_bound (omega : ℂ) {rho : ℝ} {K j : ℕ}
    (hrho : 100 ≤ rho) (homega : 100 * ‖omega‖ ≤ rho)
    (hK : 0 < K) (hj : j < K) :
    ‖(j : ℂ) * omega‖ + 3 / 4 ≤ (rho * (K : ℝ)) / 2 := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hjK : (j : ℝ) ≤ K := by exact_mod_cast hj.le
  have hn : ‖(j : ℂ) * omega‖ = (j : ℝ) * ‖omega‖ := by simp
  rw [hn]
  have hp := mul_le_mul_of_nonneg_right hjK (norm_nonneg omega)
  have hr := mul_le_mul_of_nonneg_right homega (Nat.cast_nonneg K)
  have hlarge := mul_le_mul_of_nonneg_right hrho (Nat.cast_nonneg K)
  nlinarith

/-- The collision saving persists at arbitrary logarithmic centers, with the
explicit radius cost rho*K. The matrix includes the necessary exp(j*omega)^h. -/
theorem formal_scaled_collision_bound
    {m : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (omega : ℂ) (rho : ℝ) (hrho : 100 ≤ rho) (homega : 100 * ‖omega‖ ≤ rho)
    (group : ι → κ) (transverse : κ → Fin m →₀ ℕ)
    (j ell h : ι → ℕ) (a : ι → Fin m → ℕ) (w : Fin m → ℝ)
    {K : ℕ} {H w0 v0 wstar : ℝ}
    (hK : 0 < K) (hH : 0 < H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i) (hj : ∀ r, j r < K)
    (hcol : ∀ c, w0 * h c + ∑ i, w i * a c i ≤ H)
    (hell : ((∑ r, ell r : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v0) :
    ‖Matrix.det (fun r c => Complex.exp ((j r : ℂ) * omega) ^ h c *
      PowerSeries.coeff (ell r)
        ((MatrixTranslation.periodMonomial (j r) omega (h c) (a c)).coeff
          (transverse (group r))))‖ ≤
      Real.exp (-(Real.log 2 / 4) *
        (∑ A, (Collision.multiplicity Finset.univ group A : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H *
          (rho * K / w0 + Real.log 2 / v0 +
            (Real.log (200 * K) + Real.log (rho / 100)) / wstar +
            Collision.collisionRemainder (Fintype.card ι) H)) := by
  have hrho0 : 0 < rho := by linarith
  let R : NNReal := ⟨rho * (K : ℝ), by positivity⟩
  have hR : 0 < R := by change (0 : ℝ) < rho * K; positivity
  have hR1 : (1 : ℝ) ≤ R := by
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    change (1 : ℝ) ≤ rho * K
    nlinarith
  have hb := AnalyticCollision.translated_row_determinant_exp_bound
    group (fun A c => PeriodAnalytic.columnFunction (h c) (a c) (transverse A))
    (fun r => (j r : ℂ) * omega) ell R hR hH
    (fun A c => PeriodAnalytic.differentiable_columnFunction _ _ _)
    (A := (R : ℝ) / w0 + Real.log (2 * (R : ℝ)) / wstar) (v := v0)
    (fun A c z hz => PeriodAnalytic.norm_columnFunction_le (h c) (a c) (transverse A) w
      hR1 hH.le hw0 hws hw (hcol c)
      (by simpa only [Metric.mem_sphere, dist_zero_right] using hz.le))
    (fun r => center_radius_bound omega hrho homega hK (hj r)) hell
  have hRv : (R : ℝ) = rho * K := rfl
  rw [hRv] at hb
  have hlog : Real.log (2 * (rho * (K : ℝ))) =
      Real.log (200 * K) + Real.log (rho / 100) := by
    rw [← Real.log_mul (by positivity : (200 * (K : ℝ)) ≠ 0)
      (by positivity : rho / 100 ≠ 0)]
    congr 1
    ring
  rw [hlog] at hb
  simp_rw [ScaledPeriodAnalytic.scaled_periodMonomial_coeff_eq_rowTest]
  convert! hb using 1
  congr 1
  ring

end Logarithm.ScaledCollision
end
end OAI
