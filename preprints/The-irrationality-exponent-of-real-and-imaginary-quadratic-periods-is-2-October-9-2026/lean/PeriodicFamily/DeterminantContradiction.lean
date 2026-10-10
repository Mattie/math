import PeriodicFamily.GlobalMatrixInterpolation
import PeriodicFamily.AnalyticAggregate
import PeriodicFamily.Parameters
import Logarithm.ExponentConsequence

open OAI.PeriodicFamily

namespace OAI.PeriodicFamily.DeterminantContradiction
variable {rad : ℕ} [Fact (0 < rad)]
open Filter Logarithm PiExponent DeterminantData
open scoped Topology

theorem tendsto_collisionRate {base : PeriodData rad} {nu : ℝ} (d : FixedData base nu) :
    Tendsto (collisionRate d) atTop (𝓝 (collisionLimit d)) := by
  have hv : 0 < d.v0 := by exact_mod_cast d.v0_pos
  have ht : 0 < d.base.theta := by exact_mod_cast d.base.theta_pos
  have hA : 0 < d.base.A := by exact_mod_cast d.base.A_pos
  have hh := MatrixCounting.tendsto_collisionRatio d.K d.v0 d.base.theta d.base.A
    (finiteDenominators d) hv ht hA (finiteDenominators_two_le d)
    collisionConstant d.base.eta
  have he : collisionConstant * d.base.eta ^ 2 * (d.K : ℝ) *
      (d.base.theta : ℝ) ^ d.m /
      (((d.m : ℝ) + 1) * (d.v0 : ℝ) * (d.base.A : ℝ) ^ d.m) =
        collisionLimit d := by
    unfold collisionLimit
    ring
  rw [he] at hh
  exact hh

/-- The actual scaled arithmetic and analytic determinants contradict the
actual globally interpolating matrix; no auxiliary conclusion is assumed. -/
theorem no_fixed_data {base : PeriodData rad} {nu : ℝ}
    (hnu : 2 < nu) (d : FixedData base nu) : False := by
  classical
  let error := LiteralAnalytic.analyticRemainder d
  have herror := LiteralAnalytic.tendsto_analyticRemainder d
  have hsum : Tendsto (fun H : ℝ => d.arithmeticError + d.analyticError + error H)
      atTop (𝓝 (d.arithmeticError + d.analyticError + 0)) :=
    tendsto_const_nhds.add herror
  have hsmall : ∀ᶠ H : ℝ in atTop,
      d.arithmeticError + d.analyticError + error H <
        nu * ((d.base.A : ℝ) * (1 - d.base.eta) - d.base.theta) -
          (1 - d.base.theta) :=
    hsum.eventually (Iio_mem_nhds (by simpa using d.error_sum_lt_gap))
  have hdiff : Tendsto (fun H : ℝ =>
      collisionRate d H - (1 + d.arithmeticError + d.analyticError + error H))
      atTop (𝓝 (collisionLimit d - (1 + d.arithmeticError + d.analyticError + 0))) :=
    (tendsto_collisionRate d).sub (tendsto_const_nhds.add herror)
  have hlarge : ∀ᶠ H : ℝ in atTop,
      0 < collisionRate d H - (1 + d.arithmeticError + d.analyticError + error H) := by
    apply hdiff.eventually (Ioi_mem_nhds ?_)
    have hh := d.collision_exceeds_error_sum
    change 1 + d.arithmeticError + d.analyticError < collisionLimit d at hh
    linarith
  have hcontradiction : ∀ᶠ H : ℝ in atTop,
      Function.Surjective (actualMatrix d H).mulVecLin → False := by
    filter_upwards [hsmall, hlarge, eventually_gt_atTop (0 : ℝ)] with H hsmall hlarge hH
    intro hsurj
    obtain ⟨selection, _hselection, hdet⟩ :=
      InterpolationMatrix.exists_full_row_minor_of_surjective (actualMatrix d H) hsurj
    have hdet' : (actualMinor d H selection).det ≠ 0 := hdet
    have hlower := actual_minor_arithmetic_lower_bound d H hH selection hdet'
    have hb := actualMean_bounds d H hH
    have hupper := LiteralAnalytic.actual_minor_analytic_bound d
      (by linarith : 0 ≤ nu) hH selection hdet'
    exact determinant_bounds_inconsistent nu d.base.theta
      ((d.base.A : ℝ) * (1 - d.base.eta)) (actualMean d H)
      (d.arithmeticError - slopeCost rad / d.wstar) (d.analyticError + slopeCost rad / d.wstar) (error H) (collisionRate d H)
      (Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H))
      (by linarith) hb.1 hb.2 (by linarith) (by linarith) hlower hupper
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp hcontradiction
  obtain ⟨H, hLH, hsurj⟩ := GlobalMatrixInterpolation.cofinal_actualMatrix d L
  exact hL H hLH hsurj

theorem period_eventualLowerBound (base : PeriodData rad)
    : EventualLowerBound base.angle := by
  intro nu hnu
  by_contra h
  push Not at h
  have hbad : ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ,
      Q ≤ q ∧ |base.angle - (p : ℝ) / q| ≤ (q : ℝ) ^ (-nu) := by
    intro Q
    obtain ⟨p, q, hq, herr⟩ := h (max Q 2) (le_max_right _ _)
    exact ⟨p, q, (le_max_left _ _).trans hq, herr.le⟩
  obtain ⟨d⟩ := exists_period_parameters base nu (PeriodicFamily.Arithmetic.lcmConstant + slopeCost rad)
    collisionConstant hnu (add_pos_of_pos_of_nonneg PeriodicFamily.Arithmetic.lcmConstant_pos (slopeCost_nonneg rad)) collisionConstant_pos hbad
  exact no_fixed_data hnu d

end OAI.PeriodicFamily.DeterminantContradiction
