import OAI.NumberTheory.PiExponent.Approximation.Parameters

/-! # The geometric parameter gap with a field-degree arithmetic cost

The shape parameters use the rescaled exponent `nu / degreeCost`. The actual
rational approximations must still have exponent `nu`. This module establishes
only the shape gap; conjugate and denominator errors must be paid separately.
-/

namespace OAI.AlgebraicLog.ParameterShape

open PiExponent

theorem exists_degree_shape (nu degreeCost : ℝ)
    (hdegree : 0 < degreeCost) (hnu : 2 * degreeCost < nu) :
    ∃ p : Parameters (nu / degreeCost),
      0 < nu * ((p.A : ℝ) * (1 - p.eta) - p.theta) -
        degreeCost * (1 - p.theta) := by
  have hscaled : 2 < nu / degreeCost := (lt_div_iff₀ hdegree).mpr hnu
  obtain ⟨p⟩ := exists_parameters (nu / degreeCost) hscaled
  refine ⟨p, ?_⟩
  have hgap := mul_pos hdegree p.gap_pos
  have hidentity :
      degreeCost * ((nu / degreeCost) * ((p.A : ℝ) * (1 - p.eta) - p.theta) -
        (1 - p.theta)) =
      nu * ((p.A : ℝ) * (1 - p.eta) - p.theta) - degreeCost * (1 - p.theta) := by
    field_simp
  rwa [hidentity] at hgap

/-- The weakest approximation gap occurs at the largest allowed row weight. -/
theorem row_gap_ge_shape_gap (nu degreeCost A eta theta b : ℝ)
    (hnu : degreeCost ≤ nu) (hb : b ≤ theta) :
    nu * (A * (1 - eta) - theta) - degreeCost * (1 - theta) ≤
      nu * (A * (1 - eta) - b) - degreeCost * (1 - b) := by
  have h := mul_nonneg (sub_nonneg.mpr hnu) (sub_nonneg.mpr hb)
  nlinarith only [h]

theorem exists_quadratic_shape (nu : ℝ) (hnu : 4 < nu) :
    ∃ p : Parameters (nu / 2),
      0 < nu * ((p.A : ℝ) * (1 - p.eta) - p.theta) - 2 * (1 - p.theta) := by
  exact exists_degree_shape nu 2 (by norm_num) (by nlinarith)

end OAI.AlgebraicLog.ParameterShape
