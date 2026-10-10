import Logarithm.CurveInequalityIntrinsic

namespace OAI.Logarithm

open scoped BigOperators

/-- Only the numerical and center hypotheses of the new geometric theorem.
The data contain no approximation hypothesis and no interpolation conclusion. -/
structure GeometryData where
  m : ℕ
  K : ℕ
  curveDegreeWeights : Fin (m+1) → ℚ
  curveJetWeights : Fin (m+1) → ℚ
  curveDegreeWeights_pos : ∀ i, 0 < curveDegreeWeights i
  curveJetWeights_pos : ∀ i, 0 < curveJetWeights i
  sigma : ℚ
  sigma_pos : 0 < (sigma : ℝ)
  curveY : Fin K → ℂ
  curveY_ne_zero : ∀ j, curveY j ≠ 0
  curveY_injective : Function.Injective curveY
  curveCenters : Fin K → Fin m → ℂ
  curve_volume : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
    (∏ i, (curveDegreeWeights i : ℝ)) / (∏ i, (curveJetWeights i : ℝ)) < 1
  curve_coordinate_ratio : ∀ i : Fin m,
    (1+(sigma : ℝ)) * (curveDegreeWeights i.succ : ℝ) < curveJetWeights i.succ
  curve_separated_weight_products : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
    ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
    (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
    PiExponent.PersistentWeightComparison.comparisonConstant m sigma *
      (∏ j ∈ B, (curveJetWeights j : ℝ)) < ∏ j ∈ A, (curveDegreeWeights j : ℝ)

end OAI.Logarithm
