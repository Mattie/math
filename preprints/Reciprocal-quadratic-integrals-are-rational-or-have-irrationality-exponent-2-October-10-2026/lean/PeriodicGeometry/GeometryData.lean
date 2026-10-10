import OAI.NumberTheory.PiExponent.Geometry.CurveInequalityIntrinsic

namespace OAI.PiExponent
open scoped BigOperators

/-- Numerical weights and periodic centers. No approximation, ampleness,
section, packet, or matrix-surjectivity conclusion is assumed. -/
structure PeriodicGeometryData where
  m : ℕ
  m_pos : 0 < m
  K : ℕ
  curveDegreeWeights : Fin (m+1) → ℚ
  curveJetWeights : Fin (m+1) → ℚ
  curveDegreeWeights_pos : ∀ i, 0 < curveDegreeWeights i
  curveJetWeights_pos : ∀ i, 0 < curveJetWeights i
  sigma : ℚ
  sigma_pos : 0 < (sigma : ℝ)
  curveCenters : Fin K → Fin m → ℂ
  curveCenters_injective : ∀ i, Function.Injective (fun j => curveCenters j i)
  curve_volume : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
    (∏ i, (curveDegreeWeights i : ℝ)) / (∏ i, (curveJetWeights i : ℝ)) < 1
  curve_fibre_volume : (K : ℝ) * (1+3*(sigma : ℝ))^m *
    (∏ i : Fin m, (curveDegreeWeights i.succ : ℝ)) /
      (∏ i : Fin m, (curveJetWeights i.succ : ℝ)) < 1
  curve_coordinate_ratio : ∀ i : Fin m,
    (1+(sigma : ℝ)) * (curveDegreeWeights i.succ : ℝ) < curveJetWeights i.succ
  curve_separated_weight_products : ∀ A B : Finset (Fin (m+1)), A.card = B.card →
    ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
    (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
    PersistentWeightComparison.comparisonConstant m sigma *
      (∏ j ∈ B, (curveJetWeights j : ℝ)) < ∏ j ∈ A, (curveDegreeWeights j : ℝ)

namespace PeriodicGeometryData
noncomputable section
variable (d : PeriodicGeometryData)

theorem exact_weighted_curve_inequality
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let z : Fin (d.m+1) → E := Fin.cases y x
    let hz := CurveInequality.nonconstant_coordinates z hgen htrdeg
    (1+(d.sigma : ℝ)) * ∑ p ∈ CurveContactFamily.places hfinite z d.curveCenters hz,
      (CurveContactFamily.contact hres hfinite z d.curveCenters hz d.curveJetWeights p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z d.curveDegreeWeights :=
  CurveInequality.weighted_curve_inequality y x d.curveCenters d.curveCenters_injective
    hgen htrdeg d.curveDegreeWeights d.curveJetWeights
    d.curveDegreeWeights_pos d.curveJetWeights_pos d.sigma
    (by exact_mod_cast d.sigma_pos) d.curve_volume d.curve_fibre_volume
    d.curve_separated_weight_products d.curve_coordinate_ratio

end
end PeriodicGeometryData
end OAI.PiExponent
