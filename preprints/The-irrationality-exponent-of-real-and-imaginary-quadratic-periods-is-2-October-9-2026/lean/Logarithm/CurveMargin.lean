import Logarithm.GeometryData
import OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin

namespace OAI
noncomputable section
namespace Logarithm.CurveMargin
open scoped BigOperators
open AlgebraicGeometry CategoryTheory
open PiExponent PiExponentSeshadri.Geometry NumericalAmpleness
variable (d : GeometryData)
variable {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]

def contactSum (z : Fin (d.m+1) → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) : ℝ :=
  let hres := PlaceLocalRing.residue_integral htrdeg.le
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let hz := PiExponent.CurveInequality.nonconstant_coordinates z hgen htrdeg
  ∑ p ∈ ContactFamily.places hfinite z d.curveY d.curveY_ne_zero d.curveCenters hz,
    (ContactFamily.contact hres hfinite z d.curveY d.curveY_ne_zero d.curveCenters
      hz d.curveJetWeights p : ℝ)

def poleDegree (z : Fin (d.m+1) → E) (htrdeg : Algebra.trdeg ℂ E = 1) : ℝ :=
  CurveContactSum.weightedDegree
    (CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg) z d.curveDegreeWeights

theorem actual_contact_bound (z : Fin (d.m+1) → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    (1+(d.sigma : ℝ)) * contactSum d z hgen htrdeg ≤ poleDegree d z htrdeg :=
  Logarithm.weighted_curve_inequality z d.curveY d.curveY_ne_zero d.curveCenters
    d.curveY_injective hgen htrdeg d.curveDegreeWeights d.curveJetWeights
    d.curveDegreeWeights_pos d.curveJetWeights_pos d.sigma
    (by exact_mod_cast d.sigma_pos) d.curve_volume d.curve_separated_weight_products
    d.curve_coordinate_ratio

/-- The checked contact bound supplies the positive numerical margin once the
two actual curve degrees have been identified with pole and contact sums. -/
theorem margin_of_actual_contact_degrees {B : Scheme.{0}}
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (A J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (C : IntegralCurve B) (z : Fin (d.m+1) → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) (R : ℚ) (hR : 0 < R)
    (hA : (curveDegree p A C : ℝ) = (R : ℝ) * poleDegree d z htrdeg)
    (hJ : (curveDegree p J C : ℝ) = -(R : ℝ) * contactSum d z hgen htrdeg) :
    BlowupCurveMargin.marginCoefficient a d.sigma *
      (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) := by
  apply BlowupCurveMargin.margin_of_nonnegative_degree p A J a ha hample
    d.sigma d.sigma_pos C
  rw [hA, hJ]
  have hR' : (0 : ℝ) ≤ R := by exact_mod_cast hR.le
  have h := mul_le_mul_of_nonneg_left (actual_contact_bound d z hgen htrdeg) hR'
  nlinarith

end Logarithm.CurveMargin
end
end OAI
