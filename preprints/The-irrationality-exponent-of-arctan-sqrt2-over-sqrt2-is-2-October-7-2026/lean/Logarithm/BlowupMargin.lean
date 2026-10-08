import Logarithm.BlowupGeometry
import Logarithm.CurveMargin

namespace OAI
noncomputable section
namespace Logarithm.BlowupMargin
open AlgebraicGeometry CategoryTheory
open PiExponent PiExponentSeshadri.Geometry NumericalAmpleness
open BlowupGeometry PiExponent.BlowupCurveMargin
variable (d : GeometryData)

/-- Concrete function-field coordinates and degree identities for one curve.
Existence of these data is a separate theorem, not part of GeometryData. -/
structure AffineCurveDegreeData (C : IntegralCurve (blowup d)) where
  E : Type
  [field : Field E]
  [algebra : Algebra ℂ E]
  [essFiniteType : Algebra.EssFiniteType ℂ E]
  coordinates : Fin (d.m+1) → E
  coordinates_generate : IntermediateField.adjoin ℂ (Set.range coordinates) = ⊤
  trdeg_one : Algebra.trdeg ℂ E = 1
  hyperplane_degree : (curveDegree (structureMap d) (A d) C : ℝ) =
    ((scale d).radius : ℝ) * CurveMargin.poleDegree d coordinates trdeg_one
  exceptional_degree : (curveDegree (structureMap d) (J d) C : ℝ) =
    -((scale d).radius : ℝ) * CurveMargin.contactSum d coordinates coordinates_generate trdeg_one

theorem uniform_margin_of_affine_curve_data
    (a : ℕ) (ha : 1 < a) (hample : (((A d).pow a).tensor (J d)).IsAmple)
    (hdata : ∀ C : IntegralCurve (blowup d),
      (¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ ({x} : Set _)) →
      (∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) →
      Nonempty (AffineCurveDegreeData d C)) :
    ∀ C : IntegralCurve (blowup d),
      marginCoefficient a d.sigma *
        (curveDegree (structureMap d) (((A d).pow a).tensor (J d)) C : ℝ) ≤
        (curveDegree (structureMap d) ((A d).tensor (J d)) C : ℝ) := by
  classical
  intro C
  by_cases hc : ∃ x : compactification d,
      Set.range (C.embedding ≫ projection d) ⊆ ({x} : Set _)
  · obtain ⟨x,hx⟩ := hc
    exact margin_of_contracted (structureMap d) (projection d) (hyperplane d) (J d)
      a ha hample d.sigma d.sigma_pos C x hx
  · by_cases hm : ∃ c : C.scheme,
        (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange
    · obtain ⟨r⟩ := hdata C hc hm
      let := r.field
      let := r.algebra
      let := r.essFiniteType
      exact CurveMargin.margin_of_actual_contact_degrees d (structureMap d) (A d) (J d)
        a ha hample C r.coordinates r.coordinates_generate r.trdeg_one
        (scale d).radius (by exact_mod_cast (scale d).radius_pos)
        r.hyperplane_degree r.exceptional_degree
    · exact margin_of_image_outside_chart (structureMap d) (centerIdeal d)
        (projection d) (A d) (J d) (exceptionalInclusion d) (exceptional_presents d)
        a ha hample d.sigma d.sigma_pos C (affineChart d).opensRange
        (centerIdeal_support_subset_chart d) (fun c hh => hm ⟨c,hh⟩)

end Logarithm.BlowupMargin
end
end OAI
