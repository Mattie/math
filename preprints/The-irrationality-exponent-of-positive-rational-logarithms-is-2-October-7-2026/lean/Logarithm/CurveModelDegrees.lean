import Logarithm.CurveModel
import Logarithm.BlowupExceptionalDegree
import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer

namespace OAI
noncomputable section
namespace Logarithm.CurveModel
open AlgebraicGeometry CategoryTheory
open PiExponent PiExponentSeshadri.Geometry
open BlowupGeometry CurveNormalizationModel
variable (d : GeometryData)

def degreeData (C : NumericalAmpleness.IntegralCurve (blowup d))
    (r : ModelData d C) : BlowupMargin.AffineCurveDegreeData d C := by
  letI := r.field
  letI := r.algebra
  letI := r.essFiniteType
  letI := r.parameterFinite
  letI := r.normalizationFinite
  letI := r.chartIso
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ r.E r.trdeg_one
  have hA : (NumericalAmpleness.curveDegree (structureMap d) (A d) C : ℝ) =
      ((scale d).radius : ℝ) * CurveMargin.poleDegree d r.coordinates r.trdeg_one := by
    change _ = ((scale d).radius : ℝ) *
      CurveContactSum.weightedDegree hfinite r.coordinates d.curveDegreeWeights
    exact CurveNormalizedDegreeTransfer.weighted_curveDegree
      (exponents d) r.coordinates (constantIndex d)
      ((scale d).exponents_constant d.curveDegreeWeights_pos)
      (coordinateIndex d) ((scale d).exponents_coordinate d.curveDegreeWeights_pos)
      (structureMap d) (H d) (H_ample d) C r.parameter r.parameter_transcendental
      r.normalization r.normalization_over r.chart r.chart_nonempty
      (projection d) r.generic_coordinates d.curveDegreeWeights d.curveDegreeWeights_pos
      (by exact_mod_cast (scale d).radius_pos) (scale d).degreePowers
      (scale d).degreePowers_eq (pureIndex d)
      ((scale d).exponents_pure d.curveDegreeWeights_pos)
      ((scale d).budget d.curveDegreeWeights_pos) hfinite
  have hgeneric : parameterCurveGenericPoint r.parameter r.parameter_transcendental ≫
      (r.normalization ≫ C.embedding) ≫ projection d =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval r.coordinates).toRingHom) ≫
        affineChart d := by
    have heval : (MvPolynomial.aeval r.coordinates).toRingHom =
        MvPolynomial.eval₂Hom (algebraMap ℂ r.E) r.coordinates := by
      apply RingHom.ext
      intro P
      exact MvPolynomial.aeval_def r.coordinates P
    rw [heval]
    simpa only [Category.assoc, CurveMonomialMap.genericMonomialMap, affineChart] using
      r.generic_coordinates
  have hJ : (NumericalAmpleness.curveDegree (structureMap d) (J d) C : ℝ) =
      -((scale d).radius : ℝ) *
        CurveMargin.contactSum d r.coordinates r.coordinates_generate r.trdeg_one := by
    have hd := CurveNormalizedDegreeTransfer.curveDegree_eq_normalized
      (structureMap d) (H d) (H_ample d) C r.parameter r.parameter_transcendental
      r.normalization r.normalization_over r.chart r.chart_nonempty (J d)
    have hn := blowup_exceptional_degree_eq_neg_contact_sum
      d r.coordinates r.coordinates_generate r.trdeg_one
      r.parameter r.parameter_transcendental (r.normalization ≫ C.embedding) hgeneric
    exact (congrArg (fun n : ℤ => (n : ℝ)) hd).trans hn
  exact { E := r.E
          field := r.field
          algebra := r.algebra
          essFiniteType := r.essFiniteType
          coordinates := r.coordinates
          coordinates_generate := r.coordinates_generate
          trdeg_one := r.trdeg_one
          hyperplane_degree := hA
          exceptional_degree := hJ }

end Logarithm.CurveModel
end
end OAI
