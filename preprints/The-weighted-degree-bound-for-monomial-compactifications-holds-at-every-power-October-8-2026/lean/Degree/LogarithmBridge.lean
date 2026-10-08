import Degree.AllPowers
import Logarithm.GeometricInterpolation

namespace Degree
noncomputable section
open AlgebraicGeometry CategoryTheory
open OAI OAI.PiExponent OAI.PiExponentSeshadri.Geometry
open WeightedSliceDegree AffineJetCoefficientInterface
open OAI.Logarithm OAI.Logarithm.BlowupGeometry OAI.Logarithm.GeometricInterpolation

/-- The actual compactification shared by the four preprints, with no degree threshold. -/
theorem logarithm_all_supportBound (d : GeometryData) (n : ℕ)
    (e : Frame (affineChart d) (hyperplane d)) (s : Sections (hyperplane d) n) :
    SupportBound (fun i => (d.curveDegreeWeights i : ℝ))
      ((n : ℝ) * (scale d).radius) (sectionPolynomial d n e s) := by
  unfold sectionPolynomial OAI.Logarithm.BlowupGeometry.affineChart
    OAI.Logarithm.BlowupGeometry.hyperplane
  exact monomial_all_supportBound (K := ℂ)
    (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.curveDegreeWeights_pos)
    (coordinateIndex d) ((scale d).exponents_coordinate d.curveDegreeWeights_pos)
    (fun i => (d.curveDegreeWeights i : ℝ))
    (fun i => by exact_mod_cast (d.curveDegreeWeights_pos i).le)
    (scale d).radius (exponent_budget d) n e s

/-- The original π library's admissible compactification also inherits the strengthening. -/
theorem admissible_all_supportBound {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)
    (n : ℕ) (e : Frame (AdmissibleBlowupGeometry.affineChart d)
      (AdmissibleBlowupGeometry.hyperplane d))
    (s : Sections (AdmissibleBlowupGeometry.hyperplane d) n) :
    SupportBound (fun i => (d.curveDegreeWeights i : ℝ))
      ((n : ℝ) * (AdmissibleBlowupGeometry.scale d).radius)
      (AffineJetCoefficientInterface.coefficient (AdmissibleBlowupGeometry.affineChart d)
        (AdmissibleBlowupGeometry.hyperplane d) n e s) := by
  unfold AdmissibleBlowupGeometry.affineChart AdmissibleBlowupGeometry.hyperplane
  exact monomial_all_supportBound (K := ℂ)
    (AdmissibleBlowupGeometry.exponents d) (AdmissibleBlowupGeometry.constantIndex d)
    ((AdmissibleBlowupGeometry.scale d).exponents_constant d.curveDegreeWeights_pos)
    (AdmissibleBlowupGeometry.coordinateIndex d)
    ((AdmissibleBlowupGeometry.scale d).exponents_coordinate d.curveDegreeWeights_pos)
    (fun i => (d.curveDegreeWeights i : ℝ))
    (fun i => by exact_mod_cast (d.curveDegreeWeights_pos i).le)
    (AdmissibleBlowupGeometry.scale d).radius
    (WeightedHomogeneousSubstitution.admissible_exponent_budget d) n e s

end
end Degree
