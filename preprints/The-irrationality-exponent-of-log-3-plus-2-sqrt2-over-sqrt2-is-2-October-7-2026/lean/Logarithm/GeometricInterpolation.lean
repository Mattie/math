import Logarithm.BlowupGeometry
import Logarithm.JetPackets
import OAI.NumberTheory.PiExponent.Approximation.AdmissibleMatrixFrame
import OAI.NumberTheory.PiExponent.Approximation.WeightedGlobalSectionBound
import OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivityComplete

namespace OAI
noncomputable section
namespace Logarithm.GeometricInterpolation
open AlgebraicGeometry CategoryTheory Filter
open PiExponent PiExponentSeshadri.Geometry
open Logarithm.BlowupGeometry PiExponent.AffineJetCoefficientInterface
open PiExponent.BlowupJetSurjectivity
attribute [local irreducible] BlowupGeometry.affineChart BlowupGeometry.hyperplane
  BlowupGeometry.centerIdeal WeightedCompactification.lineBundle
  WeightedCompactification.affineChartMap

variable (d : GeometryData)

def sectionPolynomial (n : ℕ) (e : Frame (affineChart d) (hyperplane d)) :
    Sections (hyperplane d) n → PiExponentApprox.FramePolynomial d.m :=
  coefficient (affineChart d) (hyperplane d) n e

theorem formalPackets_surjective_of_jetRestriction (n : ℕ)
    (e : Frame (affineChart d) (hyperplane d))
    (hjet : Function.Surjective (jetRestriction (centerIdeal d) (hyperplane d) n)) :
    Function.Surjective (fun s j =>
      JetGeometry.rationalCoefficientPacket d.curveJetWeights (n * (scale d).radius)
        (ScaledFormalJet.formalJet (d.curveY j) (d.curveCenters j)
          (sectionPolynomial d n e s))) := by
  have he : ∀ i, (scale d).radius ≤ ((scale d).jetPowers i : ℚ) * d.curveJetWeights i := by
    intro i
    rw [mul_comm, (scale d).jetPowers_eq]
  have hs : (((centerIdeal d)^n).support : Set (compactification d)) ⊆
      (affineChart d).opensRange := by
    cases n with
    | zero => simp
    | succ n => simpa using centerIdeal_support_subset_chart d
  apply JetPackets.packets_surjective_of_polynomialIdeal_quotient
    d.curveY d.curveY_ne_zero d.curveCenters d.curveY_injective
    (logCutoff d) (scale d).jetPowers (scale d).jetPowers_pos
    d.curveJetWeights d.curveJetWeights_pos (fun i => (logCutoff_strict d i).le)
    (scale d).radius he n (sectionPolynomial d n e)
  simpa only [sectionPolynomial, coefficient, Sections] using
    AffineJetPolynomial.polynomialQuotient_surjective_of_jetRestriction
    (centerIdeal d) (hyperplane d) n (affineChart d) e
    (affinePolynomialIdeal d) (centerIdeal_restrict d) hs hjet

theorem actualFrame_exists : Nonempty (Frame (affineChart d) (hyperplane d)) := by
  unfold BlowupGeometry.affineChart BlowupGeometry.hyperplane
  exact AdmissibleMatrixInterpolation.monomialFrame_exists (R := ℂ)
    (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.curveDegreeWeights_pos)
    (coordinateIndex d) ((scale d).exponents_coordinate d.curveDegreeWeights_pos)

theorem exponent_budget (j : Index d) :
    Finsupp.weight (fun i => (d.curveDegreeWeights i : ℝ))
      (exponents d j) ≤ (scale d).radius := by
  have hq := (scale d).budget d.curveDegreeWeights_pos j
  have hr : (∑ i, (d.curveDegreeWeights i : ℝ) * (exponents d j i : ℝ)) ≤
      (scale d).radius := by exact_mod_cast hq
  simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hr

theorem eventual_supportBound :
    ProjectiveCoefficientBound.EventualBound (affineChart d) (hyperplane d)
      (fun i => (d.curveDegreeWeights i : ℝ)) (scale d).radius := by
  unfold BlowupGeometry.affineChart BlowupGeometry.hyperplane
  exact WeightedGlobalSectionBound.eventual_supportBound (K := ℂ) (ι := Fin (d.m+1))
    (σ := Index d) (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.curveDegreeWeights_pos)
    (coordinateIndex d) ((scale d).exponents_coordinate d.curveDegreeWeights_pos)
    (fun i => (d.curveDegreeWeights i : ℝ)) (scale d).radius (exponent_budget d)

def WeightedPolynomials (n : ℕ) :=
  {P : PiExponentApprox.FramePolynomial d.m //
    WeightedSliceDegree.SupportBound (fun i => (d.curveDegreeWeights i : ℝ))
      ((n : ℝ) * (scale d).radius) P}

def packetMap (n : ℕ) (P : WeightedPolynomials d n) :=
  fun j : Fin d.K => JetGeometry.rationalCoefficientPacket d.curveJetWeights
    ((n : ℚ) * (scale d).radius)
    (ScaledFormalJet.formalJet (d.curveY j) (d.curveCenters j) P.val)

/-- Global jet restriction gives eventual interpolation with the sharp scaled
weighted degree bound, through the concrete affine coefficients of sections. -/
theorem eventual_packets_of_eventual_jetRestriction
    (hjet : ∀ᶠ n : ℕ in atTop, Function.Surjective
      (jetRestriction (centerIdeal d) (hyperplane d) n)) :
    ∀ᶠ n : ℕ in atTop, Function.Surjective (packetMap d n) := by
  obtain ⟨N, hN⟩ := eventual_supportBound d
  obtain ⟨e⟩ := actualFrame_exists d
  filter_upwards [hjet, eventually_ge_atTop N] with n hn hnN
  intro packets
  obtain ⟨s, hs⟩ := formalPackets_surjective_of_jetRestriction d n e hn packets
  exact ⟨⟨sectionPolynomial d n e s, hN n hnN e s⟩, hs⟩

/-- The remaining ampleness input is the actual bundle on the actual blowup. -/
theorem eventual_packets_of_blowupBundle_ample
    (hample : (blowupBundle (centerIdeal d) (hyperplane d)).IsAmple) :
    ∀ᶠ n : ℕ in atTop, Function.Surjective (packetMap d n) := by
  apply eventual_packets_of_eventual_jetRestriction d
  obtain ⟨N, hN⟩ := eventual_blowup_jetRestriction_surjective
    (compactificationStructureMap d) (centerIdeal d) (hyperplane d) hample
  exact eventually_atTop.mpr ⟨N, hN⟩

end Logarithm.GeometricInterpolation
end
end OAI
