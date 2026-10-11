import Logarithm.GeometryAmple
import Logarithm.GeometricInterpolation
import Logarithm.ScaledTruncation

namespace OAI
noncomputable section
namespace Logarithm
open Filter
open PiExponent PiExponentSeshadri.Geometry

/-- Eventual weighted logarithmic interpolation at arbitrary distinct nonzero
Y centers, proved from the numerical geometric hypotheses in GeometryData. -/
theorem eventually_weighted_logarithmic_interpolation (d : GeometryData) :
    ∀ᶠ n : ℕ in atTop,
      Function.Surjective (GeometricInterpolation.packetMap d n) := by
  apply GeometricInterpolation.eventual_packets_of_blowupBundle_ample d
  apply PiExponent.AmpleIso.isAmple_of_sheaf_iso (BlowupGeometry.interpolationBundle d)
    (PiExponent.BlowupJetSurjectivity.blowupBundle
      (BlowupGeometry.centerIdeal d) (BlowupGeometry.hyperplane d))
    (moduleTensorComm (BlowupGeometry.A d).sheaf (BlowupGeometry.J d).sheaf)
  exact BlowupGeometry.interpolationBundle_ample d

/-- The same degree-controlled interpolation holds for truncated logarithms. -/
theorem eventually_weighted_truncated_interpolation (d : GeometryData)
    (T : Fin d.m → ℕ)
    (hT : ∀ i, d.curveJetWeights i.succ ≤ (T i : ℚ) * d.curveJetWeights 0) :
    ∀ᶠ n : ℕ in atTop, Function.Surjective
      (fun P : GeometricInterpolation.WeightedPolynomials d n => fun j : Fin d.K =>
        JetGeometry.rationalCoefficientPacket d.curveJetWeights
          ((n : ℚ) * (BlowupGeometry.scale d).radius)
          (ScaledTruncation.truncatedFormalJet (d.curveY j) (d.curveCenters j) T P.val)) := by
  filter_upwards [eventually_weighted_logarithmic_interpolation d] with n hn
  exact (ScaledTruncation.formalLog_packets_surjective_iff_truncated d.curveJetWeights
    (fun i => (d.curveJetWeights_pos i).le) ((n : ℚ) * (BlowupGeometry.scale d).radius)
    T hT d.curveY d.curveCenters (fun P : GeometricInterpolation.WeightedPolynomials d n => P.val)).mp hn

end Logarithm
end
end OAI
