-- Adapted from the frozen periodic pi geometry; see extraction-manifest.json.
import PeriodicGeometry.PeriodicBlowupAmple
import OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupJetSurjectivity

namespace OAI

namespace PiExponent.PeriodicJetAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.PeriodicBlowupGeometry PiExponent.BlowupJetSurjectivity
attribute [local irreducible] PeriodicBlowupGeometry.centerIdeal
  PeriodicBlowupGeometry.hyperplane
variable (d : PeriodicGeometryData)

theorem blowupBundle_ample :
    (blowupBundle (centerIdeal d) (hyperplane d)).IsAmple := by
  apply PiExponent.AmpleIso.isAmple_of_sheaf_iso (interpolationBundle d)
    (blowupBundle (centerIdeal d) (hyperplane d))
    (moduleTensorComm (A d).sheaf (J d).sheaf)
  exact interpolationBundle_ample d

end
end PiExponent.PeriodicJetAmpleness

end OAI
