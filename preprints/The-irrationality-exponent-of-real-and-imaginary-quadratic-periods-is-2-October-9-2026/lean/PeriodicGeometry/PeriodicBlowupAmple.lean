-- Adapted from the frozen periodic pi geometry; see extraction-manifest.json.
import OAI.NumberTheory.PiExponent.Ampleness.NumericalAmplenessTheorem
import PeriodicGeometry.PeriodicCurveDegreeData

namespace OAI

noncomputable section
namespace PiExponent.PeriodicBlowupGeometry
variable (d : PeriodicGeometryData)

theorem interpolationBundle_ample : (interpolationBundle d).IsAmple :=
  NumericalAmpleness.isAmple_of_uniform_curve_margin (structureMap d)
    (H d) (interpolationBundle d) (H_ample d) (uniformMargin d)
    (uniformMargin_pos d) (uniform_curve_margin d)

end PiExponent.PeriodicBlowupGeometry

end

end OAI
