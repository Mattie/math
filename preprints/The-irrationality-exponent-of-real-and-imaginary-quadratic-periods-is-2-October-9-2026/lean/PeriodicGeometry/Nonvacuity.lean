import PeriodicGeometry.GeometryData
namespace OAI.PiExponent.PeriodicNonvacuity
noncomputable section
open scoped BigOperators

/-- A concrete two-center instance of the numerical geometric assumptions.
It is independent of any hypothetical good approximation sequence. -/
def sample : PeriodicGeometryData where
  m := 1
  m_pos := by norm_num
  K := 2
  curveDegreeWeights := fun i => if i = 0 then 1 else 16087141
  curveJetWeights := fun i => if i = 0 then 10 else 64348564
  curveDegreeWeights_pos := by intro i; fin_cases i <;> norm_num [Fin.cases]
  curveJetWeights_pos := by intro i; fin_cases i <;> norm_num [Fin.cases]
  sigma := 1/10
  sigma_pos := by norm_num
  curveCenters := fun j _ => (j.val : ℂ)
  curveCenters_injective := by
    intro i j k h
    change (j.val : ℂ) = (k.val : ℂ) at h
    apply Fin.ext
    exact_mod_cast h
  curve_volume := by norm_num [Fin.prod_univ_succ]
  curve_fibre_volume := by norm_num [Fin.prod_univ_succ]
  curve_coordinate_ratio := by intro i; fin_cases i <;> norm_num [Fin.cases]
  curve_separated_weight_products := by
    intro A B hcard i hi hiA hiB hhigh
    fin_cases A <;> fin_cases B <;> fin_cases i <;>
      norm_num [PersistentWeightComparison.comparisonConstant, Fin.cases] at *

end
end OAI.PiExponent.PeriodicNonvacuity
