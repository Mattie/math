import OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch

namespace OAI
noncomputable section
namespace Logarithm
open PiExponent PiExponent.CurveCenters PiExponent.CurveValuationCenter

variable {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}

/-- The logarithmic center may have any nonzero first coordinate. -/
def fullCenter (y : ℂ) (c : Fin m → ℂ) : Fin (m+1) → ℂ := Fin.cases y c

/-- Normalize only the first coordinate; the logarithm is then centered at one. -/
def normalized (z : Fin (m+1) → E) (y : ℂ) : Fin (m+1) → E :=
  Fin.cases (z 0 * algebraMap ℂ E y⁻¹) (fun i => z i.succ)

theorem centered_normalized (z : Fin (m+1) → E) (y : ℂ) (hy : y ≠ 0)
    (c : Fin m → ℂ) (p : NormalizedPlace ℂ E)
    (hp : Centered z (fullCenter y c) p) :
    Centered (normalized z y) (Fin.cases 1 c) p := by
  intro i
  cases i using Fin.cases with
  | zero =>
    have he : normalized z y 0 - algebraMap ℂ E 1 =
        (z 0 - algebraMap ℂ E y) * algebraMap ℂ E y⁻¹ := by
      simp only [normalized, Fin.cases_zero, map_one, map_inv₀]
      have hyn : algebraMap ℂ E y ≠ 0 := (map_ne_zero (algebraMap ℂ E)).mpr hy
      field_simp
    change 0 < p.valuation (normalized z y 0 - algebraMap ℂ E 1)
    rw [he, p.valuation.map_mul,
      CurveProductFormula.valuation_constant_eq_zero p _ (inv_ne_zero hy), add_zero]
    exact hp 0
  | succ i => exact hp i.succ

theorem normalized_nonconstant (z : Fin (m+1) → E) (y : ℂ) (hy : y ≠ 0)
    (c : Fin m → ℂ) (hz : ∃ i, z i ≠ algebraMap ℂ E (fullCenter y c i)) :
    ∃ i, normalized z y i ≠ algebraMap ℂ E ((Fin.cases 1 c : Fin (m+1) → ℂ) i) := by
  obtain ⟨i, hi⟩ := hz
  refine ⟨i, ?_⟩
  cases i using Fin.cases with
  | zero =>
    intro h
    apply hi
    have hyn : algebraMap ℂ E y ≠ 0 := (map_ne_zero (algebraMap ℂ E)).mpr hy
    simp only [normalized, Fin.cases_zero, map_one, map_inv₀] at h
    change z 0 = algebraMap ℂ E y
    field_simp at h
    exact h
  | succ i => exact hi

theorem center_index_unique_of_constant_Y
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (hy : Function.Injective y) (a : ℂ) (hz : z 0 = algebraMap ℂ E a)
    (j k : Fin K) (p q : NormalizedPlace ℂ E)
    (hp : Centered z (fullCenter (y j) (c j)) p)
    (hq : Centered z (fullCenter (y k) (c k)) q) : j = k := by
  apply hy
  exact (hp.constant_coordinate 0 a hz).symm.trans (hq.constant_coordinate 0 a hz)

variable (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p))]

/-- Branch contact for the local coordinates Y/y-1 and Xi-ci-log(Y/y). -/
def logContact (z : Fin (m+1) → E) (y : ℂ) (hy : y ≠ 0)
    (c : Fin m → ℂ) (hp : Centered z (fullCenter y c) p)
    (hz : ∃ i, z i ≠ algebraMap ℂ E (fullCenter y c i))
    (v : Fin (m+1) → ℚ) : ℚ :=
  PlaceCenteredBranch.logContact p (normalized z y) c
    (centered_normalized z y hy c p hp) (normalized_nonconstant z y hy c hz) v

theorem logContact_pos (z : Fin (m+1) → E) (y : ℂ) (hy : y ≠ 0)
    (c : Fin m → ℂ) (hp : Centered z (fullCenter y c) p)
    (hz : ∃ i, z i ≠ algebraMap ℂ E (fullCenter y c i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) :
    0 < logContact p z y hy c hp hz v :=
  PlaceCenteredBranch.logContact_pos p _ _ _ _ v hv

end Logarithm
end
end OAI
