import Logarithm.JetProductLocalization
import Logarithm.ContactFamily

namespace OAI
noncomputable section
namespace Logarithm
open PiExponent PiExponent.CurveValuationCenter PiExponent.CurveCenters
open PiExponent.PlaceValuationRing

/-- A nonconstant generic curve point cannot lie in the finite center scheme. -/
theorem map_powerIdeal_eq_top_of_transcendental
    {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (z : Fin (m+1) → E) (hz : ∃ i, Transcendental ℂ (z i))
    (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    (JetIdeals.powerIdeal y c T e).map (MvPolynomial.aeval z).toRingHom = ⊤ := by
  obtain ⟨i, hi⟩ := hz
  let P : PiExponentApprox.FramePolynomial m :=
    MvPolynomial.X i - MvPolynomial.C (fullCenter y c i)
  have hp : P ∈ (JetIdeals.powerIdeal y c T e).radical := by
    rw [JetIdeals.radical_powerIdeal y c T e he]
    change MvPolynomial.aeval (fullCenter y c) P = 0
    simp [P]
  obtain ⟨n, hn⟩ := hp
  have hne : MvPolynomial.aeval z P ≠ 0 := by
    intro h
    simp only [P, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      sub_eq_zero] at h
    exact hi (h.symm ▸ isAlgebraic_algebraMap (fullCenter y c i))
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hn)
  change IsUnit (MvPolynomial.aeval z (P ^ n))
  rw [map_pow]
  exact (isUnit_iff_ne_zero.mpr hne).pow n

/-- Exact colength of the finite-center ideal on a branch. Distinct Y values
select its local factor, whose normalized coordinates define logContact. -/
theorem polynomialIdeal_colength_eq_logContact
    {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (hyinj : Function.Injective y) (c : Fin K → Fin m → ℂ)
    (k : Fin K) (hp : Centered z (fullCenter (y k) (c k)) p)
    (hz : ∃ i, z i ≠ algebraMap ℂ E (fullCenter (y k) (c k) i))
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (R : ℚ) (he : ∀ i, v i * (e i : ℚ) = R)
    (hT : ∀ i, v i.succ < (T i : ℚ) * v 0) :
    ((Module.length (ring p) ((ring p) ⧸
      (JetIdeals.polynomialIdeal y c T e).map
        (MvPolynomial.aeval (PlaceCenteredBranch.lift p z
          (fullCenter (y k) (c k)) hp)).toRingHom)).toNat : ℚ) =
      R * logContact p z (y k) (hy k) (c k) hp hz v := by
  let a := PlaceCenteredBranch.lift p z (fullCenter (y k) (c k)) hp
  let hn := centered_normalized z (y k) (hy k) (c k) p hp
  let an := PlaceCenteredBranch.lift p (normalized z (y k)) (Fin.cases 1 (c k)) hn
  have ha : (Fin.cases (a 0) (fun i => a i.succ) : Fin (m+1) → ring p) = a := by
    funext i
    cases i using Fin.cases <;> rfl
  have hmap := JetProductLocalization.map_polynomialIdeal_eq_selected y hy hyinj c T e
    (a 0) (fun i => a i.succ) k
    (PlaceCenteredBranch.lift_residue p z (fullCenter (y k) (c k)) hp 0)
  rw [ha] at hmap
  have hY : a 0 * algebraMap ℂ (ring p) (y k)⁻¹ = an 0 := Subtype.ext rfl
  have hX : (fun i : Fin m => a i.succ) = (fun i => an i.succ) := rfl
  change ((Module.length (ring p) ((ring p) ⧸
    (JetIdeals.polynomialIdeal y c T e).map (MvPolynomial.aeval a).toRingHom)).toNat : ℚ) = _
  rw [hmap, hY, hX]
  exact LogarithmicContactIdeal.logarithmicIdeal_colength_eq_contact v hv (c k)
    (an 0) (fun i => an i.succ)
    (PlaceCenteredBranch.lift_residue p (normalized z (y k)) (Fin.cases 1 (c k)) hn 0)
    (fun i => PlaceCenteredBranch.lift_residue p (normalized z (y k))
      (Fin.cases 1 (c k)) hn i.succ)
    (PlaceCenteredBranch.logLift_nonconstant p (normalized z (y k)) (c k) hn
      (normalized_nonconstant z (y k) (hy k) (c k) hz)) T hT R e he

end Logarithm
end
end OAI
