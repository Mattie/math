import Logarithm.ContactFamily
import OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound

namespace OAI
noncomputable section
namespace Logarithm
open scoped BigOperators
open PiExponent PiExponent.CurveValuationCenter PiExponent.CurveCenters
open PiExponent.PlaceValuationRing Logarithm.ContactFamily

variable {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}

theorem weightedDegree_constant_Y
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (a : ℂ) (hY : z 0 = algebraMap ℂ E a)
    (w : Fin (m+1) → ℚ) :
    CurveContactSum.weightedDegree hfinite z w =
      CurveContactSum.weightedDegree hfinite (fun i : Fin m => z i.succ)
        (fun i => w i.succ) := by
  have he : CurveContactSum.weightedPoleDivisor hfinite z w =
      CurveContactSum.weightedPoleDivisor hfinite (fun i : Fin m => z i.succ)
        (fun i => w i.succ) := by
    ext p
    change WeightedPolynomialPole.coordinatePole p.valuation z w = _
    have horder : (fun i : Fin (m+1) =>
        (WeightedPolynomialPole.coordinateOrder p.valuation (z i) : ℚ)) =
        Fin.cases 0 (fun i : Fin m =>
          (WeightedPolynomialPole.coordinateOrder p.valuation (z i.succ) : ℚ)) := by
      funext i
      cases i using Fin.cases with
      | zero => simp [hY, CurveContactSum.coordinateOrder_constant_eq_zero]
      | succ i => rfl
    unfold WeightedPolynomialPole.coordinatePole
    rw [horder]
    exact FibreContact.weightedPole_zero_cons w _
  unfold CurveContactSum.weightedDegree
  rw [he]

/-- Distinct Y values replace all coordinatewise X-injectivity assumptions. -/
theorem no_excess_of_constant_Y
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hyinj : Function.Injective y)
    (hz : ∃ i, Transcendental ℂ (z i))
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hratio : ∀ i : Fin m, (1+(sigma : ℝ)) * (w i.succ : ℝ) < v i.succ)
    (hconst : ∃ a : ℂ, z 0 = algebraMap ℂ E a) :
    ¬ CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z y hy c hz,
        (contact hres hfinite z y hy c hz v p : ℝ) := by
  intro hexcess
  obtain ⟨a, ha⟩ := hconst
  let x : Fin m → E := fun i => z i.succ
  let S := places hfinite z y hy c hz
  let μ := fun p => (contact hres hfinite z y hy c hz v p : ℝ)
  have hdeg := weightedDegree_constant_Y hfinite z a ha w
  have hex : CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) <
      (1+(sigma : ℝ)) * ∑ p ∈ S, μ p := by
    rw [hdeg] at hexcess
    exact hexcess
  have hsum : 0 < ∑ p ∈ S, μ p := by
    have hn := CurveContactSum.weightedDegree_nonneg hfinite x (fun i => w i.succ)
    have hs : (0 : ℝ) < 1+sigma := by exact_mod_cast (by linarith : (0 : ℚ)<1+sigma)
    exact (mul_pos_iff_of_pos_left hs).mp (lt_of_le_of_lt hn hex)
  have hS : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hsum
    exact lt_irrefl _ hsum
  obtain ⟨p0,hp0⟩ := hS
  let j0 := center hfinite z y hy c hz p0 hp0
  have hcenters : ∀ p (hp : p ∈ S), center hfinite z y hy c hz p hp = j0 := by
    intro p hp
    exact center_index_unique_of_constant_Y z y c hyinj a ha _ _ p p0
      (centered hfinite z y hy c hz p hp) (centered hfinite z y hy c hz p0 hp0)
  have hcenter : ∀ p ∈ S, Centered x (c j0) p := by
    intro p hp i
    have hh := centered hfinite z y hy c hz p hp i.succ
    simpa only [hcenters p hp, fullCenter, Fin.cases_succ, x] using hh
  have hnc : ∃ i, x i ≠ algebraMap ℂ E (c j0 i) := by
    obtain ⟨i, hi⟩ := hz
    cases i using Fin.cases with
    | zero => exact (hi (ha.symm ▸ isAlgebraic_algebraMap a)).elim
    | succ i =>
      refine ⟨i, ?_⟩
      intro hh
      change z i.succ = algebraMap ℂ E (c j0 i) at hh
      exact hi (hh.symm ▸ isAlgebraic_algebraMap (c j0 i))
  obtain ⟨i, hi⟩ := hnc
  have hcoord := CoordinateContactBound.coordinate_contact_sum_le hfinite x (c j0)
    (fun i => w i.succ) (fun i => v i.succ) (fun i => hw i.succ) (fun i => hv i.succ)
    i (sub_ne_zero.mpr hi) S hcenter (fun p _ => hres p) μ (by
      intro p hp
      let := hres p
      have hc := centered hfinite z y hy c hz p hp
      have hc0 := hc.constant_coordinate 0 a ha
      have hz0 : z 0 = algebraMap ℂ E (y (center hfinite z y hy c hz p hp)) :=
        ha.trans (congrArg (algebraMap ℂ E) hc0)
      have hxnc : ∃ k : Fin m,
          z k.succ ≠ algebraMap ℂ E (c (center hfinite z y hy c hz p hp) k) := by
        simpa only [hcenters p hp] using (show ∃ k : Fin m,
          z k.succ ≠ algebraMap ℂ E (c j0 k) from ⟨i, hi⟩)
      have heq := logContact_constant_Y p z _ (hy _) _ hc
        (ContactFamily.nonconstant z _ _ hz) hz0 hxnc v
      dsimp only [μ]
      rw [contact, dite_eq_left hp, heq]
      congr 1
      simp only [hcenters p hp]
      rfl)
  have hwi : (0 : ℝ) < w i.succ := by exact_mod_cast hw i.succ
  have hb := mul_lt_mul_of_pos_left hex hwi
  have hr := mul_lt_mul_of_pos_right (hratio i) hsum
  nlinarith

end Logarithm
end
end OAI
