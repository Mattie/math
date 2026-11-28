import PiTwoCaseBridge.CurveGeometryLift
import PiTwoCaseBridge.WeightedArcs

namespace OAI.PiExponent.BridgeGeometry

noncomputable section
open AlgebraicGeometry CategoryTheory PiTwoCaseBridge.WeightedArcs
open PiExponentSeshadri

variable (d : BridgeData)

/-- Clearing the local weights simultaneously makes every pure-power center
generator have the same integer order on the associated weighted arcs. -/
theorem exists_arc_weights :
    ∃ q : ℕ, 0 < q ∧ ∃ w : Fin (d.m+1) → ℕ, (∀ i, 0 < w i) ∧
      (∀ i, (d.V i : ℝ) = (w i : ℝ) / q) ∧
      ∀ i, w i * (scale d).jetPowers i = q * (scale d).radius := by
  obtain ⟨q,hq,w,hw,heq⟩ := positive_rational_weights_common_denominator d.V d.V_pos
  refine ⟨q,hq,w,hw,heq,fun i => ?_⟩
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hscale : (d.V i : ℝ) * ((scale d).jetPowers i : ℝ) = ((scale d).radius : ℝ) := by
    exact_mod_cast (scale d).jetPowers_eq i
  rw [heq i, div_mul_eq_mul_div, div_eq_iff hq'.ne', mul_comm _ (q : ℝ)] at hscale
  exact_mod_cast hscale

def arcSubstitution (j : Fin d.K) (w : Fin (d.m+1) → ℕ) (c : Fin (d.m+1) → ℂ) :
    CompactLogJetIdeal.coordinateRing d.m →+* PowerSeries ℂ :=
  seriesArc (d.centers j) (CompactJetPolynomial.logPolynomials (logCutoff d)) w c

def arcMap (j : Fin d.K) (w : Fin (d.m+1) → ℕ) (c : Fin (d.m+1) → ℂ) :
    Spec (CommRingCat.of (PowerSeries ℂ)) ⟶ compactification d :=
  Spec.map (CommRingCat.ofHom (arcSubstitution d j w c)) ≫ affineChart d

theorem arc_ideal (j : Fin d.K) (w : Fin (d.m+1) → ℕ) (R : ℕ) (hpos : 0 < R)
    (hR : ∀ i, w i * (scale d).jetPowers i = R) (c : Fin (d.m+1) → ℂ) (hc : c ≠ 0) :
    (affinePolynomialIdeal d).map (arcSubstitution d j w c) =
      Ideal.span ({PowerSeries.X ^ R} : Set (PowerSeries ℂ)) :=
  map_centerIdeal d.centers d.centers_injective (logCutoff d) j w
    (scale d).jetPowers (scale d).jetPowers_pos R hpos hR c hc

theorem centerIdeal_comap_arc (j : Fin d.K) (w : Fin (d.m+1) → ℕ) (R : ℕ) (hpos : 0 < R)
    (hR : ∀ i, w i * (scale d).jetPowers i = R) (c : Fin (d.m+1) → ℂ) (hc : c ≠ 0) :
    (centerIdeal d).comap (arcMap d j w c) =
      IdealPullback.specIdeal (Ideal.span ({PowerSeries.X ^ R} : Set (PowerSeries ℂ))) := by
  rw [arcMap, centerIdeal_comap_specMap, arc_ideal d j w R hpos hR c hc]

/-- Every nonzero direction lifts, including directions on coordinate hyperplanes. -/
theorem existsUnique_weightedArcLift (j : Fin d.K) (w : Fin (d.m+1) → ℕ)
    (R : ℕ) (hpos : 0 < R) (hR : ∀ i, w i * (scale d).jetPowers i = R)
    (c : Fin (d.m+1) → ℂ) (hc : c ≠ 0) :
    ∃! g : Spec (CommRingCat.of (PowerSeries ℂ)) ⟶ blowup d,
      g ≫ projection d = arcMap d j w c :=
  existsUnique_lift_of_principal d (arcSubstitution d j w c) _
    (IsRegular.of_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero))
    (arc_ideal d j w R hpos hR c hc)

end
end OAI.PiExponent.BridgeGeometry
