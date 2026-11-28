import PiTwoCaseBridge.CurveGeometryCore
import PiTwoCaseBridge.WeightedArcs
import PiTwoCaseBridge.RationalWeights
import Mathlib.FieldTheory.RatFunc.Valuation
import OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomialLocal
import OAI.NumberTheory.PiExponent.Polynomials.CompositePullbackCoefficient
import OAI.NumberTheory.PiExponent.Ampleness.WeightedAffineFrame
import OAI.NumberTheory.PiExponent.Approximation.SectionPowerFrames
import OAI.NumberTheory.PiExponent.Approximation.WeightedFrameDegree
import OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientFrame
import OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface

/-! Degree of an affine coefficient, and detection by monomial curves. -/

namespace PiTwoCaseBridge.MonomialDegree

open OAI OAI.PiExponent MvPolynomial
open OAI.PiExponent.BridgeGeometry OAI.PiExponent.WeightedSliceDegree
open scoped Polynomial
open scoped Classical

variable {σ K : Type*} [Field K]

/-- A generic torus direction detects each nonzero component of the indicated weight. -/
theorem exists_direction_coeff_ne_zero [Infinite K] (w : σ → ℕ) (p : MvPolynomial σ K)
    (a : σ →₀ ℕ) (ha : a ∈ p.support) :
    ∃ c : σ → K, (∀ i, c i ≠ 0) ∧ (WeightedArcs.arc w c p).coeff (Finsupp.weight w a) ≠ 0 := by
  classical
  by_contra! h
  let n := Finsupp.weight w a
  have hz : weightedHomogeneousComponent w n p = 0 := by
    apply MvPolynomial.funext_set (fun _ ↦ ({0} : Set K)ᶜ)
      (fun _ ↦ (Set.finite_singleton (0 : K)).infinite_compl)
    intro c hc
    rw [← WeightedArcs.coeff_arc, map_zero]
    exact h c (fun i ↦ hc i (Set.mem_univ _))
  have hcoef := congrArg (fun f : MvPolynomial σ K ↦ f.coeff a) hz
  simp [coeff_weightedHomogeneousComponent, n] at hcoef
  exact mem_support_iff.mp ha hcoef

/-- The actual pole at infinity of an arc evaluation detects the support weight.
The hypothesis is the geometric pole estimate along one-parameter monomial curves. -/
theorem weight_le_of_arc_pole_bound [Infinite K] (w : σ → ℕ) (p : MvPolynomial σ K) (B : ℕ)
    (h : ∀ c : σ → K, (∀ i, c i ≠ 0) →
      RatFunc.inftyValuation K (algebraMap K[X] (RatFunc K) (WeightedArcs.arc w c p)) ≤
        WithZero.exp (B : ℤ)) (a : σ →₀ ℕ) (ha : a ∈ p.support) :
    Finsupp.weight w a ≤ B := by
  obtain ⟨c, hc, hcoeff⟩ := exists_direction_coeff_ne_zero w p a ha
  have hp : WeightedArcs.arc w c p ≠ 0 := by
    intro he
    exact hcoeff (by simp [he])
  have hval := h c hc
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation.polynomial K hp] at hval
  have hdeg : (WeightedArcs.arc w c p).natDegree ≤ B := by simpa using hval
  exact (Polynomial.le_natDegree_of_ne_zero hcoeff).trans hdeg

end PiTwoCaseBridge.MonomialDegree

namespace PiTwoCaseBridge.MonomialDegree

noncomputable section
open OAI OAI.PiExponent AlgebraicGeometry CategoryTheory
open OAI.PiExponentSeshadri.Geometry OAI.PiExponentSeshadri.Frames

variable {X : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B]

/-- The value of an affine-open function at an affine-scheme point. -/
def pointValue {U : X.Opens} (g : Spec (.of A) ⟶ U.toScheme) : Γ(U.toScheme,⊤) →+* A :=
  (Scheme.ΓSpecIso (.of A)).hom.hom.comp g.appTop.hom

theorem pointValue_natural {U : X.Opens} (g : Spec (.of A) ⟶ U.toScheme) (f : A →+* B)
    (x : Γ(U.toScheme,⊤)) :
    pointValue (Spec.map (CommRingCat.ofHom f) ≫ g) x = f (pointValue g x) := by
  change ((Spec.map (CommRingCat.ofHom f) ≫ g).appTop ≫ (Scheme.ΓSpecIso (.of B)).hom) x = _
  rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
  rfl

private theorem exists_point_frame {M : X.Modules} (η : Spec (.of A) ⟶ X)
    {U : X.Opens} (g : Spec (.of A) ⟶ U.toScheme) (hg : g ≫ U.ι = η)
    (e : M.restrict U.ι ≅ O U.toScheme) :
    ∃ F : (Scheme.Modules.pullback η).obj M ≅ O _,
      ∀ s : O X ⟶ M, LocalSectionOrder.localCoefficient F (pullbackSection η s) =
        pointValue g (coefficient e (restrictSection U.ι s)) := by
  subst η
  obtain ⟨F, hF⟩ := PullbackFrameCoefficient.exists_frame_of_factors_through_open U g e
  exact ⟨F, fun s ↦ congrArg (Scheme.ΓSpecIso (.of A)).hom (hF s)⟩

/-- At a point of an overlap the two coefficient functions differ by the same
unit for every section. The point need not be an open immersion. -/
theorem pointValue_overlap {M : X.Modules} {U V : X.Opens}
    (f : Spec (.of A) ⟶ U.toScheme) (g : Spec (.of A) ⟶ V.toScheme)
    (h : f ≫ U.ι = g ≫ V.ι) (e : M.restrict U.ι ≅ O U.toScheme)
    (d : M.restrict V.ι ≅ O V.toScheme) :
    ∃ u : Aˣ, ∀ s : O X ⟶ M, pointValue g (coefficient d (restrictSection V.ι s)) =
      (u : A) * pointValue f (coefficient e (restrictSection U.ι s)) := by
  obtain ⟨F, hF⟩ := exists_point_frame (g ≫ V.ι) f h e
  obtain ⟨G, hG⟩ := exists_point_frame (g ≫ V.ι) g rfl d
  refine ⟨Units.map (Scheme.ΓSpecIso (.of A)).hom.hom (frameChange F G), ?_⟩
  intro s
  rw [← hF, ← hG]
  unfold LocalSectionOrder.localCoefficient
  rw [coefficient_change F G, map_mul]
  rfl

/-- Across a valuation ring, a section written in a generically chosen frame
is a regular coefficient times the nth power of a coordinate. The coordinate
is any one which trivializes the bundle at the special point. -/
theorem coefficient_factors_at_special_chart {S E : Type} [CommRing S] [Field E]
    {M : X.Modules} (v₀ v : structureSheaf X ⟶ M)
    (f : Spec (.of E) ⟶ (PiExponentSeshadri.SectionOpens.isoOpen v₀).toScheme)
    (g : Spec (.of S) ⟶ (PiExponentSeshadri.SectionOpens.isoOpen v).toScheme)
    (k : S →+* E)
    (h : f ≫ (PiExponentSeshadri.SectionOpens.isoOpen v₀).ι =
      (Spec.map (CommRingCat.ofHom k) ≫ g) ≫ (PiExponentSeshadri.SectionOpens.isoOpen v).ι)
    (n : ℕ) (s : O X ⟶ modulePow X M n) :
    ∃ b : S, pointValue f (coefficient (coordinatePowerFrame v₀ n)
      (restrictSection (PiExponentSeshadri.SectionOpens.isoOpen v₀).ι s)) =
      k b * (pointValue f (coefficient (PiExponentSeshadri.Projective.sectionFrame v₀)
        (restrictSection (PiExponentSeshadri.SectionOpens.isoOpen v₀).ι v))) ^ n := by
  let g' := Spec.map (CommRingCat.ofHom k) ≫ g
  obtain ⟨u, hu⟩ := pointValue_overlap f g' h (coordinatePowerFrame v₀ n) (coordinatePowerFrame v n)
  have hi := hu (powerSection v n)
  erw [coordinatePowerFrame_normalized, coordinatePowerFrame_coefficient v₀ v n,
    map_one, map_pow] at hi
  refine ⟨pointValue g (coefficient (coordinatePowerFrame v n)
    (restrictSection (PiExponentSeshadri.SectionOpens.isoOpen v).ι s)), ?_⟩
  rw [← pointValue_natural, hu s]
  calc
    _ = (1 : E) * _ := (one_mul _).symm
    _ = _ := by rw [hi]; exact mul_right_comm _ _ _

open WeightedCompactification CurveGlobalMonomialLocal ProjectiveLocalCoefficients
open PiExponentSeshadri.SectionOpens PiExponentSeshadri.Projective

set_option maxHeartbeats 800000 in
/-- The constant-coordinate frame evaluates every other coordinate section
as its designated monomial on the parameterized affine chart. -/
theorem pointValue_coordinate {F E ι σ : Type} [CommRing F] [CommRing E] [Algebra F E]
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0) (j : ι → σ)
    (hj : ∀ i, a (j i) = Finsupp.single i 1) (x : ι → E)
    (f : Spec (.of E) ⟶ (isoOpen (coordinateSection (R := F) a z)).toScheme)
    (hf : f ≫ (isoOpen (coordinateSection a z)).ι = CurveMonomialMap.genericMonomialMap a z hz j hj x)
    (i : σ) :
    pointValue f (coefficient (sectionFrame (coordinateSection a z))
      (restrictSection (isoOpen (coordinateSection a z)).ι (coordinateSection a i))) =
      monomialCoordinates (F := F) a x i := by
  let η := CurveMonomialMap.genericMonomialMap (F := F) a z hz j hj x
  let π := projectiveMonomialMap (R := F) a
  let y := monomialCoordinates (F := F) a x
  have hp : ∃ G : (Scheme.Modules.pullback (η ≫ π)).obj
      (ProjectiveO1.lineBundle (R := F) (σ := σ)).sheaf ≅ O _,
      ∀ i, LocalSectionOrder.localCoefficient G (pullbackSection (η ≫ π)
        (ProjectiveO1.coordinateSection i)) = y i := by
    rw [show η ≫ π = _ from genericMonomialMap_comp_projectiveMonomialMap a z hz j hj x]
    apply exists_frame_coordinate_coefficients
  obtain ⟨G, hG⟩ := hp
  obtain ⟨G', hG'⟩ := CompositePullbackCoefficient.exists_frame η π G
  let F₀ : (Scheme.Modules.pullback η).obj (lineBundle (R := F) a).sheaf ≅ O _ := G'
  have monoVal (k : σ) : LocalSectionOrder.localCoefficient F₀
      (pullbackSection η (coordinateSection a k)) = y k :=
    (congrArg (Scheme.ΓSpecIso (.of E)).hom (hG' (ProjectiveO1.coordinateSection k))).trans (hG k)
  obtain ⟨T, hT⟩ := exists_point_frame η f hf (sectionFrame (coordinateSection a z))
  let unit := (Scheme.ΓSpecIso (.of E)).hom (frameChange F₀ T : Γ(Spec (.of E),⊤))
  have hmul (k : σ) :
      pointValue f (coefficient (sectionFrame (coordinateSection a z))
        (restrictSection (isoOpen (coordinateSection a z)).ι (coordinateSection a k))) = unit * y k := by
    rw [← hT, ← monoVal]
    unfold LocalSectionOrder.localCoefficient
    rw [coefficient_change F₀ T, map_mul]
  have hu := hmul z
  erw [sectionFrame_normalized, map_one, show y z = 1 from monomialCoordinates_zero a x z hz,
    mul_one] at hu
  rw [hmul, ← hu, one_mul]

/-- Properness extends the generic torus point across the valuation ring.
A generating projective coordinate gives one chart containing the whole lift. -/
theorem exists_special_coordinate_chart {S E : Type} [CommRing S] [IsDomain S]
    [ValuationRing S] [Field E] [Algebra S E] [IsFractionRing S E]
    {T : Scheme.{0}} (π : X ⟶ T) [IsProper π] (η : Spec (.of E) ⟶ X)
    (b : Spec (.of S) ⟶ T)
    (h : η ≫ π = Spec.map (CommRingCat.ofHom (algebraMap S E)) ≫ b)
    {ι : Type} {M : X.Modules} (v : ι → (O X ⟶ M)) (hv : (⨆ i, isoOpen (v i)) = ⊤) :
    ∃ (i : ι) (g : Spec (.of S) ⟶ (isoOpen (v i)).toScheme),
      (Spec.map (CommRingCat.ofHom (algebraMap S E)) ≫ g) ≫ (isoOpen (v i)).ι = η := by
  let sq : ValuativeCommSq π :=
    { R := S, K := E, i₁ := η, i₂ := b, commSq := ⟨h⟩ }
  have proper : ValuativeCriterion π := by
    have hp : IsProper π := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  obtain ⟨φ, hφ, _⟩ := (proper.existence sq).exists_lift
  have hclosed : φ (IsLocalRing.closedPoint S) ∈ ⨆ i, isoOpen (v i) := by rw [hv]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hclosed
  have hsub : Set.range φ ⊆ Set.range (isoOpen (v i)).ι := by
    rintro _ ⟨x, rfl⟩
    have hx := ((IsLocalRing.specializes_closedPoint x).map φ.continuous).mem_open
      (isoOpen (v i)).isOpen hi
    exact ⟨⟨_, hx⟩, rfl⟩
  refine ⟨i, IsOpenImmersion.lift _ φ hsub, ?_⟩
  rw [Category.assoc, IsOpenImmersion.lift_fac]
  exact hφ

open BridgeGeometry
open scoped Classical Polynomial

private abbrev vars (d : BridgeData) := Fin (d.m + 1)
private abbrev P (d : BridgeData) := MvPolynomial (vars d) ℂ
private abbrev coord (d : BridgeData) (i : Index d) :=
  coordinateSection (R := ℂ) (exponents d) i
private abbrev centerOpen (d : BridgeData) := isoOpen (coord d (constantIndex d))

private def chart (d : BridgeData) : Spec (.of (P d)) ⟶ (centerOpen d).toScheme :=
  IsOpenImmersion.lift (centerOpen d).ι (affineChart d) (by
    rw [Scheme.Opens.range_ι, show centerOpen d = (affineChart d).opensRange from
      WeightedAffineFrame.affineChart_isoOpen (exponents d) (constantIndex d)
        ((scale d).exponents_constant d.W_pos) (coordinateIndex d)
        ((scale d).exponents_coordinate d.W_pos)]
    exact Set.Subset.rfl)

private theorem chart_fac (d : BridgeData) : chart d ≫ (centerOpen d).ι = affineChart d :=
  IsOpenImmersion.lift_fac _ _ _

private def canonicalPolynomial (d : BridgeData) (n : ℕ)
    (s : AffineJetCoefficientInterface.Sections (hyperplane d) n) : P d :=
  pointValue (chart d) (coefficient (coordinatePowerFrame (coord d (constantIndex d)) n)
    (restrictSection (centerOpen d).ι s))

set_option maxHeartbeats 1200000 in
/-- On a valuative test point, the normalized coefficient is regular after
division by the nth power of one of the given projective monomials. -/
theorem coefficient_factors_on_valuation (d : BridgeData) {S E : Type}
    [CommRing S] [IsDomain S] [ValuationRing S] [Field E] [Algebra S E] [IsFractionRing S E]
    [Algebra ℂ E] (k : ℂ →+* S) (hk : (algebraMap S E).comp k = algebraMap ℂ E)
    (x : vars d → E) (n : ℕ) (s : AffineJetCoefficientInterface.Sections (hyperplane d) n) :
    ∃ (i : Index d) (b : S),
      MvPolynomial.aeval x (canonicalPolynomial d n s) =
        algebraMap S E b * monomialCoordinates (F := ℂ) (exponents d) x i ^ n := by
  let η := CurveMonomialMap.genericMonomialMap (F := ℂ) (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.W_pos) (coordinateIndex d) ((scale d).exponents_coordinate d.W_pos) x
  let ev := MvPolynomial.eval₂Hom (algebraMap ℂ E) x
  let f := Spec.map (CommRingCat.ofHom ev) ≫ chart d
  have hf : f ≫ (centerOpen d).ι = η := by rw [Category.assoc, chart_fac]; rfl
  have he : η ≫ compactificationStructureMap d =
      Spec.map (CommRingCat.ofHom (algebraMap S E)) ≫ Spec.map (CommRingCat.ofHom k) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hk]
    exact CurveMonomialMap.genericMonomialMap_over_base _ _ _ _ _ _
  obtain ⟨i, g, hg⟩ := exists_special_coordinate_chart (compactificationStructureMap d) η
    (Spec.map (CommRingCat.ofHom k)) he (coord d) (coordinateSection_cover (exponents d))
  obtain ⟨b, hb⟩ := coefficient_factors_at_special_chart (coord d (constantIndex d)) (coord d i)
    f g (algebraMap S E) (hf.trans hg.symm) n s
  have hv := pointValue_coordinate (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.W_pos) (coordinateIndex d)
    ((scale d).exponents_coordinate d.W_pos) x f hf i
  erw [hv] at hb
  exact ⟨i, b, (pointValue_natural (chart d) ev _).symm.trans hb⟩

private theorem infinity_arc_monomial_le (d : BridgeData) (w : vars d → ℕ)
    (c : vars d → ℂ) (i : Index d) :
    RatFunc.inftyValuation ℂ (algebraMap ℂ[X] (RatFunc ℂ)
      (WeightedArcs.arc w c (MvPolynomial.monomial (exponents d i) 1))) ≤
      WithZero.exp ((Finsupp.weight w (exponents d i) : ℕ) : ℤ) := by
  let p := WeightedArcs.arc w c (MvPolynomial.monomial (exponents d i) 1)
  by_cases hp : p = 0
  · change RatFunc.inftyValuation ℂ (algebraMap ℂ[X] (RatFunc ℂ) p) ≤ _
    simp [hp]
  · rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation.polynomial ℂ hp, WithZero.exp_le_exp]
    exact_mod_cast (show p.natDegree ≤ _ by
      rw [show p = _ from WeightedArcs.arc_monomial w c (exponents d i) 1]
      exact Polynomial.natDegree_C_mul_X_pow_le _ _)

set_option maxHeartbeats 1000000 in
private theorem canonical_weight_le (d : BridgeData) (w : vars d → ℕ) (B : ℕ)
    (hB : ∀ i, Finsupp.weight w (exponents d i) ≤ B)
    (n : ℕ) (s : AffineJetCoefficientInterface.Sections (hyperplane d) n)
    (a : vars d →₀ ℕ) (ha : a ∈ (canonicalPolynomial d n s).support) :
    Finsupp.weight w a ≤ n * B := by
  classical
  apply weight_le_of_arc_pole_bound w (canonicalPolynomial d n s) (n*B) _ a ha
  intro c _
  let E := RatFunc ℂ
  let v := RatFunc.inftyValuation ℂ
  let S := v.valuationSubring
  let k : ℂ →+* S := (algebraMap ℂ E).codRestrict S.toSubring (by
    intro t
    change v (RatFunc.C t) ≤ 1
    by_cases ht : t = 0 <;> simp [v, ht])
  have hk : (algebraMap S E).comp k = algebraMap ℂ E := rfl
  let α := (algebraMap ℂ[X] E).comp (WeightedArcs.arc w c).toRingHom
  let x : vars d → E := fun j ↦ α (MvPolynomial.X j)
  have hα : MvPolynomial.eval₂Hom (algebraMap ℂ E) x = α := by
    apply MvPolynomial.ringHom_ext
    · intro t
      simp [α, WeightedArcs.arc]
      exact IsScalarTower.algebraMap_apply ℂ ℂ[X] E t
    · intro j
      exact MvPolynomial.eval₂Hom_X' ..
  obtain ⟨i,b,hb⟩ := coefficient_factors_on_valuation d k hk x n s
  change MvPolynomial.eval₂Hom (algebraMap ℂ E) x _ =
    algebraMap S E b * (MvPolynomial.eval₂Hom (algebraMap ℂ E) x _) ^ n at hb
  rw [hα] at hb
  change v (α _) ≤ _
  rw [hb, map_mul, map_pow]
  have hreg : v (algebraMap S E b) ≤ 1 := b.property
  have hmon : v (α (MvPolynomial.monomial (exponents d i) 1)) ≤ WithZero.exp (B : ℤ) :=
    (infinity_arc_monomial_le d w c i).trans (WithZero.exp_le_exp.mpr (by exact_mod_cast hB i))
  calc
    _ ≤ (1 : WithZero (Multiplicative ℤ)) * WithZero.exp (B : ℤ) ^ n :=
      mul_le_mul' hreg (pow_le_pow_left' hmon n)
    _ = _ := by simp [WithZero.exp, Nat.cast_mul, mul_comm]

set_option maxHeartbeats 1000000 in
/-- Every global section obeys the weighted degree budget. Test its coefficient
on monomial curves and use regularity in the chart at infinity. -/
theorem supportBound_via_monomial_curves (d : BridgeData) (n : ℕ)
    (e : AffineJetCoefficientInterface.Frame (affineChart d) (hyperplane d))
    (s : AffineJetCoefficientInterface.Sections (hyperplane d) n) :
    WeightedSliceDegree.SupportBound (fun i ↦ (d.W i : ℝ)) ((n : ℝ) * (scale d).radius)
      (AffineJetCoefficientInterface.coefficient (affineChart d) (hyperplane d) n e s) := by
  classical
  obtain ⟨D, hD, w, _, hw⟩ := exists_integer_weights d.W d.W_pos
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hbudget (i : Index d) : Finsupp.weight w (exponents d i) ≤ D * (scale d).radius := by
    have h : (∑ j, (d.W j : ℝ) * (exponents d i j : ℝ)) ≤ (scale d).radius := by
      exact_mod_cast (scale d).budget d.W_pos i
    have h' : Finsupp.weight (fun j ↦ (d.W j : ℝ)) (exponents d i) ≤ (scale d).radius := by
      simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using h
    rw [real_weight_eq_integer_div d.W w D _ hw, div_le_iff₀ hD', mul_comm] at h'
    exact_mod_cast h'
  have hcan : WeightedSliceDegree.SupportBound (fun i ↦ (d.W i : ℝ)) ((n : ℝ) * (scale d).radius)
      (canonicalPolynomial d n s) := by
    intro a ha
    rw [real_weight_eq_integer_div d.W w D a hw, div_le_iff₀ hD']
    have h := canonical_weight_le d w _ hbudget n s a ha
    have h' : (Finsupp.weight w a : ℝ) ≤ (n : ℝ) * ((D : ℝ) * (scale d).radius) := by exact_mod_cast h
    linarith
  let j := affineChart d
  let V := j.opensRange
  let F := AffineJetCoefficientFrame.untwistPowerFrame (hyperplane d) V e n
  obtain ⟨u, hu⟩ := pointValue_overlap (chart d) j.isoOpensRange.hom
    ((chart_fac d).trans j.isoOpensRange_hom_ι.symm)
    (coordinatePowerFrame (coord d (constantIndex d)) n) F
  have hcoeff := hu s
  have heq : AffineJetCoefficientInterface.coefficient j (hyperplane d) n e s =
      pointValue j.isoOpensRange.hom (coefficient F (restrictSection V.ι s)) := by
    unfold AffineJetCoefficientInterface.coefficient AffineJetPolynomial.polynomialCoefficient
    erw [AffineJetCoefficientFrame.globalSectionCoefficient_eq]
    exact congrArg (pointValue j.isoOpensRange.hom)
      (V.topIso.hom_inv_id_apply (coefficient F (restrictSection V.ι s)))
  have hu' : AffineJetCoefficientInterface.coefficient j (hyperplane d) n e s =
      (u : P d) * canonicalPolynomial d n s := heq.trans hcoeff
  rw [hu']
  exact WeightedFrameDegree.supportBound_unit_mul _ _ _ _ u.isUnit hcan

end
end PiTwoCaseBridge.MonomialDegree
