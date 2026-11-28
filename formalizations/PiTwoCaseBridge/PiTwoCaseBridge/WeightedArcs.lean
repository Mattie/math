import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import OAI.NumberTheory.PiExponent.Jets.JetPowerIdealCoprime
import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalCurveDegree
import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalPowerPresentation

namespace PiTwoCaseBridge
namespace WeightedArcs

noncomputable section

open MvPolynomial
open scoped Polynomial

variable {σ K : Type*} [Field K]

/-- Substitution along the affine arc with integral weights `w` and direction `c`. -/
def arc (w : σ → ℕ) (c : σ → K) : MvPolynomial σ K →ₐ[K] K[X] :=
  aeval fun i => Polynomial.C (c i) * Polynomial.X ^ w i

theorem arc_monomial (w : σ → ℕ) (c : σ → K) (d : σ →₀ ℕ) (r : K) :
    arc w c (monomial d r) =
      Polynomial.C (eval c (monomial d r)) * Polynomial.X ^ Finsupp.weight w d := by
  classical
  simp only [arc, aeval_monomial, eval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Polynomial.algebraMap_eq, map_mul, map_prod, map_pow, ← pow_mul, ← Finset.prod_pow_eq_pow_sum,
    Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul]
  simp [Nat.mul_comm, mul_assoc]

/-- The coefficient of `h^n` measures precisely the degree-`n` part in this direction. -/
theorem coeff_arc (w : σ → ℕ) (c : σ → K) (p : MvPolynomial σ K) (n : ℕ) :
    (arc w c p).coeff n = eval c (weightedHomogeneousComponent w n p) := by
  classical
  rw [weightedHomogeneousComponent_apply, map_sum, Finset.sum_filter]
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, Polynomial.finsetSum_coeff, arc_monomial, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp_all [eq_comm]

/-- The pure powers defining the center in its polynomial coordinates. -/
def powerIdeal (e : σ → ℕ) : Ideal (MvPolynomial σ K) :=
  Ideal.span (Set.range fun i => X i ^ e i)

theorem map_powerIdeal (w e : σ → ℕ) (R : ℕ) (hR : ∀ i, w i * e i = R)
    (c : σ → K) (hc : c ≠ 0) :
    (powerIdeal (K := K) e).map (arc w c).toRingHom =
      Ideal.span ({Polynomial.X ^ R} : Set K[X]) := by
  classical
  have hgen (i : σ) : arc w c (X i ^ e i) = Polynomial.C (c i ^ e i) * Polynomial.X ^ R := by
    simp [arc, mul_pow, ← pow_mul, hR]
  have hspan : (powerIdeal (K := K) e).map (arc w c).toRingHom =
      Ideal.span (Set.range fun i => Polynomial.C (c i ^ e i) * Polynomial.X ^ R) := by
    rw [powerIdeal, Ideal.map_span, ← Set.range_comp]
    simp only [Function.comp_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hgen]
  rw [hspan]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
  · have ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra! h
      exact hc (funext h)
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    have h := Ideal.subset_span (s := Set.range fun j => Polynomial.C (c j ^ e j) *
      (Polynomial.X : K[X]) ^ R) (Set.mem_range_self i)
    have := Ideal.mul_mem_left _ (Polynomial.C ((c i ^ e i)⁻¹)) h
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ (pow_ne_zero _ hi), map_one, one_mul] at this

/-- Divisibility along the nonzero arcs detects the entire low-weight filtration. -/
theorem component_eq_zero_of_arc_dvd [Nonempty σ] [Infinite K]
    (w : σ → ℕ) (p : MvPolynomial σ K) (N : ℕ)
    (h : ∀ c : σ → K, c ≠ 0 → Polynomial.X ^ N ∣ arc w c p) (n : ℕ) (hn : n < N) :
    weightedHomogeneousComponent w n p = 0 := by
  classical
  apply MvPolynomial.funext_set (fun _ => ({0} : Set K)ᶜ)
    (fun _ => (Set.finite_singleton (0 : K)).infinite_compl)
  intro c hc
  have hne : c ≠ 0 := by
    intro he
    obtain ⟨i⟩ := ‹Nonempty σ›
    exact hc i (Set.mem_univ _) (by simp [he])
  rw [← coeff_arc, map_zero]
  exact Polynomial.X_pow_dvd_iff.mp (h c hne) n hn

/-- The formal arc in the original affine variables. The triangular substitution expresses
those variables in the polynomial coordinates centered at `p`. -/
def seriesArc {m : ℕ} (p : Fin m → K) (G : Fin m → Polynomial K)
    (w : Fin (m+1) → ℕ) (c : Fin (m+1) → K) :
    MvPolynomial (Fin (m+1)) K →+* PowerSeries K :=
  Polynomial.coeToPowerSeries.ringHom.comp ((arc w c).comp
    (OAI.PiExponent.AlgebraicJetPackets.triangularMap p G)).toRingHom

open OAI.PiExponent

theorem map_centerPowerIdeal {m : ℕ} (p : Fin m → K) (G : Fin m → Polynomial K)
    (w e : Fin (m+1) → ℕ) (R : ℕ) (hR : ∀ i, w i * e i = R)
    (c : Fin (m+1) → K) (hc : c ≠ 0) :
    (CompactJetPolynomial.powerIdeal p G e).map (seriesArc p G w c) =
      Ideal.span ({PowerSeries.X ^ R} : Set (PowerSeries K)) := by
  have he : CompactJetPolynomial.powerIdeal p G e =
      (powerIdeal (K := K) e).map (AlgebraicJetPackets.inverseTriangularMap p G).toRingHom := by
    rw [powerIdeal, Ideal.map_span, ← Set.range_comp]
    simp [CompactJetPolynomial.powerIdeal, CompactJetPolynomial.coordinates, Function.comp_def]
  have hcomp : (seriesArc p G w c).comp (AlgebraicJetPackets.inverseTriangularMap p G).toRingHom =
      Polynomial.coeToPowerSeries.ringHom.comp (arc w c).toRingHom := by
    apply RingHom.ext
    intro x
    change (↑(arc w c (((AlgebraicJetPackets.triangularMap p G).comp
      (AlgebraicJetPackets.inverseTriangularMap p G)) x)) : PowerSeries K) = _
    rw [AlgebraicJetPackets.triangularMap_comp_inverse]
    rfl
  rw [he, Ideal.map_map, hcomp, ← Ideal.map_map, map_powerIdeal w e R hR c hc,
    Ideal.map_span, Set.image_singleton]
  simp

/-- At a nonzero formal direction the full simultaneous center has precisely the
same pullback as the selected center. All the other factors become units. -/
theorem map_centerIdeal {ι : Type*} [Fintype ι] {m : ℕ} (p : ι → Fin m → ℂ)
    (hp : Function.Injective p) (T : Fin m → ℕ) (j : ι)
    (w e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) (R : ℕ) (hpos : 0 < R)
    (hR : ∀ i, w i * e i = R) (c : Fin (m+1) → ℂ) (hc : c ≠ 0) :
    (CompactLogJetIdeal.polynomialIdeal p T e).map
      (seriesArc (p j) (CompactJetPolynomial.logPolynomials T) w c) =
      Ideal.span ({PowerSeries.X ^ R} : Set (PowerSeries ℂ)) := by
  classical
  let G := CompactJetPolynomial.logPolynomials T
  let f := seriesArc (p j) G w c
  let I := fun k => CompactJetPolynomial.powerIdeal (p k) G e
  have hsel : (I j).map f = _ := map_centerPowerIdeal (p j) G w e R hR c hc
  have hproper : (I j).map f ≠ ⊤ := by
    intro htop
    rw [hsel] at htop
    have hu := Ideal.span_singleton_eq_top.mp htop
    have hz := hu.map (PowerSeries.constantCoeff (R := ℂ))
    simp [zero_pow hpos.ne'] at hz
  change Ideal.mapHom f (∏ k, I k) = _
  rw [map_prod, Finset.prod_eq_single j]
  · exact hsel
  · intro k _ hkj
    rw [Ideal.one_eq_top]
    change (I k).map f = ⊤
    by_contra hn
    have hsup : I k ⊔ I j = ⊤ :=
      (JetPowerIdealCoprime.powerIdeal_pairwise_isCoprime p hp G
        (CompactJetPolynomial.logPolynomials_eval_zero T) e he hkj).sup_eq
    have hm : (I k).map f ⊔ (I j).map f = ⊤ := by rw [← Ideal.map_sup, hsup, Ideal.map_top]
    exact (IsLocalRing.maximalIdeal.isMaximal (PowerSeries ℂ)).ne_top
      (top_le_iff.mp (hm ▸ sup_le (IsLocalRing.le_maximalIdeal hn)
        (IsLocalRing.le_maximalIdeal hproper)))
  · simp

/-- Equality of the generated ideal along an arc gives both the order bound and a
nonvanishing leading coefficient for some member of the generating family. -/
theorem initialForms_of_series_span {ι : Type*} [Nonempty σ] [Infinite K]
    (w : σ → ℕ) (P : ι → MvPolynomial σ K) (N : ℕ)
    (h : ∀ c : σ → K, c ≠ 0 →
      Ideal.span (Set.range fun k => (↑(arc w c (P k)) : PowerSeries K)) =
        Ideal.span {PowerSeries.X ^ N}) :
    (∀ k n, n < N → weightedHomogeneousComponent w n (P k) = 0) ∧
    ∀ c : σ → K, c ≠ 0 → ∃ k, eval c (weightedHomogeneousComponent w N (P k)) ≠ 0 := by
  have hlow (c : σ → K) (hc : c ≠ 0) (k : ι) :
      PowerSeries.X ^ N ∣ (↑(arc w c (P k)) : PowerSeries K) := by
    apply Ideal.mem_span_singleton.mp
    rw [← h c hc]
    exact Ideal.subset_span (Set.mem_range_self k)
  constructor
  · intro k n hn
    apply component_eq_zero_of_arc_dvd w (P k) N _ n hn
    intro c hc
    exact Polynomial.X_pow_dvd_iff.mpr fun d hd =>
      (Polynomial.coeff_coe _ _).symm.trans (PowerSeries.X_pow_dvd_iff.mp (hlow c hc k) d hd)
  · intro c hc
    by_contra! hall
    have hsm : Ideal.span (Set.range fun k => (↑(arc w c (P k)) : PowerSeries K)) ≤
        Ideal.span {PowerSeries.X ^ (N+1)} := by
      apply Ideal.span_le.mpr
      rintro _ ⟨k, rfl⟩
      apply Ideal.mem_span_singleton.mpr
      apply PowerSeries.X_pow_dvd_iff.mpr
      intro d hd
      obtain hd | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd)
      · exact PowerSeries.X_pow_dvd_iff.mp (hlow c hc k) d hd
      · rw [Polynomial.coeff_coe, coeff_arc, hall]
    rw [h c hc] at hsm
    have hd := Ideal.mem_span_singleton.mp (hsm (Ideal.subset_span (Set.mem_singleton _)))
    have hz := PowerSeries.X_pow_dvd_iff.mp hd N (Nat.lt_succ_self _)
    simp at hz


section Sections

open CategoryTheory AlgebraicGeometry TopologicalSpace OAI
open OAI.PiExponentSeshadri.Geometry OAI.PiExponentSeshadri.Frames
open OAI.PiExponentSeshadri.IdealPullback OAI.PiExponent.SectionZeroIdeal
open OAI.PiExponent.SectionImageIdeal OAI.PiExponent.ExceptionalCurveDegree
open OAI.PiExponent.LocalSectionOrder

variable {Y B : Scheme.{0}}

/-- Projecting a section of an exceptional twist multiplies its zero ideal by
the ideal presented by the exceptional inclusion. The assertion is local on the blowup. -/
theorem zeroIdeal_project (I : B.IdealSheafData) (π : Y ⟶ B)
    (J M : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I π J ι)
    (s : GlobalSections Y (J.tensor M).sheaf) :
    zeroIdeal M (s ≫ tensorInclusion J M ι) = zeroIdeal (J.tensor M) s * I.comap π := by
  classical
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation J
  let : J.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData J.sheaf).choose.isQuasicoherent
  rw [← PresentedIdealIso.imageIdealSheaf_eq_comap I π J ι hJ]
  choose U hy e f using common_affine_frames J M
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · intro y
    let V := U y
    let ej := (e y).some
    let em := (f y).some
    let et := tensorFrame J M V.1 ej em
    let a := Scheme.Modules.restrictUnitIso V.1.ι
    rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, zeroIdeal_on_frame M _ V em,
      zeroIdeal_on_frame (J.tensor M) s V et, imageIdealSheaf_on_frame ι V ej]
    change Ideal.span {affineMapCoefficient V a em (s ≫ tensorInclusion J M ι)} =
      Ideal.span {affineMapCoefficient V a et s} * _
    erw [affineMapCoefficient_comp V a et em, ← Ideal.span_singleton_mul_span_singleton,
      show Ideal.span {affineMapCoefficient V et em (tensorInclusion J M ι)} = _ from
        tensor_inclusion_ideal J M ι V ej em]
    rfl

/-- Local evaluation on a one-point-centered affine scheme preserves products of ideal sheaves. -/
private theorem localIdeal_mul {S : Type} [CommRing S] [IsLocalRing S]
    (I J : Y.IdealSheafData) (q : Spec (CommRingCat.of S) ⟶ Y) :
    localIdeal (I * J) q = localIdeal I q * localIdeal J q := by
  let X := Spec (CommRingCat.of S)
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top _⟩
  obtain ⟨V, hV, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show q (IsLocalRing.closedPoint S) ∈ (⊤ : Y.Opens) from trivial)
  have he : U.1 ≤ q ⁻¹ᵁ V := fun x _ =>
    ((IsLocalRing.specializes_closedPoint x).map q.continuous).mem_open V.isOpen hx
  unfold localIdeal
  rw [comap_ideal (I*J) q U ⟨V,hV⟩ he, comap_ideal I q U ⟨V,hV⟩ he,
    comap_ideal J q U ⟨V,hV⟩ he, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
    Ideal.map_mul, Ideal.map_mul]

/-- The coefficients of the projected generating sections on any local arc generate
exactly the pulled-back exceptional ideal power, in every frame of the source twist. -/
theorem projected_span {ιx S : Type} [CommRing S] [IsLocalRing S]
    (I : B.IdealSheafData) (π : Y ⟶ B) (J M : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal I π J ι) (n : ℕ)
    (s : ιx → GlobalSections Y ((J.pow n).tensor M).sheaf)
    (hcov : (⨆ k, sectionOpen Y (s k)) = ⊤)
    (q : Spec (CommRingCat.of S) ⟶ Y) (e : (M.pullback q).sheaf ≅ O _) :
    Ideal.span (Set.range fun k => localCoefficient e (pullbackSection q
      (s k ≫ tensorInclusion (J.pow n) M (idealPowerInclusion J ι n)))) =
      localIdeal I (q ≫ π) ^ n := by
  let L := (J.pow n).tensor M
  let t := fun k => s k ≫ tensorInclusion (J.pow n) M (idealPowerInclusion J ι n)
  let a := fun k => localCoefficient e (pullbackSection q (t k))
  have hs (k : ιx) : Ideal.span {a k} =
      localIdeal (zeroIdeal L (s k)) q * localIdeal I (q ≫ π) ^ n := by
    rw [← zeroIdeal_spec_top (M.pullback q) (pullbackSection q (t k)) e,
      zeroIdeal_pullback]
    change localIdeal (zeroIdeal M (t k)) q = _
    rw [zeroIdeal_project (I^n) π (J.pow n) M (idealPowerInclusion J ι n)
      (PresentedIdealIso.idealPower_presents I π J ι hJ n) (s k), localIdeal_mul]
    unfold localIdeal
    rw [← Scheme.IdealSheafData.comap_comp, comap_pow, Scheme.IdealSheafData.ideal_pow,
      Pi.pow_apply, Ideal.map_pow]
  change Ideal.span (Set.range a) = _
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨k, rfl⟩
    have hle : Ideal.span {a k} ≤ _ := (hs k).le.trans Ideal.mul_le_right
    exact hle (Ideal.subset_span (Set.mem_singleton _))
  · have hx : q (IsLocalRing.closedPoint S) ∈ ⨆ k, sectionOpen Y (s k) := by
      rw [hcov]
      trivial
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp hx
    have hz : localIdeal (zeroIdeal L (s k)) q = ⊤ := by
      apply localIdeal_eq_top_of_not_mem
      change _ ∉ ((zeroIdeal L (s k)).support : Set Y)
      rw [zeroIdeal_support]
      exact fun hn => hn hk
    have heq := hs k
    rw [hz, Ideal.top_mul] at heq
    rw [← heq]
    exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.subset_span (Set.mem_range_self k))

end Sections

end
end WeightedArcs
end PiTwoCaseBridge
