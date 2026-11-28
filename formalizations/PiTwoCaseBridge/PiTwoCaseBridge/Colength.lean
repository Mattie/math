import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Data.Finsupp.Interval
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The local algebra of the two-case interpolation bridge. -/

namespace PiTwoCaseBridge

open MvPolynomial
open scoped BigOperators

variable {σ ι K : Type*} [Field K]

/-- Nullstellensatz supplies one pure power for each variable at an isolated origin. -/
theorem purePowers_of_zeroLocus_origin [Finite σ] [IsAlgClosed K]
    (I : Ideal (MvPolynomial σ K)) (hI : zeroLocus K I = {0}) :
    ∀ i : σ, ∃ n : ℕ, (X i : MvPolynomial σ K) ^ n ∈ I := by
  intro i
  apply Ideal.mem_radical_iff.mp
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := K) I, hI,
    mem_vanishingIdeal_singleton_iff]
  simp

/-- The monomials in a finite coordinate box span the quotient by an ideal
containing a pure power of every variable. -/
theorem finiteColength_of_purePowers [Finite σ] (I : Ideal (MvPolynomial σ K))
    (hI : ∀ i : σ, ∃ n : ℕ, (X i : MvPolynomial σ K) ^ n ∈ I) :
    FiniteDimensional K (MvPolynomial σ K ⧸ I) := by
  classical
  let _ := Fintype.ofFinite σ
  choose n hn using hI
  let bound := Finsupp.equivFunOnFinite.symm n
  let q := Ideal.Quotient.mkₐ K I
  let box := (Finset.Icc 0 bound).image (fun e ↦ q (monomial e 1))
  let S : Submodule K (MvPolynomial σ K ⧸ I) := Submodule.span K (box : Set _)
  refine ⟨⟨box, Submodule.eq_top_iff'.mpr ?_⟩⟩
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K I z
  change q p ∈ S
  induction p using MvPolynomial.induction_on' with
  | monomial e a =>
    by_cases he : e ≤ bound
    · have h : q (monomial e 1) ∈ S :=
        Submodule.subset_span (Finset.mem_image.mpr
          ⟨e, Finset.mem_Icc.mpr ⟨zero_le, he⟩, rfl⟩)
      have heq : monomial e a = a • (monomial e 1 : MvPolynomial σ K) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [heq, map_smul]
      exact S.smul_mem a h
    · have hex : ∃ i, n i ≤ e i := by
        by_contra! h
        exact he (fun i ↦ (h i).le)
      obtain ⟨i, hi⟩ := hex
      have hdiv : (X i : MvPolynomial σ K) ^ n i ∣ monomial e a := by
        rw [X_pow_eq_monomial, monomial_dvd_monomial]
        exact ⟨Or.inr (Finsupp.single_le_iff.mpr hi), one_dvd _⟩
      have hz : q (monomial e a) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (I.mem_of_dvd hdiv (hn i))
      rw [hz]
      exact Submodule.zero_mem _
  | add p r hp hr =>
    rw [map_add]
    exact Submodule.add_mem _ hp hr

theorem finiteColength_of_zeroLocus_origin [Finite σ] [IsAlgClosed K]
    (I : Ideal (MvPolynomial σ K)) (hI : zeroLocus K I = {0}) :
    FiniteDimensional K (MvPolynomial σ K ⧸ I) :=
  finiteColength_of_purePowers I (purePowers_of_zeroLocus_origin I hI)

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- Lifting a finite quotient basis bounds all the degrees it needs.
Projecting to a higher homogeneous piece annihilates every basis lift. -/
theorem exists_weighted_cutoff_of_finiteColength (w : σ → ℕ)
    (g : ι → MvPolynomial σ K) (l : ℕ) (hg : ∀ i, IsWeightedHomogeneous w (g i) l)
    (hfin : FiniteDimensional K (MvPolynomial σ K ⧸ Ideal.span (Set.range g))) :
    ∃ N : ℕ, ∀ d ≥ N, ∀ f : MvPolynomial σ K,
      IsWeightedHomogeneous w f d → f ∈ Ideal.span (Set.range g) := by
  classical
  let I := Ideal.span (Set.range g)
  let Q := MvPolynomial σ K ⧸ I
  let q := Ideal.Quotient.mkₐ K I
  let A := weightedHomogeneousSubmodule K w
  have hhom : I.IsHomogeneous A := by
    apply (Ideal.IsHomogeneous.iff_exists A I).mpr
    let G : ι → SetLike.homogeneousSubmonoid A := fun i ↦ ⟨g i, l, hg i⟩
    exact ⟨Set.range G, by rw [← Set.range_comp']⟩
  let b := Module.finBasis K Q
  choose v hv using fun i ↦ Ideal.Quotient.mkₐ_surjective K I (b i)
  let B := Finset.univ.sup (fun i ↦ weightedTotalDegree w (v i))
  refine ⟨B+1, ?_⟩
  intro d hd f hf
  let c := b.repr (q f)
  have hrel : f - ∑ i, c i • v i ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (f - ∑ i, c i • v i) = 0
    rw [map_sub, map_sum]
    simp only [map_smul, q, hv]
    exact sub_eq_zero.mpr (b.sum_repr _).symm
  have hz (i) : weightedHomogeneousComponent w d (v i) = 0 := by
    apply weightedHomogeneousComponent_eq_zero
    have hi : weightedTotalDegree w (v i) ≤ B :=
      Finset.le_sup (s := Finset.univ) (f := fun j ↦ weightedTotalDegree w (v j))
        (Finset.mem_univ i)
    omega
  have hcomp := weightedHomogeneousComponent_mem_of_mem K w hhom hrel d
  simpa [map_sum, map_smul, hf.weightedHomogeneousComponent_same, hz] using hcomp

/-- A simultaneous positive cutoff for finitely many isolated initial-form systems. -/
theorem exists_common_weighted_cutoff_of_zeroLocus_origin {J : Type*} [Finite J] [Finite σ]
    [IsAlgClosed K] (w : σ → ℕ) (g : J → ι → MvPolynomial σ K) (l : ℕ)
    (hg : ∀ j i, IsWeightedHomogeneous w (g j i) l)
    (hz : ∀ j, zeroLocus K (Ideal.span (Set.range (g j))) = {0}) :
    ∃ N : ℕ, 0 < N ∧ ∀ j d, N ≤ d → ∀ f : MvPolynomial σ K,
      IsWeightedHomogeneous w f d → f ∈ Ideal.span (Set.range (g j)) := by
  classical
  let _ := Fintype.ofFinite J
  choose n hn using fun j ↦ exists_weighted_cutoff_of_finiteColength w (g j) l (hg j)
    (finiteColength_of_zeroLocus_origin _ (hz j))
  refine ⟨Finset.univ.sup n + 1, Nat.succ_pos _, ?_⟩
  intro j d hd
  apply hn j d
  exact (Finset.le_sup (Finset.mem_univ j)).trans (Nat.le_of_succ_le hd)

end PiTwoCaseBridge

/-! ## Two quadratic systems with the same positive weights -/

namespace PiTwoCaseBridge.QuadricTests

open MvPolynomial

noncomputable section

abbrev Poly := MvPolynomial Bool ℂ
abbrev weights : Bool → ℕ := fun _ ↦ 2

def pair : Bool → Poly
  | false => X false ^ 2 - X true ^ 2
  | true => X false ^ 2 + X true ^ 2

private theorem varHom (b : Bool) : IsWeightedHomogeneous weights (X b : Poly) 2 :=
  isWeightedHomogeneous_X ℂ weights b

theorem pair_homogeneous (b : Bool) : IsWeightedHomogeneous weights (pair b) 4 := by
  cases b
  · exact ((varHom false).pow 2).sub ((varHom true).pow 2)
  · exact ((varHom false).pow 2).add ((varHom true).pow 2)

theorem pair_zeroLocus : zeroLocus ℂ (Ideal.span (Set.range pair)) = {0} := by
  rw [zeroLocus_span]
  ext z
  simp only [Set.mem_ofPred_eq, Set.forall_mem_range, Set.mem_singleton_iff]
  constructor
  · intro h
    have hsub : z false ^ 2 - z true ^ 2 = 0 := by simpa [pair] using h false
    have hadd : z false ^ 2 + z true ^ 2 = 0 := by simpa [pair] using h true
    have heq := sub_eq_zero.mp hsub
    rw [heq, ← two_mul] at hadd
    have hy := (mul_eq_zero.mp hadd).resolve_left two_ne_zero
    funext b
    cases b
    · exact sq_eq_zero_iff.mp (heq.trans hy)
    · exact sq_eq_zero_iff.mp hy
  · rintro rfl b
    cases b <;> simp [pair]

theorem pair_finiteColength : FiniteDimensional ℂ (Poly ⧸ Ideal.span (Set.range pair)) :=
  finiteColength_of_zeroLocus_origin _ pair_zeroLocus

theorem pair_cutoff : ∃ N : ℕ, ∀ d ≥ N, ∀ f : Poly,
    IsWeightedHomogeneous weights f d → f ∈ Ideal.span (Set.range pair) :=
  exists_weighted_cutoff_of_finiteColength weights pair 4 pair_homogeneous pair_finiteColength

def badPair : Bool → Poly
  | false => X false ^ 2
  | true => X false * X true

/-- The point (0, 1) detects every missing power of the second variable. -/
theorem badPair_misses_powers (n : ℕ) :
    (X true : Poly) ^ n ∉ Ideal.span (Set.range badPair) := by
  let z : Bool → ℂ := fun b ↦ if b then 1 else 0
  have hz : z ∈ zeroLocus ℂ (Ideal.span (Set.range badPair)) := by
    rw [zeroLocus_span]
    simp only [Set.mem_ofPred_eq, Set.forall_mem_range]
    intro b
    cases b <;> simp [badPair, z]
  intro h
  have := mem_zeroLocus_iff.mp hz _ h
  simp [z] at this

theorem badPair_infiniteColength : ¬ FiniteDimensional ℂ (Poly ⧸ Ideal.span (Set.range badPair)) := by
  intro hfin
  have hom (b : Bool) : IsWeightedHomogeneous weights (badPair b) 4 := by
    cases b
    · exact (varHom false).pow 2
    · exact (varHom false).mul (varHom true)
  obtain ⟨N, hN⟩ := exists_weighted_cutoff_of_finiteColength weights badPair 4 hom hfin
  apply badPair_misses_powers N
  exact hN (N • 2) (by change N ≤ N * 2; omega) _ ((varHom true).pow N)

/-- Equal positive source cost and local weight force the reduction slope to one. -/
theorem boundary_no_saving (l : ℚ) (hl : 0 < l) :
    ¬ ∃ κ : ℚ, κ < 1 ∧ l ≤ κ * l := by
  rintro ⟨κ, hκ, h⟩
  exact (not_lt_of_ge h) (by simpa using mul_lt_mul_of_pos_right hκ hl)

end
end PiTwoCaseBridge.QuadricTests
