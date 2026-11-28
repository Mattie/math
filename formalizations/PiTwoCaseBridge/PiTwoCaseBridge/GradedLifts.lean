import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import PiTwoCaseBridge.Reduction
import Mathlib.Tactic.Ring

/-!
# Lifting products of initial forms

Multiplication adds local weights while preserving agreement through the
initial weight. A uniform bound on the degrees of finitely many seed lifts
then gives an affine degree bound for the entire homogeneous reduction.
-/

namespace PiTwoCaseBridge

open MvPolynomial
open scoped Classical

variable {K σ τ ι J : Type*} [Field K]

/-- The target is homogeneous of weight `n` and the two polynomials agree
on every coefficient of weight at most `n`. The target is allowed to be zero. -/
private def InitialAt (w : τ → ℕ) (n : ℕ) (p f : MvPolynomial τ K) : Prop :=
  IsWeightedHomogeneous w f n ∧
    ∀ γ, Finsupp.weight w γ ≤ n → p.coeff γ = f.coeff γ

private theorem InitialAt.mul {w : τ → ℕ} {n m : ℕ} {p q f g : MvPolynomial τ K}
    (hp : InitialAt w n p f) (hq : InitialAt w m q g) :
    InitialAt w (n + m) (p * q) (f * g) := by
  refine ⟨hp.1.mul hq.1, ?_⟩
  intro γ hγ
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨a,b⟩ hab
  have hw : Finsupp.weight w a + Finsupp.weight w b ≤ n + m := by
    rw [← map_add, Finset.mem_antidiagonal.mp hab]
    exact hγ
  by_cases ha : Finsupp.weight w a ≤ n
  · by_cases hb : Finsupp.weight w b ≤ m
    · rw [hp.2 a ha, hq.2 b hb]
    · have hf := hp.1.coeff_eq_zero a (by omega)
      rw [hp.2 a ha, hf, zero_mul, zero_mul]
  · have hb : Finsupp.weight w b < m := by omega
    rw [hq.2 b hb.le, hq.1.coeff_eq_zero b hb.ne, mul_zero, mul_zero]

private theorem initialAt_component {w : τ → ℕ} {n : ℕ} {p : MvPolynomial τ K}
    (hp : ∀ γ, Finsupp.weight w γ < n → p.coeff γ = 0) :
    InitialAt w n p (weightedHomogeneousComponent w n p) := by
  refine ⟨weightedHomogeneousComponent_isWeightedHomogeneous _ _, ?_⟩
  intro γ hγ
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with he
  · rfl
  · exact hp γ (lt_of_le_of_ne hγ he)

private theorem initialAt_list_prod {w : τ → ℕ} {n : ℕ}
    {p f : ι → MvPolynomial τ K} (h : ∀ k, InitialAt w n (p k) (f k)) (ks : List ι) :
    InitialAt w (ks.length * n) (ks.map p).prod (ks.map f).prod := by
  induction ks with
  | nil => exact ⟨by simpa using isWeightedHomogeneous_one K w, by simp⟩
  | cons k ks ih =>
    simpa [Nat.succ_mul, Nat.add_comm] using (h k).mul ih

private theorem degree_mul_le {W : σ → ℕ} {p q : MvPolynomial σ K} :
    weightedTotalDegree W (p * q) ≤ weightedTotalDegree W p + weightedTotalDegree W q := by
  classical
  rw [weightedTotalDegree, Finset.sup_le_iff]
  intro γ hγ
  have hc := mem_support_iff.mp hγ
  rw [coeff_mul] at hc
  obtain ⟨⟨a,b⟩, hab, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  rw [← Finset.mem_antidiagonal.mp hab, map_add]
  exact add_le_add (le_weightedTotalDegree W <| mem_support_iff.mpr <| left_ne_zero_of_mul hn)
    (le_weightedTotalDegree W <| mem_support_iff.mpr <| right_ne_zero_of_mul hn)

private theorem degree_list_prod_le {W : σ → ℕ} {d : ℕ}
    {p : ι → MvPolynomial σ K} (h : ∀ k, weightedTotalDegree W (p k) ≤ d) (ks : List ι) :
    weightedTotalDegree W (ks.map p).prod ≤ ks.length * d := by
  induction ks with
  | nil =>
    simpa using (isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero.mp
      (isWeightedHomogeneous_one K W)).le
  | cons k ks ih =>
    simpa [Nat.succ_mul, Nat.add_comm] using degree_mul_le.trans (add_le_add (h k) ih)

private theorem degree_le_iff_restrictSupport {W : σ → ℕ} {D : ℕ}
    {p : MvPolynomial σ K} :
    weightedTotalDegree W p ≤ D ↔ p ∈ restrictSupport K {a | Finsupp.weight W a ≤ D} := by
  rw [weightedTotalDegree, Finset.sup_le_iff]
  rfl

/-- Attainable targets at a single center form a vector space even when the
source budget and all the required zero coefficients at other centers are fixed. -/
private def attainable (W : σ → ℕ) (V : τ → ℕ) (D n : ℕ)
    (chart : J → MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K) (j : J) :
    Submodule K (MvPolynomial τ K) where
  carrier := {f | ∃ P ∈ restrictSupport K {a | Finsupp.weight W a ≤ D},
    ∀ i γ, Finsupp.weight V γ ≤ n →
      (chart i P).coeff γ = if i = j then f.coeff γ else 0}
  zero_mem' := ⟨0, Submodule.zero_mem _, by simp⟩
  add_mem' := by
    rintro f g ⟨P, hP, hp⟩ ⟨Q, hQ, hq⟩
    refine ⟨P + Q, Submodule.add_mem _ hP hQ, fun i γ hn => ?_⟩
    rw [map_add]
    change (chart i P).coeff γ + (chart i Q).coeff γ =
      if i = j then f.coeff γ + g.coeff γ else 0
    rw [hp i γ hn, hq i γ hn]
    split_ifs <;> simp
  smul_mem' := by
    rintro c f ⟨P, hP, hp⟩
    refine ⟨c • P, Submodule.smul_mem _ c hP, fun i γ hn => ?_⟩
    rw [map_smul, coeff_smul, hp i γ hn, coeff_smul]
    split_ifs <;> simp

/-- Replace each factor in a homogeneous reduction by its source generator
and its residual monomial by a fixed-cutoff CRT lift. Every requested row
through the initial weight is matched by the same polynomial. -/
theorem exists_initial_monomial_lift
    (W : σ → ℕ) (V : τ → ℕ) (L d M B : ℕ) (hL : 0 < L)
    (chart : J → MvPolynomial σ K ≃ₐ[K] MvPolynomial τ K)
    (P : ι → MvPolynomial σ K)
    (hdeg : ∀ k, weightedTotalDegree W (P k) ≤ d)
    (hord : ∀ i k γ, Finsupp.weight V γ < L → (chart i (P k)).coeff γ = 0)
    (seed : ∀ (j : J) (β : τ →₀ ℕ), Finsupp.weight V β < M →
      ∃ Q : MvPolynomial σ K, weightedTotalDegree W Q ≤ B ∧
        ∀ i γ, Finsupp.weight V γ < M → (chart i Q).coeff γ =
          (if i = j then monomial β 1 else 0 : MvPolynomial τ K).coeff γ)
    (j : J) (α : τ →₀ ℕ)
    (hred : monomial α (1 : K) ∈ Submodule.span K
      (reductionTerms V (fun k => weightedHomogeneousComponent V L (chart j (P k)))
        L M (Finsupp.weight V α))) :
    ∃ Q : MvPolynomial σ K,
      L * weightedTotalDegree W Q ≤ d * Finsupp.weight V α + L * B ∧
      ∀ i γ, Finsupp.weight V γ ≤ Finsupp.weight V α →
        (chart i Q).coeff γ = if i = j ∧ γ = α then 1 else 0 := by
  classical
  let n := Finsupp.weight V α
  let C := d * n + L * B
  let f (i : J) (k : ι) := weightedHomogeneousComponent V L (chart i (P k))
  have hterms : reductionTerms V (f j) L M n ⊆ attainable W V (C / L) n chart j := by
    rintro _ ⟨ks, β, hβ, hn, rfl⟩
    obtain ⟨S, hS, hs⟩ := seed j β hβ
    refine ⟨(ks.map P).prod * S, degree_le_iff_restrictSupport.mp ?_, ?_⟩
    · apply (Nat.le_div_iff_mul_le hL).mpr
      rw [Nat.mul_comm]
      calc
        _ ≤ L * (ks.length * d + B) := Nat.mul_le_mul_left L
          (degree_mul_le.trans (add_le_add (degree_list_prod_le hdeg ks) hS))
        _ = d * (ks.length * L) + L * B := by ring
        _ ≤ C := Nat.add_le_add_right (Nat.mul_le_mul_left d (by omega)) _
    · intro i γ hγ
      have hseed : InitialAt V (Finsupp.weight V β) (chart i S)
          (if i = j then monomial β 1 else 0) := by
        refine ⟨?_, fun a ha => hs i a (ha.trans_lt hβ)⟩
        split_ifs
        · exact isWeightedHomogeneous_monomial V β 1 rfl
        · exact isWeightedHomogeneous_zero K V _
      have hprod := initialAt_list_prod
        (fun k => initialAt_component (hord i k)) ks
      have hcoeff := (hprod.mul hseed).2 γ (hn.symm ▸ hγ)
      rw [map_mul, map_list_prod, List.map_map]
      by_cases hij : i = j
      · subst i
        simpa [f, Function.comp_def] using hcoeff
      · simpa [hij, f, Function.comp_def] using hcoeff
  obtain ⟨Q, hQ, hc⟩ := (Submodule.span_le.mpr hterms) hred
  refine ⟨Q, ?_, fun i γ hγ => ?_⟩
  · rw [Nat.mul_comm]
    exact (Nat.le_div_iff_mul_le hL).mp (degree_le_iff_restrictSupport.mpr hQ)
  · rw [hc i γ hγ]
    by_cases hi : i = j
    · simp [hi, coeff_monomial, eq_comm]
    · simp [hi]

end PiTwoCaseBridge
