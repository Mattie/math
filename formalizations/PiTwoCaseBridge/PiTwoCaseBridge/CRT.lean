import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import OAI.NumberTheory.PiExponent.Jets.JetPowerIdealCoprime

/-!
# Fixed-cutoff simultaneous monomial lifts

Positive integral weights dominate ordinary total degree. Thus the ordinary
Chinese remainder theorem for powers of distinct point ideals prescribes
every coefficient below a fixed weighted cutoff, in arbitrary polynomial
charts centered at those points.
-/

namespace PiTwoCaseBridge

open MvPolynomial OAI.PiExponent

variable {σ K J : Type*} [Field K]

private theorem degree_le_positive_weight (v : σ → ℕ) (hv : ∀ i, 0 < v i)
    (α : σ →₀ ℕ) : α.degree ≤ Finsupp.weight v α := by
  classical
  rw [Finsupp.degree_apply, Finsupp.weight_apply]
  exact Finset.sum_le_sum fun i _ => Nat.le_mul_of_pos_right _ (hv i)

/-- A polynomial in the ordinary origin ideal to power `M` has zero
coefficients in every positive integral weight strictly below `M`. -/
theorem coeff_eq_zero_of_mem_origin_pow (v : σ → ℕ) (hv : ∀ i, 0 < v i)
    {M : ℕ} {p : MvPolynomial σ K} (hp : p ∈ idealOfVars σ K ^ M)
    (α : σ →₀ ℕ) (hα : Finsupp.weight v α < M) : p.coeff α = 0 :=
  (mem_pow_idealOfVars_iff' M p).mp hp α ((degree_le_positive_weight v hv α).trans_lt hα)

/-- Transport ordinary vanishing at the center to weighted vanishing in its chart. -/
theorem chart_coeff_eq_zero_of_mem_point_pow (v : σ → ℕ) (hv : ∀ i, 0 < v i)
    (c : σ → K) (E : MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K)
    (hE : ∀ p, aeval (0 : σ → K) (E p) = aeval c p)
    {M : ℕ} {p : MvPolynomial σ K} (hp : p ∈ WeightedBezout.pointIdeal c ^ M)
    (α : σ →₀ ℕ) (hα : Finsupp.weight v α < M) : (E p).coeff α = 0 := by
  have horigin : WeightedBezout.pointIdeal (0 : σ → K) = idealOfVars σ K := by
    simp [WeightedBezout.pointIdeal_eq_span, idealOfVars]
  have hmap : Ideal.map E.toRingHom (WeightedBezout.pointIdeal c) ≤ idealOfVars σ K := by
    rw [Ideal.map_le_iff_le_comap]
    intro q hq
    change E q ∈ idealOfVars σ K
    rw [← horigin, WeightedBezout.mem_pointIdeal, hE]
    exact hq
  apply coeff_eq_zero_of_mem_origin_pow v hv _ α hα
  have hmem := Ideal.mem_map_of_mem E.toRingHom hp
  rw [Ideal.map_pow] at hmem
  exact (pow_le_pow_left' hmap M) hmem

/-- Simultaneous CRT in centered charts, for arbitrary prescribed local polynomials. -/
theorem exists_crt_chart_lift [Finite J] (v : σ → ℕ) (hv : ∀ i, 0 < v i)
    (c : J → σ → K) (hc : Function.Injective c)
    (E : J → MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K)
    (hE : ∀ j p, aeval (0 : σ → K) (E j p) = aeval (c j) p)
    (M : ℕ) (target : J → MvPolynomial σ K) :
    ∃ p : MvPolynomial σ K, ∀ j α, Finsupp.weight v α < M →
      (E j p).coeff α = (target j).coeff α := by
  classical
  have hcop : Pairwise (fun i j =>
      IsCoprime (WeightedBezout.pointIdeal (c i) ^ M) (WeightedBezout.pointIdeal (c j) ^ M)) := by
    intro i j hij
    apply IsCoprime.pow
    apply Ideal.isCoprime_of_isMaximal
    exact fun heq => hij (hc (JetPowerIdealCoprime.pointIdeal_injective heq))
  obtain ⟨p, hp⟩ := Ideal.exists_forall_sub_mem_ideal hcop (fun j => (E j).symm (target j))
  refine ⟨p, fun j α hα => ?_⟩
  have hzero := chart_coeff_eq_zero_of_mem_point_pow v hv (c j) (E j) (hE j) (hp j) α hα
  simpa only [map_sub, AlgEquiv.apply_symm_apply, coeff_sub, sub_eq_zero] using hzero

/-- All monomials below a fixed cutoff have simultaneous delta lifts, and one
source weighted-degree bound works for the entire finite family. -/
theorem exists_bounded_crt_monomial_lifts [Finite J] [Finite σ] [DecidableEq J]
    (W v : σ → ℕ) (hv : ∀ i, 0 < v i)
    (c : J → σ → K) (hc : Function.Injective c)
    (E : J → MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K)
    (hE : ∀ j p, aeval (0 : σ → K) (E j p) = aeval (c j) p) (M : ℕ) :
    ∃ B : ℕ, ∃ lifts : J → (σ →₀ ℕ) → MvPolynomial σ K,
      ∀ j β, Finsupp.weight v β < M →
        (lifts j β).weightedTotalDegree W ≤ B ∧ ∀ k α, Finsupp.weight v α < M →
          (E k (lifts j β)).coeff α =
            (if k = j then monomial β 1 else 0 : MvPolynomial σ K).coeff α := by
  classical
  choose lifts hlifts using fun (j : J) (β : σ →₀ ℕ) =>
    exists_crt_chart_lift v hv c hc E hE M
      (fun k => if k = j then monomial β 1 else 0)
  let := Fintype.ofFinite J
  let small := (Finsupp.finite_of_nat_weight_lt v (fun i => (hv i).ne') M).toFinset
  refine ⟨Finset.univ.sup (fun j : J => small.sup (fun β => (lifts j β).weightedTotalDegree W)),
    lifts, fun j β hβ => ⟨?_, hlifts j β⟩⟩
  have hmem : β ∈ small := by simpa [small] using hβ
  exact (Finset.le_sup (f := fun γ => (lifts j γ).weightedTotalDegree W) hmem).trans
    (Finset.le_sup (f := fun k : J => small.sup (fun γ => (lifts k γ).weightedTotalDegree W))
      (Finset.mem_univ j))

end PiTwoCaseBridge
