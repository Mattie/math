import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Ideal.Operations

/-!
# Finite weighted polynomial reduction

Above a cutoff, homogeneous ideal membership permits reduction by the
generators. Projecting onto the original weight makes each surviving
coefficient monomial exactly one generator degree smaller.
-/

namespace PiTwoCaseBridge

open MvPolynomial

variable {K σ ι : Type*} [Field K]

/-- Products of generators times a monomial below the cutoff, with prescribed total weight. -/
def reductionTerms (w : σ → ℕ) (f : ι → MvPolynomial σ K) (L M n : ℕ) :
    Set (MvPolynomial σ K) :=
  {p | ∃ (ks : List ι) (β : σ →₀ ℕ), Finsupp.weight w β < M ∧
    ks.length * L + Finsupp.weight w β = n ∧ p = (ks.map f).prod * monomial β 1}

private theorem generator_mul_mem_span_reductionTerms
    (w : σ → ℕ) (f : ι → MvPolynomial σ K) (L M n : ℕ) (i : ι)
    {p : MvPolynomial σ K} (hp : p ∈ Submodule.span K (reductionTerms w f L M n)) :
    f i * p ∈ Submodule.span K (reductionTerms w f L M (L + n)) := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ks, β, hβ, hn, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨i :: ks, β, hβ, ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · simp [mul_assoc]
  | zero => simp
  | add _ _ _ _ hx hy => simpa only [mul_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa only [mul_smul_comm] using Submodule.smul_mem _ a hx

/-- Every homogeneous polynomial has an expansion preserving weight at each reduction. -/
theorem homogeneous_mem_span_reductionTerms [Finite ι]
    (w : σ → ℕ) (f : ι → MvPolynomial σ K) (L M : ℕ) (hL : 0 < L)
    (hf : ∀ i, IsWeightedHomogeneous w (f i) L)
    (hcut : ∀ n ≥ M, ∀ p : MvPolynomial σ K, IsWeightedHomogeneous w p n →
      p ∈ Ideal.span (Set.range f))
    (n : ℕ) (p : MvPolynomial σ K) (hp : IsWeightedHomogeneous w p n) :
    p ∈ Submodule.span K (reductionTerms w f L M n) := by
  classical
  let := Fintype.ofFinite ι
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hlow : n < M
    · rw [p.as_sum]
      apply Submodule.sum_mem
      intro β hβ
      have hw : Finsupp.weight w β = n := hp (mem_support_iff.mp hβ)
      have hterm : monomial β (1 : K) ∈ reductionTerms w f L M n :=
        ⟨[], β, hw.trans_lt hlow, by simpa using hw, by simp⟩
      simpa only [smul_monomial, smul_eq_mul, mul_one] using
        (Submodule.span K (reductionTerms w f L M n)).smul_mem (p.coeff β)
          (Submodule.subset_span hterm)
    · obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp
        (hcut n (Nat.le_of_not_gt hlow) p hp)
      rw [← hp.weightedHomogeneousComponent_same, ← hc, map_sum]
      apply Submodule.sum_mem
      intro i _
      have hsplit := congrArg
        (fun t : MvPolynomial σ K => weightedHomogeneousComponent w n (t * f i)) (c i).as_sum
      rw [hsplit]
      rw [Finset.sum_mul, map_sum]
      apply Submodule.sum_mem
      intro β _
      let b : MvPolynomial σ K := monomial β ((c i).coeff β)
      have hb : IsWeightedHomogeneous w b (Finsupp.weight w β) :=
        isWeightedHomogeneous_monomial w β _ rfl
      have hprod := hb.mul (hf i)
      change weightedHomogeneousComponent w n (b * f i) ∈ _
      by_cases hw : n = Finsupp.weight w β + L
      · rw [hw, hprod.weightedHomogeneousComponent_same, mul_comm, Nat.add_comm]
        exact generator_mul_mem_span_reductionTerms w f L M _ i
          (ih _ (by omega) b hb)
      · rw [hprod.weightedHomogeneousComponent_ne n hw]
        exact Submodule.zero_mem _

/-- A monomial of weight n is a finite linear combination of products of q generators
times low monomials, with q times the generator degree plus the residual weight equal to n. -/
theorem monomial_mem_span_reductionTerms [Finite ι]
    (w : σ → ℕ) (f : ι → MvPolynomial σ K) (L M : ℕ) (hL : 0 < L)
    (hf : ∀ i, IsWeightedHomogeneous w (f i) L)
    (hcut : ∀ n ≥ M, ∀ p : MvPolynomial σ K, IsWeightedHomogeneous w p n →
      p ∈ Ideal.span (Set.range f))
    (α : σ →₀ ℕ) :
    monomial α (1 : K) ∈ Submodule.span K (reductionTerms w f L M (Finsupp.weight w α)) :=
  homogeneous_mem_span_reductionTerms w f L M hL hf hcut _ _
    (isWeightedHomogeneous_monomial w α 1 rfl)

end PiTwoCaseBridge
