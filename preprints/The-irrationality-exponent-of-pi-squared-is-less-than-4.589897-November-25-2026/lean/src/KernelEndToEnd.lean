import KernelBridge
import KernelContent

/-!
# A common divisor of both integer coefficients

`translated_prime_dvd` applies the residue cancellations to the normalized
first column of Leibtag et al. At each positive level the same two integers
are divisible by every eligible prime. Since these primes are distinct,
`published_column_factor` divides both integers by their full product.
-/

open Finset Zeta2Blueprint Zeta2NextTwo Zeta2ArithmeticNormalization
noncomputable section

namespace PrimeNumerator.KernelEndToEnd

/-- Each translated prime divides both entries of the very same normalized
integer column used in the published irrationality-measure argument. -/
theorem translated_prime_dvd {N p : ℕ} [Fact p.Prime] (pn : p < N)
    (hp2 : 50*N < p^2) (hs : InShell (N%p) 0 p)
    {z : Fin 2 → ℤ} (hz : KernelContent.PublishedColumn N z) :
    ∀ i, (p : ℤ) ∣ z i := by
  let A := 2*N/p+1
  have hshift := Bounds.harmonic_shift pn hp2
  change 2*N < A*p ∧ A*p < 3*N ∧ A+11*N/p < p at hshift
  have hN : 1 ≤ N := by omega
  obtain ⟨hfield, hfull, hpartial⟩ := KernelBridge.sums_translated N p pn hp2 hs
  have hcoef := KernelBridge.residue_translated N p pn hp2 hs
  have heval := KernelBridge.evaluation_translated N p pn hp2 hs
  have hpoly := KernelNumerator.kernel_divided_translated N 0 p hN (by decide) pn hp2
    (Qpoly N p) hcoef heval
  have hJ := KernelNumerator.J_val_translated N 0 p hN (by decide) hp2 (hexp N p) A
    (Qpoly N p) (by simpa only [pow_zero, one_mul] using hfield) hpoly
  have hH := KernelNumerator.harmonic_val_translated N 0 p hp2 A (by omega) (Qpoly N p)
    (by simpa only [pow_zero, one_mul] using hfull)
    (by simpa only [pow_zero, one_mul] using hpartial) hcoef
  exact KernelContent.prime_dvd_published pn hp2 hshift.1.le (by omega) hH hJ hz

/-- Choose the two integers once at each positive level. The same entries
are divisible by every eligible translated prime at that level. -/
theorem published_pair_content (N : ℕ) (hN : 1 ≤ N) :
    ∃ z : Fin 2 → ℤ, KernelContent.PublishedColumn N z ∧
      ∀ p : ℕ, p.Prime → p < N → 50*N < p^2 → InShell (N%p) 0 p →
        (p : ℤ) ∣ z 0 ∧ (p : ℤ) ∣ z 1 := by
  obtain ⟨z, hz⟩ := KernelContent.published_column_exists N hN
  refine ⟨z, hz, ?_⟩
  intro p pp pn hp2 hs
  let : Fact p.Prime := ⟨pp⟩
  exact ⟨translated_prime_dvd pn hp2 hs hz 0, translated_prime_dvd pn hp2 hs hz 1⟩

/-- All eligible translated primes at level N, each with multiplicity one. -/
def translatedProduct (N : ℕ) : ℕ :=
  ∏ p ∈ (range N).filter (fun p => p.Prime ∧ 50*N < p^2 ∧ InShell (N%p) 0 p), p

/-- Dividing both entries by the complete finite product leaves one integer
column. The factorization is an equality of integers for each entry. -/
theorem published_column_factor {N : ℕ} {z : Fin 2 → ℤ}
    (hz : KernelContent.PublishedColumn N z) :
    ∃ reduced : Fin 2 → ℤ, ∀ i, z i = (translatedProduct N : ℤ) * reduced i := by
  classical
  have hd : ∀ i, (translatedProduct N : ℤ) ∣ z i := by
    intro i
    rw [translatedProduct, Nat.cast_prod]
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      exact ((Nat.coprime_primes (mem_filter.mp hp).2.1 (mem_filter.mp hq).2.1).2 hpq).isCoprime
    · intro p hp
      obtain ⟨hmem, pp, hp2, hs⟩ := mem_filter.mp hp
      let : Fact p.Prime := ⟨pp⟩
      exact translated_prime_dvd (mem_range.mp hmem) hp2 hs hz i
  choose reduced h using hd
  exact ⟨reduced, h⟩

#print axioms published_column_factor
#print axioms translated_prime_dvd
#print axioms published_pair_content

end PrimeNumerator.KernelEndToEnd