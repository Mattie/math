import KernelNumerator

/-! Divisibility after the published column-zero normalization, including the
division by the product of the original shell primes. -/

open Finset Zeta2Blueprint Zeta2NextTwo Zeta2ArithmeticNormalization
noncomputable section

namespace PrimeNumerator.KernelContent

/-- Both rows of the integer vector used in the published irrationality
criterion have precisely this rational value. -/
def PublishedColumn (N : ℕ) (z : Fin 2 → ℤ) : Prop :=
  ∀ i, ((CN N * lcmUpTo (12*N) * lcmUpTo (13*N) : ℕ) /
    (GN N * HN N 0 : ℕ) : ℚ) * readout N i 0 = z i

theorem published_column_exists (N : ℕ) (hN : 1 ≤ N) :
    ∃ z : Fin 2 → ℤ, PublishedColumn N z := by
  simpa only [PublishedColumn, Fin.val_zero, Nat.add_zero] using
    Zeta2ArithmeticNormalization.arithmetic_normalization N hN (0 : Fin 3)

/-- Every prime in any original shell is larger than the level. -/
theorem level_lt_of_shell {N r q : ℕ} (hs : InShell N r q) : N < q := by
  unfold InShell at hs
  omega

theorem prime_not_dvd_shell_product {N r p : ℕ} (pp : p.Prime) (hp : p ≤ N) :
    ¬ p ∣ HN N r := by
  intro h
  obtain ⟨q, hq, hdvd⟩ := (Prime.dvd_finsetProd_iff pp.prime _).1 h
  obtain ⟨_, hqprime, _, hs⟩ := mem_filter.mp hq
  have he := (Nat.prime_dvd_prime_iff_eq pp hqprime).mp hdvd
  have hlt := level_lt_of_shell hs
  omega

/-- Multiplying a published integer by the shell product gives its integer
representative before division by HN. -/
theorem baseline_of_published {N : ℕ} {z : Fin 2 → ℤ} (hz : PublishedColumn N z) :
    ∀ i, ((CN N * lcmUpTo (12*N) * lcmUpTo (13*N) : ℕ) / (GN N : ℕ) : ℚ) *
      readout N i 0 = ((HN N 0 : ℤ) * z i : ℤ) := by
  have hH : (HN N 0 : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (prod_ne_zero_iff.2 fun p hp => (mem_filter.1 hp).2.1.ne_zero)
  intro i
  rw [Int.cast_mul, Int.cast_natCast, ← hz i, Nat.cast_mul (GN N) (HN N 0)]
  rw [div_mul_eq_div_div, ← mul_assoc, mul_div_cancel₀ _ hH]

/-- Both entries of every vector representing the published integer pair have
the extra prime divisor once the two local numerator valuations are known. -/
theorem prime_dvd_published {N p A : ℕ} [Fact p.Prime] (pn : p < N) (hp2 : 50*N < p^2)
    (hη₁ : 2*N ≤ A*p) (hη₂ : A*p ≤ 9*N)
    (hH : pInt p (hexp N p + 1) ((p : ℚ)^2 *
      ∑ j ∈ range (11*N + 1), (j : ℚ)^(0 : ℕ) * cj N j * harm2 (j + A*p)))
    (hJ : pInt p (hexp N p + 1) ((p : ℚ)^2 * Jfun (A*p) (Spoly N 0)))
    {z : Fin 2 → ℤ} (hz : PublishedColumn N z) (i : Fin 2) : (p : ℤ) ∣ z i := by
  have pp : p.Prime := Fact.out
  have hb := baseline_of_published hz
  have hd := KernelNumerator.column_zero_divides_translated N p A (by omega) pn hp2 hη₁ hη₂
    hH hJ (fun j => (HN N 0 : ℤ) * z j) hb i
  exact ((pz_prime pp).dvd_or_dvd hd).resolve_left
    (fun h => prime_not_dvd_shell_product pp pn.le (Int.natCast_dvd_natCast.mp h))

#print axioms published_column_exists
#print axioms prime_not_dvd_shell_product
#print axioms prime_dvd_published

end PrimeNumerator.KernelContent