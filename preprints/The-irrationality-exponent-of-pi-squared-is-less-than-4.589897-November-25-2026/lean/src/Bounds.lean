import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Elementary interpolation and harmonic cutoffs for translated primes. -/
namespace PrimeNumerator.Bounds

theorem prime_large {p n : ℕ} (hpn : p < n) (h : 50*n < p^2) : 50 < p := by
  by_contra! bad
  have upper := Nat.mul_le_mul_left p bad
  nlinarith

/-- This K supplies the three numerical conclusions of the original shellK
lemma for any of the three column indices, throughout the translated range. -/
theorem interpolation {p n j : ℕ} (hpn : p < n) (h : 50*n < p^2) (hj : j < 3) :
    let K := (p-1)/3
    2 ≤ K ∧ 13*n+j < p*K ∧ 3*K+1 ≤ p := by
  have large := prime_large hpn h
  let K := (p-1)/3
  change 2 ≤ K ∧ 13*n+j < p*K ∧ 3*K+1 ≤ p
  have frac : 3*p ≤ 10*K := by dsimp [K]; omega
  have bound := Nat.mul_le_mul_left p frac
  exact ⟨by dsimp [K]; omega, by nlinarith, by dsimp [K]; omega⟩

/-- One admissible block-aligned harmonic argument, with distinct high poles. -/
theorem harmonic_shift {p n : ℕ} (hpn : p < n) (h : 50*n < p^2) :
    let A := 2*n/p+1
    2*n < A*p ∧ A*p < 3*n ∧ A+11*n/p < p := by
  have large := prime_large hpn h
  have pos : 0 < p := by omega
  have low := Nat.mod_add_div (2*n) p
  have rem := Nat.mod_lt (2*n) pos
  have high := Nat.div_mul_le_self (11*n) p
  have a1 : 2*n < (2*n/p+1)*p := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2*n/p) p]
    omega
  have a2 : (2*n/p+1)*p < 3*n := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (2*n/p) p]
    omega
  refine ⟨a1, a2, ?_⟩
  apply (Nat.mul_lt_mul_right pos).mp
  rw [Nat.add_mul]
  nlinarith

#print axioms prime_large
#print axioms interpolation
#print axioms harmonic_shift
end PrimeNumerator.Bounds
