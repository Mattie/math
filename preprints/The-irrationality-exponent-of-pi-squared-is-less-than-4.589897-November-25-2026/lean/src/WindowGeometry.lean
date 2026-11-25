import Zeta2FourTrajectoryMatrices.Blueprint.defs

/-!
# The six translated prime intervals

At level `N` a window selects primes by the location of `N/p`. The index
`j` selects one of six base intervals and `t` translates its endpoints.
For sufficiently large levels, every prime selected in periods 1 through
1,000,000 divides the common product. Distinct positive-period windows are disjoint.
-/

open Finset Zeta2Blueprint

namespace PrimeNumerator.WindowGeometry

def knum : Fin 6 → ℕ := ![2, 3, 4, 5, 6, 12]
def anum : Fin 6 → ℕ := ![1, 2, 3, 3, 4, 8]
def aden : Fin 6 → ℕ := ![8, 9, 10, 8, 9, 9]

/-- Primes with `N/p` strictly between `t + anum/aden` and `t + knum/13`. -/
def window (N t : ℕ) (j : Fin 6) : Finset ℕ :=
  (range (8*N+1)).filter (fun p => p.Prime ∧
    13*N < (13*t+knum j)*p ∧ (aden j*t+anum j)*p < aden j*N)

private theorem quotient_bounds {N t p : ℕ} {j : Fin 6} (hp : p ∈ window N t j) :
    t*p < N ∧ N < (t+1)*p := by
  obtain ⟨_, _, hright, hleft⟩ := mem_filter.mp hp
  have hK : knum j ≤ 13 := by fin_cases j <;> decide
  constructor
  · apply Nat.lt_of_mul_lt_mul_left (a := aden j)
    exact lt_of_le_of_lt (by rw [add_mul, mul_assoc]; omega) hleft
  · apply Nat.lt_of_mul_lt_mul_left (a := 13)
    refine lt_of_lt_of_le hright ?_
    rw [← mul_assoc]
    apply Nat.mul_le_mul_right
    omega

private theorem quotient_eq {N t p : ℕ} {j : Fin 6} (hp : p ∈ window N t j) :
    N/p = t := by
  have hpos := (mem_filter.mp hp).2.1.pos
  obtain ⟨h₁,h₂⟩ := quotient_bounds hp
  have lo := (Nat.le_div_iff_mul_le hpos).2 h₁.le
  have hi := (Nat.div_lt_iff_lt_mul hpos).2 h₂
  omega

private theorem residue_bounds {N t p : ℕ} {j : Fin 6} (hp : p ∈ window N t j) :
    13*(N%p) < knum j*p ∧ anum j*p < aden j*(N%p) := by
  obtain ⟨_, _, hright, hleft⟩ := mem_filter.mp hp
  have heq : t*p + N%p = N := by
    rw [← quotient_eq hp, Nat.mul_comm, Nat.div_add_mod]
  rw [← heq, Nat.mul_add, Nat.add_mul, Nat.mul_assoc] at hright hleft
  omega

theorem window_subset {N i : ℕ} (hN : 50*1000001^2 ≤ N) (hi : i<1000000) (j : Fin 6) :
    window N (i+1) j ⊆ (range N).filter (fun p => p.Prime ∧ 50*N < p^2 ∧ InShell (N%p) 0 p) := by
  intro p hp
  obtain ⟨lo,hi'⟩ := quotient_bounds hp
  have hmul := Nat.mul_le_mul_right p (show i+1+1 ≤ 1000001 by omega)
  have hN' : N < 1000001*p := hi'.trans_le hmul
  have hbig : 50*1000001 ≤ p := by omega
  have hsq : 50*N < p^2 := calc
    50*N < 50*(1000001*p) := by omega
    _ = (50*1000001)*p := by ring
    _ ≤ p^2 := by simpa [pow_two] using Nat.mul_le_mul_right p hbig
  apply mem_filter.mpr
  refine ⟨mem_range.mpr (lt_of_le_of_lt ?_ lo), (mem_filter.mp hp).2.1, hsq, ?_⟩
  · rw [Nat.add_mul, Nat.one_mul]
    omega
  · obtain ⟨hr,hl⟩ := residue_bounds hp
    fin_cases j <;> simp [knum, anum, aden, InShell] at * <;> omega

theorem window_disjoint (N : ℕ) {i k : ℕ} {j l : Fin 6} (hne : (i,j) ≠ (k,l)) :
    Disjoint (window N (i+1) j) (window N (k+1) l) := by
  apply Finset.disjoint_left.mpr
  intro p hj hl
  have eqt := (quotient_eq hj).symm.trans (quotient_eq hl)
  have eik : i = k := by omega
  subst k
  have ene : j ≠ l := fun e => hne (congrArg (Prod.mk i) e)
  obtain ⟨hrj,hlj⟩ := residue_bounds hj
  obtain ⟨hrl,hll⟩ := residue_bounds hl
  fin_cases j <;> fin_cases l <;> simp [knum, anum, aden] at * <;> omega

#print axioms window_subset
#print axioms window_disjoint

end PrimeNumerator.WindowGeometry
