import Lean.Elab.Tactic.Omega

/-! Integer floor identities for the factorials of the actual two kernels.
On factorial arguments in [0,p²), Legendre's formula has only this one floor. -/
namespace PrimeNumerator.KernelDigits

def borrow (x y : Int) : Int := if x < y then 1 else 0

theorem subtract_digits (p A B x y : Int) (hp : 0 < p) (hx : 0 ≤ x) (hxp : x < p)
    (hy : 0 ≤ y) (hyp : y ≤ p) :
    let q := A-B-borrow x y
    let r := x-y+p*borrow x y
    ((p*A+x)-(p*B+y))/p = q ∧ ((p*A+x)-(p*B+y))%p = r := by
  dsimp only
  have decomp : (p*A+x)-(p*B+y) = (x-y+p*borrow x y) + p*(A-B-borrow x y) := by
    rw [Int.mul_sub, Int.mul_sub]
    omega
  have bounds : 0 ≤ x-y+p*borrow x y ∧ x-y+p*borrow x y < p := by
    unfold borrow
    split <;> simp only [Int.mul_one, Int.mul_zero] <;> omega
  rw [decomp, Int.add_mul_ediv_left _ _ (by omega : p ≠ 0), Int.ediv_eq_zero_of_lt bounds.1 bounds.2,
    Int.add_mul_emod_self_left, Int.emod_eq_of_lt bounds.1 bounds.2, Int.zero_add]
  exact ⟨rfl,rfl⟩

def chooseOrder (p n m : Int) : Int := n/p - m/p - (n-m)/p

theorem choose_order (p n m : Int) (hp : 0 < p) :
    chooseOrder p n m = borrow (n%p) (m%p) := by
  have h := (subtract_digits p (n/p) (m/p) (n%p) (m%p) hp
    (Int.emod_nonneg _ (by omega)) (Int.emod_lt_of_pos _ hp)
    (Int.emod_nonneg _ (by omega)) (by have := Int.emod_lt_of_pos m hp; omega)).1
  have ne := Int.emod_add_mul_ediv n p
  have me := Int.emod_add_mul_ediv m p
  have en : p*(n/p)+n%p = n := by omega
  have em : p*(m/p)+m%p = m := by omega
  rw [en, em] at h
  unfold chooseOrder
  omega

theorem gap_order (p s m : Int) (hp : 0 < p) :
    m/p+(s-m-1)/p-s/p = borrow (m%p) (s%p) - 1 := by
  have h := (subtract_digits p (s/p) (m/p) (s%p) (m%p+1) hp
    (Int.emod_nonneg _ (by omega)) (Int.emod_lt_of_pos _ hp)
    (by have := Int.emod_nonneg m (by omega : p ≠ 0); omega)
    (by have := Int.emod_lt_of_pos m hp; omega)).1
  have se := Int.emod_add_mul_ediv s p
  have me := Int.emod_add_mul_ediv m p
  have en : p*(s/p)+s%p-(p*(m/p)+(m%p+1)) = s-m-1 := by omega
  rw [en] at h
  unfold borrow at h ⊢
  split at h <;> split <;> omega

def numeratorOrder (p n s : Int) : Int :=
  chooseOrder p (s+9*n) (8*n) + chooseOrder p (s+10*n) (8*n) +
    chooseOrder p (s+11*n) (8*n)

def carry (p n s : Int) : Int :=
  borrow ((11*n)%p) (s%p) + borrow ((s+9*n)%p) ((8*n)%p) +
    borrow ((s+10*n)%p) ((8*n)%p) + borrow ((s+11*n)%p) ((8*n)%p)

theorem coefficient_floor_order (p n j : Int) (hp : 0 < p) :
    chooseOrder p (11*n) j + numeratorOrder p n j = carry p n j := by
  simp only [numeratorOrder, carry, choose_order p _ _ hp]
  omega

theorem rational_kernel_floor_order (p n s : Int) (hp : 0 < p) :
    numeratorOrder p n s + ((11*n)/p + (s-11*n-1)/p - s/p) = carry p n s - 1 := by
  simp only [numeratorOrder, carry, choose_order p _ _ hp, gap_order p s (11*n) hp]
  omega

theorem carry_shift (p n k V : Int) : carry p n (k+p*V) = carry p n k := by
  have shifted (u : Int) : (k+p*V+u*n)%p = (k+u*n)%p := by
    rw [show k+p*V+u*n = (k+u*n)+p*V by omega, Int.add_mul_emod_self_left]
  simp only [carry, Int.add_mul_emod_self_left, shifted 9, shifted 10, shifted 11]

/-- For any two high digits, the two raw factorial orders differ by one. -/
theorem same_low_order_gap (p n k V l : Int) (hp : 0 < p) :
    let s := k+p*V
    let j := k+p*l
    numeratorOrder p n s + ((11*n)/p+(s-11*n-1)/p-s/p) =
      chooseOrder p (11*n) j + numeratorOrder p n j - 1 := by
  dsimp only
  rw [rational_kernel_floor_order _ _ _ hp, coefficient_floor_order _ _ _ hp,
    carry_shift, carry_shift]

/-- The coefficient and kernel calculations give the same Wilson-sign parity. -/
theorem common_scalar_parity (p k d M l H e : Int) (odd : p % 2 = 1) :
    (k+p*l+H+(1-e+d-k)+(M-e-l))%2 = (d-M+H-1)%2 ∧
    ((M+d)+(H-1)+(d-k+e+1)+(1-e+d-k))%2 = (d-M+H-1)%2 := by
  have hm : (p*l)%2 = l%2 := by rw [Int.mul_emod, odd, Int.one_mul, Int.emod_emod]
  constructor <;> omega

#print axioms coefficient_floor_order
#print axioms rational_kernel_floor_order
#print axioms same_low_order_gap
#print axioms common_scalar_parity
end PrimeNumerator.KernelDigits
