import Lean

/-!
# Translating the carry and degree conditions

Write the level as `t * p + r`. Adding a multiple of `p` preserves each low
residue and shifts each high quotient by a known multiple of `t`. Thus the
same low digits attain the minimum carry in every translate, and the degree
inequality used for cancellation carries over from the base interval.
-/

namespace PrimeChambers

theorem quotient_translate (p t r k u : Nat) (hp : 0 < p) :
    (k + u * (t * p + r)) / p = (k + u * r) / p + u * t := by
  have h := Nat.add_mul_div_right (k + u * r) (u * t) hp
  simpa [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem residue_translate (p t r k u : Nat) :
    (k + u * (t * p + r)) % p = (k + u * r) % p := by
  have h := Nat.add_mul_mod_self_right (k + u * r) (u * t) p
  simpa [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def carry (p n k : Nat) : Nat :=
  (if k > (11*n)%p then 1 else 0) +
  (if (k+9*n)%p < (8*n)%p then 1 else 0) +
  (if (k+10*n)%p < (8*n)%p then 1 else 0) +
  (if (k+11*n)%p < (8*n)%p then 1 else 0)

theorem carry_translate (p t r k : Nat) : carry p (t*p+r) k = carry p r k := by
  have h8 := residue_translate p t r 0 8
  have h11 := residue_translate p t r 0 11
  simp only [Nat.zero_add] at h8 h11
  simp only [carry, h8, h11, residue_translate]

theorem minimum_support_translate (p t r H : Nat) :
    (∀ k, k < p → H ≤ carry p r k) ∧
      (∃ k, k < p ∧ carry p r k = H) ↔
    (∀ k, k < p → H ≤ carry p (t*p+r) k) ∧
      (∃ k, k < p ∧ carry p (t*p+r) k = H) := by
  simp only [carry_translate]

theorem degree_translate (p t r a M H : Nat) (h : M ≤ 3*a+H) :
    13*r < (3*a+H-M)*p ↔
      13*(t*p+r) < (3*(8*t+a)+H-(11*t+M))*p := by
  have eq : 3*(8*t+a)+H-(11*t+M) = 13*t+(3*a+H-M) := by omega
  rw [eq]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
  omega

theorem high_floor_equal_translate (p t r k l u : Nat) (hp : 0 < p) :
    (k + u*r)/p = (l + u*r)/p ↔
      (k + u*(t*p+r))/p = (l + u*(t*p+r))/p := by
  rw [quotient_translate p t r k u hp, quotient_translate p t r l u hp]
  omega

theorem degree_translate_source (p t r a M H : Nat) (h : M ≤ 3*a) :
    13*r < (3*a-M+H)*p ↔
      13*(t*p+r) < (3*(8*t+a)-(11*t+M)+H)*p := by
  have h1 : 3*a-M+H = 3*a+H-M := by omega
  have h2 : 3*(8*t+a)-(11*t+M)+H = 3*(8*t+a)+H-(11*t+M) := by omega
  rw [h1, h2]
  exact degree_translate p t r a M H (by omega)

#print axioms high_floor_equal_translate
#print axioms degree_translate_source
#print axioms quotient_translate
#print axioms residue_translate
#print axioms carry_translate
#print axioms minimum_support_translate
#print axioms degree_translate
end PrimeChambers

