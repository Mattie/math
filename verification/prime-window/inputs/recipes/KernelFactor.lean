import Zeta2FourTrajectoryMatrices.FiniteReadout.blueprint_next_two

/-!
# The low-digit polynomial in a translated interval

The coefficients of the first-column polynomial depend only on the level
modulo `p`. The factorization of Leibtag et al. at the residue level therefore
supplies a quotient of degree strictly below `p - 1` at the translated level.
This is the degree bound needed to sum the quotient over the field.
-/

open Finset Polynomial Zeta2Blueprint Zeta2NextTwo

namespace PrimeNumerator.KernelFactor

theorem mul_mod_N (N p u : ℕ) : (u * N) % p = (u * (N % p)) % p := by
  exact (Nat.ModEq.refl u).mul (show N ≡ N % p [MOD p] by simp [Nat.ModEq])

theorem cast_mul_mod_N (N p u : ℕ) :
    ((u * N : ℕ) : ZMod p) = ((u * (N % p) : ℕ) : ZMod p) :=
  (ZMod.natCast_eq_natCast_iff _ _ _).2 (mul_mod_N N p u)

theorem chi_mod_N (N p k : ℕ) (hp : 0 < p) (hk : k < p) :
    chi N p k = chi (N % p) p k := by
  have off (u : ℕ) : (k + u * N) % p = (k + u * (N % p)) % p :=
    (Nat.ModEq.refl k).add (mul_mod_N N p u)
  rw [chi_id N p k hp hk, chi_id (N % p) p k hp hk, mul_mod_N N p 11,
    mul_mod_N N p 8, off 9, off 10, off 11]

/-- The continuous infimum defining `phi` agrees at every integral translate. -/
theorem phi_mod_N (N p : ℕ) (hp : 0 < p) :
    phi ((N : ℝ) / p) = phi (((N % p : ℕ) : ℝ) / p) := by
  apply le_antisymm
  · apply phi_ge (N % p) p hp
    intro j hj0 hj
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj0
    rw [← chi_mod_N N p k hp (by exact_mod_cast hj)]
    exact phi_le_chi N p hp k
  · apply phi_ge N p hp
    intro j hj0 hj
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hj0
    rw [chi_mod_N N p k hp (by exact_mod_cast hj)]
    exact phi_le_chi (N % p) p hp k

/-- First-column factorization at the original index. The quotient from the base
shell works verbatim, since every coefficient in the polynomial identity repeats. -/
theorem polyQ_factor_translated (N p : ℕ) [Fact p.Prime] (hN : 1 ≤ N % p)
    (hp : 50 * N < p ^ 2) (hs : InShell (N % p) 0 p) :
    let b := 8 * N % p
    let d := 11 * N % p
    let h := (phi ((N : ℝ) / p)).toNat
    let f : (ZMod p)[X] := binomPoly (ZMod p) ((9 * N : ℕ) : ZMod p) b *
      binomPoly (ZMod p) ((10 * N : ℕ) : ZMod p) b *
      binomPoly (ZMod p) ((11 * N : ℕ) : ZMod p) b
    let g : (ZMod p)[X] := ∏ j ∈ range (d + 1), (X - C (j : ZMod p))
    ∃ Q : (ZMod p)[X], f * (X ^ p - X) ^ (1 - h) =
      (X ^ p - X) ^ (h - 1) * g * Q ∧ Q.natDegree < p - 1 := by
  have hp' := (Fact.out : p.Prime).pos
  have hsmall : 50 * (N % p) < p ^ 2 :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 50 (Nat.mod_le N p)) hp
  dsimp only
  rw [mul_mod_N N p 8, mul_mod_N N p 11, cast_mul_mod_N N p 9,
    cast_mul_mod_N N p 10, cast_mul_mod_N N p 11, phi_mod_N N p hp']
  simpa only [pow_zero, one_mul] using polyQ_factor (N % p) 0 p hN (by decide) hsmall hs

#print axioms phi_mod_N
#print axioms polyQ_factor_translated

end PrimeNumerator.KernelFactor
