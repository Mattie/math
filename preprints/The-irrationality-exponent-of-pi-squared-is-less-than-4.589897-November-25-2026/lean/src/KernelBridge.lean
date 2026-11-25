import KernelFactor
import KernelLocal
import Zeta2FourTrajectoryMatrices.ArithmeticNormalization.arithmetic_normalization

/-!
# Cancellation within residue blocks

Writing an index as a high digit and a low digit isolates a polynomial in
the low digit. Its sum vanishes on each complete block and on the final
partial block. Consequently the divided binomial residues still sum to zero
when each block is multiplied by an arbitrary weight depending on its high digit.
-/

open Finset Polynomial Zeta2Blueprint Zeta2NextTwo Zeta2ArithmeticNormalization

noncomputable section
namespace PrimeNumerator.KernelBridge

theorem qpoly_mod_N (N p : ℕ) [Fact p.Prime] :
    Qpoly N p = Qpoly (N % p) p := by
  unfold Qpoly hexp
  rw [KernelFactor.mul_mod_N N p 8, KernelFactor.mul_mod_N N p 11,
    KernelFactor.cast_mul_mod_N N p 9, KernelFactor.cast_mul_mod_N N p 10,
    KernelFactor.cast_mul_mod_N N p 11, KernelFactor.phi_mod_N N p (Fact.out : p.Prime).pos]

def LowFactor (N p : ℕ) [Fact p.Prime] (Q : (ZMod p)[X]) : Prop :=
  binomPoly (ZMod p) ((9 * N : ℕ) : ZMod p) (8 * N % p) *
    binomPoly (ZMod p) ((10 * N : ℕ) : ZMod p) (8 * N % p) *
    binomPoly (ZMod p) ((11 * N : ℕ) : ZMod p) (8 * N % p) *
      (X ^ p - X) ^ (1 - hexp N p) =
    (X ^ p - X) ^ (hexp N p - 1) *
      (∏ j ∈ range (11 * N % p + 1), (X - C (j : ZMod p))) * Q

theorem factor_translated (N p : ℕ) [Fact p.Prime] (hp2 : 50*N < p^2)
    (hs : InShell (N%p) 0 p) : LowFactor N p (Qpoly N p) := by
  have base := KernelChamber.base_shell N p hp2 hs
  have pos : 1 ≤ N % p := by have := base.1; omega
  unfold LowFactor hexp
  rw [qpoly_mod_N N p, KernelFactor.mul_mod_N N p 8, KernelFactor.mul_mod_N N p 11,
    KernelFactor.cast_mul_mod_N N p 9, KernelFactor.cast_mul_mod_N N p 10,
    KernelFactor.cast_mul_mod_N N p 11, KernelFactor.phi_mod_N N p (Fact.out : p.Prime).pos]
  exact (Qpoly_spec (N % p) 0 p pos (by decide) base).1

theorem sums_translated (N p : ℕ) [Fact p.Prime] (_pn : p < N) (hp2 : 50*N < p^2)
    (hs : InShell (N%p) 0 p) :
    (∑ k : ZMod p, (Qpoly N p).eval k = 0) ∧
    (∑ k ∈ range p, (Qpoly N p).eval (k : ZMod p) = 0) ∧
    (∑ k ∈ range (11*N % p + 1), (Qpoly N p).eval (k : ZMod p) = 0) := by
  have base := KernelChamber.base_shell N p hp2 hs
  have pos : 1 ≤ N % p := by have := base.1; omega
  rw [qpoly_mod_N N p, KernelFactor.mul_mod_N N p 11]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [pow_zero, one_mul] using Qpoly_sum_zero (N%p) 0 p pos (by decide) base
  · simpa only [pow_zero, one_mul] using Qsum_range (N%p) 0 p pos (by decide) base
  · simpa only [pow_zero, one_mul] using Q_partial (N%p) 0 p pos (by decide) base

theorem residue_translated (N p : ℕ) [Fact p.Prime] (pn : p < N) (hp2 : 50*N < p^2)
    (hs : InShell (N%p) 0 p) :
    ∃ (κ : ZMod p) (Acoef : ℕ → ZMod p), ∀ j ≤ 11 * N,
      ((cZ N j / (p : ℤ) ^ hexp N p : ℤ) : ZMod p) =
        κ * (Qpoly N p).eval ((j % p : ℕ) : ZMod p) * Acoef (j / p) :=
  KernelLocal.residue_of_uniform N p (by omega) hp2
    (KernelChamber.uniform_translated N p pn hp2 hs) _ (factor_translated N p hp2 hs)

theorem evaluation_translated (N p : ℕ) [Fact p.Prime] (pn : p < N) (hp2 : 50*N < p^2)
    (hs : InShell (N%p) 0 p) :
    ∃ U : ℤ → ZMod p, ∀ k : ℕ, k < p → ∀ V : ℤ, ((11 * N / p : ℕ) : ℤ) + 1 ≤ V →
      V + ((11 * N / p : ℕ) : ℤ) + 2 ≤ p →
      Reduces p ((p : ℚ) ^ ((1 : ℤ) - (hexp N p : ℤ)) *
        ((Fpoly N).eval ((k : ℚ) + p * V) *
          ((-1) ^ (11 * N) * ((11 * N).factorial : ℚ) /
            ∏ j ∈ range (11 * N + 1), ((k : ℚ) + p * V - j))))
        ((Qpoly N p).eval (k : ZMod p) * U V) :=
  KernelLocal.evaluation_of_uniform N p (by omega) hp2
    (KernelChamber.uniform_translated N p pn hp2 hs) _ (factor_translated N p hp2 hs)

/-- Every high-digit weighting of the true divided binomial residues cancels. -/
theorem weighted_residue_sum (N p : ℕ) [Fact p.Prime] (pn : p < N) (hp2 : 50*N < p^2)
    (hs : InShell (N%p) 0 p) (w : ℕ → ZMod p) :
    ∑ j ∈ range (11 * N + 1),
      ((cZ N j / (p : ℤ) ^ hexp N p : ℤ) : ZMod p) * w (j / p) = 0 := by
  obtain ⟨κ, A, h⟩ := residue_translated N p pn hp2 hs
  obtain ⟨_, hf, hd⟩ := sums_translated N p pn hp2 hs
  have e : ∀ j ∈ range (11 * N + 1),
      ((cZ N j / (p : ℤ) ^ hexp N p : ℤ) : ZMod p) * w (j / p) =
      κ * ((Qpoly N p).eval ((j % p : ℕ) : ZMod p) * (A (j / p) * w (j / p))) := by
    intro j hj
    rw [h j (by have := mem_range.1 hj; omega)]
    ring
  rw [sum_congr rfl e, ← mul_sum, show 11 * N + 1 = p * (11 * N / p) + (11 * N % p + 1) by
    rw [← add_assoc, Nat.div_add_mod]]
  exact (congrArg (κ * ·) (block_sum (fun k => (Qpoly N p).eval (k : ZMod p))
    (fun l => A l * w l) p (11 * N / p) (11 * N % p)
    (Nat.mod_lt _ (Fact.out : p.Prime).pos) hf hd)).trans (mul_zero κ)

#print axioms qpoly_mod_N
#print axioms sums_translated
#print axioms residue_translated
#print axioms evaluation_translated
#print axioms weighted_residue_sum
end PrimeNumerator.KernelBridge
