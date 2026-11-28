import PiTwoCaseBridge.Colength
import PiTwoCaseBridge.CRT
import PiTwoCaseBridge.GradedLifts
import PiTwoCaseBridge.Packets

/-!
# Finite algebra of the strict interpolation bridge

A fixed family of source polynomials of degree at most `d` has order at
least `L` at every center. Its weight-`L` pieces give homogeneous reduction.
The only additional source cost is the fixed CRT table for the low remainders.
-/

namespace PiTwoCaseBridge

open MvPolynomial
open scoped Classical

variable {K σ J ι : Type*} [Field K] [Fintype σ] [Fintype J] [Finite ι]

theorem exists_polynomialPackets_of_finiteColength
    (W V : σ → ℕ) (hV : ∀ i, 0 < V i)
    (c : J → σ → K) (hc : Function.Injective c)
    (chart : J → MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K)
    (hchart : ∀ j p, aeval (0 : σ → K) (chart j p) = aeval (c j) p)
    (L d : ℕ) (hL : 0 < L) (P : ι → MvPolynomial σ K)
    (hdegree : ∀ i, weightedTotalDegree W (P i) ≤ d)
    (horder : ∀ j i a, Finsupp.weight V a < L → (chart j (P i)).coeff a = 0)
    (hcolength : ∀ j, FiniteDimensional K (MvPolynomial σ K ⧸
      Ideal.span (Set.range fun i => weightedHomogeneousComponent V L (chart j (P i))))) :
    ∃ B : ℕ, ∀ T : ℕ, Function.Surjective
      (polynomialPacket chart W V L (d * T + L * B) T) := by
  classical
  let f (j : J) (i : ι) := weightedHomogeneousComponent V L (chart j (P i))
  have hom (j : J) (i : ι) : IsWeightedHomogeneous V (f j i) L :=
    weightedHomogeneousComponent_isWeightedHomogeneous L _
  choose bound hbound using fun j =>
    exists_weighted_cutoff_of_finiteColength V (f j) L (hom j) (hcolength j)
  let M : ℕ := Finset.univ.sup bound + 1
  obtain ⟨B, seed, hseed⟩ := exists_bounded_crt_monomial_lifts W V hV c hc chart hchart M
  refine ⟨B, fun T => ?_⟩
  apply surjective_polynomialPacket_of_initial_monomials chart W V hV L d B T
  intro j a _
  apply exists_initial_monomial_lift W V L d M B hL chart P hdegree horder
    (fun j b hb => ⟨seed j b, hseed j b hb⟩) j a
  refine monomial_mem_span_reductionTerms V (f j) L M hL (hom j) ?_ a
  intro n hn H Hhom
  apply hbound j n _ H Hhom
  exact (Finset.le_sup (Finset.mem_univ j)).trans (Nat.le_of_succ_le hn)

theorem exists_polynomialPackets_of_zeroLocus [IsAlgClosed K]
    (W V : σ → ℕ) (hV : ∀ i, 0 < V i)
    (c : J → σ → K) (hc : Function.Injective c)
    (chart : J → MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K)
    (hchart : ∀ j p, aeval (0 : σ → K) (chart j p) = aeval (c j) p)
    (L d : ℕ) (hL : 0 < L) (P : ι → MvPolynomial σ K)
    (hdegree : ∀ i, weightedTotalDegree W (P i) ≤ d)
    (horder : ∀ j i a, Finsupp.weight V a < L → (chart j (P i)).coeff a = 0)
    (hzero : ∀ j, zeroLocus K
      (Ideal.span (Set.range fun i => weightedHomogeneousComponent V L (chart j (P i)))) =
        {0}) :
    ∃ B : ℕ, ∀ T : ℕ, Function.Surjective
      (polynomialPacket chart W V L (d * T + L * B) T) :=
  exists_polynomialPackets_of_finiteColength W V hV c hc chart hchart L d hL P hdegree horder
    (fun j => finiteColength_of_zeroLocus_origin _ (hzero j))

end PiTwoCaseBridge
