import PiTwoCaseBridge.FiniteInterpolation
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Analysis.Complex.Polynomial.Basic
import OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout

/-!
# The finite interpolation hypotheses at two points of the complex line

The generator `X(X-1)` has source degree two. At 0 and 1 its first
nonzero terms are respectively `-X` and `X`, both of local weight three.
-/

namespace PiTwoCaseBridge.TwoCenterExample

open MvPolynomial OAI.PiExponent.WeightedBezout

noncomputable section

abbrev W : Unit → ℕ := 1
abbrev V : Unit → ℕ := fun _ => 3
abbrev Poly := MvPolynomial Unit ℂ

def center (j : Bool) : Unit → ℂ := fun _ => if j then 1 else 0
def chart (j : Bool) : Poly ≃ₐ[ℂ] Poly := translationEquiv (center j)
def generator : Poly := X () * (X () - 1)
def linear (j : Bool) : Poly := if j then X () else -X ()

theorem center_injective : Function.Injective center := by
  intro i j h
  have h' := congrFun h ()
  cases i <;> cases j <;> simp_all [center]

theorem chart_at_zero (j : Bool) (p : Poly) :
    aeval (0 : Unit → ℂ) (chart j p) = aeval (center j) p := by
  have h : (aeval (R := ℂ) (0 : Unit → ℂ)).comp (translation (center j)) =
      aeval (center j) := by
    ext i
    simp [translation]
  exact DFunLike.congr_fun h p

theorem source_degree : weightedTotalDegree W generator ≤ 2 := by
  rw [weightedTotalDegree_one, generator]
  apply (totalDegree_mul _ _).trans
  have h := totalDegree_sub_C_le (X () : Poly) (1 : ℂ)
  simpa using Nat.add_le_add_left h 1

theorem chart_expansion (j : Bool) : chart j generator = X () ^ 2 + linear j := by
  change translation (center j) generator = _
  cases j <;> simp [translation, generator, linear, center] <;> ring

private theorem linear_homogeneous (j : Bool) : IsWeightedHomogeneous V (linear j) 3 := by
  have h : IsWeightedHomogeneous V (X () : Poly) 3 := isWeightedHomogeneous_X ℂ V ()
  cases j
  · exact h.neg
  · exact h

private theorem square_homogeneous : IsWeightedHomogeneous V (X () ^ 2 : Poly) 6 :=
  (isWeightedHomogeneous_X ℂ V ()).pow 2

theorem local_order (j : Bool) (a : Unit →₀ ℕ) (ha : Finsupp.weight V a < 3) :
    (chart j generator).coeff a = 0 := by
  rw [chart_expansion]
  change (X () ^ 2 : Poly).coeff a + (linear j).coeff a = 0
  rw [square_homogeneous.coeff_eq_zero a (by omega),
    (linear_homogeneous j).coeff_eq_zero a ha.ne, zero_add]

theorem initial_form (j : Bool) :
    weightedHomogeneousComponent V 3 (chart j generator) = linear j := by
  rw [chart_expansion, map_add, square_homogeneous.weightedHomogeneousComponent_ne 3 (by decide),
    (linear_homogeneous j).weightedHomogeneousComponent_same, zero_add]

theorem initial_zero_locus (j : Bool) :
    zeroLocus ℂ (Ideal.span (Set.range fun _ : Unit =>
      weightedHomogeneousComponent V 3 (chart j generator))) = {0} := by
  rw [initial_form, zeroLocus_span]
  ext x
  simp only [Set.mem_ofPred_eq, Set.forall_mem_range, forall_const, Set.mem_singleton_iff]
  have h : aeval x (linear j) = 0 ↔ x () = 0 := by
    cases j <;> simp [linear]
  rw [h]
  constructor
  · intro hx
    funext i
    cases i
    exact hx
  · intro hx
    simp [hx]

theorem strict_margin : 0 < (2 / 3 : ℚ) ∧ (2 / 3 : ℚ) < 1 := by norm_num

/-- At every cutoff a common polynomial interpolates both packets within
the source bound `(2/3)T+B`, for one fixed additive constant. -/
theorem simultaneous_packets :
    ∃ B : ℕ, ∀ T : ℕ, Function.Surjective
      (polynomialPacket chart W V 3 (2 * T + 3 * B) T) :=
  exists_polynomialPackets_of_zeroLocus W V (fun _ => by norm_num [V]) center center_injective
    chart chart_at_zero 3 2 (by decide) (fun _ : Unit => generator)
    (fun _ => source_degree) (fun j _ => local_order j) initial_zero_locus

end

end PiTwoCaseBridge.TwoCenterExample
