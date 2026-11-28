import PiTwoCaseBridge.Certificate
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! A two-center example of strict interpolation in the full logarithmic jets. -/

namespace PiTwoCaseBridge.LogExample

open OAI OAI.PiExponent PiExponentApprox MvPolynomial

noncomputable section

abbrev integerW : Fin 2 → ℕ := 1
abbrev integerV : Fin 2 → ℕ := fun _ => 3
abbrev W : Fin 2 → ℚ := 1
abbrev V : Fin 2 → ℚ := fun _ => 3

def center (j : Bool) : Fin 1 → ℂ := fun _ => if j then 1 else 0

def generator : Bool → FramePolynomial 1
  | false => X 0 - 1
  | true => X 1 * (X 1 - 1)

private abbrev cutoff : Fin 1 → ℕ := fun _ => 2

/-- The linear term of the logarithm couples the two local variables. -/
private def linear : FramePolynomial 1 := X 1 + X 0

private def firstForm (j : Bool) : Bool → FramePolynomial 1
  | false => X 0
  | true => if j then linear else -linear

private theorem trunc_log_two : PowerSeries.trunc 2 (PowerSeries.log ℂ) = Polynomial.X := by
  ext n
  cases n with
  | zero => simp [PowerSeries.coeff_trunc, PowerSeries.coeff_log]
  | succ n =>
    cases n with
    | zero => simp [PowerSeries.coeff_trunc, PowerSeries.coeff_log]
    | succ n => simp [PowerSeries.coeff_trunc, Polynomial.coeff_X]

private theorem chart_Y (j : Bool) :
    logarithmicChart (center j) cutoff (X 0) = 1 + X 0 :=
  AlgebraicJetPackets.triangularMap_X_zero _ _

private theorem chart_X (j : Bool) :
    logarithmicChart (center j) cutoff (X 1) = C (center j 0) + linear := by
  change AlgebraicJetPackets.triangularMap (center j) _ (X (0 : Fin 1).succ) = _
  rw [AlgebraicJetPackets.triangularMap_X_succ, trunc_log_two, Polynomial.aeval_X]
  simp [linear, add_assoc]

private theorem chart_first (j : Bool) :
    logarithmicChart (center j) cutoff (generator false) = X 0 := by
  simp [generator, chart_Y]

private theorem chart_second (j : Bool) :
    logarithmicChart (center j) cutoff (generator true) = linear ^ 2 + firstForm j true := by
  rw [generator, map_mul, map_sub, map_one, chart_X]
  cases j <;> simp [center, firstForm] <;> ring

private theorem form_homogeneous (j k : Bool) :
    IsWeightedHomogeneous integerV (firstForm j k) 3 := by
  have h (i : Fin 2) : IsWeightedHomogeneous integerV (X i : FramePolynomial 1) 3 :=
    isWeightedHomogeneous_X ℂ integerV i
  have hl := (h 1).add (h 0)
  cases k
  · exact h 0
  · cases j
    · exact hl.neg
    · exact hl

private theorem square_homogeneous : IsWeightedHomogeneous integerV (linear ^ 2) 6 :=
  (form_homogeneous true true).pow 2

theorem local_order (j k : Bool) (a : Fin 2 →₀ ℕ) (ha : Finsupp.weight integerV a < 3) :
    (logarithmicChart (center j) cutoff (generator k)).coeff a = 0 := by
  cases k
  · rw [chart_first]
    exact (form_homogeneous j false).coeff_eq_zero a ha.ne
  · rw [chart_second]
    change (linear ^ 2).coeff a + (firstForm j true).coeff a = 0
    rw [square_homogeneous.coeff_eq_zero a (by omega),
      (form_homogeneous j true).coeff_eq_zero a ha.ne, zero_add]

private theorem initial_form (j k : Bool) :
    weightedHomogeneousComponent integerV 3
      (logarithmicChart (center j) cutoff (generator k)) = firstForm j k := by
  cases k
  · rw [chart_first]
    exact (form_homogeneous j false).weightedHomogeneousComponent_same
  · rw [chart_second, map_add, square_homogeneous.weightedHomogeneousComponent_ne 3 (by decide),
      (form_homogeneous j true).weightedHomogeneousComponent_same, zero_add]

theorem isolated_origin (j : Bool) :
    zeroLocus ℂ (Ideal.span (Set.range fun k =>
      weightedHomogeneousComponent integerV 3
        (logarithmicChart (center j) cutoff (generator k)))) = {0} := by
  simp only [initial_form, zeroLocus_span]
  ext x
  simp only [Set.mem_ofPred_eq, Set.forall_mem_range, Set.mem_singleton_iff]
  constructor
  · intro h
    have hx : x 0 = 0 := by simpa [firstForm] using h false
    have hy : x 1 = 0 := by
      cases j <;> simpa [firstForm, linear, hx] using h true
    funext i
    fin_cases i
    · exact hx
    · exact hy
  · rintro rfl k
    cases k <;> cases j <;> simp [firstForm, linear]

theorem source_degree (k : Bool) : weightedTotalDegree integerW (generator k) ≤ 2 := by
  rw [weightedTotalDegree_one]
  have h (i : Fin 2) : (X i - 1 : FramePolynomial 1).totalDegree ≤ 1 := by
    simpa using totalDegree_sub_C_le (X i : FramePolynomial 1) (1 : ℂ)
  cases k
  · exact (h 0).trans (by decide)
  · exact (totalDegree_mul _ _).trans (by simpa using Nat.add_le_add_left (h 1) 1)

private theorem center_injective : Function.Injective center := by
  intro i j h
  have hij := congrFun h 0
  cases i <;> cases j <;> simp_all [center]

/-- One polynomial realizes arbitrary full logarithmic jets of each positive real
cutoff at both (1,0) and (1,1), with a fixed strictly subunit degree slope. -/
theorem simultaneous_logarithmic_interpolation : StrictInterpolation W V center :=
  strictInterpolation_of_initialForms W V center center_injective cutoff
    (fun _ => by norm_num [V, cutoff]) 1 1 (by decide) (by decide) integerW integerV
    (fun _ => by norm_num [W, integerW]) (fun _ => by norm_num [V, integerV])
    (fun _ => by norm_num [integerV]) 3 2 (by decide) (by decide) (by decide)
    generator source_degree local_order isolated_origin

end

end PiTwoCaseBridge.LogExample
