import OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree

/-!
Weighted support bounds can be recovered from a positive power over a field.
The lexicographic tie-breaker prevents cancellation at the leading monomial.
-/

namespace Degree
noncomputable section
open OAI.PiExponent.WeightedSliceDegree

variable {ι K : Type} [LinearOrder ι] [Field K]

abbrev DegreeOrder (ι : Type) := Lex (NNReal × Lex (ι →₀ ℕ))

def orderedWeight (w : ι → NNReal) (a : ι →₀ ℕ) : DegreeOrder ι :=
  toLex (Finsupp.weight w a, toLex a)

omit [LinearOrder ι] in
lemma orderedWeight_injective (w : ι → NNReal) :
    Function.Injective (orderedWeight w) := by
  intro a b h
  exact congrArg (fun t : DegreeOrder ι => ofLex (ofLex t).2) h

omit [LinearOrder ι] in
lemma orderedWeight_add (w : ι → NNReal) (a b : ι →₀ ℕ) :
    orderedWeight w (a + b) = orderedWeight w a + orderedWeight w b := by
  change (Finsupp.weight w (a + b), toLex (a + b)) =
    (Finsupp.weight w a + Finsupp.weight w b, toLex a + toLex b)
  rw [map_add]
  rfl

omit [LinearOrder ι] in
lemma orderedWeight_zero (w : ι → NNReal) : orderedWeight w 0 = 0 := by
  simp [orderedWeight]

lemma first_le_of_orderedWeight_le (w : ι → NNReal) {a b : ι →₀ ℕ}
    (h : orderedWeight w a ≤ orderedWeight w b) :
    Finsupp.weight w a ≤ Finsupp.weight w b := by
  exact Prod.Lex.monotone_fst _ _ h

lemma supDegree_pow (w : ι → NNReal) (p : MvPolynomial ι K) (hp : p ≠ 0)
    (k : ℕ) :
    AddMonoidAlgebra.supDegree (orderedWeight w) (p ^ k) =
      k • AddMonoidAlgebra.supDegree (orderedWeight w) p := by
  induction k with
  | zero =>
      simp [AddMonoidAlgebra.supDegree, orderedWeight]
  | succ k ih =>
      rw [pow_succ]
      rw [AddMonoidAlgebra.supDegree_mul (orderedWeight_injective w)
        (orderedWeight_add w) ?_ (pow_ne_zero k hp) hp, ih, succ_nsmul]
      exact mul_ne_zero
        ((AddMonoidAlgebra.leadingCoeff_ne_zero (orderedWeight_injective w)).mpr
          (pow_ne_zero k hp))
        ((AddMonoidAlgebra.leadingCoeff_ne_zero (orderedWeight_injective w)).mpr hp)

omit [LinearOrder ι] in
lemma real_weight (w : ι → NNReal) (a : ι →₀ ℕ) :
    (Finsupp.weight w a : ℝ) = Finsupp.weight (fun i => (w i : ℝ)) a := by
  simp [Finsupp.weight_apply, Finsupp.sum, NNReal.coe_sum]

/-- A weighted bound on a positive power gives the bound before taking the power. -/
theorem supportBound_of_pow (w : ι → NNReal) (B : ℝ)
    (p : MvPolynomial ι K) {k : ℕ} (hk : 0 < k)
    (h : SupportBound (fun i => (w i : ℝ)) ((k : ℝ) * B) (p ^ k)) :
    SupportBound (fun i => (w i : ℝ)) B p := by
  classical
  by_cases hp : p = 0
  · subst p
    exact supportBound_zero _ _
  obtain ⟨a, ha, hmax⟩ := AddMonoidAlgebra.exists_supDegree_mem_support
    (orderedWeight w) hp
  obtain ⟨b, hb, hbmax⟩ := AddMonoidAlgebra.exists_supDegree_mem_support
    (orderedWeight w) (pow_ne_zero k hp)
  have he : orderedWeight w b = k • orderedWeight w a := by
    rw [← hbmax, supDegree_pow w p hp, hmax]
  have hw : Finsupp.weight (fun i => (w i : ℝ)) b =
      (k : ℝ) * Finsupp.weight (fun i => (w i : ℝ)) a := by
    have ht := congrArg (fun t : DegreeOrder ι => ((ofLex t).1 : ℝ)) he
    change (Finsupp.weight w b : ℝ) = (k • Finsupp.weight w a : NNReal) at ht
    simpa [real_weight, nsmul_eq_mul] using ht
  have hwa : Finsupp.weight (fun i => (w i : ℝ)) a ≤ B := by
    have hkb := h b hb
    rw [hw] at hkb
    have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
    nlinarith
  intro d hd
  have hm : orderedWeight w d ≤ orderedWeight w a := by
    rw [← hmax]
    exact Finset.le_sup hd
  have hr := first_le_of_orderedWeight_le w hm
  have hrreal : (Finsupp.weight w d : ℝ) ≤ (Finsupp.weight w a : ℝ) := hr
  rw [real_weight, real_weight] at hrreal
  exact hrreal.trans hwa

/-- Uniformly bounded positive powers force weighted degree zero. -/
theorem supportBound_zero_of_pow_bounded (w : ι → NNReal) (B : ℝ)
    (p : MvPolynomial ι K)
    (h : ∀ k : ℕ, 0 < k → SupportBound (fun i => (w i : ℝ)) B (p ^ k)) :
    SupportBound (fun i => (w i : ℝ)) 0 p := by
  intro d hd
  by_contra hle
  have hpos : 0 < Finsupp.weight (fun i => (w i : ℝ)) d := lt_of_not_ge hle
  let δ := Finsupp.weight (fun i => (w i : ℝ)) d / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (B / δ))
  have hkreal : (1 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hkpos : 0 < k := by exact_mod_cast (lt_trans zero_lt_one hkreal)
  have hB : B ≤ (k : ℝ) * δ := by
    have ht : B / δ < (k : ℝ) := lt_of_le_of_lt (le_max_right _ _) hk
    have hm := (div_lt_iff₀ hδ).mp ht
    exact hm.le
  have hp := supportBound_of_pow w δ p hkpos ((h k hkpos).mono hB)
  have hw := hp d hd
  dsimp [δ] at hw
  linarith

end
end Degree
