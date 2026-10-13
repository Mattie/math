import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import PairedAffine.Concrete
import DenominatorAffine.Endpoint

namespace OAI.DenominatorAffine
noncomputable section
open PairedAffine

private theorem fixed_sqrtTwo_embeddings_distinct :
    Field.sigma true true ≠ Field.sigma true false := by
  intro h
  have hv := congrArg (fun f : Field.F →ₐ[ℚ] ℂ => f Field.sqrtThree) h
  simp only [Field.sigma_sqrtThree, Field.signedRoot,
    Bool.false_eq_true, ↓reduceIte] at hv
  have hr := congrArg Complex.re hv
  simp at hr
  have hp := Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)
  linarith

private def fixedSqrtTwo : Finset (Field.F →ₐ[ℚ] ℂ) := by
  classical
  exact {Field.sigma true true, Field.sigma true false}

private theorem fixedSqrtTwo_card : fixedSqrtTwo.card = 2 := by
  classical
  simp [fixedSqrtTwo, fixed_sqrtTwo_embeddings_distinct]

private theorem fixedSqrtTwo_image (σ : Field.F →ₐ[ℚ] ℂ) (hσ : σ ∈ fixedSqrtTwo) :
    σ Field.sqrtTwo = (Real.sqrt 2 : ℂ) := by
  classical
  simp only [fixedSqrtTwo, Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl <;> simp [Field.signedRoot]

/-- The auxiliary sqrt(3) duplicates both embeddings of Q(sqrt(2));
the degree-to-good-embedding ratio stays two. -/
theorem log_three_halves_add_sqrt_two_eventualLowerBound :
    AlgebraicLog.EventualLowerBoundFour (Real.log (3 / 2) + Real.sqrt 2) := by
  classical
  have hlog : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  apply Endpoint.paired_fixed_denominator_eventualLowerBound ((3 : Field.F) / 2) 1 Field.sqrtTwo 2 (by norm_num)
    (by
      have he : (2 : Field.F) * (3 / 2) = 3 := by norm_num
      change IsIntegral ℤ ((2 : Field.F) * (3 / 2))
      rw [he]
      exact isIntegral_natCast 3) 1 (by norm_num)
    (by simp only [Nat.cast_one, one_mul]; exact isIntegral_one)
    (by convert Field.sqrtTwo_integral using 1 <;> first | simp only [Nat.cast_one, one_mul] | exact Subsingleton.elim _ _)
    Field.degree (Field.sigma true true) (3 / 2) (by norm_num) (by norm_num)
    (by norm_num [map_ofNat])
    (Real.log (3 / 2) + Real.sqrt 2) (ne_of_gt (by positivity))
    fixedSqrtTwo fixedSqrtTwo_card
  · intro σ hσ
    rw [fixedSqrtTwo_image σ hσ]
    simp only [map_one, one_mul, Complex.ofReal_add, add_sub_cancel_right]
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]
    norm_num [map_ofNat]
  · intro σ _
    simp


theorem log_three_halves_add_sqrt_two_explicit_bound (nu : ℝ) (hnu : 4 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤ |Real.log (3 / 2) + Real.sqrt 2 - (p : ℝ) / q| :=
  log_three_halves_add_sqrt_two_eventualLowerBound nu hnu

theorem log_three_halves_add_sqrt_two_irrational :
    Irrational (Real.log (3 / 2) + Real.sqrt 2) :=
  AlgebraicLog.irrational_of_eventualLowerBoundFour
    log_three_halves_add_sqrt_two_eventualLowerBound

theorem log_three_halves_add_sqrt_two_irrationalityExponent_le_four :
    PiExponent.irrationalityExponent (Real.log (3 / 2) + Real.sqrt 2) ≤ 4 :=
  AlgebraicLog.irrationalityExponent_le_four_of_eventualLowerBoundFour
    log_three_halves_add_sqrt_two_eventualLowerBound

theorem log_three_halves_add_sqrt_two_standard_exponent_le_four :
    Irrational (Real.log (3 / 2) + Real.sqrt 2) ∧
      ∀ nu : ℝ, 4 < nu → ¬ LiouvilleWith nu (Real.log (3 / 2) + Real.sqrt 2) := by
  refine ⟨log_three_halves_add_sqrt_two_irrational, ?_⟩
  intro nu hnu hl
  let mu : ℝ := (4 + nu) / 2
  have hmu : 4 < mu := by dsimp [mu]; linarith
  have hmunu : mu < nu := by dsimp [mu]; linarith
  obtain ⟨Q, _, hb⟩ := log_three_halves_add_sqrt_two_explicit_bound mu hmu
  have hf := hl.frequently_lt_rpow_neg hmunu
  obtain ⟨q, ⟨p, _, hp⟩, hq⟩ :=
    (hf.and_eventually (Filter.eventually_ge_atTop Q)).exists
  exact (not_lt_of_ge (hb p q hq)) hp
end
end OAI.DenominatorAffine