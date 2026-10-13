import PairedAffine.Concrete
import PairedAffine.Endpoint

namespace OAI.PairedAffine
noncomputable section

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
theorem log_two_add_sqrt_two_eventualLowerBound :
    AlgebraicLog.EventualLowerBoundFour (Real.log 2 + Real.sqrt 2) := by
  classical
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply Endpoint.paired_eventualLowerBound (2 : Field.F) 1 Field.sqrtTwo
    (isIntegral_natCast 2) isIntegral_one Field.sqrtTwo_integral
    Field.degree (Field.sigma true true) 2 (by norm_num) (by norm_num)
    (by simp [map_ofNat])
    (Real.log 2 + Real.sqrt 2) (ne_of_gt (by positivity))
    fixedSqrtTwo fixedSqrtTwo_card
  · intro σ hσ
    rw [fixedSqrtTwo_image σ hσ]
    simp only [map_one, one_mul, Complex.ofReal_add, add_sub_cancel_right]
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num [map_ofNat]
  · intro σ _
    simp

theorem sqrt_two_mul_log_two_eventualLowerBound :
    AlgebraicLog.EventualLowerBoundFour (Real.sqrt 2 * Real.log 2) := by
  classical
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have he : Complex.exp (Real.log 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  apply Endpoint.paired_eventualLowerBound (4 : Field.F) Field.sqrtTwo 0
    (isIntegral_natCast 4) Field.sqrtTwo_integral isIntegral_zero
    Field.degree (Field.sigma true true) 4 (by norm_num) (by norm_num)
    (by simp [map_ofNat])
    (Real.sqrt 2 * Real.log 2) (ne_of_gt (by positivity))
    fixedSqrtTwo fixedSqrtTwo_card
  · intro σ hσ
    rw [fixedSqrtTwo_image σ hσ]
    simp only [map_zero, sub_zero, Complex.ofReal_mul]
    rw [← mul_assoc, ← pow_two, hs, two_mul, Complex.exp_add, he]
    norm_num [map_ofNat]
  · intro σ hσ
    rw [fixedSqrtTwo_image σ hσ]
    simp [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg (2 : ℝ))]

theorem log_two_add_sqrt_two_explicit_bound (nu : ℝ) (hnu : 4 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤ |Real.log 2 + Real.sqrt 2 - (p : ℝ) / q| :=
  log_two_add_sqrt_two_eventualLowerBound nu hnu

theorem sqrt_two_mul_log_two_explicit_bound (nu : ℝ) (hnu : 4 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤ |Real.sqrt 2 * Real.log 2 - (p : ℝ) / q| :=
  sqrt_two_mul_log_two_eventualLowerBound nu hnu

theorem log_two_add_sqrt_two_irrational : Irrational (Real.log 2 + Real.sqrt 2) :=
  AlgebraicLog.irrational_of_eventualLowerBoundFour log_two_add_sqrt_two_eventualLowerBound

theorem sqrt_two_mul_log_two_irrational : Irrational (Real.sqrt 2 * Real.log 2) :=
  AlgebraicLog.irrational_of_eventualLowerBoundFour sqrt_two_mul_log_two_eventualLowerBound

theorem log_two_add_sqrt_two_irrationalityExponent_le_four :
    PiExponent.irrationalityExponent (Real.log 2 + Real.sqrt 2) ≤ 4 :=
  AlgebraicLog.irrationalityExponent_le_four_of_eventualLowerBoundFour
    log_two_add_sqrt_two_eventualLowerBound

theorem sqrt_two_mul_log_two_irrationalityExponent_le_four :
    PiExponent.irrationalityExponent (Real.sqrt 2 * Real.log 2) ≤ 4 :=
  AlgebraicLog.irrationalityExponent_le_four_of_eventualLowerBoundFour
    sqrt_two_mul_log_two_eventualLowerBound

end
end OAI.PairedAffine
