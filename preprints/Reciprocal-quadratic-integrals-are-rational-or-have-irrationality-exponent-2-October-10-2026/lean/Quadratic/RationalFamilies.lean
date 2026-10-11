import Quadratic.Families
import Mathlib.Algebra.Squarefree.Basic

namespace OAI.Quadratic
open PiExponent
noncomputable section

theorem no_int_square_of_squarefree (d : ℕ) (hd : 1 < d) (hsf : Squarefree d) :
    ∀ n : ℤ, n * n ≠ (d : ℤ) := by
  intro n hn
  have hu : IsUnit n := (Int.squarefree_natCast.mpr hsf) n (by rw [hn])
  rcases Int.isUnit_iff.mp hu with h | h
  · rw [h] at hn
    norm_num at hn
    omega
  · rw [h] at hn
    norm_num at hn
    omega

theorem rational_common_denominator (A B : ℚ) :
    ∃ a b : ℤ, ∃ c : ℕ, 0 < c ∧ (a : ℚ) / (c : ℚ) = A ∧ (b : ℚ) / (c : ℚ) = B := by
  have ha : (A.den : ℚ) ≠ 0 := by exact_mod_cast A.pos.ne'
  have hb : (B.den : ℚ) ≠ 0 := by exact_mod_cast B.pos.ne'
  refine ⟨A.num * (B.den : ℤ), B.num * (A.den : ℤ), A.den * B.den,
    Nat.mul_pos A.pos B.pos, ?_, ?_⟩
  · push_cast
    calc
      _ = (A.num : ℚ) / (A.den : ℚ) := by field_simp
      _ = A := A.num_div_den
  · push_cast
    calc
      _ = (B.num : ℚ) / (B.den : ℚ) := by field_simp
      _ = B := B.num_div_den

/-- Rational coefficients express membership in the specified real quadratic field. -/
theorem real_quadratic_eventualLowerBound (d : ℕ) (hd : 1 < d) (hsf : Squarefree d)
    (A B : ℚ) (hN : A ^ 2 - (d : ℚ) * B ^ 2 = 1)
    (hpos : 0 < (A : ℝ) + (B : ℝ) * Real.sqrt d)
    (hne : (A : ℝ) + (B : ℝ) * Real.sqrt d ≠ 1) :
    EventualLowerBound (Real.log ((A : ℝ) + (B : ℝ) * Real.sqrt d) / Real.sqrt d) := by
  obtain ⟨a, b, c, hc, hA, hB⟩ := rational_common_denominator A B
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  have hNQ : (a : ℚ) * (a : ℚ) - (d : ℚ) * (b : ℚ) * (b : ℚ) = (c : ℚ) ^ 2 := by
    rw [← hA, ← hB] at hN
    field_simp [hcQ] at hN
    nlinarith only [hN]
  have hNZ : a * a - (d : ℤ) * b * b = (c : ℤ) ^ 2 := by exact_mod_cast hNQ
  have hAR : (a : ℝ) / (c : ℝ) = (A : ℝ) := by exact_mod_cast hA
  have hBR : (b : ℝ) / (c : ℝ) = (B : ℝ) := by exact_mod_cast hB
  have hv : realValue d a b c = (A : ℝ) + (B : ℝ) * Real.sqrt d := by
    unfold realValue
    rw [add_div, mul_div_right_comm, hAR, hBR]
  simpa only [hv] using real_norm_one_eventualLowerBound d (by omega)
    (no_int_square_of_squarefree d hd hsf) a b c hc hNZ
      (by simpa only [hv] using hpos) (by simpa only [hv] using hne)

theorem real_quadratic_exponent (d : ℕ) (hd : 1 < d) (hsf : Squarefree d)
    (A B : ℚ) (hN : A ^ 2 - (d : ℚ) * B ^ 2 = 1)
    (hpos : 0 < (A : ℝ) + (B : ℝ) * Real.sqrt d)
    (hne : (A : ℝ) + (B : ℝ) * Real.sqrt d ≠ 1) :
    irrationalityExponent (Real.log ((A : ℝ) + (B : ℝ) * Real.sqrt d) / Real.sqrt d) = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    (real_quadratic_eventualLowerBound d hd hsf A B hN hpos hne)

/-- Squarefreeness is unnecessary for the imaginary statement; every real branch is allowed. -/
theorem imaginary_quadratic_eventualLowerBound (d : ℕ) (hd : 0 < d) (x : ℝ) (A B : ℚ)
    (he : Complex.exp ((Complex.I * (Real.sqrt d : ℂ)) * (x : ℂ)) =
      (A : ℂ) + (B : ℂ) * (Complex.I * (Real.sqrt d : ℂ)))
    (hn : ∀ n : ℕ, 0 < n → ((A : ℂ) + (B : ℂ) * (Complex.I * (Real.sqrt d : ℂ))) ^ n ≠ 1) :
    EventualLowerBound x := by
  obtain ⟨a, b, c, hc, hA, hB⟩ := rational_common_denominator A B
  have hAC : (a : ℂ) / (c : ℂ) = (A : ℂ) := by exact_mod_cast hA
  have hBC : (b : ℂ) / (c : ℂ) = (B : ℂ) := by exact_mod_cast hB
  have hv : imaginaryValue d a b c = (A : ℂ) + (B : ℂ) * (Complex.I * (Real.sqrt d : ℂ)) := by
    unfold imaginaryValue
    rw [add_div, mul_div_right_comm, hAC, hBC]
  exact imaginary_non_torsion_eventualLowerBound d hd x a b c hc
    (by simpa only [hv] using he) (by simpa only [hv] using hn)

theorem imaginary_quadratic_exponent (d : ℕ) (hd : 0 < d) (x : ℝ) (A B : ℚ)
    (he : Complex.exp ((Complex.I * (Real.sqrt d : ℂ)) * (x : ℂ)) =
      (A : ℂ) + (B : ℂ) * (Complex.I * (Real.sqrt d : ℂ)))
    (hn : ∀ n : ℕ, 0 < n → ((A : ℂ) + (B : ℂ) * (Complex.I * (Real.sqrt d : ℂ))) ^ n ≠ 1) :
    irrationalityExponent x = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    (imaginary_quadratic_eventualLowerBound d hd x A B he hn)

end
end OAI.Quadratic
