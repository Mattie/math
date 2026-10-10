import Combined
import StandardBridge
import Mathlib.Data.Nat.Squarefree

set_option autoImplicit false

namespace CompareChallenge

private theorem literal_bound {x : ℝ} (h : OAI.PiExponent.EventualLowerBound x) :
    ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (1 : ℝ) / (q : ℝ) ^ ν ≤ |x - (p : ℝ) / (q : ℝ)| := by
  intro ν hν
  obtain ⟨Q, hQ, hb⟩ := h ν hν
  refine ⟨Q, hQ, fun p q hq => ?_⟩
  simpa only [Real.rpow_neg (Nat.cast_nonneg q), one_div] using hb p q hq


/-- Conventional irrationality exponent two, expressed using standard definitions. -/
theorem pi_sqrt_exponent_two (r : ℚ) (hr : 0 < r) :
    Irrational (Real.pi / Real.sqrt (r : ℝ)) ∧
      ∀ ν : ℝ, 2 < ν → ¬ LiouvilleWith ν (Real.pi / Real.sqrt (r : ℝ)) := by
  exact standard_exponent_two_of_eventual_bound _
    (literal_bound (OAI.PeriodicFamily.rational_scaled_pi_eventualLowerBound r hr))

theorem pi_sqrt_eventual_bound (r : ℚ) (hr : 0 < r) :
    ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (1 : ℝ) / (q : ℝ) ^ ν ≤
          |Real.pi / Real.sqrt (r : ℝ) - (p : ℝ) / (q : ℝ)| := by
  exact literal_bound (OAI.PeriodicFamily.rational_scaled_pi_eventualLowerBound r hr)

/-- The positive real logarithm, including units below one. -/
theorem quadratic_log_exponent_two
    (d : ℕ) (hd : Squarefree d) (hd1 : 1 < d) (A B : ℚ)
    (hnorm : A ^ 2 - (d : ℚ) * B ^ 2 = 1)
    (hpos : 0 < (A : ℝ) + (B : ℝ) * Real.sqrt (d : ℝ))
    (hne : (A : ℝ) + (B : ℝ) * Real.sqrt (d : ℝ) ≠ 1) :
    Irrational (Real.log ((A : ℝ) + (B : ℝ) * Real.sqrt (d : ℝ)) /
      Real.sqrt (d : ℝ)) ∧
    ∀ ν : ℝ, 2 < ν → ¬ LiouvilleWith ν
      (Real.log ((A : ℝ) + (B : ℝ) * Real.sqrt (d : ℝ)) /
        Real.sqrt (d : ℝ)) := by
  exact standard_exponent_two_of_eventual_bound _
    (literal_bound (OAI.Quadratic.real_quadratic_eventualLowerBound d hd1 hd A B hnorm hpos hne))

theorem quadratic_log_eventual_bound
    (d : ℕ) (hd : Squarefree d) (hd1 : 1 < d) (A B : ℚ)
    (hnorm : A ^ 2 - (d : ℚ) * B ^ 2 = 1)
    (hpos : 0 < (A : ℝ) + (B : ℝ) * Real.sqrt (d : ℝ))
    (hne : (A : ℝ) + (B : ℝ) * Real.sqrt (d : ℝ) ≠ 1) :
    ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (1 : ℝ) / (q : ℝ) ^ ν ≤
          |Real.log ((A : ℝ) + (B : ℝ) * Real.sqrt (d : ℝ)) /
            Real.sqrt (d : ℝ) - (p : ℝ) / (q : ℝ)| := by
  exact literal_bound
    (OAI.Quadratic.real_quadratic_eventualLowerBound d hd1 hd A B hnorm hpos hne)

/-- The exponential equation includes every real branch and every torsion value. -/
theorem imaginary_quadratic_exponent_two
    (d : ℕ) (hd : 0 < d) (x : ℝ) (hx : x ≠ 0) (A B : ℚ)
    (hexp : Complex.exp (Complex.I * (Real.sqrt (d : ℝ) : ℂ) * (x : ℂ)) =
      (A : ℂ) + (B : ℂ) * Complex.I * (Real.sqrt (d : ℝ) : ℂ)) :
    Irrational x ∧ ∀ ν : ℝ, 2 < ν → ¬ LiouvilleWith ν x := by
  have he : Complex.exp ((Complex.I * (Real.sqrt d : ℂ)) * (x : ℂ)) =
      (A : ℂ) + (B : ℂ) * (Complex.I * (Real.sqrt d : ℂ)) := by
    simpa only [mul_assoc] using hexp
  exact standard_exponent_two_of_eventual_bound _
    (literal_bound (OAI.Applications.imaginary_quadratic_all_eventualLowerBound d hd x hx A B he))

theorem imaginary_quadratic_eventual_bound
    (d : ℕ) (hd : 0 < d) (x : ℝ) (hx : x ≠ 0) (A B : ℚ)
    (hexp : Complex.exp (Complex.I * (Real.sqrt (d : ℝ) : ℂ) * (x : ℂ)) =
      (A : ℂ) + (B : ℂ) * Complex.I * (Real.sqrt (d : ℝ) : ℂ)) :
    ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (1 : ℝ) / (q : ℝ) ^ ν ≤ |x - (p : ℝ) / (q : ℝ)| := by
  have he : Complex.exp ((Complex.I * (Real.sqrt d : ℂ)) * (x : ℂ)) =
      (A : ℂ) + (B : ℂ) * (Complex.I * (Real.sqrt d : ℂ)) := by
    simpa only [mul_assoc] using hexp
  exact literal_bound
    (OAI.Applications.imaginary_quadratic_all_eventualLowerBound d hd x hx A B he)

end CompareChallenge
