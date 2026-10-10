import Quadratic.RationalFamilies

namespace QuadraticFamilySpecification
open OAI.PiExponent

theorem real_bound (d : ℕ) (hd : 1 < d) (hsf : Squarefree d)
    (A B : ℚ) (hN : A ^ 2 - (d : ℚ) * B ^ 2 = 1)
    (hpos : 0 < (A : ℝ) + (B : ℝ) * Real.sqrt d)
    (hne : (A : ℝ) + (B : ℝ) * Real.sqrt d ≠ 1) (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-nu) ≤
        |Real.log ((A : ℝ) + (B : ℝ) * Real.sqrt d) / Real.sqrt d - (p : ℝ) / (q : ℝ)| :=
  (eventualLowerBound_iff_integer _).mp
    (OAI.Quadratic.real_quadratic_eventualLowerBound d hd hsf A B hN hpos hne) nu hnu

theorem imaginary_bound (d : ℕ) (hd : 0 < d) (x : ℝ) (A B : ℚ)
    (he : Complex.exp ((Complex.I * (Real.sqrt d : ℂ)) * (x : ℂ)) =
      (A : ℂ) + (B : ℂ) * (Complex.I * (Real.sqrt d : ℂ)))
    (hn : ∀ n : ℕ, 0 < n → ((A : ℂ) + (B : ℂ) * (Complex.I * (Real.sqrt d : ℂ))) ^ n ≠ 1)
    (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℤ, 2 ≤ Q ∧ ∀ p q : ℤ, Q ≤ q → (q : ℝ) ^ (-nu) ≤ |x - (p : ℝ) / (q : ℝ)| :=
  (eventualLowerBound_iff_integer _).mp
    (OAI.Quadratic.imaginary_quadratic_eventualLowerBound d hd x A B he hn) nu hnu

theorem real_exponent (d : ℕ) (hd : 1 < d) (hsf : Squarefree d)
    (A B : ℚ) (hN : A ^ 2 - (d : ℚ) * B ^ 2 = 1)
    (hpos : 0 < (A : ℝ) + (B : ℝ) * Real.sqrt d)
    (hne : (A : ℝ) + (B : ℝ) * Real.sqrt d ≠ 1) :
    irrationalityExponent (Real.log ((A : ℝ) + (B : ℝ) * Real.sqrt d) / Real.sqrt d) = 2 :=
  OAI.Quadratic.real_quadratic_exponent d hd hsf A B hN hpos hne

theorem imaginary_exponent (d : ℕ) (hd : 0 < d) (x : ℝ) (A B : ℚ)
    (he : Complex.exp ((Complex.I * (Real.sqrt d : ℂ)) * (x : ℂ)) =
      (A : ℂ) + (B : ℂ) * (Complex.I * (Real.sqrt d : ℂ)))
    (hn : ∀ n : ℕ, 0 < n → ((A : ℂ) + (B : ℂ) * (Complex.I * (Real.sqrt d : ℂ))) ^ n ≠ 1) :
    irrationalityExponent x = 2 := OAI.Quadratic.imaginary_quadratic_exponent d hd x A B he hn

/-- A nonintegral real norm-one value tests denominator two and slope greater than two. -/
theorem golden_squared_exponent :
    irrationalityExponent (Real.log ((3 + Real.sqrt 5) / 2) / Real.sqrt 5) = 2 := by
  have hsf : Squarefree (5 : ℕ) := (by norm_num : Nat.Prime 5).squarefree
  have hh := real_exponent 5 (by norm_num) hsf (3/2) (1/2) (by norm_num)
    (by norm_num; nlinarith [Real.sqrt_nonneg 5])
    (by norm_num; nlinarith [Real.sqrt_nonneg 5])
  have hv : ((3/2 : ℚ) : ℝ) + ((1/2 : ℚ) : ℝ) * Real.sqrt 5 = (3 + Real.sqrt 5) / 2 := by
    norm_num
    ring
  simpa only [Nat.cast_ofNat, hv] using hh

end QuadraticFamilySpecification

#print axioms QuadraticFamilySpecification.real_bound
#print axioms QuadraticFamilySpecification.imaginary_bound
#print axioms QuadraticFamilySpecification.real_exponent
#print axioms QuadraticFamilySpecification.imaginary_exponent
#print axioms QuadraticFamilySpecification.golden_squared_exponent
#print OAI.Quadratic.Context
#check @OAI.Quadratic.real_quadratic_eventualLowerBound
#check @OAI.Quadratic.imaginary_quadratic_eventualLowerBound
