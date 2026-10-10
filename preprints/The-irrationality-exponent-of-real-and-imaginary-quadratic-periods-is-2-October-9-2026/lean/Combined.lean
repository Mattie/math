import Quadratic.RationalFamilies
import PeriodicFamily.Main

noncomputable section
namespace OAI.Applications
open PiExponent

/-- Combining the two preserved families removes the root-of-unity exclusion.
The literal real angle must still be nonzero. -/
theorem imaginary_quadratic_all_eventualLowerBound
    (d : ℕ) (hd : 0 < d) (x : ℝ) (hx : x ≠ 0) (A B : ℚ)
    (he : Complex.exp ((Complex.I * (Real.sqrt d : ℂ)) * (x : ℂ)) =
      (A : ℂ) + (B : ℂ) * (Complex.I * (Real.sqrt d : ℂ))) :
    EventualLowerBound x := by
  by_cases hn : ∀ n : ℕ, 0 < n →
      ((A : ℂ) + (B : ℂ) * (Complex.I * (Real.sqrt d : ℂ))) ^ n ≠ 1
  · exact Quadratic.imaginary_quadratic_eventualLowerBound d hd x A B he hn
  · push_neg at hn
    obtain ⟨n, hn, hp⟩ := hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hexp : Complex.exp (PeriodicFamily.rotation d * (((n : ℝ) * x : ℝ) : ℂ)) = 1 := by
      have heq : PeriodicFamily.rotation d * (((n : ℝ) * x : ℝ) : ℂ) =
          (n : ℂ) * ((Complex.I * (Real.sqrt d : ℂ)) * (x : ℂ)) := by
        unfold PeriodicFamily.rotation
        push_cast
        ring
      rw [heq, Complex.exp_nat_mul, he, hp]
    let base : PeriodicFamily.PeriodData d := {
      num := 1
      den := 1
      den_pos := by norm_num
      angle := (n : ℝ) * x
      angle_ne_zero := mul_ne_zero hnR hx
      exp_angle := by simpa using hexp
      value_eq_one := by simp }
    letI : Fact (0 < d) := ⟨hd⟩
    have h := Imaginary.eventualLowerBound_div_nat
      (PeriodicFamily.DeterminantContradiction.period_eventualLowerBound base) n hn
    simpa [base, mul_div_cancel_left₀ x hnR] using h

theorem imaginary_quadratic_all_exponent
    (d : ℕ) (hd : 0 < d) (x : ℝ) (hx : x ≠ 0) (A B : ℚ)
    (he : Complex.exp ((Complex.I * (Real.sqrt d : ℂ)) * (x : ℂ)) =
      (A : ℂ) + (B : ℂ) * (Complex.I * (Real.sqrt d : ℂ))) :
    irrationalityExponent x = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    (imaginary_quadratic_all_eventualLowerBound d hd x hx A B he)

#print axioms imaginary_quadratic_all_eventualLowerBound
#print axioms imaginary_quadratic_all_exponent
end OAI.Applications