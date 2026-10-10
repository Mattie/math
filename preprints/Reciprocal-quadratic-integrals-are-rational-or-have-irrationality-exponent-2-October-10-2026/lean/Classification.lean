import RepeatedRoot
import PositiveSolution

noncomputable section
open intervalIntegral Set
namespace OAI.IntegralClassification

/-- Among pole-free genuine rational quadratics, rationality detects a repeated root. -/
theorem rational_iff_discriminant_zero (A B C a b : ℚ) (hA : A ≠ 0) (hab : a < b)
    (hp : ∀ x ∈ Icc (a:ℝ) (b:ℝ), (A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ) ≠ 0) :
    (∃ r : ℚ, (∫ x : ℝ in (a:ℝ)..(b:ℝ), 1/((A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ))) = (r:ℝ)) ↔
      B^2-4*A*C=0 := by
  constructor
  · rintro ⟨r,hr⟩
    by_contra hD
    have hi := (PositiveIntegralCheck.nonzero_discriminant_exponent_two
      A B C a b hA hab hD hp).1
    exact hi.ne_rat r hr
  · intro hD
    exact repeated_root_rational A B C a b hA hD hab hp

/-- The complementary case is irrational and has the inherited exponent-two bound. -/
theorem irrational_iff_discriminant_ne_zero (A B C a b : ℚ) (hA : A ≠ 0) (hab : a < b)
    (hp : ∀ x ∈ Icc (a:ℝ) (b:ℝ), (A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ) ≠ 0) :
    Irrational (∫ x : ℝ in (a:ℝ)..(b:ℝ), 1/((A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ))) ↔
      B^2-4*A*C≠0 := by
  constructor
  · intro hi hD
    obtain ⟨r,hr⟩ := repeated_root_rational A B C a b hA hD hab hp
    exact hi.ne_rat r hr
  · intro hD
    exact (PositiveIntegralCheck.nonzero_discriminant_exponent_two A B C a b hA hab hD hp).1

/-- Full dichotomy, exposing ordinary rationality and the literal approximation bound. -/
theorem reciprocal_quadratic_dichotomy (A B C a b : ℚ) (hA : A ≠ 0) (hab : a < b)
    (hp : ∀ x ∈ Icc (a:ℝ) (b:ℝ), (A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ) ≠ 0) :
    (B^2-4*A*C=0 ∧
      ∃ r : ℚ, (∫ x : ℝ in (a:ℝ)..(b:ℝ), 1/((A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ))) = (r:ℝ)) ∨
    (B^2-4*A*C≠0 ∧
      Irrational (∫ x : ℝ in (a:ℝ)..(b:ℝ), 1/((A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ))) ∧
      (∀ ν : ℝ, 2<ν →
        ¬LiouvilleWith ν (∫ x : ℝ in (a:ℝ)..(b:ℝ), 1/((A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ)))) ∧
      (∀ ν : ℝ, 2<ν → ∃ Q : ℕ, 2≤Q ∧ ∀ (p : ℤ) (q : ℕ), Q≤q →
        1/(q:ℝ)^ν ≤ |(∫ x : ℝ in (a:ℝ)..(b:ℝ),
          1/((A:ℝ)*x^2+(B:ℝ)*x+(C:ℝ)))-(p:ℝ)/(q:ℝ)|)) := by
  by_cases hD : B^2-4*A*C=0
  · exact Or.inl ⟨hD,repeated_root_rational A B C a b hA hD hab hp⟩
  · obtain ⟨hi,hn⟩ := PositiveIntegralCheck.nonzero_discriminant_exponent_two A B C a b hA hab hD hp
    exact Or.inr ⟨hD,hi,hn,PositiveIntegralCheck.nonzero_discriminant_bound A B C a b hA hab hD hp⟩

end OAI.IntegralClassification
