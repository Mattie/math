import PositiveMain
noncomputable section
open intervalIntegral Set OAI.PiExponent
namespace OAI.PositiveIntegrals.Controls

/-- Pole-free interval between the two roots, with a negative integrand. -/
theorem between_roots : EventualLowerBound (∫ x : ℝ in (-1)..1, 1/(x^2-3)) := by
  have h := OAI.Integrals.positive_discriminant_bound 1 0 (-3) (-1) 1
    (by norm_num) (by norm_num) (by norm_num) (by
      intro x hx
      norm_num at hx ⊢
      have hh := mul_nonneg (by linarith [hx.1] : 0 ≤ x+1)
        (by linarith [hx.2] : 0 ≤ 1-x)
      nlinarith)
  simpa [sub_eq_add_neg] using h

/-- Negative leading coefficient, positive discriminant, and a positive integrand. -/
theorem negative_leading : EventualLowerBound (∫ x : ℝ in (-1)..1, 1/(-x^2+3)) := by
  have h := OAI.Integrals.positive_discriminant_bound (-1) 0 3 (-1) 1
    (by norm_num) (by norm_num) (by norm_num) (by
      intro x hx
      norm_num at hx ⊢
      have hh := mul_nonneg (by linarith [hx.1] : 0 ≤ x+1)
        (by linarith [hx.2] : 0 ≤ 1-x)
      nlinarith)
  simpa [sub_eq_add_neg] using h

/-- Square discriminant: both roots are rational and outside the integration interval. -/
theorem square_discriminant : EventualLowerBound (∫ x : ℝ in 2..3, 1/(x^2-1)) := by
  have h := OAI.Integrals.positive_discriminant_bound 1 0 (-1) 2 3
    (by norm_num) (by norm_num) (by norm_num) (by
      intro x hx
      norm_num at hx ⊢
      nlinarith [sq_nonneg (x-2)])
  simpa [sub_eq_add_neg] using h

#print axioms between_roots
#print axioms negative_leading
#print axioms square_discriminant
end OAI.PositiveIntegrals.Controls
