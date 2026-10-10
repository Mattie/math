import PositiveSquareclass

namespace PositiveIntegrals

/-- Rationalizing a quadratic cross ratio produces coefficients of norm one. -/
theorem crossratio_norm_coefficients (r u v : ℚ)
    (hu : u ^ 2 - r ≠ 0) (hv : v ^ 2 - r ≠ 0)
    (s : ℝ) (hs : s ^ 2 = (r : ℝ)) :
    ∃ P S : ℚ, P ^ 2 - r * S ^ 2 = 1 ∧
      ((v : ℝ) - s) * ((u : ℝ) + s) /
        (((v : ℝ) + s) * ((u : ℝ) - s)) = (P : ℝ) + (S : ℝ) * s := by
  let X : ℚ := v * u - r
  let Y : ℚ := v - u
  let D : ℚ := X ^ 2 - r * Y ^ 2
  have hD : D ≠ 0 := by
    have heq : D = (v ^ 2 - r) * (u ^ 2 - r) := by dsimp [D, X, Y]; ring
    rw [heq]
    exact mul_ne_zero hv hu
  refine ⟨(X ^ 2 + r * Y ^ 2) / D, 2 * X * Y / D, ?_, ?_⟩
  · field_simp
    dsimp [D]
    ring
  · have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD
    have hur : (u : ℝ) ^ 2 - (r : ℝ) ≠ 0 := by exact_mod_cast hu
    have hvr : (v : ℝ) ^ 2 - (r : ℝ) ≠ 0 := by exact_mod_cast hv
    have huv : (((v : ℝ) + s) * ((u : ℝ) - s)) ≠ 0 := by
      apply mul_ne_zero
      · intro h
        apply hvr
        have hh : (v : ℝ) = -s := by linarith
        rw [hh]
        nlinarith
      · intro h
        apply hur
        have hh : (u : ℝ) = s := by linarith
        rw [hh]
        nlinarith
    push_cast
    apply (div_eq_iff huv).mpr
    field_simp
    dsimp [D, X, Y]
    push_cast
    rw [← hs]
    ring

/-- Expressing the root in a rational squareclass transfers the norm identity. -/
theorem crossratio_squareclass_norm_coefficients (r u v c : ℚ) (d : ℕ)
    (hu : u ^ 2 - r ≠ 0) (hv : v ^ 2 - r ≠ 0)
    (s : ℝ) (hs : s ^ 2 = (r : ℝ))
    (hrc : r = c ^ 2 * d) (hsrepr : s = (c : ℝ) * Real.sqrt (d : ℝ)) :
    ∃ P T : ℚ, P ^ 2 - (d : ℚ) * T ^ 2 = 1 ∧
      ((v : ℝ) - s) * ((u : ℝ) + s) /
        (((v : ℝ) + s) * ((u : ℝ) - s)) =
          (P : ℝ) + (T : ℝ) * Real.sqrt (d : ℝ) := by
  obtain ⟨P, S, hnorm, heq⟩ := crossratio_norm_coefficients r u v hu hv s hs
  refine ⟨P, S * c, ?_, ?_⟩
  · rw [hrc] at hnorm
    nlinarith [hnorm]
  · rw [heq, hsrepr]
    push_cast
    ring

end PositiveIntegrals

#print axioms PositiveIntegrals.crossratio_norm_coefficients
#print axioms PositiveIntegrals.crossratio_squareclass_norm_coefficients
