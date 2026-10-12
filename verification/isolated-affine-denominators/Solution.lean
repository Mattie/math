import DenominatorAffine.Pilot

set_option autoImplicit false
namespace DenominatorAffineVerification

theorem general_eventual_lower_bound {F : Type*} [Field F] [NumberField F]
    (a u v : F) (hdegree : Module.finrank ℚ F = 4) (σ₀ : F →ₐ[ℚ] ℂ)
    (base : ℝ) (hbase : 0 < base) (hbase1 : base ≠ 1)
    (hbaseImage : σ₀ a = (base : ℂ)) (x : ℝ) (hx : x ≠ 0)
    (good : Finset (F →ₐ[ℚ] ℂ)) (hgood : good.card = 2)
    (hcompatible : ∀ σ ∈ good, Complex.exp (σ u * ((x : ℂ) - σ v)) = σ a)
    (hscale : ∀ σ ∈ good, ‖σ u‖ ≤ 2) :
    ∀ nu : ℝ, 4 < nu → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (q : ℝ) ^ (-nu) ≤ |x - (p : ℝ) / (q : ℝ)| :=
  OAI.DenominatorAffine.Endpoint.paired_eventualLowerBound a u v hdegree σ₀
    base hbase hbase1 hbaseImage x hx good hgood hcompatible hscale

theorem eventual_lower_bound :
    ∀ nu : ℝ, 4 < nu → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (q : ℝ) ^ (-nu) ≤ |Real.log ((3 : ℝ) / 2) + Real.sqrt 2 - (p : ℝ) / (q : ℝ)| := OAI.DenominatorAffine.log_three_halves_add_sqrt_two_eventualLowerBound

theorem explicit_bound :
    ∀ nu : ℝ, 4 < nu → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (q : ℝ) ^ (-nu) ≤ |Real.log ((3 : ℝ) / 2) + Real.sqrt 2 - (p : ℝ) / (q : ℝ)| := OAI.DenominatorAffine.log_three_halves_add_sqrt_two_explicit_bound

theorem irrational : Irrational (Real.log ((3 : ℝ) / 2) + Real.sqrt 2) := OAI.DenominatorAffine.log_three_halves_add_sqrt_two_irrational

theorem irrationality_exponent_le_four :
    sSup {nu : ℝ | 0 < nu ∧
      ({r : ℚ | 2 ≤ r.den ∧ 0 < |Real.log ((3 : ℝ) / 2) + Real.sqrt 2 - (r : ℝ)| ∧
        |Real.log ((3 : ℝ) / 2) + Real.sqrt 2 - (r : ℝ)| < (r.den : ℝ) ^ (-nu)} : Set ℚ).Infinite} ≤ 4 := OAI.DenominatorAffine.log_three_halves_add_sqrt_two_irrationalityExponent_le_four

theorem standard_exponent_le_four :
    Irrational (Real.log ((3 : ℝ) / 2) + Real.sqrt 2) ∧
      ∀ nu : ℝ, 4 < nu → ¬ LiouvilleWith nu (Real.log ((3 : ℝ) / 2) + Real.sqrt 2) := OAI.DenominatorAffine.log_three_halves_add_sqrt_two_standard_exponent_le_four

end DenominatorAffineVerification
