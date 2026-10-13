import AffineCubic.Pilot

set_option autoImplicit false
set_option warningAsError true
namespace AffineCubicVerification

theorem eventual_lower_bound :
    ∀ nu : ℝ, 6 < nu → ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
        (q : ℝ) ^ (-nu) ≤
          |Real.log 2 + (2 : ℝ) ^ (1 / 3 : ℝ) - (p : ℝ) / (q : ℝ)| :=
  OAI.AffineCubic.Pilot.eventualLowerBound

theorem irrational : Irrational (Real.log 2 + (2 : ℝ) ^ (1 / 3 : ℝ)) :=
  OAI.AffineCubic.Pilot.irrational

theorem irrationality_exponent_le_six :
    sSup {nu : ℝ | 0 < nu ∧
      ({r : ℚ | 2 ≤ r.den ∧
        0 < |Real.log 2 + (2 : ℝ) ^ (1 / 3 : ℝ) - (r : ℝ)| ∧
        |Real.log 2 + (2 : ℝ) ^ (1 / 3 : ℝ) - (r : ℝ)| <
          (r.den : ℝ) ^ (-nu)} : Set ℚ).Infinite} ≤ 6 :=
  OAI.AffineCubic.Pilot.irrationalityExponent_le_six

theorem not_liouvilleWith :
    ∀ nu : ℝ, 6 < nu →
      ¬ LiouvilleWith nu (Real.log 2 + (2 : ℝ) ^ (1 / 3 : ℝ)) :=
  OAI.AffineCubic.Pilot.not_liouvilleWith

end AffineCubicVerification
