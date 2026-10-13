import AlgebraicLog.ParameterShape

namespace OAI.AffineCubic

/-- Final comparison with coefficient three on the saved row weight. -/
theorem cubic_determinant_bounds_inconsistent
    (nu theta Aeta b Ear Ean error collision logAbs : ℝ)
    (hnu : 3 < nu) (hb : 0 ≤ b) (hbtheta : b ≤ theta)
    (hgap : Ear + Ean + error < nu * (Aeta - theta) - 3 * (1 - theta))
    (hcollision : 3 + Ear + Ean + error < collision)
    (hlower : -3 * (1 - b) - Ear ≤ logAbs)
    (hupper : logAbs ≤ Ean + error + max (-collision) (-nu * (Aeta - b))) : False := by
  have hrow : 0 ≤ (nu - 3) * (theta - b) := mul_nonneg (by linarith) (by linarith)
  rcases le_total (-collision) (-nu * (Aeta - b)) with h | h
  · rw [max_eq_right h] at hupper
    nlinarith only [hrow, hgap, hlower, hupper]
  · rw [max_eq_left h] at hupper
    nlinarith only [hb, hcollision, hlower, hupper]

end OAI.AffineCubic
