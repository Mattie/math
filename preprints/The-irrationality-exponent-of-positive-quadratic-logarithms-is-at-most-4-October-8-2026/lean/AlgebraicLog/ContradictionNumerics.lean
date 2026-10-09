import AlgebraicLog.ParameterShape

namespace OAI.AlgebraicLog

/-- Final comparison with coefficient two on the saved row weight. -/
theorem quadratic_determinant_bounds_inconsistent
    (nu theta Aeta b Ear Ean error collision logAbs : ℝ)
    (hnu : 2 < nu) (hb : 0 ≤ b) (hbtheta : b ≤ theta)
    (hgap : Ear + Ean + error < nu * (Aeta - theta) - 2 * (1 - theta))
    (hcollision : 2 + Ear + Ean + error < collision)
    (hlower : -2 * (1 - b) - Ear ≤ logAbs)
    (hupper : logAbs ≤ Ean + error + max (-collision) (-nu * (Aeta - b))) : False := by
  have hrow : 0 ≤ (nu - 2) * (theta - b) := mul_nonneg (by linarith) (by linarith)
  rcases le_total (-collision) (-nu * (Aeta - b)) with h | h
  · rw [max_eq_right h] at hupper
    nlinarith only [hrow, hgap, hlower, hupper]
  · rw [max_eq_left h] at hupper
    nlinarith only [hb, hcollision, hlower, hupper]

end OAI.AlgebraicLog
