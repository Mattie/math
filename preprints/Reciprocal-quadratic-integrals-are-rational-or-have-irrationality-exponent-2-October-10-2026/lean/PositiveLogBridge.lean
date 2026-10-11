import PositiveScaling
import PositiveSquareclass
import PositiveCrossRatio
import Quadratic.RationalFamilies
import Logarithm.Main
noncomputable section
open Real intervalIntegral Set OAI.PiExponent
namespace OAI.Integrals

/-- Transfer the rational-log or real-quadratic endpoint to a positive rational radicand. -/
theorem norm_one_log_bound (c : ℚ) (d : ℕ) (hc : 0<c) (hd : 0<d)
    (hsf : Squarefree d) (P T : ℚ) (hN : P^2-(d:ℚ)*T^2=1)
    (ha : 0<(P:ℝ)+(T:ℝ)*sqrt d) (hne : (P:ℝ)+(T:ℝ)*sqrt d ≠ 1) :
    EventualLowerBound (log ((P:ℝ)+(T:ℝ)*sqrt d)/((c:ℝ)*sqrt d)) := by
  have hb : EventualLowerBound (log ((P:ℝ)+(T:ℝ)*sqrt d)/sqrt d) := by
    by_cases hd1 : d=1
    · have hpos : 0<P+T := by exact_mod_cast (by simpa [hd1] using ha : (0:ℝ)<(P:ℝ)+(T:ℝ))
      have hne' : P+T≠1 := by
        intro hh
        apply hne
        simpa [hd1] using congrArg (fun z : ℚ => (z:ℝ)) hh
      simpa [hd1] using OAI.Logarithm.DeterminantContradiction.rational_log_eventualLowerBound
        (P+T) hpos hne'
    · exact OAI.Quadratic.real_quadratic_eventualLowerBound d (by omega) hsf P T hN ha hne
  convert eventualLowerBound_div_pos_rat hb c hc using 1
  ring
end OAI.Integrals
