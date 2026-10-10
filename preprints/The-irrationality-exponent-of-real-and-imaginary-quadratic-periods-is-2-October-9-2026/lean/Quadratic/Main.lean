import Quadratic.Contexts
import Quadratic.DeterminantContradiction
import Logarithm.ExponentConsequence

namespace OAI.Quadratic
open PiExponent
noncomputable section

theorem period_irrationalityExponent_eq_two {f : Context} (base : PeriodData f) :
    irrationalityExponent base.angle = 2 :=
  LogarithmExtension.exponent_eq_two_of_eventualLowerBound
    (DeterminantContradiction.period_eventualLowerBound base)

end
end OAI.Quadratic
