import Logarithm.Scaling

namespace OAI
noncomputable section
namespace Logarithm
open scoped BigOperators
open MvPolynomial

theorem scaleY_monomial {m : ℕ} (y : ℂ) (d : Fin (m+1) →₀ ℕ) (r : ℂ) :
    scaleY y (monomial d r) = C (y ^ d 0) * monomial d r := by
  rw [scaleY, aeval_monomial, monomial_eq,
    d.prod_fintype _ (fun _ => pow_zero _), d.prod_fintype _ (fun _ => pow_zero _)]
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, mul_pow, ← map_pow, MvPolynomial.algebraMap_eq]
  ring

end Logarithm
end
end OAI
