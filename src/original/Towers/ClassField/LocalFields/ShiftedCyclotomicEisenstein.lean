import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral

/-!
# Appendix exercise A-9: norms from local cyclotomic extensions

Milne shifts the `p^(n+1)`-st cyclotomic polynomial by one, observes that it is
Eisenstein, and reads the norm of `zeta - 1` from its constant coefficient.
Mathlib already proves the Eisenstein theorem.  The two elementary polynomial
facts used in the argument are recorded below.

Identifying this polynomial as the minimal polynomial over `Q_p`, and then
connecting its constant coefficient to the field norm in the completed
cyclotomic extension, is not yet packaged by the current local cyclotomic API.
-/

namespace Towers.CField.LFields.SCEisens

open Ideal Polynomial
open scoped Polynomial

variable (p : ℕ) [hp : Fact p.Prime]

local notation "P" => Submodule.span ℤ {(p : ℤ)}

/-- Mathlib's Eisenstein theorem for the shifted prime-power cyclotomic
polynomial, in the indexing used in its library statement. -/
theorem shifte_cyclo_eisen (n : ℕ) :
    ((cyclotomic (p ^ (n + 1)) ℤ).comp (X + 1)).IsEisensteinAt P :=
  cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p n

/-- The value at one of a prime-power cyclotomic polynomial is `p`. -/
theorem cyclotomic_prime_one (n : ℕ) :
    eval (1 : ℤ) (cyclotomic (p ^ (n + 1)) ℤ) = p := by
  rw [cyclotomic_prime_pow_eq_geom_sum hp.out]
  rw [eval_finsetSum]
  simp only [eval_pow, eval_X, one_pow, Finset.sum_const, Finset.card_range,
    Nat.smul_one_eq_cast]

/-- Therefore the constant coefficient after shifting by one is `p`; this is
the coefficient that becomes the norm of `zeta - 1` in Milne's proof. -/
theorem shifted_cyclotomic_coeff (n : ℕ) :
    (((cyclotomic (p ^ (n + 1)) ℤ).comp (X + 1)).coeff 0) = p := by
  rw [coeff_zero_eq_eval_zero, eval_comp]
  simp [cyclotomic_prime_one]

end Towers.CField.LFields.SCEisens
