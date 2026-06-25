import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Milne, Algebraic Number Theory, Remark 7.17

For the rational function field `k(T)`, the finite-prime contribution of a
nonzero rational function is the degree of its numerator minus the degree of
its denominator.  The valuation at infinity is the negative of this number,
so the total additive valuation is zero.
-/

namespace Submission.NumberTheory.Milne

open Polynomial UniqueFactorizationMonoid

variable {k : Type*} [Field k] [NormalizationMonoid k]

/-- The degree of a nonzero polynomial is the sum of the degrees of its
normalized irreducible factors, counted with multiplicity. -/
theorem nat_normalized_factors (f : k[X]) (hf : f ≠ 0) :
    ((normalizedFactors f).map Polynomial.natDegree).sum = f.natDegree := by
  rw [← Polynomial.natDegree_multiset_prod (normalizedFactors f)
    (UniqueFactorizationMonoid.zero_notMem_normalizedFactors f)]
  exact Polynomial.natDegree_eq_of_degree_eq
    (Polynomial.degree_eq_degree_of_associated
      (UniqueFactorizationMonoid.prod_normalizedFactors hf))

/-- The weighted sum of the finite orders of a nonzero rational function.
Each irreducible polynomial is weighted by the degree of its residue field
over `k`. -/
noncomputable def rationalFunctionDegree (x : RatFunc k) : ℤ :=
  (((normalizedFactors x.num).map Polynomial.natDegree).sum : ℤ) -
    (((normalizedFactors x.denom).map Polynomial.natDegree).sum : ℤ)

/-- Milne, Remark 7.17, for `k(T)`: the weighted finite orders and the order
at infinity of a nonzero rational function sum to zero. -/
theorem function_additive_formula (x : RatFunc k) (hx : x ≠ 0) :
    rationalFunctionDegree x + (-x.intDegree) = 0 := by
  rw [rationalFunctionDegree,
    nat_normalized_factors x.num (RatFunc.num_ne_zero hx),
    nat_normalized_factors x.denom x.denom_ne_zero]
  simp [RatFunc.intDegree]

end Submission.NumberTheory.Milne
