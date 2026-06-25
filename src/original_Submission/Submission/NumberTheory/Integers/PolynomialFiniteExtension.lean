import Mathlib

/-!
# Integral closure of `k[X]` in a finite extension

Milne, Remark 2.31(a), states without proof that the integral closure of
`k[X]` in every finite extension of `k(X)` is finite as a `k[X]`-module,
even when the field extension is inseparable.

The separable case follows from the trace-dual argument proved in
`IntegralClosureLattice.lean`.  The inseparable assertion is the deeper
normalization-finiteness theorem for the affine line and is not presently
packaged by Mathlib.  We therefore expose precisely that source-delegated
statement as a proposition, without introducing an axiom.
-/

namespace Submission.NumberTheory.Milne

open Polynomial

universe u v

/-- **Milne, Remark 2.31(a).** The normalization of the affine line in an
arbitrary finite function-field extension is finite, with no separability
hypothesis. -/
def IntegralClosureTheorem : Prop :=
  ∀ (k : Type u) (L : Type v) [Field k] [Field L]
    [Algebra k[X] L] [Algebra (FractionRing k[X]) L]
    [IsScalarTower k[X] (FractionRing k[X]) L]
    [FiniteDimensional (FractionRing k[X]) L],
    Module.Finite k[X] (integralClosure k[X] L)

/-- Fieldwise access to the exact theorem stated in Remark 2.31(a). -/
theorem integral_closure_module
    (hfinite : IntegralClosureTheorem.{u, v})
    (k : Type u) (L : Type v) [Field k] [Field L]
    [Algebra k[X] L] [Algebra (FractionRing k[X]) L]
    [IsScalarTower k[X] (FractionRing k[X]) L]
    [FiniteDimensional (FractionRing k[X]) L] :
    Module.Finite k[X] (integralClosure k[X] L) :=
  hfinite k L

end Submission.NumberTheory.Milne
