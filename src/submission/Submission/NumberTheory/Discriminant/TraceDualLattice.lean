import Mathlib

/-!
# Milne, Algebraic Number Theory, Remark 2.33

The trace-dual of the lattice spanned by a field basis is the lattice spanned by its
trace-dual basis.
-/

namespace Submission.NumberTheory.Milne

open scoped Pointwise

/-- Membership in the trace-dual lattice means that the trace pairing with every element of
the original lattice belongs to the base ring. This is the definition of `C*` in Remark 2.33. -/
theorem trace_dual
    (A K L : Type*) [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    {ι : Type*} (b : Module.Basis ι K L) (x : L) :
    x ∈ (Algebra.traceForm K L).dualSubmodule
        (Submodule.span A (Set.range b)) ↔
      ∀ y ∈ Submodule.span A (Set.range b),
        Algebra.trace K L (x * y) ∈ (1 : Submodule A K) := by
  rfl

/-- If `C` is the `A`-span of a `K`-basis `b`, then its trace-dual lattice `C*` is the
`A`-span of the trace-dual basis. This is Remark 2.33(a). -/
theorem trace_dual_span
    (A K L : Type*) [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Module.Basis ι K L) :
    (Algebra.traceForm K L).dualSubmodule (Submodule.span A (Set.range b)) =
      Submodule.span A (Set.range b.traceDual) := by
  classical
  exact (Algebra.traceForm K L).dualSubmodule_span_of_basis
    (traceForm_nondegenerate K L) b

/-- The coordinates of an element in the trace-dual basis are its traces against the original
basis. This is the coefficient calculation used in Proposition 2.29 and Remark 2.33. -/
theorem traceDual_apply
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Module.Basis ι K L) (x : L) (i : ι) :
    b.traceDual.repr x i = Algebra.trace K L (x * b i) := by
  exact b.traceDual_repr_apply x i

/-- If `L = K[β]` and `β` is integral over `A`, then the trace-dual of `A[β]` is
`f'(β)⁻¹ A[β]`, where `f` is the minimal polynomial of `β` over `K`. This is the
conclusion of Remark 2.33(b). -/
theorem dual_derivative_smul
    (A K L : Type*) [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (x : L) (hx : Algebra.adjoin K {x} = ⊤) (hAx : IsIntegral A x) :
    (Algebra.traceForm K L).dualSubmodule
        (Subalgebra.toSubmodule (Algebra.adjoin A {x})) =
      (Polynomial.aeval x (minpoly K x).derivative : L)⁻¹ •
        Subalgebra.toSubmodule (Algebra.adjoin A {x}) := by
  exact traceForm_dualSubmodule_adjoin A K hx hAx

end Submission.NumberTheory.Milne
