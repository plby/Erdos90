import Mathlib

/-!
# Milne, Algebraic Number Theory, Corollary 2.21

The trace and norm of an integral element in a finite extension of a fraction field belong to the
integrally closed base domain.
-/

namespace Submission.NumberTheory.Milne

/-- Let `K` be the fraction field of an integrally closed domain `A`, and let `L / K` be finite.
If `x : L` is integral over `A`, then its trace and norm from `L` to `K` are both in the image
of `A` in `K`. -/
theorem integral_norm_base
    (A K L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] {x : L} (hx : IsIntegral A x) :
    (∃ a : A, algebraMap A K a = Algebra.trace K L x) ∧
      ∃ b : A, algebraMap A K b = Algebra.norm K x := by
  constructor
  · exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace hx)
  · exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm K hx)

end Submission.NumberTheory.Milne
