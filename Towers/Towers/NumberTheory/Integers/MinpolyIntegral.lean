import Mathlib

/-!
# Milne, Algebraic Number Theory, Proposition 2.11

Over an integrally closed domain, an element of a finite field extension is integral precisely
when the coefficients of its minimal polynomial over the fraction field belong to the domain.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

/-- Let `K` be the fraction field of an integrally closed domain `A`, and let `L / K` be finite.
An element of `L` is integral over `A` exactly when every coefficient of its minimal polynomial
over `K` lies in the image of `A`.

Membership in `Polynomial.lifts (algebraMap A K)` is Mathlib's bundled formulation of the
coefficient condition. -/
theorem integral_minpoly_lifts
    (A K L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] (x : L) :
    IsIntegral A x ↔ minpoly K x ∈ Polynomial.lifts (algebraMap A K) := by
  constructor
  · intro hx
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hx]
    rw [Polynomial.mem_lifts]
    exact ⟨minpoly A x, rfl⟩
  · intro hx
    have hxK : IsIntegral K x := Algebra.IsIntegral.isIntegral x
    obtain ⟨p, hp, -, hmonic⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic hx (minpoly.monic hxK)
    refine ⟨p, hmonic, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K x p, hp, minpoly.aeval]

end Towers.NumberTheory.Milne
