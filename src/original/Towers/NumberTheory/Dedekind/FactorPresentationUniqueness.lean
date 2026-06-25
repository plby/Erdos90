import Towers.NumberTheory.Dedekind.ExteriorAnnihilatorInvariant

/-!
# Uniqueness of invariant-factor presentations

The exterior-power invariants show that two descending cyclic presentations of the same module,
with the same number of slots, have identical ideal families.
-/

namespace Towers.NumberTheory.Milne

open scoped DirectSum

/-- Two equal-length antitone cyclic presentations of one module have the same invariant
factors. -/
theorem invariant_factors_common
    (A T : Type*) [CommRing A]
    [AddCommGroup T] [Module A T]
    (n : ℕ) (I J : Fin n → Ideal A) (hI : Antitone I) (hJ : Antitone J)
    (eI : T ≃ₗ[A] DirectSum (Fin n) (fun i ↦ A ⧸ I i))
    (eJ : T ≃ₗ[A] DirectSum (Fin n) (fun i ↦ A ⧸ J i)) :
    I = J :=
  invariant_factors_linear A n I J hI hJ (eI.symm ≪≫ₗ eJ)

end Towers.NumberTheory.Milne
