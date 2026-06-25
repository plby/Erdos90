import Mathlib.Algebra.Group.Pi.Units
import Towers.ClassField.RayClassGroups.Modulus

/-!
# Chapter V, Section 1, Theorem 1.7: the finite CRT factor

The finite part of the quotient in Theorem 1.7 is the unit group of the
integers modulo the finite ideal of the modulus.  The Chinese remainder
theorem identifies it with the product of the unit groups modulo the prime
powers occurring in the modulus.
-/

namespace Towers.CField.RCGroups

open IsDedekindDomain NumberField

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

namespace Modulus

/-- The Chinese remainder decomposition of the ring modulo the finite part
of a modulus. -/
noncomputable def finiteQuotientPi (m : Modulus K) :
    (𝓞 K ⧸ m.finiteIdeal) ≃+*
      ∀ p : m.finiteSupport,
        𝓞 K ⧸ p.1.asIdeal ^ m.finite p.1 :=
  HeightOneSpectrum.quotientEquivPiOfProdEq
    m.finiteIdeal
    (fun p : m.finiteSupport ↦ p.1)
    (fun p : m.finiteSupport ↦ m.finite p.1)
    (fun _ _ h ↦ Subtype.coe_injective.ne h)
    (Finset.prod_coe_sort m.finite.support
      fun p ↦ p.asIdeal ^ m.finite p)

/-- The finite Chinese remainder factor in Theorem 1.7, at the level of
unit groups. -/
noncomputable def finiteUnitsPi (m : Modulus K) :
    (𝓞 K ⧸ m.finiteIdeal)ˣ ≃*
      ∀ p : m.finiteSupport,
        (𝓞 K ⧸ p.1.asIdeal ^ m.finite p.1)ˣ :=
  (Units.mapEquiv (m.finiteQuotientPi K).toMulEquiv).trans
    MulEquiv.piUnits

end Modulus

end

end Towers.CField.RCGroups
