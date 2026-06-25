import Towers.NumberTheory.Density.ChebotarevDensity

/-!
# Chapter V, Section 3, Theorem 3.23: Chebotarev density

The Towers ANT development states the exact natural-density assertion as
`ChebotarevDensityTheorem` and proves its formal consequences.  The analytic
proof of that proposition is not yet in Mathlib, so this file gives
source-numbered wrappers conditional on the exact statement rather than
introducing an axiom.
-/

namespace Towers.CField.ARecip

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne

noncomputable section

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The exact Chebotarev density assertion for the arithmetic Frobenius
class map of `L / K`. -/
abbrev ChebotarevStatement : Prop := ChebotarevDensityTheorem K L

/-- Theorem 3.23, once the analytic Chebotarev statement is supplied. -/
theorem frobenius_class_density
    (hcheb : ChebotarevStatement K L) (C : ConjClasses Gal(L/K)) :
    PNDensit K
      {p | arithmeticFrobeniusClass K L p = C}
      ((C.carrier.ncard : ℝ) / Nat.card Gal(L/K)) :=
  natural_density_frobenius K L hcheb C

/-- The abelian specialization of Theorem 3.23: each individual Frobenius
element has density `1 / |G|`. -/
theorem chebotarev_abelian_density
    {G : Type*} [CommGroup G] [Finite G]
    {frobeniusClass : HeightOneSpectrum (𝓞 K) → Option (ConjClasses G)}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) (sigma : G) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk sigma))
      (1 / Nat.card G) :=
  abelian_density_chebotarev K hcheb sigma

end

end Towers.CField.ARecip
