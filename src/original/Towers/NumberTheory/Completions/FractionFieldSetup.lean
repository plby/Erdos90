import Towers.NumberTheory.Completions.SemilocalPrimeModule
import Mathlib.RingTheory.DedekindDomain.IntegralClosure


/-!
# Fraction fields of a semilocalized extension

For a finite extension of Dedekind domains `R → S`, localizing both rings
at the complement of a prime of `R` does not change their fraction fields.
This file packages the compatible algebra structures, fraction-ring
properties, integral closure, and the common-denominator localization needed
by the completion argument.
-/

namespace Towers.NumberTheory.Milne

open Algebra IsDedekindDomain IsLocalization nonZeroDivisors

noncomputable section

universe u

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra
  Localization.AtPrime.liftAlgebra

variable {R S : Type u} [CommRing R] [CommRing S]
  [IsDomain R] [IsDomain S]
  [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

omit [IsDedekindDomain R] in
/-- The lower local ring has the original lower fraction field. -/
theorem prime_fraction_ring
    (p : Ideal R) [p.IsPrime] :
    IsFractionRing (Localization.AtPrime p) (FractionRing R) := by
  infer_instance

omit [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S]
  [Algebra.IsSeparable (FractionRing R) (FractionRing S)] in
/-- The semilocal upper ring has the original upper fraction field, using
the localization lift algebra supplied by the Dedekind localization setup. -/
theorem semilocalization_prime_fraction
    (p : Ideal R) [p.IsPrime] :
    IsFractionRing (SemilocalizationAtPrime S p) (FractionRing S) := by
  infer_instance

omit [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S]
  [Algebra.IsSeparable (FractionRing R) (FractionRing S)] in
/-- The lower local fraction field embeds coherently in the upper fraction
field. -/
theorem fraction_scalar_tower
    (p : Ideal R) [p.IsPrime] :
    IsScalarTower (Localization.AtPrime p) (FractionRing R)
      (FractionRing S) := by
  infer_instance

omit [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S]
  [Algebra.IsSeparable (FractionRing R) (FractionRing S)] in
/-- The semilocal integral extension and its upper fraction field form the
expected scalar tower. -/
theorem semilocalization_fraction_tower
    (p : Ideal R) [p.IsPrime] :
    IsScalarTower (Localization.AtPrime p)
      (SemilocalizationAtPrime S p) (FractionRing S) := by
  infer_instance

omit [IsDedekindDomain R] [Algebra.IsSeparable (FractionRing R) (FractionRing S)] in
/-- The semilocal upper ring is the integral closure of the lower local ring
inside the original upper fraction field. -/
theorem semilocalization_fraction_ring
    (p : Ideal R) [p.IsPrime] :
    IsIntegralClosure (SemilocalizationAtPrime S p)
      (Localization.AtPrime p) (FractionRing S) := by
  exact IsIntegralClosure.of_isIntegrallyClosed
    (SemilocalizationAtPrime S p) (Localization.AtPrime p) (FractionRing S)

omit [IsDedekindDomain R] in
/-- The upper fraction field is obtained from the semilocal upper ring by
inverting the images of all non-zero elements of the lower local ring. -/
theorem semilo_local_ring
    (p : Ideal R) [p.IsPrime] :
    IsLocalization
      (Algebra.algebraMapSubmonoid (SemilocalizationAtPrime S p)
        (Localization.AtPrime p)⁰)
      (FractionRing S) := by
  letI : IsIntegralClosure (SemilocalizationAtPrime S p)
      (Localization.AtPrime p) (FractionRing S) :=
    semilocalization_fraction_ring p
  exact IsIntegralClosure.isLocalization_of_isSeparable
    (Localization.AtPrime p) (FractionRing R) (FractionRing S)
      (SemilocalizationAtPrime S p)

end

end Towers.NumberTheory.Milne
