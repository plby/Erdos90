import Towers.NumberTheory.Completions.SemilocalCompletionFactor

/-!
# The lower local prime in the semilocal completion setup

For a nonzero prime `p` of a Dedekind domain, the maximal ideal of `R_p`
is a height-one prime.  Its extension to the semilocalized upper ring is
nonzero, and a global upper prime selects the corresponding factor in the
semilocal completion product.
-/

namespace Towers.NumberTheory.Milne

open Ideal IsDedekindDomain UniqueFactorizationMonoid

noncomputable section

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
  [IsDomain R] [IsDomain S] [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [FaithfulSMul R S]

/-- The height-one prime of `R_p` given by its maximal ideal. -/
noncomputable def maximalHeightSpectrum
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) :
    HeightOneSpectrum (Localization.AtPrime p) := by
  let A := Localization.AtPrime p
  have hmax : (IsLocalRing.maximalIdeal A).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  have hne : IsLocalRing.maximalIdeal A ≠ ⊥ := by
    have hpmap : p.map (algebraMap R A) ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot hp
    simpa only [A, IsLocalization.AtPrime.map_eq_maximalIdeal] using hpmap
  exact ⟨IsLocalRing.maximalIdeal A, hmax, hne⟩

omit [IsDedekindDomain R] in
@[simp]
theorem height_spectrum_ideal
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) :
    (maximalHeightSpectrum p hp).asIdeal =
      IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
  rfl

omit [IsDedekindDomain R] [IsDedekindDomain S] in
/-- The lower maximal ideal remains nonzero after extension to the
semilocalization of the upper ring. -/
theorem maximal_semilocalization_bot
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p)
          (SemilocalizationAtPrime S p)) ≠ ⊥ := by
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime p) ≠ ⊥ :=
    (maximalHeightSpectrum p hp).ne_bot
  exact Ideal.map_ne_bot_of_ne_bot hmax

omit [IsDomain S] [IsDedekindDomain R] [IsDedekindDomain S]
    [FaithfulSMul R S] in
/-- The extended lower prime is the ideal used to index the semilocal
completion decomposition. -/
@[simp]
theorem maximal_height_spectrum
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥) :
    (maximalHeightSpectrum p hp).asIdeal.map
        (algebraMap (Localization.AtPrime p)
          (SemilocalizationAtPrime S p)) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p)
          (SemilocalizationAtPrime S p)) :=
  rfl

/-- The selected factor and the semilocal upper prime give the same
completed field. -/
noncomputable def selectedSemilocalAdic
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥)
    {L : Type u} [Field L]
    [Algebra (SemilocalizationAtPrime S p) L]
    [IsFractionRing (SemilocalizationAtPrime S p) L]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] (hP : P ≠ ⊥) :
    (factorHeightSpectrum
      ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (SemilocalizationAtPrime S p)))
      (semilocalFactorIndex p hp P)).adicCompletion L ≃+*
      (semilocalHeightSpectrum p P hP).adicCompletion L :=
  RingEquiv.cast (R := fun v : HeightOneSpectrum (SemilocalizationAtPrime S p) =>
    v.adicCompletion L)
    (spectrum_semilocal_index p hp P hP)

/-- The selected factor and the semilocal upper prime give the same
completed valuation integer ring. -/
noncomputable def selectedSemilocalIntegers
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥)
    {L : Type u} [Field L]
    [Algebra (SemilocalizationAtPrime S p) L]
    [IsFractionRing (SemilocalizationAtPrime S p) L]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] (hP : P ≠ ⊥) :
    (factorHeightSpectrum
      ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (SemilocalizationAtPrime S p)))
      (semilocalFactorIndex p hp P)).adicCompletionIntegers L ≃+*
      (semilocalHeightSpectrum p P hP).adicCompletionIntegers L :=
  RingEquiv.cast (R := fun v : HeightOneSpectrum (SemilocalizationAtPrime S p) =>
    v.adicCompletionIntegers L)
    (spectrum_semilocal_index p hp P hP)

end

end Towers.NumberTheory.Milne
