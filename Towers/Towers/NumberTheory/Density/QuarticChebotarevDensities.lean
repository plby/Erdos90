import Towers.NumberTheory.Density.CubicChebotarevDensities

/-!
# Milne, Chapter 8, Example 8.37: the `S₄` cycle-type table

Milne's quartic table records that `S₄` contains one identity, six
transpositions, three double transpositions, eight three-cycles, and six
four-cycles.  This file proves those class sizes and derives their conditional
Chebotarev densities.
-/

namespace Towers.NumberTheory.Milne

open Equiv IsDedekindDomain NumberField

noncomputable section

/-- The symmetric group on four letters has order twenty-four. -/
theorem s4_card : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_perm]
  norm_num

/-- There are six transpositions in `S₄`. -/
theorem s_conjugacy_ncard
    (g : Equiv.Perm (Fin 4)) (hg : g.cycleType = {2}) :
    (ConjClasses.mk g).carrier.ncard = 6 := by
  rw [conjugacy_ncard_type, hg]
  rw [Equiv.Perm.card_of_cycleType_singleton (by norm_num) (by norm_num)]
  norm_num [Nat.choose]

/-- There are three double transpositions in `S₄`. -/
theorem transposition_conjugacy_ncard
    (g : Equiv.Perm (Fin 4)) (hg : g.cycleType = {2, 2}) :
    (ConjClasses.mk g).carrier.ncard = 3 := by
  rw [conjugacy_ncard_type, hg]
  rw [Equiv.Perm.card_of_cycleType]
  norm_num

/-- There are eight three-cycles in `S₄`. -/
theorem s_4_ncard
    (g : Equiv.Perm (Fin 4)) (hg : g.cycleType = {3}) :
    (ConjClasses.mk g).carrier.ncard = 8 := by
  rw [conjugacy_ncard_type, hg]
  rw [Equiv.Perm.card_of_cycleType_singleton (by norm_num) (by norm_num)]
  norm_num

/-- There are six four-cycles in `S₄`. -/
theorem cycle_conjugacy_ncard
    (g : Equiv.Perm (Fin 4)) (hg : g.cycleType = {4}) :
    (ConjClasses.mk g).carrier.ncard = 6 := by
  rw [conjugacy_ncard_type, hg]
  rw [Equiv.Perm.card_of_cycleType_singleton (by norm_num) (by norm_num)]
  norm_num

variable (K : Type*) [Field K] [NumberField K]

/-- The identity cycle type has density `1/24` for an `S₄` extension. -/
theorem s_4_identity
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses (Equiv.Perm (Fin 4)))}
    (hcheb : ChebotarevDensityProperty K frobeniusClass) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk 1))
      (1 / 24) := by
  simpa [s4_card] using identity_frobenius_density K hcheb

/-- The transposition cycle type has density `1/4` for an `S₄` extension. -/
theorem s_4_transposition
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses (Equiv.Perm (Fin 4)))}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    (g : Equiv.Perm (Fin 4)) (hg : g.cycleType = {2}) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk g))
      (1 / 4) := by
  have h := hcheb (ConjClasses.mk g)
  rw [s_conjugacy_ncard g hg, s4_card] at h
  convert h using 1 ; norm_num

/-- The double-transposition cycle type has density `1/8` for an `S₄`
extension. -/
theorem s_4_double
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses (Equiv.Perm (Fin 4)))}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    (g : Equiv.Perm (Fin 4)) (hg : g.cycleType = {2, 2}) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk g))
      (1 / 8) := by
  have h := hcheb (ConjClasses.mk g)
  rw [transposition_conjugacy_ncard g hg, s4_card] at h
  convert h using 1 ; norm_num

/-- The three-cycle type has density `1/3` for an `S₄` extension. -/
theorem s_4_chebotarev
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses (Equiv.Perm (Fin 4)))}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    (g : Equiv.Perm (Fin 4)) (hg : g.cycleType = {3}) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk g))
      (1 / 3) := by
  have h := hcheb (ConjClasses.mk g)
  rw [s_4_ncard g hg, s4_card] at h
  convert h using 1 ; norm_num

/-- The four-cycle type has density `1/4` for an `S₄` extension. -/
theorem s_4_cycle
    {frobeniusClass : HeightOneSpectrum (𝓞 K) →
      Option (ConjClasses (Equiv.Perm (Fin 4)))}
    (hcheb : ChebotarevDensityProperty K frobeniusClass)
    (g : Equiv.Perm (Fin 4)) (hg : g.cycleType = {4}) :
    PNDensit K
      (primesFrobeniusClass K frobeniusClass (ConjClasses.mk g))
      (1 / 4) := by
  have h := hcheb (ConjClasses.mk g)
  rw [cycle_conjugacy_ncard g hg, s4_card] at h
  convert h using 1 ; norm_num

end

end Towers.NumberTheory.Milne
