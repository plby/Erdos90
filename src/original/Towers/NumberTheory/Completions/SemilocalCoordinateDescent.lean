import Towers.NumberTheory.Completions.DifferentCompletionDescent
import Towers.NumberTheory.Completions.SemilocalAtPrime
import Mathlib.RingTheory.DedekindDomain.Instances

/-!
# Descending a semilocal completed different bound at one coordinate

An upper prime `P` above `p` determines a height-one prime of the
semilocal localization of the upper ring at `p`.  A bound for the completed
image of the semilocal different descends faithfully to that local ring.
The equivalence with the ordinary local ring at `P` then gives the desired
bound for the localization of the global different.
-/

namespace Towers.NumberTheory.Milne

open Ideal IsDedekindDomain

noncomputable section

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
  [IsDomain R] [IsDomain S] [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [FaithfulSMul R S]

/-- The height-one prime of the semilocal upper ring corresponding to a
nonzero upper prime `P` lying over `p`. -/
noncomputable def semilocalHeightSpectrum
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (hP : P ≠ ⊥) : HeightOneSpectrum (SemilocalizationAtPrime S p) := by
  let B := SemilocalizationAtPrime S p
  let q : Ideal B := sPrime p P
  refine ⟨q, semilocal_prime p P, ?_⟩
  intro hq
  have hM : Algebra.algebraMapSubmonoid S p.primeCompl ≤
      nonZeroDivisors S :=
    algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul S
      p.primeCompl_le_nonZeroDivisors
  have hinj : Function.Injective (algebraMap S B) :=
    IsLocalization.injective B hM
  have hcomap := semilocalPrime_comap p P
  change q.comap (algebraMap S B) = P at hcomap
  rw [hq, Ideal.comap_bot_of_injective _ hinj] at hcomap
  exact hP hcomap.symm

section Different

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra
  Localization.AtPrime.liftAlgebra

variable [Module.Finite R S] [Module.IsTorsionFree R S]
variable [IsIntegralClosure S R (FractionRing S)]
variable [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

set_option synthInstance.maxHeartbeats 300000 in
-- The completed valuation ring and the twice-localized Dedekind ring both
-- require several localization instances.
set_option maxHeartbeats 1000000 in
/-- A completed bound for the semilocal different at the coordinate
corresponding to `P` descends to the localization of the global different
in `S_P`. -/
theorem localized_different_semilocal
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (hP : P ≠ ⊥)
    [Finite (SemilocalizationAtPrime S p ⧸ sPrime p P)]
    (Dhat : Ideal ((semilocalHeightSpectrum p P hP).adicCompletionIntegers
      (FractionRing S)))
    (n : ℕ)
    (hD : (differentIdeal (Localization.AtPrime p)
          (SemilocalizationAtPrime S p)).map
        (algebraMap (SemilocalizationAtPrime S p)
          ((semilocalHeightSpectrum p P hP).adicCompletionIntegers
            (FractionRing S))) = Dhat)
    (hbound : Dhat ∣
      IsLocalRing.maximalIdeal
        ((semilocalHeightSpectrum p P hP).adicCompletionIntegers
          (FractionRing S)) ^ n) :
    (differentIdeal R S).map
        (algebraMap S (Localization.AtPrime P)) ∣
      IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ n := by
  let B := SemilocalizationAtPrime S p
  let q : Ideal B := sPrime p P
  let v : HeightOneSpectrum B := semilocalHeightSpectrum p P hP
  let e := primeEquivSemilocal p P
  letI : Finite (B ⧸ v.asIdeal) := by
    change Finite (B ⧸ q)
    infer_instance
  have hsemilocal :
      (differentIdeal (Localization.AtPrime p) B).map
          (algebraMap B (Localization.AtPrime q)) ∣
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ n := by
    exact localized_dvd_maximal
      (K := FractionRing S) v
      (differentIdeal (Localization.AtPrime p) B) Dhat n hD hbound
  rw [Ideal.dvd_iff_le] at hsemilocal ⊢
  apply (e.toRingEquiv.idealComapOrderIso.symm.le_iff_le).mp
  change (IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ n).map
      e.toRingEquiv ≤
    ((differentIdeal R S).map
      (algebraMap S (Localization.AtPrime P))).map e.toRingEquiv
  dsimp only [e, q, B] at hsemilocal ⊢
  rw [Ideal.map_pow,
    maximal_ideal_semilocal,
    different_ideal_semilocal]
  exact hsemilocal

end Different

end

end Towers.NumberTheory.Milne
