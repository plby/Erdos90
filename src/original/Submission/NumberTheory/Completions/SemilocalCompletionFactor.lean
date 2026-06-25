import Submission.NumberTheory.Completions.SemilocalCompletionAssembly
import Submission.NumberTheory.Completions.SemilocalCoordinateDescent


/-!
# A global upper prime as a semilocal completion factor

An upper prime `P` above a nonzero lower prime `p` maps to a prime of the
semilocalization of the upper ring.  This prime divides the extension of the
maximal ideal of `R_p`, hence occurs among the factors indexing the product
decomposition of its completion.
-/

namespace Submission.NumberTheory.Milne

open Ideal IsDedekindDomain UniqueFactorizationMonoid

noncomputable section

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
  [IsDomain R] [IsDomain S] [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [FaithfulSMul R S]

omit [IsDedekindDomain R] in
/-- The semilocal prime attached to `P` divides the extension of the maximal
ideal of `R_p`. -/
theorem semilocal_dvd_mapped
    (p : Ideal R) [p.IsPrime]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    sPrime p P ∣
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (SemilocalizationAtPrime S p)) := by
  have hqover : (sPrime p P).LiesOver
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) :=
    IsLocalization.AtPrime.liesOver_map_of_liesOver p
      (Localization.AtPrime p) (SemilocalizationAtPrime S p) P
  apply Ideal.dvd_iff_le.mpr
  apply Ideal.map_le_iff_le_comap.mpr
  exact hqover.over.le

/-- The semilocal prime attached to `P` occurs among the prime factors of the
extension of the maximal ideal of `R_p`. -/
theorem semilocal_mapped_maximal
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥)
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    sPrime p P ∈ factors
      ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (SemilocalizationAtPrime S p))) := by
  let A := Localization.AtPrime p
  let B := SemilocalizationAtPrime S p
  let I := IsLocalRing.maximalIdeal A
  let J := I.map (algebraMap A B)
  let q := sPrime p P
  have hI : I ≠ ⊥ := by
    have hpmap : p.map (algebraMap R A) ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot hp
    simpa only [I, A, IsLocalization.AtPrime.map_eq_maximalIdeal] using hpmap
  have hJ : J ≠ 0 := Ideal.map_ne_bot_of_ne_bot hI
  have hqdvd : q ∣ J := semilocal_dvd_mapped p P
  have hqne : q ≠ ⊥ := by
    intro hq
    have hJq : J ≤ q := Ideal.dvd_iff_le.mp hqdvd
    exact hJ (le_bot_iff.mp (hq ▸ hJq))
  have hqprime : Prime q :=
    Ideal.prime_of_isPrime hqne (semilocal_prime p P)
  obtain ⟨q', hq'mem, hqq'⟩ :=
    exists_mem_factors_of_dvd hJ hqprime.irreducible hqdvd
  have hqq' : q = q' := associated_iff_eq.mp hqq'
  simpa only [q, J, I, B, A, hqq'] using hq'mem

/-- The factor-coordinate of the semilocal completion selected by an upper
prime `P` above `p`. -/
noncomputable def semilocalFactorIndex
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥)
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    (factors
      ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p)
          (SemilocalizationAtPrime S p)))).toFinset :=
  ⟨sPrime p P, Multiset.mem_toFinset.mpr
    (semilocal_mapped_maximal p hp P)⟩

/-- The factor spectrum selected by `P` has underlying ideal equal to the
semilocal prime attached to `P`. -/
@[simp]
theorem height_spectrum_semilocal
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥)
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] (hP : P ≠ ⊥) :
    (factorHeightSpectrum
      ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (SemilocalizationAtPrime S p)))
      (semilocalFactorIndex p hp P)).asIdeal =
        (semilocalHeightSpectrum p P hP).asIdeal := by
  rfl

/-- The factor spectrum selected by `P` is exactly its semilocal height-one
spectrum. -/
@[simp]
theorem spectrum_semilocal_index
    (p : Ideal R) [p.IsPrime] (hp : p ≠ ⊥)
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] (hP : P ≠ ⊥) :
    factorHeightSpectrum
      ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (SemilocalizationAtPrime S p)))
      (semilocalFactorIndex p hp P) =
        semilocalHeightSpectrum p P hP := by
  apply HeightOneSpectrum.ext
  exact height_spectrum_semilocal p hp P hP

end

end Submission.NumberTheory.Milne
