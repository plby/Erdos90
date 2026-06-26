import Towers.ClassField.BrauerLocalization.CokernelAssembly
import Towers.ClassField.NormIndex.SplitAwayNorm
import Towers.ClassField.NormIndex.ContainsAllRamified

/-!
# Assembly of the later results in Chapter VII, Section 4

Once Lemma VII.4.5 is unconditional, the already formalized split-away norm
and Frobenius fixed-field arguments give Propositions VII.4.6 and VII.4.7.
-/

namespace Towers.CField.BLoc

open Ideal IsDedekindDomain NumberField Set
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.NIndex
open Towers.CField.ARecip

universe u

/-- **Proposition VII.4.6.**  A nontrivial finite solvable Galois
extension has infinitely many finite primes that do not split completely. -/
theorem nontrivial_nonsplit_primes : NontrivialNonsplitPrimes.{u} :=
  split_away_only cyclicSubextensionDegree

/-- **Proposition VII.4.7.**  Frobenius elements outside any finite
ramified exceptional set generate the whole solvable Galois group. -/
theorem elements_generate_away :
    ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      [IsSolvable Gal(L/K)],
      ∀ T : Finset (FinitePrime L),
        ContainsRamifiedPrimes (K := K) (L := L) T →
          frobeniusGeneratedSubgroup (K := K) (L := L) T = ⊤ :=
  numberElementStatement nontrivial_nonsplit_primes

/-- The finite primes upstairs whose contractions lie in a fixed finite set
of base places form a finite set. -/
theorem primesAboveBridge :
    PrimesAboveBridge.{u} := by
  classical
  intro K _ _ L S
  let R := NumberField.RingOfIntegers K
  let T := NumberField.RingOfIntegers L.carrier
  let U : Set (FinitePrime L.carrier) :=
    {Q | (Sum.inl (Q.under R) : NumberFieldPlace K) ∈ S}
  have hfiber : ∀ P : FinitePrime K,
      Set.Finite {Q : FinitePrime L.carrier | Q.under R = P} := by
    intro P
    apply Set.Finite.of_finite_image
        (f := fun Q : FinitePrime L.carrier ↦ Q.asIdeal)
    · apply (finite_places
          (K := K) (L := L.carrier) P.asIdeal).subset
      rintro I ⟨Q, hQ, rfl⟩
      change Q.asIdeal ∈ P.asIdeal.primesOver T
      exact ⟨Q.isPrime,
        ⟨(congrArg HeightOneSpectrum.asIdeal hQ).symm⟩⟩
    · intro Q _ Z _ hQZ
      exact HeightOneSpectrum.ext hQZ
  let V : Set (FinitePrime L.carrier) :=
    ⋃ P ∈ (S.toLeft : Set (FinitePrime K)),
      {Q : FinitePrime L.carrier | Q.under R = P}
  have hV : V.Finite :=
    S.toLeft.finite_toSet.biUnion fun P _ ↦ hfiber P
  have hU : U.Finite := by
    apply hV.subset
    intro Q hQ
    apply Set.mem_iUnion.mpr
    refine ⟨Q.under R, ?_⟩
    apply Set.mem_iUnion.mpr
    refine ⟨?_, rfl⟩
    change (Sum.inl (Q.under R) : NumberFieldPlace K) ∈ S at hQ
    exact Finset.mem_toLeft.mpr hQ
  refine ⟨hU.toFinset, ?_⟩
  intro Q
  rw [Set.Finite.mem_toFinset]
  rfl

/-- **Corollary VII.4.8.**  The ideal Artin map away from a finite set
containing the infinite and ramified places is surjective. -/
theorem artin_away_ramification : (∀ (K : Type u) [Field K] [NumberField K]
      (L : ANExt K)
      (S : Finset (NumberFieldPlace K)),
      ContainsAllPlaces K S →
        RamifiedContainedSupport L S →
          IdealArtinSurjective L S) :=
  containsRamifiedStatement elements_generate_away
    primesAboveBridge

end Towers.CField.BLoc
