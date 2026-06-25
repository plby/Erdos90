import Submission.ClassField.ArtinReciprocity.Statements
import Submission.ClassField.NormIndex.FractionalIdealPrime
import Submission.ClassField.NormIndex.NumberFieldElement

/-!
# Chapter VII, Section 4, Corollary 4.8

For a finite abelian extension `L/K` and a finite set `S` of places containing
the infinite and ramified places, the Artin map on fractional ideals prime to
`S` is onto `Gal(L/K)`.

The Chapter V API describes the literal ideal Artin map by `IsArtinMap`: its
domain is `IdealsPrimeTo`, the subgroup of nonzero fractional ideals generated
by finite primes outside `S`, and it sends each such prime to its arithmetic
Frobenius.  The proof below applies Proposition 4.7 to the finite set of primes
of `L` lying above `S` and shows that all its Frobenius generators lie in the
range of this actual ideal map.
-/

namespace Submission.CField.NIndex

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.RCGroups
open Submission.CField.ARecip
open Submission.CField.Ideles

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  RingOfIntegers K

/-- The source hypothesis that `S` contains every finite prime ramified in
`L`.  It is stated upstairs so that it uses exactly the same unramifiedness
predicate as the arithmetic Frobenius map; the displayed member of `S` is the
contracted prime of `K`. -/
def RamifiedContainedSupport
    {K : Type u} [Field K] [NumberField K]
    (L : ANExt K)
    (S : Finset (NumberFieldPlace K)) : Prop :=
  ∀ Q : FinitePrime L.carrier,
    ¬Algebra.IsUnramifiedAt (OK K) Q.asIdeal →
      (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∈ S

/-- The literal conclusion that the Artin/Frobenius map on `I^S` is
surjective.  The universal quantifier is only the existing Chapter V way of
naming the Artin map: `IsArtinMap` says precisely that prime generators are
sent to their arithmetic Frobenius elements. -/
def IdealArtinSurjective
    {K : Type u} [Field K] [NumberField K]
    (L : ANExt K)
    (S : Finset (NumberFieldPlace K)) : Prop :=
  ∀ ψ : IdealsPrimeTo (OK K) K S.toLeft →* Gal(L.carrier/K),
    IsArtinMap L S.toLeft ψ → Function.Surjective ψ

/-- The finite collection of primes of `L` above the finite members of `S`.
This bridge isolates only the standard finiteness of the primes above a finite
set of base primes.  Its equivalence records the collection exactly, so it
contains no Frobenius-generation or surjectivity conclusion. -/
def PrimesAboveBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : ANExt K)
    (S : Finset (NumberFieldPlace K)),
    ∃ T : Finset (FinitePrime L.carrier),
      ∀ Q : FinitePrime L.carrier,
        Q ∈ T ↔
          (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∈ S

/-- Corollary 4.8 follows from Proposition 4.7: every Frobenius generator
outside the primes above `S` is the image of its contracted prime ideal in
`I^S`. -/
theorem containsRamifiedStatement
    (h47 : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsSolvable Gal(L/K)],
          ∀ T : Finset (FinitePrime L),
            ContainsRamifiedPrimes (K := K) (L := L) T →
              frobeniusGeneratedSubgroup (K := K) (L := L) T = ⊤))
    (hprimes : PrimesAboveBridge.{u}) :
    (∀ (K : Type u) [Field K] [NumberField K]
          (L : ANExt K)
          (S : Finset (NumberFieldPlace K)),
          ContainsAllPlaces K S →
            RamifiedContainedSupport L S →
              IdealArtinSurjective L S) := by
  intro K _ _ L S _hInfinite hramified ψ hψ
  letI : CommGroup Gal(L.carrier/K) :=
    { (inferInstance : Group Gal(L.carrier/K)) with mul_comm := mul_comm' }
  obtain ⟨T, hT⟩ := hprimes K L S
  have hcontains : ContainsRamifiedPrimes
      (K := K) (L := L.carrier) T := by
    intro Q hQoutside
    by_contra hQramified
    exact hQoutside ((hT Q).2 (hramified Q hQramified))
  have hgenerated : frobeniusGeneratedSubgroup
      (K := K) (L := L.carrier) T = ⊤ := by
    exact h47 K L.carrier T hcontains
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hgenerated]
  apply (Subgroup.closure_le (MonoidHom.range ψ)).2
  rintro sigma ⟨Q, hQoutside, rfl⟩
  let P : L.PAbove :=
    { downstairs := Q.under (OK K)
      upstairs := Q
      liesOver := ⟨rfl⟩ }
  have hQunramified :
      Algebra.IsUnramifiedAt (OK K) Q.asIdeal :=
    hcontains Q hQoutside
  have hPoutside : P.downstairs ∉ S.toLeft := by
    intro hPmem
    apply hQoutside
    apply (hT Q).2
    exact Finset.mem_toLeft.mp hPmem
  obtain ⟨I, _hIprime, hI⟩ := hψ P hPoutside hQunramified
  refine ⟨I, ?_⟩
  change ψ I = numberFrobeniusElement (K := K) Q
  exact hI

end

end Submission.CField.NIndex
