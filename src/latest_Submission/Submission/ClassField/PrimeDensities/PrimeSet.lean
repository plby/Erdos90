import Submission.ClassField.ArtinReciprocity.Statements
import Submission.ClassField.PrimeDensities.IsGaloisClosure

/-!
# Chapter VI, Section 3, Corollary 3.8

For a finite abelian extension `L/K` and a finite set `S` containing the
ramified primes, Milne proves that the ideal Artin map `I^S → Gal(L/K)` is
surjective.  This file states the result using the project's literal
`IdealsPrimeTo` group and `IsArtinMap` predicate.

The only missing algebraic interface is the fixed field of the image of an
Artin map: primes outside `S` split in that fixed field, and triviality of
the fixed field makes the Artin map surjective.  Once this exact adapter is
supplied, Theorem 3.4 and Proposition 3.1 prove the corollary verbatim.
-/

namespace Submission.CField.PDensit

open IsDedekindDomain NumberField NumberField.InfinitePlace Set
open Submission.NumberTheory.Milne
open Submission.CField.RCGroups
open Submission.CField.ARecip

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The finite and infinite parts of the finite prime set `S` in Corollary
3.8.  The infinite part is recorded faithfully although only the finite part
enters the ideal group `I^S`. -/
structure PrimeSet (K : Type u) [Field K] [NumberField K] where
  finite : Finset (HeightOneSpectrum (𝓞 K))
  infinite : Finset (RealInfinitePlace K)
  containsInfinite : ∀ w : RealInfinitePlace K, w ∈ infinite

/-- Literal conclusion for one extension, one prime set, and one map which
is identified as the ideal Artin map by its Frobenius values. -/
def PrimeSetConclusion
    (L : ANExt K)
    (S : PrimeSet K)
    (ψ : IdealsPrimeTo (𝓞 K) K S.finite →* Gal(L.carrier/K)) : Prop :=
  L.RamifiedPrimes ⊆ (S.finite : Set (HeightOneSpectrum (𝓞 K))) →
    IsArtinMap L S.finite ψ → Function.Surjective ψ

/-- The exact fixed-field object needed in Milne's proof.  Its carrier is
`L^H`, where `H` is the image of `ψ`.  Because `L/K` is abelian this field is
again finite Galois over `K`.

The two propositions are precisely the Galois-correspondence adapters not
yet available for the source-facing ideal Artin map:
* Frobenius restriction makes every prime outside `S` split completely in
  the fixed field;
* if that fixed field has degree one, the image subgroup is all of
  `Gal(L/K)`. -/
structure ArtinImageData
    (L : ANExt K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ψ : IdealsPrimeTo (𝓞 K) K S →* Gal(L.carrier/K)) where
  carrier : Type u
  [field : Field carrier]
  [numberField : NumberField carrier]
  [algebra : Algebra K carrier]
  [finiteDimensional : FiniteDimensional K carrier]
  galoisClosure : Type u
  [closureField : Field galoisClosure]
  [closureNumberField : NumberField galoisClosure]
  [closureAlgebra : Algebra K galoisClosure]
  [fixedFieldAlgebra : Algebra carrier galoisClosure]
  [scalarTower : IsScalarTower K carrier galoisClosure]
  [closureFiniteDimensional : FiniteDimensional K galoisClosure]
  [closureIsGalois : IsGalois K galoisClosure]
  isGaloisClosure : IsGaloisClosure K carrier galoisClosure
  outsideS_splits :
    {p : HeightOneSpectrum (𝓞 K) | p ∉ S} ⊆ splittingPrimes K carrier
  degree_one_surjective :
    Module.finrank K galoisClosure = 1 → Function.Surjective ψ

attribute [instance]
  ArtinImageData.field
  ArtinImageData.numberField
  ArtinImageData.algebra
  ArtinImageData.finiteDimensional
  ArtinImageData.closureField
  ArtinImageData.closureNumberField
  ArtinImageData.closureAlgebra
  ArtinImageData.fixedFieldAlgebra
  ArtinImageData.scalarTower
  ArtinImageData.closureFiniteDimensional
  ArtinImageData.closureIsGalois

/-- The narrow missing fixed-field/Frobenius adapter.  It assumes exactly
that `S` contains the ramified primes and that `ψ` is the Artin map. -/
def ArtinImageBridge : Prop :=
  ∀ (L : ANExt K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (ψ : IdealsPrimeTo (𝓞 K) K S →* Gal(L.carrier/K)),
    L.RamifiedPrimes ⊆ (S : Set (HeightOneSpectrum (𝓞 K))) →
      IsArtinMap L S ψ → Nonempty (ArtinImageData L S ψ)

/-- The complement of a finite set of primes has polar density one, by
parts (a), (c), and (e) of Proposition 3.1. -/
theorem polar_density_compl
    (h31 : EulerDensityLaws K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    PrimePolarDensity K {p | p ∉ S} 1 := by
  rcases h31 with ⟨hall, hnonneg, hadd, hmono, hfinite⟩
  have hSfinite : ((S : Set (HeightOneSpectrum (𝓞 K)))).Finite :=
    S.finite_toSet
  have hSzero : PrimePolarDensity K
      (S : Set (HeightOneSpectrum (𝓞 K))) 0 := hfinite _ hSfinite
  have hunion :
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))) =
        (S : Set (HeightOneSpectrum (𝓞 K))) ∪ {p | p ∉ S} := by
    ext p
    simp only [mem_univ, mem_union, Finset.mem_coe, mem_setOf_eq, true_iff]
    exact Classical.em (p ∈ S)
  have hdis : Disjoint
      (S : Set (HeightOneSpectrum (𝓞 K))) {p | p ∉ S} := by
    exact Set.disjoint_left.2 fun p hpS hpNot ↦ hpNot hpS
  have hthird := (hadd Set.univ (S : Set _)
    {p : HeightOneSpectrum (𝓞 K) | p ∉ S} 1 0 0 hunion hdis).2.1
  simpa using hthird ⟨hall, hSzero⟩

/-- The density argument in Corollary 3.8: a finite Galois extension in
which every prime outside a finite set splits has degree one. -/
theorem finrank_cofinite_splitting
    (h31 : EulerDensityLaws K)
    (h34 : (∀ (K L M : Type u)
          [Field K] [NumberField K]
          [Field L] [NumberField L]
          [Field M] [NumberField M]
          [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
          [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K M],
          GaloisClosureConclusion K L M))
    (E M : Type u) [Field E] [NumberField E]
    [Field M] [NumberField M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional K E] [FiniteDimensional K M] [IsGalois K M]
    (hclosure : IsGaloisClosure K E M)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (houtside : {p : HeightOneSpectrum (𝓞 K) | p ∉ S} ⊆
      splittingPrimes K E) :
    Module.finrank K M = 1 := by
  have hsplitDensity : PrimePolarDensity K (splittingPrimes K E)
      (1 / (Module.finrank K M : ℝ)) :=
    h34 K E M hclosure
  have houtsideDensity := polar_density_compl
    (K := K) h31 S
  have hle : (1 : ℝ) ≤ 1 / (Module.finrank K M : ℝ) :=
    h31.2.2.2.1 _ _ _ _ houtside houtsideDensity hsplitDensity
  have hdpos : 0 < (Module.finrank K M : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := M))
  have hdle : (Module.finrank K M : ℝ) ≤ 1 := by
    simpa using (le_div_iff₀ hdpos).mp hle
  have hdleNat : Module.finrank K M ≤ 1 := by exact_mod_cast hdle
  exact Nat.le_antisymm hdleNat Module.finrank_pos

/-- Proposition 3.1, Theorem 3.4, and the fixed-field adapter prove the
literal ideal-Artin surjectivity statement. -/
theorem set_fixed_bridge
    (h31 : EulerDensityLaws K)
    (h34 : (∀ (K L M : Type u)
          [Field K] [NumberField K]
          [Field L] [NumberField L]
          [Field M] [NumberField M]
          [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
          [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K M],
          GaloisClosureConclusion K L M))
    (hfixed : ArtinImageBridge (K := K)) :
    ∀ (L : ANExt K)
    (S : PrimeSet K)
    (ψ : IdealsPrimeTo (𝓞 K) K S.finite →* Gal(L.carrier/K)),
    PrimeSetConclusion L S ψ
  := by
  intro L S ψ hram hψ
  let data := Classical.choice (hfixed L S.finite ψ hram hψ)
  apply data.degree_one_surjective
  exact finrank_cofinite_splitting (K := K) h31 h34
    data.carrier data.galoisClosure data.isGaloisClosure
    S.finite data.outsideS_splits

end

end Submission.CField.PDensit
