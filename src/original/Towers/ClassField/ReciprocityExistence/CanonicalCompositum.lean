import Towers.ClassField.ReciprocityExistence.FiniteCompositum
import Towers.ClassField.ReciprocityExistence.InfiniteCompositum

/-!
# Canonical compositum Artin data for VII.8.4(b)

The abstract proof of VII.8.4(b) consumes `CADataa`.
At finite places its commutative squares are not extra reciprocity
assumptions: the canonical local maps are projections of the norm square in
III.3.2.  This file packages precisely that construction.

The archimedean square remains explicit because it is the elementary
real/complex norm-residue square rather than an instance of the
nonarchimedean theorem III.3.2.
-/

namespace Towers.CField.RExist

open Filter Set
open NumberField IsDedekindDomain
open Towers.CField.LRecip
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.NIndex
open scoped IsMulCommutative

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- Canonical local input for the compositum argument.  The finite squares
are supplied by transported projected presentations of Lemma III.3.2, not
by bare commutativity hypotheses. -/
structure CCArtin
    (K K' M : Type u)
    [Field K] [NumberField K] [Field K'] [NumberField K'] [Field M]
    [Algebra K K'] [FiniteDimensional K K']
    [Algebra K' M] [Algebra K M] [IsScalarTower K K' M]
    (E : IntermediateField K M)
    [FiniteDimensional K E] [IsGalois K E]
    [FiniteDimensional K' M] [IsGalois K' M]
    [IsMulCommutative Gal(E/K)] [IsMulCommutative Gal(M/K')] where
  lower : FAProduc K Gal(E/K)
  upper : FAProduc K' Gal(M/K')
  hcompositum : E ⊔ IntermediateField.adjoin K
    (Set.range (algebraMap K' M)) = ⊤
  finite_canonical : ∀ (P : HeightOneSpectrum (OK K))
      (Q : PlacesAbovePrime K K' P),
    PSquare
      (completionNormLiteral (K := K) (L := K') P Q)
      (lower.finite.localHom P)
      (upper.finite.localHom Q.1)
      (compositumGaloisRestriction (K := K) (K' := K') (M := M) E)
  infinite_commutes : ∀ (v : InfinitePlace K)
      (w : InfinitePlacesAbove (K := K) (L := K') v)
      (z : w.1.1.Completionˣ),
    compositumGaloisRestriction (K := K) (K' := K') (M := M) E
        (upper.infinite w.1 z) =
      lower.infinite v
        (infiniteCompletionNorm (K := K) (L := K') v w z)

namespace CCArtin

variable {K K' M : Type u}
    [Field K] [NumberField K] [Field K'] [NumberField K'] [Field M]
    [Algebra K K'] [FiniteDimensional K K']
    [Algebra K' M] [Algebra K M] [IsScalarTower K K' M]
    {E : IntermediateField K M}
    [FiniteDimensional K E] [IsGalois K E]
    [FiniteDimensional K' M] [IsGalois K' M]
    [IsMulCommutative Gal(E/K)] [IsMulCommutative Gal(M/K')]

/-- Forget the canonical III.3.2 presentations after deriving each finite
commutative square. -/
noncomputable def compositumArtinData
    (D : CCArtin K K' M E) :
    CADataa K K' M E where
  lower := D.lower
  upper := D.upper
  hcompositum := D.hcompositum
  finite_commutes := fun P Q z => by
    have hsquare := (D.finite_canonical P Q).commutes
    exact DFunLike.congr_fun hsquare z
  infinite_commutes := D.infinite_commutes

/-- The global compositum Artin square built from the canonical projected
III.3.2 squares. -/
theorem commutes
    (D : CCArtin K K' M E) :
    (compositumGaloisRestriction
      (K := K) (K' := K') (M := M) E).comp D.upper.artin =
      D.lower.artin.comp (ideleNorm (K := K) (L := K')) :=
  D.compositumArtinData.commutes

/-- **Lemma VII.8.4(b), canonical compositum form.**  Product reciprocity
for `E/K` descends along the idèle norm to the compositum over `K'`.
The finite local compatibility is obtained from III.3.2. -/
theorem baseChange
    (D : CCArtin K K' M E)
    (hreciprocity : TrivialPrincipalIdeles
      (OK K) K Gal(E/K) D.lower.artin) :
    TrivialPrincipalIdeles
      (OK K') K' Gal(M/K') D.upper.artin :=
  D.compositumArtinData.baseChange hreciprocity

section CanonicalConstruction

variable {K₀ K₁ M₀ : Type}
    [Field K₀] [NumberField K₀] [Field K₁] [NumberField K₁]
    [Field M₀]
    [Algebra K₀ K₁] [FiniteDimensional K₀ K₁]
    [Algebra K₁ M₀] [Algebra K₀ M₀] [IsScalarTower K₀ K₁ M₀]
    {E₀ : IntermediateField K₀ M₀}
    [FiniteDimensional K₀ E₀] [IsGalois K₀ E₀]
    [FiniteDimensional K₁ M₀] [IsGalois K₁ M₀]
    [IsMulCommutative Gal(E₀/K₀)] [IsMulCommutative Gal(M₀/K₁)]

/-- Assemble canonical local data from supplied restricted-product support
certificates.  The public constructor below obtains both certificates from
finite ramification and the compositum square. -/
noncomputable def canonicalOfSupport
    (hcompositum : E₀ ⊔ IntermediateField.adjoin K₀
      (Set.range (algebraMap K₁ M₀)) = ⊤)
    (hlowerFinite :
      letI : NumberField E₀ := NumberField.of_module_finite K₀ E₀
      ∀ᶠ P in cofinite,
        ∀ x : (P.adicCompletion K₀)ˣ,
          x ∈ IdeleUnitSubgroup (OK K₀) K₀ P →
            canonicalArtinHom K₀ E₀ P x = 1)
    (hupperFinite :
      ∀ᶠ Q in cofinite,
        ∀ x : (Q.adicCompletion K₁)ˣ,
          x ∈ IdeleUnitSubgroup (OK K₁) K₁ Q →
            compositumUpperArtin
              K₀ K₁ M₀ E₀ Q x = 1) :
    CCArtin K₀ K₁ M₀ E₀ := by
  letI : NumberField E₀ := NumberField.of_module_finite K₀ E₀
  letI : NumberField M₀ := NumberField.of_module_finite K₁ M₀
  let lowerFinite : RLFam (A := Gal(E₀/K₀))
      (fun P : HeightOneSpectrum (OK K₀) ↦
        IdeleUnitSubgroup (OK K₀) K₀ P) :=
    { localHom := canonicalArtinHom K₀ E₀
      eventually_units := hlowerFinite }
  let upperFinite : RLFam (A := Gal(M₀/K₁))
      (fun Q : HeightOneSpectrum (OK K₁) ↦
        IdeleUnitSubgroup (OK K₁) K₁ Q) :=
    { localHom := compositumUpperArtin
        K₀ K₁ M₀ E₀
      eventually_units := hupperFinite }
  let lower : FAProduc K₀ Gal(E₀/K₀) :=
    { finite := lowerFinite
      infinite := canonicalGlobalArtin K₀ E₀ }
  let upper : FAProduc K₁ Gal(M₀/K₁) :=
    { finite := upperFinite
      infinite := canonicalGlobalArtin K₁ M₀ }
  refine
    { lower := lower
      upper := upper
      hcompositum := hcompositum
      finite_canonical := ?_
      infinite_commutes := ?_ }
  · intro P Q
    cases Q with
    | mk Q hQ =>
      subst P
      simpa only [lower, upper, lowerFinite, upperFinite] using
        (compositum_projected_square
          K₀ K₁ M₀ E₀ Q)
  · intro v w z
    exact DFunLike.congr_fun
      (compositum_artin_commutes
        K₀ K₁ M₀ E₀ hcompositum v w) z

/-- Construct all local Artin data in VII.8.4(b) canonically.  Finite
ramification gives the lower restricted-product support; the III.3.2 square,
unit preservation under completed norms, and injectivity of compositum
restriction give the upper support. -/
noncomputable def canonical
    (hcompositum : E₀ ⊔ IntermediateField.adjoin K₀
      (Set.range (algebraMap K₁ M₀)) = ⊤) :
    CCArtin K₀ K₁ M₀ E₀ := by
  letI : NumberField E₀ := NumberField.of_module_finite K₀ E₀
  letI : NumberField M₀ := NumberField.of_module_finite K₁ M₀
  refine canonicalOfSupport hcompositum
    (eventually_trivial_units K₀ E₀) ?_
  filter_upwards
    [compositum_upper_eventually
      K₀ K₁ M₀ E₀ hcompositum] with Q hQ
  intro x hx
  exact (MonoidHom.mem_ker.mp (hQ hx))

/-- **Lemma VII.8.4(b)** with every finite and archimedean local map and
both restricted Artin products instantiated canonically. -/
theorem baseChange_canonical
    (hcompositum : E₀ ⊔ IntermediateField.adjoin K₀
      (Set.range (algebraMap K₁ M₀)) = ⊤)
    (hreciprocity :
      letI : NumberField E₀ := NumberField.of_module_finite K₀ E₀
      TrivialPrincipalIdeles (OK K₀) K₀ Gal(E₀/K₀)
        (canonical hcompositum).lower.artin) :
    letI : NumberField M₀ := NumberField.of_module_finite K₁ M₀
    TrivialPrincipalIdeles (OK K₁) K₁ Gal(M₀/K₁)
      (canonical hcompositum).upper.artin := by
  letI : NumberField E₀ := NumberField.of_module_finite K₀ E₀
  letI : NumberField M₀ := NumberField.of_module_finite K₁ M₀
  exact (canonical hcompositum).baseChange hreciprocity

end CanonicalConstruction

end CCArtin

end

end Towers.CField.RExist
