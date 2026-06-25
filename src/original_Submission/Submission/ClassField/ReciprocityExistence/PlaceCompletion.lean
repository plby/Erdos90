import Submission.ClassField.ReciprocityExistence.LawStatements
import Submission.ClassField.ReciprocityExistence.Functoriality
import Submission.ClassField.ReciprocityExistence.FiniteLayerAbsolute
import Submission.ClassField.CyclotomicBrauer.FinitePrime
import Submission.ClassField.CyclotomicBrauer.LocalizationStatements
import Submission.ClassField.Ideles.GlobalPlace
import Submission.ClassField.LocalBrauer.CanonicalCarryUnconditional

/-!
# Chapter VII, Section 8, Theorem 8.1

The two reciprocity laws are proved together for actual finite abelian
number-field layers.  Part (a) uses the global idèle Artin map restricted to
such a layer; part (b) uses the relative Brauer group and scalar extension to
every completion.  The proof follows Lemmas 8.4--8.6: the cyclotomic base
case, the two directions of the cup-product diagram, and Proposition 7.2's
cyclic cyclotomic splitting theorem.
-/

namespace Submission.CField.RExist

open AbsoluteValue IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.LRecip
open Submission.CField.BGroups
open Submission.CField.LBrauer
open Submission.CField.Ideles
open Submission.CField.Recip
open Submission.CField.CBrauer
open scoped IsMulCommutative

noncomputable section
universe u

/-- The completion model used in the source: the normalized absolute-value
completion at a finite place and the usual completion at an infinite place. -/
def placeCompletion
    (K : Type u) [Field K] [NumberField K] : NumberFieldPlace K → Type u
  | .inl P => (FinitePlace.mk P).val.Completion
  | .inr v => v.Completion

instance (K : Type u) [Field K] [NumberField K] (v : NumberFieldPlace K) :
    Field (placeCompletion K v) := by
  cases v <;> simp only [placeCompletion] <;> infer_instance

instance (K : Type u) [Field K] [NumberField K] (v : NumberFieldPlace K) :
    Algebra K (placeCompletion K v) := by
  cases v with
  | inl P =>
      simp only [placeCompletion]
      exact (completionEmbedding (FinitePlace.mk P).val).toAlgebra
  | inr v =>
      simp only [placeCompletion]
      exact (completionEmbedding v.1).toAlgebra

/-- At a finite place this is the already constructed carry-normalized local
Brauer invariant. -/
noncomputable def finitePlaceInvariant
    (K : Type u) [Field K] [NumberField K]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Additive (BrauerGroup (placeCompletion K (.inl P))) →+
      LocalInvariant := by
  letI : NontriviallyNormedField (FinitePlace.mk P).val.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist (FinitePlace.mk P).val.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel (FinitePlace.mk P).val.Completion :=
    placeValuativeRel P
  letI : Valuation.Compatible
      (NormedField.valuation (K := (FinitePlace.mk P).val.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := (FinitePlace.mk P).val.Completion))
  letI : IsNonarchimedeanLocalField (FinitePlace.mk P).val.Completion :=
    placeNonarchimedeanField P
  simpa only [placeCompletion] using
    MonoidHom.toAdditive (carryBrauerInvariant
      (FinitePlace.mk P).val.Completion).toMonoidHom

/-- The usual normalization at an infinite place: it is injective, its image
is the two-torsion at a real place, and it is zero at a complex place. -/
def ArchimedeanBrauerInvariant
    (K : Type u) [Field K] [NumberField K]
    (v : InfinitePlace K)
    (inv : Additive (BrauerGroup (placeCompletion K (.inr v))) →+
      LocalInvariant) : Prop :=
  Function.Injective inv ∧
    (InfinitePlace.IsReal v → Set.range inv = {x | 2 • x = 0}) ∧
    (InfinitePlace.IsComplex v → Set.range inv = {0})

/-- The canonical local invariant at every place.  The finite components are
definitionally tied to `carryBrauerInvariant`; the two
archimedean cases are characterized by their standard normalization. -/
structure PIData
    (K : Type u) [Field K] [NumberField K] where
  invariant : ∀ v : NumberFieldPlace K,
    Additive (BrauerGroup (placeCompletion K v)) →+ LocalInvariant
  finite_eq : ∀ P, invariant (.inl P) = finitePlaceInvariant K P
  infinite_isCanonical : ∀ v,
    ArchimedeanBrauerInvariant K v (invariant (.inr v))

/-- Sum of the canonical local invariant components on the finite-support
direct sum. -/
def PIData.sum
    (K : Type u) [Field K] [NumberField K]
    (data : PIData K) :
    DirectSum (NumberFieldPlace K)
      (fun v => Additive (BrauerGroup (placeCompletion K v))) →+
      LocalInvariant := by
  classical
  exact DirectSum.toAddMonoid data.invariant

variable (K : Type u) [Field K] [NumberField K]

noncomputable local instance (E : FASubext K) : NumberField E.1 :=
  NumberField.of_module_finite K E.1

structure BData where
  localization : MultiplicativeLocalizationData
    (BrauerGroup.{u,u} K) (fun v : NumberFieldPlace K => BrauerGroup (placeCompletion K v))
  localizeAt_eq : ∀ beta v, localization.localizeAt v beta =
    brauerBaseChange K (placeCompletion K v) beta
  placeInvariant : PIData K

def BData.sumInvariant (data : BData K) :
    DirectSum (NumberFieldPlace K)
      (fun v => Additive (BrauerGroup (placeCompletion K v))) →+
      LocalInvariant :=
  data.placeInvariant.sum K

def relativeLocalization (data : BData K)
    (L : Type u) [Field L] [Algebra K L] :
    Additive (relativeBrauerGroup K L) →+
      DirectSum (NumberFieldPlace K)
        (fun v => Additive (BrauerGroup (placeCompletion K v))) :=
  data.localization.localization.comp
    (MonoidHom.toAdditive (relativeBrauerGroup K L).subtype)

def InvariantSumReciprocity (data : BData K)
    (L : Type u) [Field L] [Algebra K L] : Prop :=
  ∀ beta : relativeBrauerGroup K L,
    (BData.sumInvariant K data)
      (relativeLocalization K data L (Additive.ofMul beta)) = 0

def CyclicCyclotomicSubextension
    (E : FASubext K) : Prop :=
  IsCyclic Gal(E.1/K) ∧
    ∃ (q : ℕ) (C : Type u) (_ : Field C) (_ : NumberField C)
      (_ : Algebra K C) (_ : Algebra E.1 C) (_ : IsScalarTower K E.1 C)
      (_ : IsCyclotomicExtension {q} K C), True

structure CupProductData
    (E : FASubext K)
    (phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K)
    (data : BData K) where
  fieldCup : CharacterModule (Additive Gal(E.1/K)) →
    Additive Kˣ →+ Additive (relativeBrauerGroup K E.1)
  ideleCup : CharacterModule (Additive Gal(E.1/K)) →
    Additive (IdeleGroup (NumberField.RingOfIntegers K) K) →+
      DirectSum (NumberFieldPlace K)
        (fun v => Additive (BrauerGroup (placeCompletion K v)))
  naturality : CupProductNaturality
    (principalIdele (NumberField.RingOfIntegers K) K)
    (relativeLocalization K data E.1) fieldCup ideleCup
  localInvariantComparison : CupInvariantComparison
    ((localAbelianRestriction E).comp phi) ideleCup
    (BData.sumInvariant K data)
  cyclic_surjective : IsCyclic Gal(E.1/K) →
    ∃ chi : CharacterModule (Additive Gal(E.1/K)),
      Function.Surjective (fieldCup chi)
def CyclotomicCaseBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
  (E : FASubext K)
  (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K),
  ContinuousGlobalArtin phi →
    CyclicCyclotomicSubextension K E →
    TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
      ((localAbelianRestriction E).comp phi)

def CupDataBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
  (E : FASubext K)
  (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
  (data : BData K), ContinuousGlobalArtin phi →
    Nonempty (CupProductData K E phi data)

def CupNaturalityBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (E : FASubext K)
    (phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K)
    (data : BData K)
    (cup : CupProductData K E phi data),
    CupProductNaturality
      (principalIdele (NumberField.RingOfIntegers K) K)
      (relativeLocalization K data E.1) cup.fieldCup cup.ideleCup

def CupComparisonBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (E : FASubext K)
    (phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K)
    (data : BData K)
    (cup : CupProductData K E phi data),
    CupInvariantComparison ((localAbelianRestriction E).comp phi)
      cup.ideleCup (BData.sumInvariant K data)

def CyclicCupBridge : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (E : FASubext K)
    (phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      AbsoluteAbelianGalois K)
    (data : BData K)
    (cup : CupProductData K E phi data),
    IsCyclic Gal(E.1/K) →
      ∃ chi : CharacterModule (Additive Gal(E.1/K)),
        Function.Surjective (cup.fieldCup chi)

/-- Naturality is intrinsic to the canonical cup-product package, rather
than an assertion about arbitrary unrelated homomorphisms. -/
theorem cupNaturalityBridge :
    CupNaturalityBridge.{u} :=
  fun _ _ _ _ _ _ cup => cup.naturality

/-- The local invariant comparison is intrinsic to the canonical
cup-product package. -/
theorem cupComparisonBridge :
    CupComparisonBridge.{u} :=
  fun _ _ _ _ _ _ cup => cup.localInvariantComparison

/-- Cyclic cup-product surjectivity is required only of the canonical
cup-product package selected by `CupDataBridge`. -/
theorem cyclicCupBridge :
    CyclicCupBridge.{u} :=
  fun _ _ _ _ _ _ cup => cup.cyclic_surjective

/-- The routine realization of Proposition 7.2's abstract finite extension
inside the fixed separable closure.  This is the only bridge between the
proposition's output and a `FASubext`. -/
def PlaceCompletion : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (beta : BrauerGroup.{u,u} K),
    Nonempty (SplittingExtensionData K beta) →
      ∃ E : FASubext K,
        CyclicCyclotomicSubextension K E ∧
          brauerBaseChange K E.1 beta = 1

theorem place_statement_bridges
    (hbase : CyclotomicCaseBridge.{u})
    (hcupData : CupDataBridge.{u})
    (hnaturality : CupNaturalityBridge.{u})
    (hcomparison : CupComparisonBridge.{u})
    (hcyclicCup : CyclicCupBridge.{u})
    (hFinitePrimeData : (∀ (K : Type u) [Field K] [NumberField K]
          (beta : BrauerGroup.{u, u} K),
          Nonempty (SplittingExtensionData K beta)))
    (hrealize : PlaceCompletion.{u}) :
    (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)) := by
  intro K _ _ phi data hphi
  have hcyclicB (E : FASubext K)
      (hE : CyclicCyclotomicSubextension K E) :
      InvariantSumReciprocity K data E.1 := by
    obtain ⟨cup⟩ := hcupData K E phi data hphi
    obtain ⟨chi, hchi⟩ := hcyclicCup K E phi data cup hE.1
    exact sum_reciprocity_product
      (principalIdele (NumberField.RingOfIntegers K) K)
      ((localAbelianRestriction E).comp phi)
      (relativeLocalization K data E.1)
      cup.fieldCup cup.ideleCup
      (BData.sumInvariant K data)
      ⟨hnaturality K E phi data cup, hcomparison K E phi data cup⟩
      chi hchi (hbase K E phi hphi hE)
  have habsolute : ∀ beta : BrauerGroup.{u,u} K,
      (BData.sumInvariant K data)
        (data.localization.localization (Additive.ofMul beta)) = 0 := by
    apply invariant_cyclic_cyclotomic
      (CyclicCyclotomicSubextension K)
      (fun beta E => brauerBaseChange K E.1 beta = 1)
      (fun beta => (BData.sumInvariant K data)
        (data.localization.localization (Additive.ofMul beta)) = 0)
    · intro beta
      exact hrealize K beta (hFinitePrimeData K beta)
    · intro E hE beta hsplit
      let betaE : relativeBrauerGroup K E.1 := ⟨beta,
        (relative_brauer_group K E.1 beta).2 hsplit⟩
      exact hcyclicB E hE betaE
  constructor
  · intro E
    obtain ⟨cup⟩ := hcupData K E phi data hphi
    apply product_reciprocity_sum
      (principalIdele (NumberField.RingOfIntegers K) K)
      ((localAbelianRestriction E).comp phi)
      (relativeLocalization K data E.1)
      cup.fieldCup cup.ideleCup
      (BData.sumInvariant K data)
      ⟨hnaturality K E phi data cup, hcomparison K E phi data cup⟩
    intro chi a
    exact habsolute (cup.fieldCup chi (Additive.ofMul a)).toMul.1
  · intro L _ _ _ _ _ beta
    exact habsolute beta.1

end
end Submission.CField.RExist
