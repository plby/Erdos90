import Submission.ClassField.ReciprocityExistence.PlaceCompletion
import Submission.ClassField.BrauerGroups.BrauerTrivialClass
import Submission.ClassField.CyclotomicBrauer.PlaceAlgEquiv

/-!
# Realizing Proposition VII.7.2 inside the fixed separable closure

The splitting extension in Proposition VII.7.2 is initially an abstract
number field.  This file transports it to its chosen image in
`SeparableClosure K`, as required by Theorem VII.8.1.
-/

namespace Submission.CField.RExist

open NumberField
open Submission.CField.LFTheory
open Submission.CField.BGroups
open Submission.CField.CBrauer
open Submission.CField.Ideles
open Submission.CField.Recip
open scoped TensorProduct

noncomputable section

universe u

/-- Regard Proposition VII.7.2's abstract cyclic extension as a bundled
finite abelian extension. -/
private noncomputable def finiteAbelianExtension
    {K : Type u} [Field K] [NumberField K]
    (data : FEData K)
    (hcyclic : data.IsCyclicCyclotomic) :
    FAExt K := by
  letI : Field data.L := data.fieldL
  letI : Algebra K data.L := data.algebraKL
  letI : FiniteDimensional K data.L := data.finiteDimensionalKL
  letI : IsGalois K data.L := data.isGaloisKL
  letI : IsCyclic Gal(data.L/K) := hcyclic.1
  exact
    { carrier := data.L
      field := inferInstance
      algebra := inferInstance
      finiteDimensional := inferInstance
      isGalois := inferInstance
      isAbelian := IsCyclic.isMulCommutative }

/-- The realization bridge required by Theorem VII.8.1. -/
theorem realization :
    PlaceCompletion.{u} := by
  intro K _ _ beta hdata
  obtain ⟨splitting⟩ := hdata
  let data := splitting.extension
  letI : Field data.L := data.fieldL
  letI : NumberField data.L := data.numberFieldL
  letI : Algebra K data.L := data.algebraKL
  letI : FiniteDimensional K data.L := data.finiteDimensionalKL
  letI : IsGalois K data.L := data.isGaloisKL
  let A : FAExt K :=
    finiteAbelianExtension data splitting.isCyclicCyclotomic
  let E : FASubext K :=
    A.finiteAbelianSubextension
  let e : data.L ≃ₐ[K] E.1 := A.algSeparableClosure
  letI : NumberField E.1 := NumberField.of_module_finite K E.1
  refine ⟨E, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · exact e.autCongr.isCyclic.mp splitting.isCyclicCyclotomic.1
    · obtain ⟨q, C, fieldC, numberFieldC, algebraKC, algebraLC,
          towerKLC, hcyclo, _⟩ := splitting.isCyclicCyclotomic.2
      letI : Field C := fieldC
      letI : NumberField C := numberFieldC
      letI : Algebra K C := algebraKC
      letI : Algebra data.L C := algebraLC
      letI : IsScalarTower K data.L C := towerKLC
      letI : Algebra E.1 C :=
        ((algebraMap data.L C).comp e.symm.toRingHom).toAlgebra
      have towerKEC : IsScalarTower K E.1 C := by
        apply IsScalarTower.of_algebraMap_eq'
        ext x
        change algebraMap K C x =
          algebraMap data.L C (e.symm (algebraMap K E.1 x))
        rw [e.symm.commutes]
        exact IsScalarTower.algebraMap_apply K data.L C x
      exact ⟨q, C, inferInstance, inferInstance, inferInstance,
        inferInstance, towerKEC, hcyclo, trivial⟩
  · exact brauer_change_alg K data.L E.1 e beta
      splitting.splits

/-- Theorem VII.8.1 with Proposition VII.7.2 and the separable-closure
realization step discharged.  The remaining inputs are the substantive
cyclotomic base case and construction of the canonical cup-product package. -/
theorem realization_remaining_bridges
    (hbase : CyclotomicCaseBridge.{u})
    (hcupData : CupDataBridge.{u}) :
    (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)) :=
  place_statement_bridges hbase hcupData
    cupNaturalityBridge
    cupComparisonBridge cyclicCupBridge
    placeAlgStatement
      realization

end

end Submission.CField.RExist
