import Towers.ClassField.BrauerLocalization.CrossedProduct
import Towers.ClassField.BrauerLocalization.InfiniteCrossedProduct
import Towers.ClassField.BrauerLocalization.CohomologicalData

/-!
# Absolute Brauer localization injectivity from VII.5.1

The finite and infinite completion comparisons first give the literal
relative-Brauer coordinate square.  This file then passes from relative
classes split by one finite Galois extension to arbitrary Brauer classes,
using the fact that every Brauer class is split by some finite Galois
subextension of the separable closure.
-/

namespace Towers.CField.BLoc

open NumberField
open Towers.NumberTheory.Milne
open Towers.CField.BGroups
open Towers.CField.CProduca
open Towers.CField.Ideles
open Towers.CField.CIdeles
open Towers.CField.CBrauer
open Towers.CField.RExist
open Towers.CField.HNorm
open Towers.CField.GClass

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Brauer scalar extension depends only on the underlying algebra map. -/
private theorem brauer_change_algebra
    {k M : Type u} [Field k] [Field M]
    (a b : Algebra k M) (h : a = b) :
    @brauerBaseChange k M inferInstance inferInstance a =
      @brauerBaseChange k M inferInstance inferInstance b := by
  subst b
  rfl

/-- The finite and infinite chosen-completion crossed-product comparisons
give the uniform comparison at every number-field place. -/
theorem chosenCompletionCompatibility
    (completion : HasseCompletionData K L) :
    ChosenCompletionCompatibility
      (K := K) (L := L) completion :=
  chosen_compatibility_infinite
    (K := K) (L := L) completion
    (completionCrossedCompatibility
      (K := K) (L := L) completion)
    (chosenCrossedCompatibility
      (K := K) (L := L) completion)

/-- The completion-product/local-Brauer square is unconditionally
compatible with scalar extension. -/
theorem completionBrauerCompatibility
    (completion : HasseCompletionData K L) :
    CompletionBrauerCompatibility
      (K := K) (L := L) completion :=
  brauer_compatibility_crossed
    (K := K) (L := L) completion
    (chosenCompletionCompatibility
      (K := K) (L := L) completion)

/-- Cohomological localization of a relative Brauer class agrees at every
coordinate with literal scalar extension to the base completion. -/
theorem relativeBrauerCompatibility
    (completion : HasseCompletionData K L) :
    RelativeBrauerCompatibility K L completion :=
  relative_compatibility_naturality
    K L completion
    (completionBrauerCompatibility
      (K := K) (L := L) completion)

/-- The relative-Brauer coordinate comparison is uniform in the finite
Galois extension and the chosen completions. -/
theorem relativeCompatibilityStatement :
    (∀ (K L : Type u) [Field K] [NumberField K]
          [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L]
          (completion : HasseCompletionData K L),
          RelativeBrauerCompatibility K L completion) := by
  intro K L _ _ _ _ _ _ _ completion
  exact relativeBrauerCompatibility
    (K := K) (L := L) completion

/-- The canonical local invariant maps and finite-support global Brauer
localization required by VIII.4.2 can be constructed unconditionally. -/
theorem brauerConstructionBridge :
    BrauerConstructionBridge.{u} :=
  brauer_cohomological_compatibility
    relativeCompatibilityStatement

set_option synthInstance.maxHeartbeats 1000000 in
-- The proof compares two dependent direct sums of completion Brauer groups.
set_option maxHeartbeats 4000000 in
/-- Under VII.5.1, absolute Brauer localization is injective.  The proof
chooses one finite Galois splitting field for the difference of two classes
and applies the already constructed relative localization injection. -/
theorem brauer_localization_cohomology
    (h51 : IdeleCohomologyClaims.{u})
    (K : Type u) [Field K] [NumberField K]
    (data : BData K) :
    Function.Injective data.localization.localization := by
  intro x y hxy
  let beta : BrauerGroup K := (x - y).toMul
  have hmem : beta ∈
      ⋃ E : FiniteGaloisIntermediateField K (SeparableClosure K),
        relativeBrauerClasses K E := by
    rw [← brauer_i_classes K]
    trivial
  obtain ⟨E, hbeta⟩ := Set.mem_iUnion.1 hmem
  letI : NumberField E := NumberField.of_module_finite K E
  let completion : HasseCompletionData K E :=
    Classical.choice (hasseExistenceBridge K E)
  let z : relativeBrauerGroup K E := ⟨beta, hbeta⟩
  let relativeData :=
    relativeCohomologicalLocalization K E completion
  have hdiff : data.localization.localization (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hzloc : relativeData.localization (Additive.ofMul z) = 0 := by
    apply DirectSum.ext
    intro v
    have hdataV := congrArg (fun q => q v) hdiff
    have hrelativeV := relativeData.localization_apply z v
    change (DirectSum.component ℤ (NumberFieldPlace K)
      (fun w => Additive
        (localRelativeBrauer K E completion w)) v)
        (relativeData.localization (Additive.ofMul z)) = 0
    rw [hrelativeV]
    apply Additive.ofMul.injective
    apply Subtype.ext
    change ((relativeCohomologicalLocalize K E completion v z :
      localRelativeBrauer K E completion v) :
        BrauerGroup (hasseAbsoluteValue v).Completion) = 1
    rw [relativeBrauerCompatibility
      (K := K) (L := E) completion z v]
    cases v with
    | inl P =>
        let v := (FinitePlace.mk P).val
        change @brauerBaseChange K v.Completion inferInstance inferInstance
            (completionBaseAlgebra v) beta = 1
        have hdataCoord := data.localizeAt_eq beta (.inl P)
        change data.localization.localizeAt (.inl P) beta =
          @brauerBaseChange K v.Completion inferInstance inferInstance
            (completionEmbedding v).toAlgebra beta at hdataCoord
        have hlocal : data.localization.localizeAt (.inl P) beta = 1 := by
          apply Additive.ofMul.injective
          rw [← data.localization.localization_apply beta (.inl P)]
          simpa [beta] using hdataV
        have hmap := brauer_change_algebra
          (completionEmbedding v).toAlgebra (completionBaseAlgebra v) (by
            apply Algebra.algebra_ext
            intro a
            rfl)
        rw [hmap] at hdataCoord
        rw [← hdataCoord, hlocal]
        rfl
    | inr v =>
        change @brauerBaseChange K v.1.Completion inferInstance inferInstance
            (completionBaseAlgebra v.1) beta = 1
        have hdataCoord := data.localizeAt_eq beta (.inr v)
        change data.localization.localizeAt (.inr v) beta =
          @brauerBaseChange K v.1.Completion inferInstance inferInstance
            (completionEmbedding v.1).toAlgebra beta at hdataCoord
        have hlocal : data.localization.localizeAt (.inr v) beta = 1 := by
          apply Additive.ofMul.injective
          rw [← data.localization.localization_apply beta (.inr v)]
          simpa [beta] using hdataV
        have hmap := brauer_change_algebra
          (completionEmbedding v.1).toAlgebra
            (completionBaseAlgebra v.1) (by
              apply Algebra.algebra_ext
              intro a
              rfl)
        rw [hmap] at hdataCoord
        rw [← hdataCoord, hlocal]
        rfl
  have hzadd : Additive.ofMul z = 0 := by
    apply cohomological_localization_injective
      K E completion h51
    simpa using hzloc
  have hz : z = 1 := Additive.ofMul.injective hzadd
  apply sub_eq_zero.mp
  apply Additive.toMul.injective
  change beta = 1
  exact congrArg Subtype.val hz

/-- Uniform formulation of the localization-injectivity consequence of
VII.5.1, ready for the VIII.4.2 exactness assembly. -/
theorem localization_injectivity_cohomology
    (h51 : IdeleCohomologyClaims.{u}) :
    ∀ (K : Type u) [Field K] [NumberField K]
      (data : BData K),
      Function.Injective data.localization.localization := by
  intro K _ _ data
  exact brauer_localization_cohomology h51 K data

end

end Towers.CField.BLoc
