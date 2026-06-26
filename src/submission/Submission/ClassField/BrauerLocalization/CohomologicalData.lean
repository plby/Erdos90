import Submission.ClassField.BrauerLocalization.RelativeIdele
import Submission.ClassField.BrauerLocalization.H2Comparison
import Submission.ClassField.BrauerLocalization.CompletionNaturality
import Submission.ClassField.BrauerLocalization.Main
import Submission.ClassField.CrossedProducts.TensorRightCongr
import Submission.ClassField.GlobalClass.BrauerSequenceStatements

/-!
# Cohomological relative-Brauer localization data

This file bundles the already-constructed idèle-cohomology map and local
crossed-product comparisons as genuine multiplicative localization data.  It
isolates the remaining arithmetic theorem as one coordinate equality: after
all Shapiro and crossed-product identifications, a coordinate must be scalar
extension of the original Brauer class to the base completion.
-/

namespace Submission.CField.BLoc

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.BGroups
open Submission.CField.CProduca
open Submission.CField.Ideles
open Submission.CField.CIdeles
open Submission.CField.CBrauer
open Submission.CField.RExist
open Submission.CField.HNorm
open Submission.CField.GClass

noncomputable section

universe u

variable (K L : Type u) [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

set_option synthInstance.maxHeartbeats 300000 in
-- The dependent local crossed-product family requires a deeper instance search.
/-- The direct-sum map obtained from principal idèles, Proposition VII.2.5,
Shapiro, and the local crossed-product equivalences. -/
noncomputable def brauerCohomologicalLocalization :
    (completion : HasseCompletionData K L) →
    Additive (relativeBrauerGroup K L) →+
      DirectSum (NumberFieldPlace K)
        (fun v => Additive
          (localRelativeBrauer K L completion v)) :=
  fun completion =>
    (directRelativeBrauer
        K L completion).toAddMonoidHom.comp
      (relativeH2 K L)

set_option synthInstance.maxHeartbeats 300000 in
-- Elaborating a component of the dependent direct sum requires the same search.
/-- One coordinate of the cohomological localization, written
multiplicatively. -/
noncomputable def relativeCohomologicalLocalize
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :
    relativeBrauerGroup K L →*
      localRelativeBrauer K L completion v :=
  ((DirectSum.component ℤ (NumberFieldPlace K)
      (fun w => Additive
        (localRelativeBrauer K L completion w)) v).toAddMonoidHom.comp
    (brauerCohomologicalLocalization K L completion)).toMultiplicative

set_option synthInstance.maxHeartbeats 300000 in
-- The structure elaborates both dependent maps and all local group instances.
/-- The cohomological construction, before proving that its coordinates are
literally scalar extension. -/
noncomputable def relativeCohomologicalLocalization
    (completion : HasseCompletionData K L) :
    MultiplicativeLocalizationData (relativeBrauerGroup K L)
      (fun v => localRelativeBrauer K L completion v) where
  localizeAt := relativeCohomologicalLocalize K L completion
  localization := brauerCohomologicalLocalization K L completion
  localization_apply _ _ := rfl

/-- Finite support is automatic from the cohomological direct-sum target. -/
theorem relative_cohomological_localization
    (completion : HasseCompletionData K L)
    (x : relativeBrauerGroup K L) :
    Set.Finite {v : NumberFieldPlace K |
      relativeCohomologicalLocalize K L completion v x ≠ 1} := by
  let data := relativeCohomologicalLocalization K L completion
  let y := data.localization (Additive.ofMul x)
  apply (DFinsupp.finite_support y).subset
  intro v hv hy
  apply hv
  apply Additive.ofMul.injective
  have hcoord := data.localization_apply x v
  change y v = Additive.ofMul
    (relativeCohomologicalLocalize K L completion v x) at hcoord
  rw [hy] at hcoord
  change Additive.ofMul
    (relativeCohomologicalLocalize K L completion v x) = 0
  exact hcoord.symm

/-- Under VII.5.1, the cohomological localization data is injective. -/
theorem cohomological_localization_injective
    (completion : HasseCompletionData K L)
    (h51 : IdeleCohomologyClaims.{u}) :
    BrauerLocalizationInjectivity
      (relativeCohomologicalLocalization K L completion) := by
  rw [BrauerLocalizationInjectivity]
  intro x y hxy
  apply relative_brauer_injective K L h51
  apply (directRelativeBrauer
    K L completion).injective
  exact hxy

/-- The sole remaining coordinate theorem: cohomological localization agrees
with scalar extension of Brauer classes to the base completion. -/
def RelativeBrauerCompatibility
    (completion : HasseCompletionData K L) : Prop :=
  ∀ (x : relativeBrauerGroup K L) (v : NumberFieldPlace K),
    ((relativeCohomologicalLocalize K L completion v x :
        localRelativeBrauer K L completion v) :
      BrauerGroup (hasseAbsoluteValue v).Completion) =
      brauerBaseChange K (hasseAbsoluteValue v).Completion
        (x : BrauerGroup K)

/-- The full coordinate square follows by composing its two genuine
naturality inputs: principal idèles become diagonal completion products, and
Shapiro/crossed products turn that diagonal class into scalar extension. -/
theorem relative_compatibility_naturalities
    (completion : HasseCompletionData K L)
    (hidele : ResizedPrincipalNaturality
      (K := K) (L := L))
    (hlocal : CompletionBrauerCompatibility
      (K := K) (L := L) completion) :
    RelativeBrauerCompatibility K L completion := by
  intro x v
  have hp := hidele
    (relativeBrauerResized K L (Additive.ofMul x)) v
  have hp' :
      relativeH2 K L (Additive.ofMul x) v =
        resizedGlobalUnits
          (K := K) (L := L) v
          (relativeBrauerResized K L
            (Additive.ofMul x)) := by
    simpa [relativeH2,
      relativeResized2] using hp
  change Subtype.val
    ((directRelativeBrauer
      K L completion
      (relativeH2 K L (Additive.ofMul x)) v).toMul) = _
  rw [direct_relative_brauer,
    hp']
  exact hlocal x v

/-- After proving the direct-limit coordinate formula, only the local
Shapiro/crossed-product compatibility remains in the localization square. -/
theorem relative_compatibility_naturality
    (completion : HasseCompletionData K L)
    (hlocal : CompletionBrauerCompatibility
      (K := K) (L := L) completion) :
    RelativeBrauerCompatibility K L completion :=
  relative_compatibility_naturalities
    K L completion
    (resizedPrincipalNaturality
      (K := K) (L := L)) hlocal

/-- The global coordinate square now reduces solely to crossed-product base
change at the chosen completions. -/
theorem relative_compatibility_crossed
    (completion : HasseCompletionData K L)
    (hcrossed : ChosenCompletionCompatibility
      (K := K) (L := L) completion) :
    RelativeBrauerCompatibility K L completion :=
  relative_compatibility_naturality
    K L completion
    (brauer_compatibility_crossed
      (K := K) (L := L) completion hcrossed)

set_option maxHeartbeats 1000000 in
-- Unfolding the dependent local relative-Brauer family is computationally heavy.
set_option synthInstance.maxHeartbeats 300000 in
-- The chosen-completion algebra and Galois instances require a deeper search.
/-- Once coordinate compatibility is proved, the cohomological package is
the exact arithmetic relative-Brauer localization data of Theorem VII.7.1. -/
noncomputable def relativeCohomologicalCompatibility
    (completion : HasseCompletionData K L)
    (hcompat : RelativeBrauerCompatibility
      K L completion) :
    RelativeLocalizationData (K := K) (L := L)
      (fun v => (hasseAbsoluteValue v).Completion)
      (fun v => chosenCompletionExtension K L completion v) where
  multiplicativeLocalizationData :=
    relativeCohomologicalLocalization K L completion
  localizeAt_coe := by
    intro x v
    exact hcompat x v

/-- Coordinate compatibility converts the formal finite support of the
cohomological direct sum into finite support of actual Brauer scalar
extension for every class split by `L`. -/
theorem brauer_change_relative
    (completion : HasseCompletionData K L)
    (hcompat : RelativeBrauerCompatibility
      K L completion)
    (beta : BrauerGroup K) (hbeta : beta ∈ relativeBrauerGroup K L) :
    Set.Finite {v : NumberFieldPlace K |
      brauerBaseChange K (hasseAbsoluteValue v).Completion beta ≠ 1} := by
  let x : relativeBrauerGroup K L := ⟨beta, hbeta⟩
  apply (relative_cohomological_localization
    K L completion x).subset
  intro v hv hlocal
  change brauerBaseChange K
    (hasseAbsoluteValue v).Completion beta ≠ 1 at hv
  apply hv
  have hcoord := hcompat x v
  rw [← hcoord]
  exact congrArg Subtype.val hlocal

private theorem brauer_change_algebra
    {k M : Type u} [Field k] [Field M]
    (a b : Algebra k M) (h : a = b) :
    @brauerBaseChange k M inferInstance inferInstance a =
      @brauerBaseChange k M inferInstance inferInstance b := by
  subst b
  rfl

/-- The relative finite-support theorem in the exact completion presentation
used by `BData`. -/
theorem brauer_support_relative
    (completion : HasseCompletionData K L)
    (hcompat : RelativeBrauerCompatibility
      K L completion)
    (beta : BrauerGroup K) (hbeta : beta ∈ relativeBrauerGroup K L) :
    Set.Finite {v : NumberFieldPlace K |
      brauerBaseChange K (Submission.CField.RExist.placeCompletion K v) beta ≠ 1} := by
  apply (brauer_change_relative
    K L completion hcompat beta hbeta).subset
  intro v hv
  cases v with
  | inl P =>
      let v := (FinitePlace.mk P).val
      change @brauerBaseChange K v.Completion inferInstance inferInstance
        (completionEmbedding v).toAlgebra beta ≠ 1 at hv
      change @brauerBaseChange K v.Completion inferInstance inferInstance
        (completionBaseAlgebra v) beta ≠ 1
      have hmap := brauer_change_algebra
        (completionEmbedding v).toAlgebra (completionBaseAlgebra v) (by
          apply Algebra.algebra_ext
          intro x
          rfl)
      rw [hmap] at hv
      exact hv
  | inr v =>
      change @brauerBaseChange K v.1.Completion inferInstance inferInstance
        (completionEmbedding v.1).toAlgebra beta ≠ 1 at hv
      change @brauerBaseChange K v.1.Completion inferInstance inferInstance
        (completionBaseAlgebra v.1) beta ≠ 1
      have hmap := brauer_change_algebra
        (completionEmbedding v.1).toAlgebra (completionBaseAlgebra v.1) (by
          apply Algebra.algebra_ext
          intro x
          rfl)
      rw [hmap] at hv
      exact hv

/-- The global finite-support input for VIII.4.2 follows from the one
remaining coordinate naturality theorem. -/
theorem change_cohomological_compatibility
    (hcompat : (∀ (K L : Type u) [Field K] [NumberField K]
          [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L]
          (completion : HasseCompletionData K L),
          RelativeBrauerCompatibility K L completion))
    (K : Type u) [Field K] [NumberField K] :
    GlobalChangeSupport K := by
  intro beta
  have hmem : beta ∈
      ⋃ E : FiniteGaloisIntermediateField K (SeparableClosure K),
        relativeBrauerClasses K E := by
    rw [← brauer_i_classes K]
    trivial
  obtain ⟨E, hbeta⟩ := Set.mem_iUnion.1 hmem
  letI : NumberField E := NumberField.of_module_finite K E
  let completion : HasseCompletionData K E :=
    Classical.choice
      (hasseExistenceBridge K E)
  exact brauer_support_relative
    K E completion
    (hcompat K E completion) beta hbeta

/-- The canonical Brauer localization and all local invariant maps, assuming
only the remaining cohomological coordinate square. -/
noncomputable def brauerCohomologicalCompatibility
    (hcompat : (∀ (K L : Type u) [Field K] [NumberField K]
          [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L]
          (completion : HasseCompletionData K L),
          RelativeBrauerCompatibility K L completion))
    (K : Type u) [Field K] [NumberField K] :
    BData K :=
  brauerDataSupport K
    (change_cohomological_compatibility
      hcompat K)

/-- The construction bridge in the source statement has now been reduced to
the single coordinate naturality theorem. -/
theorem brauer_cohomological_compatibility
    (hcompat : (∀ (K L : Type u) [Field K] [NumberField K]
          [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L]
          (completion : HasseCompletionData K L),
          RelativeBrauerCompatibility K L completion)) :
    BrauerConstructionBridge.{u} := by
  intro K _ _
  exact ⟨brauerCohomologicalCompatibility hcompat K⟩

end

end Submission.CField.BLoc
