import Submission.ClassField.BrauerLocalization.BrauerKernelLifting
import Submission.ClassField.BrauerLocalization.ExactnessAssembly

/-!
# Arithmetic assembly of the kernel-lifting component of VIII.4.2

This file separates the remaining kernel argument into two arithmetic inputs:

* a tailored finite cyclic extension which kills every coordinate of a local
  tuple of invariant sum zero; and
* the finite cyclic relative Brauer sequence, in the exact orientation saying
  that a zero-sum tuple of local relative classes is globally relative.

Everything after those two inputs, including passage back to the absolute
Brauer localization used in VIII.4.2, is proved here.
-/

namespace Submission.CField.BLoc

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.BGroups
open Submission.CField.LFTheory
open Submission.CField.Ideles
open Submission.CField.Recip
open Submission.CField.CIdeles
open Submission.CField.CBrauer
open Submission.CField.RExist
open Submission.CField.HNorm
open Submission.CField.GClass

noncomputable section

universe u

/-- The tailored-extension input in the exact form needed by kernel lifting.
It includes the chosen completion above every place and asserts actual
triviality after scalar extension of every coordinate. -/
def KillingExtension : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (data : BData K)
    (y : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K v)))),
    BData.sumInvariant K data y = 0 →
      ∃ (L : Type u) (_ : Field L) (_ : NumberField L)
        (_ : Algebra K L) (_ : FiniteDimensional K L)
        (_ : IsGalois K L) (_ : IsCyclic Gal(L/K))
        (completion : HasseCompletionData K L),
        ∀ v, brauerLiftingChange K L completion v (y v).toMul = 1

set_option synthInstance.maxHeartbeats 300000 in
-- The dependent local relative-Brauer family unfolds completion instances.
/-- The finite cyclic relative sequence, restricted to the exact kernel
statement used in VIII.4.2.  The local tuple is written in the same chosen
completion models as the cohomological localization. -/
def RelativeBrauerLifting : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (placeInvariant : PIData K)
    (y : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (localRelativeBrauer K L completion v))),
    placeInvariant.sum K
        (brauerDirectInclusion K L completion y) = 0 →
      y ∈ Set.range (brauerCohomologicalLocalization K L completion)

set_option synthInstance.maxHeartbeats 300000 in
-- The dependent local relative-Brauer family unfolds completion instances.
/-- Data-aware form of the finite cyclic relative kernel statement.  This is
the exact strength needed by the VIII.4.2 assembly and allows VII.8.1 to be
applied directly to the same `BData`. -/
def BrauerLiftingData : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (data : BData K)
    (y : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (localRelativeBrauer K L completion v))),
    data.placeInvariant.sum K
        (brauerDirectInclusion K L completion y) = 0 →
      y ∈ Set.range (brauerCohomologicalLocalization K L completion)

/-- The place-invariant-only statement implies its data-aware specialization. -/
theorem brauer_lifting_invariant
    (hrelative : RelativeBrauerLifting.{u}) :
    BrauerLiftingData.{u} := by
  intro K L _ _ _ _ _ _ _ _ completion data
  exact hrelative K L completion data.placeInvariant

private theorem brauer_change_algebra
    {k M : Type u} [Field k] [Field M]
    (a b : Algebra k M) (h : a = b) :
    @brauerBaseChange k M inferInstance inferInstance a =
      @brauerBaseChange k M inferInstance inferInstance b := by
  subst b
  rfl

set_option maxHeartbeats 4000000 in
-- The two dependent direct sums use propositionally equal completion algebras.
/-- Absolute localization of a relative Brauer class agrees with inclusion
of its cohomological relative localization. -/
theorem localization_brauer_cohomological
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (completion : HasseCompletionData K L)
    (data : BData K)
    (beta : Additive (relativeBrauerGroup K L)) :
    data.localization.localization
        (Additive.ofMul (beta.toMul : BrauerGroup K)) =
      brauerDirectInclusion K L completion
        (brauerCohomologicalLocalization K L completion beta) := by
  apply DirectSum.ext
  intro v
  have hrelative := (relativeCohomologicalLocalization
    K L completion).localization_apply beta.toMul v
  change brauerCohomologicalLocalization K L completion beta v =
    Additive.ofMul
      (relativeCohomologicalLocalize K L completion v beta.toMul) at hrelative
  change (DirectSum.component ℤ (NumberFieldPlace K)
      (fun w ↦ Additive (BrauerGroup (Submission.CField.RExist.placeCompletion K w))) v)
        (data.localization.localization
          (Additive.ofMul (beta.toMul : BrauerGroup K))) =
    localBrauerInclusion K L completion v
      (brauerCohomologicalLocalization K L completion beta v)
  rw [data.localization.localization_apply (beta.toMul : BrauerGroup K)]
  rw [hrelative]
  cases v with
  | inl P =>
      let v := (FinitePlace.mk P).val
      apply Additive.ofMul.injective
      change data.localization.localizeAt (.inl P)
          (beta.toMul : BrauerGroup K) =
        (relativeCohomologicalLocalize K L completion (.inl P)
          beta.toMul).val
      rw [relativeBrauerCompatibility
        (K := K) (L := L) completion beta.toMul (.inl P)]
      have hdata := data.localizeAt_eq (beta.toMul : BrauerGroup K) (.inl P)
      change data.localization.localizeAt (.inl P)
          (beta.toMul : BrauerGroup K) =
        @brauerBaseChange K v.Completion inferInstance inferInstance
          (completionEmbedding v).toAlgebra (beta.toMul : BrauerGroup K) at hdata
      have hmap := brauer_change_algebra
        (completionEmbedding v).toAlgebra (completionBaseAlgebra v) (by
          apply Algebra.algebra_ext
          intro a
          rfl)
      rw [hmap] at hdata
      exact hdata
  | inr v =>
      apply Additive.ofMul.injective
      change data.localization.localizeAt (.inr v)
          (beta.toMul : BrauerGroup K) =
        (relativeCohomologicalLocalize K L completion (.inr v)
          beta.toMul).val
      rw [relativeBrauerCompatibility
        (K := K) (L := L) completion beta.toMul (.inr v)]
      have hdata := data.localizeAt_eq (beta.toMul : BrauerGroup K) (.inr v)
      change data.localization.localizeAt (.inr v)
          (beta.toMul : BrauerGroup K) =
        @brauerBaseChange K v.1.Completion inferInstance inferInstance
          (completionEmbedding v.1).toAlgebra
          (beta.toMul : BrauerGroup K) at hdata
      have hmap := brauer_change_algebra
        (completionEmbedding v.1).toAlgebra (completionBaseAlgebra v.1) (by
          apply Algebra.algebra_ext
          intro a
          rfl)
      rw [hmap] at hdata
      exact hdata

set_option maxHeartbeats 4000000 in
-- The existential extension installs a dependent family of completion instances.
/-- The killing extension and the data-aware finite cyclic relative sequence
imply the kernel-lifting component of Theorem VIII.4.2. -/
theorem lifting_killing_data
    (hkill : KillingExtension.{u})
    (hrelative : BrauerLiftingData.{u}) :
    KernelLifting.{u} := by
  intro K _ _ data y hy
  obtain ⟨L, fieldL, numberFieldL, algebraKL, finiteDimensionalKL,
      isGaloisKL, isCyclicKL, completion, hlocal⟩ := hkill K data y hy
  letI : Field L := fieldL
  letI : NumberField L := numberFieldL
  letI : Algebra K L := algebraKL
  letI : FiniteDimensional K L := finiteDimensionalKL
  letI : IsGalois K L := isGaloisKL
  letI : IsCyclic Gal(L/K) := isCyclicKL
  obtain ⟨z, hz⟩ :=
    direct_base_change
      K L completion y hlocal
  have hzsum : data.placeInvariant.sum K
      (brauerDirectInclusion K L completion z) = 0 := by
    rw [hz]
    exact hy
  obtain ⟨beta, hbeta⟩ :=
    hrelative K L completion data z hzsum
  refine ⟨Additive.ofMul (beta.toMul : BrauerGroup K), ?_⟩
  rw [localization_brauer_cohomological
    K L completion data beta, hbeta, hz]

/-- The original place-invariant-only input also implies kernel lifting via
the data-aware assembly. -/
theorem lifting_killing_relative
    (hkill : KillingExtension.{u})
    (hrelative : RelativeBrauerLifting.{u}) :
    KernelLifting.{u} :=
  lifting_killing_data
    hkill
      (brauer_lifting_invariant
        hrelative)

/-- Final VIII.4.2 route with kernel lifting supplied by its two remaining
arithmetic components. -/
theorem lifting_assembly_components
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (hkill : KillingExtension.{u})
    (hrelative : RelativeBrauerLifting.{u}) :
    GlobalLocalizationSequence.{u} :=
  exactness_assembly_lifting
    h51 hArtin h81
      (lifting_killing_relative
        hkill hrelative)

end

end Submission.CField.BLoc
