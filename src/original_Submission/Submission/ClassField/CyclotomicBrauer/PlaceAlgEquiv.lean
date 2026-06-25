import Submission.ClassField.CyclotomicBrauer.LocalizationInjectivity
import Submission.ClassField.CyclotomicBrauer.RationalBaseChange
import Submission.ClassField.BrauerGroups.BrauerTrivialClass
import Submission.ClassField.NormIndex.CompletionPlaceBridge
import Submission.ClassField.BrauerLocalization.KillingSelection

/-!
# Chapter VII, Section 7, Proposition 7.2

This file discharges the arithmetic bridges in the source-statement file:
finite support and local invariant annihilation, Theorem 7.1, and the cyclic
cyclotomic extension constructed in Lemma 7.3.
-/

namespace Submission.CField.CBrauer

open AbsoluteValue IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.BGroups
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.RExist
open Submission.CField.HNorm
open Submission.CField.BLoc

noncomputable section

universe u

/-- The two finite-completion models used in Chapters V and VII agree as
extensions of the global number field. -/
noncomputable def placeCompletionAlg
    (K : Type u) [Field K] [NumberField K]
    (P : finitePrime K) :
    letI : Algebra K (FinitePlace.mk P).val.Completion :=
      (completionEmbedding (FinitePlace.mk P).val).toAlgebra
    letI : Algebra K (P.adicCompletion K) :=
      (FinitePlace.embedding P).toAlgebra
    (FinitePlace.mk P).val.Completion ≃ₐ[K] P.adicCompletion K := by
  letI : Algebra K (FinitePlace.mk P).val.Completion :=
    (completionEmbedding (FinitePlace.mk P).val).toAlgebra
  letI : Algebra K (P.adicCompletion K) :=
    (FinitePlace.embedding P).toAlgebra
  exact AlgEquiv.ofRingEquiv
    (f := placeCompletionAdic P)
    (finite_place_adic P)

/-- The Brauer-group consequence of Theorem 7.1 in the exact form used by
Proposition 7.2. -/
theorem globalBrauerBridge :
    GlobalBrauerBridge.{u} := by
  intro K _ _ beta hlocal
  let data := brauerData K
  apply Additive.ofMul.injective
  apply brauerLocalization_injective K
  apply DirectSum.ext
  intro v
  change (DirectSum.component ℤ (NumberFieldPlace K)
      (fun w => Additive (BrauerGroup (RExist.placeCompletion K w))) v)
        (data.localization.localization (Additive.ofMul beta)) =
    (DirectSum.component ℤ (NumberFieldPlace K)
      (fun w => Additive (BrauerGroup (RExist.placeCompletion K w))) v)
        (data.localization.localization (Additive.ofMul 1))
  rw [data.localization.localization_apply,
    data.localization.localization_apply]
  rw [data.localizeAt_eq, data.localizeAt_eq, map_one]
  cases v with
  | inl P =>
      letI : Algebra K (FinitePlace.mk P).val.Completion :=
        (completionEmbedding (FinitePlace.mk P).val).toAlgebra
      letI : Algebra K (P.adicCompletion K) :=
        (FinitePlace.embedding P).toAlgebra
      have hnormalized := brauer_change_alg
        K (P.adicCompletion K) (FinitePlace.mk P).val.Completion
        (placeCompletionAlg K P).symm beta
        (by simpa only [RExist.placeCompletion] using hlocal (.inl P))
      exact congrArg Additive.ofMul hnormalized
  | inr v =>
      exact congrArg Additive.ofMul
        (by simpa only [RExist.placeCompletion] using
          hlocal (.inr v))

set_option synthInstance.maxHeartbeats 500000 in
-- Completion-place conjugacy unfolds several dependent algebra structures.
set_option maxHeartbeats 3000000 in
-- Completion-place conjugacy unfolds several dependent algebra structures.
/-- In a finite Galois extension, triviality after scalar extension to one
normalized completion above a finite prime transports to every completion
above that prime. -/
theorem brauer_change_completions
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : finitePrime K)
    (z w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (x : BrauerGroup (FinitePlace.mk P).val.Completion)
    (hz :
      letI : Algebra (FinitePlace.mk P).val.Completion z.1.Completion :=
        (completionLies (FinitePlace.mk P).val z.1 z.2).toAlgebra
      brauerBaseChange (FinitePlace.mk P).val.Completion z.1.Completion x = 1) :
    letI : Algebra (FinitePlace.mk P).val.Completion w.1.Completion :=
      (completionLies (FinitePlace.mk P).val w.1 w.2).toAlgebra
    brauerBaseChange (FinitePlace.mk P).val.Completion w.1.Completion x = 1 := by
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v) :=
    completion_above_pretransitive P
  obtain ⟨sigma, hsigma⟩ := MulAction.exists_smul_eq Gal(L/K) z w
  have hz' : sigma⁻¹ • w = z := by
    calc
      sigma⁻¹ • w = sigma⁻¹ • (sigma • z) :=
        congrArg (fun q => sigma⁻¹ • q) hsigma.symm
      _ = z := inv_smul_smul sigma z
  subst z
  letI : Algebra v.Completion (sigma⁻¹ • w).1.Completion :=
    (completionLies v (sigma⁻¹ • w).1
      (sigma⁻¹ • w).2).toAlgebra
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : SMul v.Completion w.1.Completion := Algebra.toSMul
  exact brauer_change_alg
    v.Completion (sigma⁻¹ • w).1.Completion w.1.Completion
    (completionTransportAlg v sigma w) x hz

/-- A normalized upper completion is canonically equivalent, over the upper
global field, to the adic completion at its centered prime. -/
noncomputable def upperAlgAdic
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : finitePrime K)
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    let Q := upperPrime (K := K) (L := L) P
      (placeUpperFactor (K := K) (L := L) P w)
    letI : Algebra L w.1.Completion := (completionEmbedding w.1).toAlgebra
    letI : Algebra L (Q.adicCompletion L) := (FinitePlace.embedding Q).toAlgebra
    w.1.Completion ≃ₐ[L] Q.adicCompletion L := by
  let Q := upperPrime (K := K) (L := L) P
    (placeUpperFactor (K := K) (L := L) P w)
  letI : Algebra L w.1.Completion := (completionEmbedding w.1).toAlgebra
  letI : Algebra L (Q.adicCompletion L) := (FinitePlace.embedding Q).toAlgebra
  exact AlgEquiv.ofRingEquiv
    (f := completionPlaceAdic (K := K) (L := L) P w)
    (place_adic_embedding
      (K := K) (L := L) P w)

/-- Coordinates of the canonical localization are the concrete completion
base changes, after forgetting the additive wrapper. -/
theorem localization_coordinate_mul
    (K : Type u) [Field K] [NumberField K]
    (data : BData K) (beta : BrauerGroup K)
    (v : NumberFieldPlace K) :
    (data.localization.localization (Additive.ofMul beta) v).toMul =
      brauerBaseChange K (RExist.placeCompletion K v) beta := by
  have h := data.localization.localization_apply beta v
  change data.localization.localization (Additive.ofMul beta) v =
    Additive.ofMul (data.localization.localizeAt v beta) at h
  rw [h, data.localizeAt_eq]
  simp

set_option synthInstance.maxHeartbeats 500000 in
-- Both completion towers carry dependent algebra structures.
set_option maxHeartbeats 3000000 in
-- Both completion towers carry dependent algebra structures.
/-- If the localization of a global Brauer class dies in a normalized upper
completion, then the base-changed global class dies in the adic completion
at the centered upper prime. -/
theorem split_centered_prime
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (beta : BrauerGroup K) (P : finitePrime K)
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (hw :
      letI : Algebra K (FinitePlace.mk P).val.Completion :=
        (completionEmbedding (FinitePlace.mk P).val).toAlgebra
      letI : Algebra (FinitePlace.mk P).val.Completion w.1.Completion :=
        (completionLies
          (FinitePlace.mk P).val w.1 w.2).toAlgebra
      brauerBaseChange (FinitePlace.mk P).val.Completion w.1.Completion
        (brauerBaseChange K (FinitePlace.mk P).val.Completion beta) = 1) :
    let Q := upperPrime (K := K) (L := L) P
      (placeUpperFactor (K := K) (L := L) P w)
    letI : Algebra L (Q.adicCompletion L) := (FinitePlace.embedding Q).toAlgebra
    brauerBaseChange L (Q.adicCompletion L) (brauerBaseChange K L beta) = 1 := by
  let v := (FinitePlace.mk P).val
  let Q := upperPrime (K := K) (L := L) P
    (placeUpperFactor (K := K) (L := L) P w)
  letI : Algebra K v.Completion := (completionEmbedding v).toAlgebra
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Algebra L w.1.Completion := (completionEmbedding w.1).toAlgebra
  letI : Algebra K w.1.Completion :=
    ((completionEmbedding w.1).comp (algebraMap K L)).toAlgebra
  letI : SMul K v.Completion := Algebra.toSMul
  letI : SMul K w.1.Completion := Algebra.toSMul
  letI : IsScalarTower K v.Completion w.1.Completion := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (completion_lies_comp v w.1 w.2).symm
  have hglobalW : brauerBaseChange K w.1.Completion beta = 1 := by
    rw [← base_change_tower K v.Completion w.1.Completion beta]
    exact hw
  letI : Algebra L (Q.adicCompletion L) := (FinitePlace.embedding Q).toAlgebra
  letI : Algebra K (Q.adicCompletion L) :=
    ((algebraMap L (Q.adicCompletion L)).comp (algebraMap K L)).toAlgebra
  letI : SMul L (Q.adicCompletion L) := Algebra.toSMul
  letI : SMul K (Q.adicCompletion L) := Algebra.toSMul
  let eL := upperAlgAdic K L P w
  let eK : w.1.Completion ≃ₐ[K] Q.adicCompletion L :=
    AlgEquiv.ofRingEquiv (f := eL.toRingEquiv) (fun x => by
      change eL (completionEmbedding w.1 (algebraMap K L x)) =
        FinitePlace.embedding Q (algebraMap K L x)
      exact eL.commutes (algebraMap K L x))
  have hglobalQ : brauerBaseChange K (Q.adicCompletion L) beta = 1 :=
    brauer_change_alg
      K w.1.Completion (Q.adicCompletion L) eK beta hglobalW
  letI : IsScalarTower K L (Q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact calc
    brauerBaseChange L (Q.adicCompletion L) (brauerBaseChange K L beta) =
        brauerBaseChange K (Q.adicCompletion L) beta :=
      base_change_tower K L (Q.adicCompletion L) beta
    _ = 1 := hglobalQ

set_option synthInstance.maxHeartbeats 1000000 in
-- The finite-place branch combines dependent completion choices and transport.
set_option maxHeartbeats 6000000 in
-- The finite-place branch combines dependent completion choices and transport.
/-- **Proposition VII.7.2.** Every Brauer class over a number field is split
by a finite cyclic cyclotomic extension. -/
theorem placeAlgStatement : (∀ (K : Type u) [Field K] [NumberField K]
      (beta : BrauerGroup.{u, u} K),
      Nonempty (SplittingExtensionData K beta)) := by
  intro K _ _ beta
  let data := brauerData K
  let y := data.localization.localization (Additive.ofMul beta)
  let S := finitePlaceSupport K y
  let m := localInvariantAnnihilator K data y
  have hm : 0 < m := invariant_annihilator_pos K data y
  obtain ⟨extension, hcyclicCyclotomic, htotallyComplex, hdegrees⟩ :=
    rationalBaseChange K S m hm
  letI : Field extension.L := extension.fieldL
  letI : NumberField extension.L := extension.numberFieldL
  letI : Algebra K extension.L := extension.algebraKL
  letI : FiniteDimensional K extension.L := extension.finiteDimensionalKL
  letI : IsGalois K extension.L := extension.isGaloisKL
  letI : IsCyclic Gal(extension.L/K) := hcyclicCyclotomic.1
  letI : NumberField.IsTotallyComplex extension.L := htotallyComplex
  obtain ⟨selection⟩ :=
    finite_completion_selection K extension S m hdegrees
  refine ⟨⟨extension, hcyclicCyclotomic, ?_⟩⟩
  apply globalBrauerBridge extension.L
    (brauerBaseChange K extension.L beta)
  intro place
  cases place with
  | inr q =>
      have hqcomplex : InfinitePlace.IsComplex q :=
        NumberField.IsTotallyComplex.isComplex q
      letI : IsAlgClosed (RExist.placeCompletion extension.L (.inr q)) := by
        change IsAlgClosed q.1.Completion
        exact alg_closed_ring
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex hqcomplex).symm
      exact @Subsingleton.elim
        (BrauerGroup (RExist.placeCompletion extension.L (.inr q)))
        (brauer_subsingleton_closed
          (RExist.placeCompletion extension.L (.inr q))) _ _
  | inl Q =>
      let P : finitePrime K :=
        Q.under (NumberField.RingOfIntegers K)
      let Qabove : FinitePrimesAbove (K := K) (L := extension.L) P :=
        ⟨Q, rfl⟩
      let qFactor : UpperPrimeFactors (K := K) (L := extension.L) P :=
        (upperPrimesAbove
          (K := K) (L := extension.L) P).symm Qabove
      let w : CompletionPlacesAbove (L := extension.L) (FinitePlace.mk P).val :=
        (placesAboveFactors
          (K := K) (L := extension.L) P).symm qFactor
      have hfactor : placeUpperFactor
          (K := K) (L := extension.L) P w = qFactor := by
        exact (placesAboveFactors
          (K := K) (L := extension.L) P).apply_symm_apply qFactor
      have hcenter : upperPrime (K := K) (L := extension.L) P qFactor = Q := by
        have hfiber := (upperPrimesAbove
          (K := K) (L := extension.L) P).apply_symm_apply Qabove
        exact congrArg Subtype.val hfiber
      have hcenterW : upperPrime (K := K) (L := extension.L) P
          (placeUpperFactor
            (K := K) (L := extension.L) P w) = Q := by
        rw [hfactor, hcenter]
      let v := (FinitePlace.mk P).val
      letI : Algebra K v.Completion := (completionEmbedding v).toAlgebra
      letI : Algebra v.Completion w.1.Completion :=
        (completionLies v w.1 w.2).toAlgebra
      have hlocalY : brauerBaseChange v.Completion w.1.Completion
          (y (.inl P)).toMul = 1 := by
        by_cases hP : P ∈ S
        · let Ps : S := ⟨P, hP⟩
          have hselected :=
            selected_change_direct
              K extension.L data y selection Ps
          exact brauer_change_completions
            K extension.L P (selection.selected Ps) w (y (.inl P)).toMul
            hselected
        · have hyP : y (.inl P) = 0 :=
            coordinate_not_support K y P hP
          rw [hyP]
          exact map_one (brauerBaseChange v.Completion w.1.Completion)
      have hcoord := localization_coordinate_mul
        K data beta (.inl P)
      change (y (.inl P)).toMul =
        brauerBaseChange K v.Completion beta at hcoord
      rw [hcoord] at hlocalY
      let R := upperPrime (K := K) (L := extension.L) P
        (placeUpperFactor
          (K := K) (L := extension.L) P w)
      letI : Algebra extension.L (R.adicCompletion extension.L) :=
        (FinitePlace.embedding R).toAlgebra
      letI : Algebra extension.L (Q.adicCompletion extension.L) :=
        Ideles.instAlgebraPlaceCompletion extension.L (.inl Q)
      have hcentered : brauerBaseChange extension.L
          (R.adicCompletion extension.L)
          (brauerBaseChange K extension.L beta) = 1 := by
        exact split_centered_prime
          K extension.L beta P w hlocalY
      let eCenter : R.adicCompletion extension.L ≃ₐ[extension.L]
          Q.adicCompletion extension.L :=
        AlgEquiv.ofRingEquiv
          (f := RingEquiv.cast (R := fun T => T.adicCompletion extension.L)
            hcenterW)
          (fun x => by
            change RingEquiv.cast
                (R := fun T => T.adicCompletion extension.L) hcenterW
                (FinitePlace.embedding R x) =
              FinitePlace.embedding Q x
            exact
              Submission.CField.NIndex.adic_completion_embedding
                hcenterW x)
      simpa only [Ideles.placeCompletion] using
        (brauer_change_alg extension.L
          (R.adicCompletion extension.L)
          (Q.adicCompletion extension.L) eCenter
          (brauerBaseChange K extension.L beta) hcentered)

end

end Submission.CField.CBrauer
