import Submission.ClassField.BrauerLocalization.H2Naturality

/-!
# Infinite-place crossed-product naturality for relative Brauer localization

This file proves the archimedean analogue of the finite local
Galois/stabilizer comparison at the level of normalized multiplicative
two-cocycles.  The remaining archimedean work is therefore algebraic:
identify scalar extension of the global crossed product with the local
crossed product represented by this restricted completed cocycle.
-/

namespace Submission.CField.BLoc

open CategoryTheory Representation groupCohomology
open NumberField
open Submission.NumberTheory.Milne
open Submission.CField.CProduca
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.HNorm

noncomputable section

universe u

variable {K L : Type u} [Field K] [hK : NumberField K]
  [Field L] [hL : NumberField L] [Algebra K L]
  [hKL : FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

set_option synthInstance.maxHeartbeats 500000 in
-- The archimedean completion and Galois instances elaborate together.
set_option maxHeartbeats 1000000 in
-- Identifying the infinite completion Galois group unfolds the chosen-place transport.
/-- The local Galois group of an infinite chosen completion, identified with
the stabilizer of the chosen global place. -/
noncomputable def infiniteCompletionStabilizer
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    let hwv := infinite_lies_comap v w.1 w.2
    let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
    letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwv).toAlgebra
    CompletionPlaceStabilizer v.1 w0 ≃*
      Gal(w.1.1.Completion/v.1.Completion) := by
  let hwv := infinite_lies_comap v w.1 w.2
  let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  exact (MulEquiv.subgroupCongr
      (hasse_stabilizer_decomposition
        v.1 w0)).trans
    (infiniteDecompositionGroup v w.1)

set_option synthInstance.maxHeartbeats 500000 in
-- Relabelling coefficients exposes both completion action instances.
set_option maxHeartbeats 1000000 in
-- Relabelling the multiplicative cocycle unfolds both stabilizer actions.
/-- Relabel an infinite chosen-completion multiplicative `H²` class by the
global place stabilizer. -/
noncomputable def infinite2Stabilizer
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    let hwv := infinite_lies_comap v w.1 w.2
    let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
    letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwv).toAlgebra
    letI : MulDistribMulAction (CompletionPlaceStabilizer v.1 w0)
        w.1.1.Completionˣ := completionDistribAction v.1 w0
    MHTwo Gal(w.1.1.Completion/v.1.Completion)
        w.1.1.Completionˣ →*
      MHTwo (CompletionPlaceStabilizer v.1 w0)
        w.1.1.Completionˣ := by
  let hwv := infinite_lies_comap v w.1 w.2
  let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : MulDistribMulAction (CompletionPlaceStabilizer v.1 w0)
      w.1.1.Completionˣ := completionDistribAction v.1 w0
  let e := infiniteCompletionStabilizer
    (K := K) (L := L) v w
  exact MHTwo.restrictionHom e.toMonoidHom
    (fun sigma y => by
      apply Units.ext
      exact stabilizer_decomposition_action
        v.1 w0 sigma y)

set_option synthInstance.maxHeartbeats 500000 in
-- The categorical and multiplicative cocycle models unfold simultaneously.
set_option maxHeartbeats 1500000 in
-- Comparing the two local cohomology models unfolds their dependent actions.
omit hK hL hKL in
/-- The infinite local `H²` relabelling equivalence sends a multiplicative
local class to restriction along the stabilizer-to-local-Galois
isomorphism. -/
theorem infinite_stabilizer_multiplicative
    [NumberField K] [NumberField L] [FiniteDimensional K L]
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    let hwv := infinite_lies_comap v w.1 w.2
    let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
    letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
    letI : Algebra v.1.Completion w.1.1.Completion :=
      (completionLies v.1 w.1.1 hwv).toAlgebra
    letI : Module.Finite v.1.Completion w.1.1.Completion :=
      infinite_completion_module (K := K) (L := L) v w
    letI : IsGalois v.1.Completion w.1.1.Completion :=
      infiniteHasseGalois K L v w
    letI : MulSemiringAction (CompletionPlaceStabilizer v.1 w0)
        w.1.1.Completion := stabilizerSemiringAction v.1 w0
    letI : MulDistribMulAction (CompletionPlaceStabilizer v.1 w0)
        w.1.1.Completionˣ := completionDistribAction v.1 w0
    ∀ x : MHTwo Gal(w.1.1.Completion/v.1.Completion)
        w.1.1.Completionˣ,
    (infiniteHStabilizer
        (K := K) (L := L) v w)
        (multiplicativeLiftAdditive x) =
      multiplicativeLiftAdditive
        (infinite2Stabilizer
          (K := K) (L := L) v w x) := by
  let hwv := infinite_lies_comap v w.1 w.2
  let w0 : CompletionPlacesAbove (L := L) v.1 := ⟨w.1.1, hwv⟩
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteHasseGalois K L v w
  letI : MulDistribMulAction Gal(w.1.1.Completion/v.1.Completion)
      w.1.1.Completionˣ := Units.mulDistribMulActionRight
  letI : MulSemiringAction (CompletionPlaceStabilizer v.1 w0)
      w.1.1.Completion := stabilizerSemiringAction v.1 w0
  letI : MulDistribMulAction (CompletionPlaceStabilizer v.1 w0)
      w.1.1.Completionˣ := completionDistribAction v.1 w0
  dsimp only
  intro x
  let e := infiniteCompletionStabilizer
    (K := K) (L := L) v w
  have hsmul : ∀ sigma : CompletionPlaceStabilizer v.1 w0,
      ∀ y : w.1.1.Completionˣ, sigma • y = e sigma • y := by
    intro sigma y
    apply Units.ext
    change stabilizerRingHom v.1 w0 sigma (y : w.1.1.Completion) =
      (e sigma : w.1.1.Completion ≃ₐ[v.1.Completion]
        w.1.1.Completion) (y : w.1.1.Completion)
    exact stabilizer_decomposition_action v.1 w0 sigma y
  induction x using Quotient.inductionOn with
  | _ c =>
      change (infiniteHStabilizer
          (K := K) (L := L) v w)
          (normalizedCocycleU c) =
        multiplicativeLiftAdditive
          (infinite2Stabilizer
            (K := K) (L := L) v w (MHTwo.mk c))
      unfold infinite2Stabilizer
      change (infiniteHStabilizer
          (K := K) (L := L) v w)
          (normalizedCocycleU c) =
        normalizedCocycleU
          (NMCocycl₂.restrict e.toMonoidHom hsmul c)
      unfold infiniteHStabilizer
        hasseHMul
      dsimp only
      change groupCohomology.map
          (MonoidHom.id (CompletionPlaceStabilizer v.1 w0))
          (hasseRestrictIso e _).hom 2
          (groupCohomology.map e.toMonoidHom (𝟙 _) 2
            (normalizedCocycleU c)) =
        normalizedCocycleU
          (NMCocycl₂.restrict e.toMonoidHom hsmul c)
      rw [normalizedCocycleU,
        normalizedCocycleU,
        H2π_comp_map_apply, H2π_comp_map_apply]
      congr 1

end

end Submission.CField.BLoc
