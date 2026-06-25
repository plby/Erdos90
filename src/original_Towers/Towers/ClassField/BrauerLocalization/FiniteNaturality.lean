import Towers.ClassField.BrauerLocalization.H2Naturality

/-!
# Finite-place crossed-product naturality for relative Brauer localization

This file compares the chosen-completion categorical `H²` class with the
normalized multiplicative cocycle obtained by restricting to the chosen
place stabilizer and applying the completion embedding to coefficients.
The subsequent algebraic step identifies that cocycle with the
decomposition-field cocycle used by scalar extension of crossed products.
-/

namespace Towers.CField.BLoc

open CategoryTheory Representation groupCohomology
open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.BGroups
open Towers.CField.CProduca
open Towers.CField.LBrauer
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.HNorm

noncomputable section

universe u

variable {K L : Type u} [Field K] [hK : NumberField K]
  [Field L] [hL : NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

set_option maxHeartbeats 500000 in
-- The two completion-Galois equivalences elaborate together.
/-- The local Galois group of a finite chosen completion, identified with
the stabilizer of the chosen global place. -/
noncomputable def completionStabilizerEquiv
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (w : CompletionPlacesAbove (L := L) v) :
    letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    CompletionPlaceStabilizer v w ≃* Gal(w.1.Completion/v.Completion) := by
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  exact (MulEquiv.subgroupCongr
      (hasse_stabilizer_decomposition
        v w)).trans
    (decompositionCompletionExtension v w.1)

set_option synthInstance.maxHeartbeats 500000 in
-- Relabelling coefficients exposes both completion action instances.
set_option maxHeartbeats 500000 in
-- The cocycle restriction homomorphism unfolds the relabelled action.
/-- Relabel a finite chosen-completion multiplicative `H²` class by the
global place stabilizer. -/
noncomputable def localHStabilizer
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (w : CompletionPlacesAbove (L := L) v) :
    letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : MulDistribMulAction (CompletionPlaceStabilizer v w)
        w.1.Completionˣ := completionDistribAction v w
    MHTwo Gal(w.1.Completion/v.Completion) w.1.Completionˣ →*
      MHTwo (CompletionPlaceStabilizer v w) w.1.Completionˣ := by
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : MulDistribMulAction (CompletionPlaceStabilizer v w)
      w.1.Completionˣ := completionDistribAction v w
  let e : CompletionPlaceStabilizer v w ≃*
      Gal(w.1.Completion/v.Completion) :=
    (MulEquiv.subgroupCongr
      (hasse_stabilizer_decomposition v w)).trans
        (decompositionCompletionExtension v w.1)
  exact MHTwo.restrictionHom e.toMonoidHom
    (fun sigma y => by
      apply Units.ext
      exact stabilizer_decomposition_action
        v w sigma y)

set_option synthInstance.maxHeartbeats 200000 in
-- The categorical and multiplicative cocycle models elaborate together.
set_option maxHeartbeats 500000 in
-- The proof unfolds both degree-two cohomology maps on representatives.
omit hK hL in
/-- The finite local `H²` relabelling equivalence sends a multiplicative
local class to restriction along the stabilizer-to-local-Galois
isomorphism. -/
theorem h_stabilizer_multiplicative
    [NumberField K] [NumberField L]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v)
    (w : CompletionPlacesAbove (L := L) v) :
    let W := CompletionPlacesAbove (L := L) v
    letI : Finite W := absolute_extensions_separable v
    letI : Nonempty W :=
      absolute_value_extension (K := K) (L := L) v
    letI : MulAction.IsPretransitive Gal(L/K) W :=
      above_pretr_nonar v hvna
    letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      Towers.NumberTheory.Milne.placeCompletionDimensional v w
    letI : IsGalois v.Completion w.1.Completion :=
      placeCompletionGalois v w
    letI : MulSemiringAction (CompletionPlaceStabilizer v w)
        w.1.Completion := stabilizerSemiringAction v w
    letI : MulDistribMulAction (CompletionPlaceStabilizer v w)
        w.1.Completionˣ := completionDistribAction v w
    ∀ x : MHTwo Gal(w.1.Completion/v.Completion) w.1.Completionˣ,
    (h2Stabilizer
        (K := K) (L := L) v w hvna)
        (multiplicativeLiftAdditive x) =
      multiplicativeLiftAdditive
        (localHStabilizer
          (K := K) (L := L) v w x) := by
  let W := CompletionPlacesAbove (L := L) v
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W :=
    absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    above_pretr_nonar v hvna
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  letI : MulDistribMulAction Gal(w.1.Completion/v.Completion)
      w.1.Completionˣ := Units.mulDistribMulActionRight
  letI : MulSemiringAction (CompletionPlaceStabilizer v w)
      w.1.Completion := stabilizerSemiringAction v w
  letI : MulDistribMulAction (CompletionPlaceStabilizer v w)
      w.1.Completionˣ := completionDistribAction v w
  dsimp only
  intro x
  let e : CompletionPlaceStabilizer v w ≃*
      Gal(w.1.Completion/v.Completion) :=
    (MulEquiv.subgroupCongr
      (hasse_stabilizer_decomposition v w)).trans
        (decompositionCompletionExtension v w.1)
  have hsmul : ∀ sigma : CompletionPlaceStabilizer v w,
      ∀ y : w.1.Completionˣ, sigma • y = e sigma • y := by
    intro sigma y
    apply Units.ext
    change stabilizerRingHom v w sigma (y : w.1.Completion) =
      (e sigma : w.1.Completion ≃ₐ[v.Completion] w.1.Completion)
        (y : w.1.Completion)
    exact stabilizer_decomposition_action v w sigma y
  induction x using Quotient.inductionOn with
  | _ c =>
      change (h2Stabilizer
          (K := K) (L := L) v w hvna)
          (normalizedCocycleU c) =
        multiplicativeLiftAdditive
          (localHStabilizer
            (K := K) (L := L) v w (MHTwo.mk c))
      unfold localHStabilizer
      change (h2Stabilizer
          (K := K) (L := L) v w hvna)
          (normalizedCocycleU c) =
        normalizedCocycleU
          (NMCocycl₂.restrict e.toMonoidHom hsmul c)
      unfold h2Stabilizer
        hasseHMul
      dsimp only
      change groupCohomology.map
          (MonoidHom.id (CompletionPlaceStabilizer v w))
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

end Towers.CField.BLoc
