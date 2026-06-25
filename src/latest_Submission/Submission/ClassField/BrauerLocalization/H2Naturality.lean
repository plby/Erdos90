import Submission.ClassField.BrauerLocalization.CompletionNaturality
import Submission.FieldTheory.CentralFactorSet

/-!
# Multiplicative H² naturality for chosen completions

This file identifies the categorical restriction-and-completion map used in
the idèle argument with restriction and coefficient change on normalized
multiplicative cocycles.
-/

namespace Submission.CField.BLoc

open CategoryTheory Representation groupCohomology
open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.CProduca
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.HNorm

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

/-- Convert the direct multiplicative presentation of global-units `H²`
to the resized representation used in the idèle short exact sequence. -/
noncomputable def hasseGlobalResized :
    H2 (hasseGlobalRepresentation K L) ≃+
      H2 (resizedRepresentation K L) :=
  (((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 2).mapIso
    (resizedIsoHasse K L)).toLinearEquiv.toAddEquiv).symm

omit [NumberField K] [NumberField L] in
/-- The local relative-Brauer comparison sends a represented crossed
product to the resized additive class of its defining cocycle. -/
theorem relative_brauer_cohomology
    (c : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ)) :
    relativeBrauer2 K L
        (Additive.ofMul (CProduc.relativeBrauerClass K L c)) =
      multiplicativeLiftAdditive (MHTwo.mk c) := by
  change multiplicativeLiftAdditive
      ((CProduc.hRelativeBrauer K L).symm
        (CProduc.relativeBrauerClass K L c)) = _
  have hc : CProduc.relativeBrauerClass K L c =
      CProduc.hRelativeBrauer K L
        (MHTwo.mk c) := rfl
  rw [hc, MulEquiv.symm_apply_apply]

/-- The resized global relative-Brauer comparison has the corresponding
representative formula after the canonical global-units representation
transport. -/
theorem relative_brauer_resized
    (c : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ)) :
    relativeBrauerResized K L
        (Additive.ofMul (CProduc.relativeBrauerClass K L c)) =
      hasseGlobalResized
        (K := K) (L := L)
        (multiplicativeLiftAdditive (MHTwo.mk c)) := by
  change hasseGlobalResized (K := K) (L := L)
      (relativeBrauer2 K L
        (Additive.ofMul (CProduc.relativeBrauerClass K L c))) = _
  rw [relative_brauer_cohomology]

/-- Restrict a global multiplicative `H²` class to the stabilizer of the
chosen completion and apply `Lˣ → L_wˣ` to its coefficients. -/
noncomputable def multiplicativeChosenStabilizer
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :
    let w := hasseChosenPlace completion v
    let H := CompletionPlaceStabilizer (hasseAbsoluteValue v) w
    letI : MulDistribMulAction H w.1.Completionˣ :=
      completionDistribAction
        (hasseAbsoluteValue v) w
    MHTwo Gal(L/K) Lˣ →*
      MHTwo H w.1.Completionˣ := by
  let w := hasseChosenPlace completion v
  let H := CompletionPlaceStabilizer (hasseAbsoluteValue v) w
  letI : MulDistribMulAction H Lˣ :=
    (inferInstance : MulDistribMulAction Gal(L/K) Lˣ).compHom
      Lˣ H.subtype
  letI : MulDistribMulAction H w.1.Completionˣ :=
    completionDistribAction
      (hasseAbsoluteValue v) w
  let f : Lˣ →* w.1.Completionˣ := Units.map (completionEmbedding w.1)
  have hf : ∀ sigma : H, ∀ x : Lˣ, f (sigma • x) = sigma • f x := by
    intro sigma x
    apply Units.ext
    exact (place_stabilizer_embedding
      (hasseAbsoluteValue v) w sigma (x : L)).symm
  exact (MHTwo.mapCoefficientsHom f hf).comp
    (MHTwo.restrictionHom H.subtype (fun _ _ => rfl))

set_option maxHeartbeats 1000000 in
-- Unfolding the three universe-resizing cohomology maps is expensive.
/-- The universe-resized categorical class of the restricted completed
cocycle is exactly the map used by the chosen-completion localization data. -/
theorem multiplicative_additive_chosen
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K)
    (x : MHTwo Gal(L/K) Lˣ) :
    let w := hasseChosenPlace completion v
    let H := CompletionPlaceStabilizer (hasseAbsoluteValue v) w
    letI : MulDistribMulAction H w.1.Completionˣ :=
      completionDistribAction
        (hasseAbsoluteValue v) w
    uliftHasseNorm
        (K := K) (L := L) (hasseAbsoluteValue v)
        (hasseChosenPlace completion v)
        (resizedGlobalChosen
          (K := K) (L := L) completion v
          (hasseGlobalResized
            (K := K) (L := L)
            (multiplicativeLiftAdditive x))) =
      multiplicativeLiftAdditive
        (multiplicativeChosenStabilizer
          (K := K) (L := L) completion v x) := by
  let w := hasseChosenPlace completion v
  let H := CompletionPlaceStabilizer (hasseAbsoluteValue v) w
  letI : MulDistribMulAction H Lˣ :=
    (inferInstance : MulDistribMulAction Gal(L/K) Lˣ).compHom
      Lˣ H.subtype
  letI : MulDistribMulAction H w.1.Completionˣ :=
    completionDistribAction
      (hasseAbsoluteValue v) w
  let f : Lˣ →* w.1.Completionˣ := Units.map (completionEmbedding w.1)
  have hf : ∀ sigma : H, ∀ y : Lˣ, f (sigma • y) = sigma • f y := by
    intro sigma y
    apply Units.ext
    exact (place_stabilizer_embedding
      (hasseAbsoluteValue v) w sigma (y : L)).symm
  dsimp only
  induction x using Quotient.inductionOn with
  | _ c =>
      change groupCohomology.map (MonoidHom.id H)
          (uliftIsoHasse
            (K := K) (L := L) (hasseAbsoluteValue v) w).hom 2
          (groupCohomology.map H.subtype
            (unitsChosenRepresentation
              (K := K) (L := L) completion v) 2
            (groupCohomology.map (MonoidHom.id Gal(L/K))
              (resizedIsoHasse K L).inv 2
              (normalizedCocycleU c))) =
        normalizedCocycleU
          (NMCocycl₂.mapCoefficients f hf
            (NMCocycl₂.restrict H.subtype
              (fun _ _ => rfl) c))
      rw [normalizedCocycleU,
        normalizedCocycleU,
        H2π_comp_map_apply, H2π_comp_map_apply,
        H2π_comp_map_apply]
      congr 1

end

end Submission.CField.BLoc
