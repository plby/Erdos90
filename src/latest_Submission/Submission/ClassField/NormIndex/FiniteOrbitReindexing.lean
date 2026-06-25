import Submission.ClassField.NormIndex.FiniteTransportComposition

/-!
# Orbit reindexing for finite local norms

The local norm formula is centered at each completion place.  To multiply
those formulas at one chosen coordinate, this file transports each centered
factor to that coordinate and reindexes the resulting place/stabilizer pairs
by the global Galois group.
-/

namespace Submission.CField.NIndex

open Ideal IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Place-indexed stabilizer elements. -/
abbrev PlacePointStabilizers
    (v : AbsoluteValue K ℝ) :=
  Σ w : CompletionPlacesAbove (L := L) v, CompletionPlaceStabilizer v w

/-- A place together with an element of its own stabilizer determines the
global element `r_w h`, where `r_w` returns that place to `w₀`. -/
noncomputable def pointStabilizerGalois
    (v : AbsoluteValue K ℝ)
    (w₀ : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)] :
    PlacePointStabilizers (K := K) (L := L) v → Gal(L/K) :=
  fun p => completionPlaceReturn v w₀ p.1 * p.2.1

/-- Inverse to `pointStabilizerGalois`. -/
noncomputable def galoisPointStabilizer
    (v : AbsoluteValue K ℝ)
    (w₀ : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)] :
    Gal(L/K) → PlacePointStabilizers (K := K) (L := L) v := by
  intro sigma
  let w : CompletionPlacesAbove (L := L) v := sigma⁻¹ • w₀
  let r := completionPlaceReturn v w₀ w
  have hr : r⁻¹ • w₀ = w := by
    calc
      r⁻¹ • w₀ = r⁻¹ • (r • w) := by
        rw [place_return_smul v w₀ w]
      _ = w := inv_smul_smul r w
  refine ⟨w, ⟨r⁻¹ * sigma, ?_⟩⟩
  change (r⁻¹ * sigma) • w = w
  rw [mul_smul]
  rw [show sigma • w = w₀ by
    dsimp only [w]
    exact smul_inv_smul sigma w₀]
  exact hr

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
@[simp]
theorem point_stabilizer_after
    (v : AbsoluteValue K ℝ)
    (w₀ : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)]
    (sigma : Gal(L/K)) :
    pointStabilizerGalois v w₀
        (galoisPointStabilizer v w₀ sigma) = sigma := by
  dsimp [pointStabilizerGalois,
    galoisPointStabilizer]
  simp

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
@[simp]
theorem point_after_forward
    (v : AbsoluteValue K ℝ)
    (w₀ : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)]
    (p : PlacePointStabilizers (K := K) (L := L) v) :
    galoisPointStabilizer v w₀
        (pointStabilizerGalois v w₀ p) = p := by
  rcases p with ⟨w, h⟩
  let r := completionPlaceReturn v w₀ w
  have hr : r⁻¹ • w₀ = w := by
    calc
      r⁻¹ • w₀ = r⁻¹ • (r • w) := by
        rw [place_return_smul v w₀ w]
      _ = w := inv_smul_smul r w
  have hsource :
      ((r * h.1)⁻¹ • w₀ : CompletionPlacesAbove (L := L) v) = w := by
    calc
      (r * h.1)⁻¹ • w₀ = h.1⁻¹ • (r⁻¹ • w₀) := by
        rw [mul_inv_rev, mul_smul]
      _ = h.1⁻¹ • w := congrArg (fun z => h.1⁻¹ • z) hr
      _ = w := (h⁻¹).2
  have hw :
      (galoisPointStabilizer v w₀
        (pointStabilizerGalois v w₀ ⟨w, h⟩)).1 = w :=
    hsource
  apply Sigma.ext hw
  apply (Subtype.heq_iff_coe_eq (fun sigma : Gal(L/K) => by rw [hw])).2
  change (completionPlaceReturn v w₀ ((r * h.1)⁻¹ • w₀))⁻¹ *
      (r * h.1) = h.1
  rw [hsource]
  dsimp only [r]
  simp

/-- The global Galois group is the disjoint union of the stabilizers of all
completion places above `v`. -/
noncomputable def placePointStabilizer
    (v : AbsoluteValue K ℝ)
    (w₀ : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)] :
    PlacePointStabilizers (K := K) (L := L) v ≃ Gal(L/K) where
  toFun := pointStabilizerGalois v w₀
  invFun := galoisPointStabilizer v w₀
  left_inv := point_after_forward v w₀
  right_inv := point_stabilizer_after v w₀

omit [NumberField K] [NumberField L] [FiniteDimensional K L]
  [IsGalois K L] in
@[simp]
theorem place_point_stabilizer
    (v : AbsoluteValue K ℝ)
    (w₀ : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)]
    (w : CompletionPlacesAbove (L := L) v)
    (h : CompletionPlaceStabilizer v w) :
    placePointStabilizer v w₀ ⟨w, h⟩ =
      completionPlaceReturn v w₀ w * h.1 :=
  rfl

end

end Submission.CField.NIndex
