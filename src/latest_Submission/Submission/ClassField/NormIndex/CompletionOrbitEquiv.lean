import Submission.ClassField.IdeleCohomology.CompletionInducedModule

/-!
# Splitting the Galois group by a completion-place orbit

For a chosen completion place `w0` above `v`, a choice of an element carrying
each `w` back to `w0` identifies the Galois group with the sigma type of a
place above `v` and an element of the stabilizer of `w0`.

The orientation here is chosen for the norm calculation: if
`r w = completionPlaceReturn v w0 w`, then `r w • w = w0`, and the element
associated to `(w, h)` is `h * r w`.  Its inverse therefore sends `w0` to
`w`.
-/

namespace Submission.CField.NIndex

open AbsoluteValue
open Submission.NumberTheory.Milne
open Submission.CField.ICohomo

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The explicit forward map from a place and a stabilizer element to the
global Galois group. -/
noncomputable def completionStabilizerGalois
    (v : AbsoluteValue K ℝ)
    (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)] :
    (Σ _w : CompletionPlacesAbove (L := L) v,
      CompletionPlaceStabilizer v w0) → Gal(L/K) :=
  fun p ↦ p.2.1 * completionPlaceReturn v w0 p.1

/-- The inverse map.  The source place of `sigma` is `sigma⁻¹ • w0`; after
choosing `r` carrying that place to `w0`, the residual element
`sigma * r⁻¹` stabilizes `w0`. -/
noncomputable def galoisOrbitStabilizer
    (v : AbsoluteValue K ℝ)
    (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)] :
    Gal(L/K) →
      (Σ _w : CompletionPlacesAbove (L := L) v,
        CompletionPlaceStabilizer v w0) := by
  intro sigma
  let w : CompletionPlacesAbove (L := L) v := sigma⁻¹ • w0
  let r : Gal(L/K) := completionPlaceReturn v w0 w
  refine ⟨w, ⟨sigma * r⁻¹, ?_⟩⟩
  change (sigma * r⁻¹) • w0 = w0
  have hr : r⁻¹ • w0 = w := by
    calc
      r⁻¹ • w0 = r⁻¹ • (r • w) := by
        rw [place_return_smul v w0 w]
      _ = w := inv_smul_smul r w
  rw [mul_smul, hr]
  exact smul_inv_smul sigma w0

/-- The inverse of the forward element attached to `(w,h)` sends `w0` back
to `w`.  This is the source-coordinate identity needed when a product over
the Galois group is regrouped by completion places. -/
@[simp]
theorem stabilizer_galois_smul
    (v : AbsoluteValue K ℝ)
    (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)]
    (w : CompletionPlacesAbove (L := L) v)
    (h : CompletionPlaceStabilizer v w0) :
    (completionStabilizerGalois v w0 ⟨w, h⟩)⁻¹ • w0 = w := by
  let r : Gal(L/K) := completionPlaceReturn v w0 w
  change (h.1 * r)⁻¹ • w0 = w
  calc
    (h.1 * r)⁻¹ • w0 = r⁻¹ • (h.1⁻¹ • w0) := by
      rw [mul_inv_rev, mul_smul]
    _ = r⁻¹ • w0 :=
      congrArg (fun z ↦ r⁻¹ • z) (h⁻¹).2
    _ = r⁻¹ • (r • w) := by rw [place_return_smul v w0 w]
    _ = w := inv_smul_smul r w

@[simp]
theorem stabilizer_after_inverse
    (v : AbsoluteValue K ℝ)
    (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)]
    (sigma : Gal(L/K)) :
    completionStabilizerGalois v w0
        (galoisOrbitStabilizer v w0 sigma) = sigma := by
  dsimp [completionStabilizerGalois,
    galoisOrbitStabilizer]
  simp

@[simp]
theorem stabilizer_after_forward
    (v : AbsoluteValue K ℝ)
    (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)]
    (p : Σ _w : CompletionPlacesAbove (L := L) v,
      CompletionPlaceStabilizer v w0) :
    galoisOrbitStabilizer v w0
        (completionStabilizerGalois v w0 p) = p := by
  rcases p with ⟨w, h⟩
  have hw :
      (galoisOrbitStabilizer v w0
        (completionStabilizerGalois v w0 ⟨w, h⟩)).1 = w :=
    stabilizer_galois_smul v w0 w h
  have hh :
      (galoisOrbitStabilizer v w0
        (completionStabilizerGalois v w0 ⟨w, h⟩)).2 = h := by
    apply Subtype.ext
    change
      (h.1 * completionPlaceReturn v w0 w) *
          (completionPlaceReturn v w0
            ((h.1 * completionPlaceReturn v w0 w)⁻¹ • w0))⁻¹ = h.1
    have hsource :
        (h.1 * completionPlaceReturn v w0 w)⁻¹ • w0 = w :=
      stabilizer_galois_smul v w0 w h
    rw [hsource]
    simp
  exact Sigma.ext hw (heq_of_eq hh)

/-- The orbit/stabilizer decomposition with the representative orientation
used by the completion-product norm calculation. -/
noncomputable def completionPlaceStabilizer
    (v : AbsoluteValue K ℝ)
    (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)] :
    (Σ _w : CompletionPlacesAbove (L := L) v,
      CompletionPlaceStabilizer v w0) ≃ Gal(L/K) where
  toFun := completionStabilizerGalois v w0
  invFun := galoisOrbitStabilizer v w0
  left_inv := stabilizer_after_forward v w0
  right_inv := stabilizer_after_inverse v w0

@[simp]
theorem completion_place_stabilizer
    (v : AbsoluteValue K ℝ)
    (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)]
    (w : CompletionPlacesAbove (L := L) v)
    (h : CompletionPlaceStabilizer v w0) :
    completionPlaceStabilizer v w0 ⟨w, h⟩ =
      h.1 * completionPlaceReturn v w0 w :=
  rfl

/-- Source-place form stated directly for the equivalence. -/
@[simp]
theorem stabilizer_inv_smul
    (v : AbsoluteValue K ℝ)
    (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)]
    (w : CompletionPlacesAbove (L := L) v)
    (h : CompletionPlaceStabilizer v w0) :
    (completionPlaceStabilizer v w0 ⟨w, h⟩)⁻¹ • w0 = w :=
  stabilizer_galois_smul v w0 w h

@[simp]
theorem stabilizer_symm_fst
    (v : AbsoluteValue K ℝ)
    (w0 : CompletionPlacesAbove (L := L) v)
    [MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v)]
    (sigma : Gal(L/K)) :
    ((completionPlaceStabilizer v w0).symm sigma).1 = sigma⁻¹ • w0 :=
  rfl

end

end Submission.CField.NIndex
