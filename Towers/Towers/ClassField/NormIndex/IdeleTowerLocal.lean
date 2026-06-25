import Mathlib.RingTheory.Norm.Transitivity
import Towers.ClassField.NormIndex.IdeleTowerPlaces

/-!
# Local norm transitivity in completion towers

This file proves the archimedean local identity needed for transitivity of
the concrete idèle norm.  The key point is that the completion maps in a
tower compose, so `Algebra.norm_norm` applies to the three completed fields.
-/

namespace Towers.CField.NIndex

open NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles

noncomputable section

universe u

set_option maxHeartbeats 2000000 in
-- The three completion algebras and their finite-module structures are
-- definitionally large and need extra normalization time.
set_option maxRecDepth 100000 in
/-- Transitivity of the field norm along a tower of archimedean
completions. -/
theorem infinite_completion_trans
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    (v : InfinitePlace K)
    (u : InfinitePlacesAbove (K := K) (L := E) v)
    (w : InfinitePlacesAbove (K := E) (L := L) u.1)
    (z : w.1.Completionˣ) :
    let wKL : InfinitePlacesAbove (K := K) (L := L) v :=
      (infiniteAboveTower K E L v).symm ⟨u, w⟩
    infiniteCompletionNorm (K := K) (L := L) v wKL z =
      infiniteCompletionNorm (K := K) (L := E) v u
        (infiniteCompletionNorm (K := E) (L := L) u.1 w z) := by
  let wKL : InfinitePlacesAbove (K := K) (L := L) v :=
    (infiniteAboveTower K E L v).symm ⟨u, w⟩
  letI : Algebra v.1.Completion u.1.1.Completion :=
    (completionLies v.1 u.1.1
      (infinite_lies_comap v u.1 u.2)).toAlgebra
  letI : Algebra u.1.1.Completion w.1.1.Completion :=
    (completionLies u.1.1 w.1.1
      (infinite_lies_comap u.1 w.1 w.2)).toAlgebra
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1
      (infinite_lies_comap v wKL.1 wKL.2)).toAlgebra
  letI : IsScalarTower v.1.Completion u.1.1.Completion
      w.1.1.Completion := by
    apply IsScalarTower.of_algebraMap_eq'
    simpa only [wKL, infiniteAboveTower] using
      (completion_lies_trans v.1 u.1.1 w.1.1
        (infinite_lies_comap v u.1 u.2)
        (infinite_lies_comap u.1 w.1 w.2)
        (infinite_lies_comap v wKL.1 wKL.2)).symm
  letI : Module.Finite v.1.Completion u.1.1.Completion :=
    infinite_completion_module (K := K) (L := E) v u
  letI : Module.Finite u.1.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := E) (L := L) u.1 w
  apply Units.ext
  change Algebra.norm v.1.Completion (z : w.1.Completion) =
    Algebra.norm v.1.Completion
      (Algebra.norm u.1.1.Completion (z : w.1.Completion))
  exact (Algebra.norm_norm (R := v.1.Completion)
    (S := u.1.1.Completion) (A := w.1.1.Completion)).symm

set_option maxHeartbeats 2000000 in
-- Reindexing both dependent products exposes the local completion theorem.
set_option maxRecDepth 100000 in
/-- Transitivity of the archimedean component of the concrete idèle norm. -/
theorem infinite_idele_trans
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L] :
    infiniteIdeleNorm (K := K) (L := L) =
      (infiniteIdeleNorm (K := K) (L := E)).comp
        (infiniteIdeleNorm (K := E) (L := L)) := by
  apply MonoidHom.ext
  intro x
  apply MulEquiv.piUnits.injective
  funext v
  letI : Fintype (InfinitePlacesAbove (K := K) (L := L) v) :=
    infiniteCor84ExtensionsFintype v
  letI : Fintype (InfinitePlacesAbove (K := K) (L := E) v) :=
    infiniteCor84ExtensionsFintype v
  letI (u : InfinitePlacesAbove (K := K) (L := E) v) :
      Fintype (InfinitePlacesAbove (K := E) (L := L) u.1) :=
    infiniteCor84ExtensionsFintype u.1
  change infiniteNorm (K := K) (L := L) v x =
    infiniteNorm (K := K) (L := E) v
      (infiniteIdeleNorm (K := E) (L := L) x)
  rw [infinite_norm, infinite_norm]
  let e := infiniteAboveTower K E L v
  calc
    (∏ w : InfinitePlacesAbove (K := K) (L := L) v,
        infiniteCompletionNorm (K := K) (L := L) v w
          (MulEquiv.piUnits x w.1)) =
        ∏ uw : Σ u : InfinitePlacesAbove (K := K) (L := E) v,
            InfinitePlacesAbove (K := E) (L := L) u.1,
          infiniteCompletionNorm (K := K) (L := L) v (e.symm uw)
            (MulEquiv.piUnits x uw.2.1) := by
      exact (e.symm.prod_comp (fun w ↦
        infiniteCompletionNorm (K := K) (L := L) v w
          (MulEquiv.piUnits x w.1))).symm
    _ = ∏ u : InfinitePlacesAbove (K := K) (L := E) v,
        ∏ w : InfinitePlacesAbove (K := E) (L := L) u.1,
          infiniteCompletionNorm (K := K) (L := L) v (e.symm ⟨u, w⟩)
            (MulEquiv.piUnits x w.1) := Fintype.prod_sigma _
    _ = ∏ u : InfinitePlacesAbove (K := K) (L := E) v,
        ∏ w : InfinitePlacesAbove (K := E) (L := L) u.1,
          infiniteCompletionNorm (K := K) (L := E) v u
            (infiniteCompletionNorm (K := E) (L := L) u.1 w
              (MulEquiv.piUnits x w.1)) := by
      apply Finset.prod_congr rfl
      intro u _
      apply Finset.prod_congr rfl
      intro w _
      exact infinite_completion_trans v u w (MulEquiv.piUnits x w.1)
    _ = ∏ u : InfinitePlacesAbove (K := K) (L := E) v,
        infiniteCompletionNorm (K := K) (L := E) v u
          (∏ w : InfinitePlacesAbove (K := E) (L := L) u.1,
            infiniteCompletionNorm (K := E) (L := L) u.1 w
              (MulEquiv.piUnits x w.1)) := by
      apply Finset.prod_congr rfl
      intro u _
      rw [map_prod]
    _ = ∏ u : InfinitePlacesAbove (K := K) (L := E) v,
        infiniteCompletionNorm (K := K) (L := E) v u
          (MulEquiv.piUnits (infiniteIdeleNorm (K := E) (L := L) x) u.1) := by
      apply Finset.prod_congr rfl
      intro u _
      rw [infinite_idele, infinite_norm]

end

end Towers.CField.NIndex
