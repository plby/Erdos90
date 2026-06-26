import Towers.ClassField.BrauerLocalization.AbsoluteKernelLifting
import Towers.ClassField.BrauerLocalization.H2Comparison
import Towers.ClassField.ReciprocityExistence.PlaceCompletion

/-!
# Coordinatewise lifting to local relative Brauer groups

For a chosen finite Galois extension and one completion above every base
place, the local relative Brauer group is the kernel of scalar extension to
the chosen upper completion.  This file specializes the generic direct-sum
subgroup lift to those actual kernels.
-/

namespace Towers.CField.BLoc

open NumberField
open Towers.CField.BGroups
open Towers.CField.Ideles
open Towers.CField.RExist
open Towers.CField.HNorm

noncomputable section

universe u

variable (K L : Type u) [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The chosen local relative Brauer group, viewed additively as a subgroup
of the absolute local Brauer group used in Theorem VIII.4.2. -/
noncomputable def relativeBrauerSubgroup
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :
    AddSubgroup (Additive (BrauerGroup (Towers.CField.RExist.placeCompletion K v))) := by
  cases v with
  | inl P =>
      exact (localRelativeBrauer K L completion (.inl P)).toAddSubgroup
  | inr v =>
      exact (localRelativeBrauer K L completion (.inr v)).toAddSubgroup

/-- Scalar extension from the completion model in Theorem VIII.4.2 to the
chosen upper completion.  Splitting on the place aligns the two
definitionally equal base-completion presentations for instance synthesis. -/
noncomputable def brauerLiftingChange
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :
    BrauerGroup (Towers.CField.RExist.placeCompletion K v) →*
      BrauerGroup (chosenCompletionExtension K L completion v) := by
  cases v with
  | inl P =>
      exact @brauerBaseChange
        (Towers.CField.RExist.placeCompletion K (.inl P))
        (chosenCompletionExtension K L completion (.inl P))
        inferInstance inferInstance
        (chosenCompletionAlgebra K L completion (.inl P))
  | inr v =>
      exact @brauerBaseChange
        (Towers.CField.RExist.placeCompletion K (.inr v))
        (chosenCompletionExtension K L completion (.inr v))
        inferInstance inferInstance
        (chosenCompletionAlgebra K L completion (.inr v))

/-- Inclusion of a chosen local relative Brauer group into the absolute
Brauer group of the base completion, in the completion presentation used by
Theorem VIII.4.2. -/
noncomputable def localBrauerInclusion
    (completion : HasseCompletionData K L)
    (v : NumberFieldPlace K) :
    Additive (localRelativeBrauer K L completion v) →+
      Additive (BrauerGroup (Towers.CField.RExist.placeCompletion K v)) := by
  cases v with
  | inl P =>
      exact MonoidHom.toAdditive
        (localRelativeBrauer K L completion (.inl P)).subtype
  | inr v =>
      exact MonoidHom.toAdditive
        (localRelativeBrauer K L completion (.inr v)).subtype

set_option synthInstance.maxHeartbeats 300000 in
-- The dependent relative-Brauer family unfolds the chosen completion algebra.
/-- Coordinatewise inclusion of the selected local relative Brauer groups
into the absolute local Brauer direct sum. -/
noncomputable def brauerDirectInclusion
    (completion : HasseCompletionData K L) :
    DirectSum (NumberFieldPlace K)
        (fun v ↦ Additive (localRelativeBrauer K L completion v)) →+
      DirectSum (NumberFieldPlace K)
        (fun v ↦ Additive (BrauerGroup (Towers.CField.RExist.placeCompletion K v))) :=
  DirectSum.map (localBrauerInclusion K L completion)

/-- A local family lying in every selected relative Brauer kernel lifts to
the direct sum of those kernels. -/
theorem brauer_direct_lift
    (completion : HasseCompletionData K L)
    (x : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup (Towers.CField.RExist.placeCompletion K v))))
    (hx : ∀ v, x v ∈
      relativeBrauerSubgroup K L completion v) :
    ∃ y : DirectSum (NumberFieldPlace K)
        (fun v ↦ relativeBrauerSubgroup K L completion v),
      DirectSum.map (fun v ↦
        (relativeBrauerSubgroup K L completion v).subtype) y =
          x :=
  direct_subtype_lift
    (relativeBrauerSubgroup K L completion) x hx

/-- The membership hypothesis above is exactly local triviality after scalar
extension to each chosen upper completion. -/
theorem brauer_direct_change
    (completion : HasseCompletionData K L)
    (x : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup (Towers.CField.RExist.placeCompletion K v))))
    (hx : ∀ v,
      brauerLiftingChange K L completion v (x v).toMul = 1) :
    ∃ y : DirectSum (NumberFieldPlace K)
        (fun v ↦ relativeBrauerSubgroup K L completion v),
      DirectSum.map (fun v ↦
        (relativeBrauerSubgroup K L completion v).subtype) y =
          x := by
  apply brauer_direct_lift K L completion x
  intro v
  cases v with
  | inl P => exact hx (.inl P)
  | inr v => exact hx (.inr v)

set_option maxHeartbeats 4000000 in
-- The direct-sum extensionality proof unfolds both place branches.
set_option synthInstance.maxHeartbeats 300000 in
-- Elaborating both dependent direct sums requires the chosen-completion instances.
/-- The preceding lift, with its domain written exactly as the local-relative
Brauer direct sum used by the cohomological localization map. -/
theorem direct_base_change
    (completion : HasseCompletionData K L)
    (x : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (BrauerGroup (Towers.CField.RExist.placeCompletion K v))))
    (hx : ∀ v,
      brauerLiftingChange K L completion v (x v).toMul = 1) :
    ∃ y : DirectSum (NumberFieldPlace K)
        (fun v ↦ Additive (localRelativeBrauer K L completion v)),
      brauerDirectInclusion K L completion y = x := by
  classical
  let liftCoordinate : ∀ v, Additive
      (localRelativeBrauer K L completion v) := fun v => by
    cases v with
    | inl P => exact Additive.ofMul ⟨(x (.inl P)).toMul, hx (.inl P)⟩
    | inr v => exact Additive.ofMul ⟨(x (.inr v)).toMul, hx (.inr v)⟩
  let y : DirectSum (NumberFieldPlace K)
      (fun v ↦ Additive (localRelativeBrauer K L completion v)) :=
    DFinsupp.mk x.support fun v => liftCoordinate v.1
  refine ⟨y, ?_⟩
  ext v
  cases v with
  | inl P =>
      by_cases hP : (.inl P : NumberFieldPlace K) ∈ x.support
      · simp only [brauerDirectInclusion,
          SetLike.coe_sort_coe, DirectSum.map_apply,
          localBrauerInclusion, DFinsupp.mk_apply, hP,
          ↓reduceDIte, MonoidHom.toAdditive_apply_apply, toMul_ofMul, y]
        change (liftCoordinate (.inl P)).toMul.1 = (x (.inl P)).toMul
        rfl
      · have hxP : x (.inl P) = 0 := by
          simpa only [DFinsupp.mem_support_toFun, not_ne_iff] using hP
        simp [brauerDirectInclusion,
          localBrauerInclusion, y, DFinsupp.mk_apply, hP, hxP]
  | inr v =>
      by_cases hv : (.inr v : NumberFieldPlace K) ∈ x.support
      · simp only [brauerDirectInclusion,
          SetLike.coe_sort_coe, DirectSum.map_apply,
          localBrauerInclusion, DFinsupp.mk_apply, hv,
          ↓reduceDIte, MonoidHom.toAdditive_apply_apply, toMul_ofMul, y]
        change (liftCoordinate (.inr v)).toMul.1 = (x (.inr v)).toMul
        rfl
      · have hxv : x (.inr v) = 0 := by
          simpa only [DFinsupp.mem_support_toFun, not_ne_iff] using hv
        simp [brauerDirectInclusion,
          localBrauerInclusion, y, DFinsupp.mk_apply, hv, hxv]

end

end Towers.CField.BLoc
