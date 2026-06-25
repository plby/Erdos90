import Submission.ClassField.NormIndex.PrincipalIdelesSmul
import Submission.ClassField.KummerNormIndex.FiniteExtensionTower

/-!
# Transitivity of the canonical idèle-class extension map

The coordinatewise inclusion `C_K → C_L` is functorial in a tower.  The
finite-coordinate input was established in Section 4; here it is assembled
on finite idèles, infinite idèles, full idèles, and finally idèle classes.
-/

namespace Submission.CField.KNIndex

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.NIndex

noncomputable section

universe u

private abbrev OK (F : Type u) [Field F] [NumberField F] :=
  NumberField.RingOfIntegers F

private theorem infinite_comap_tower
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    (w : InfinitePlace L) :
    (w.comap (algebraMap E L)).comap (algebraMap K E) =
      w.comap (algebraMap K L) := by
  rw [← InfinitePlace.comap_comp]
  congr 1
  exact (IsScalarTower.algebraMap_eq K E L).symm

private theorem infinite_place_dependent
    {K : Type u} [Field K] [NumberField K]
    {v v' : InfinitePlace K} (h : v = v')
    (x : (z : InfinitePlace K) → z.1.Completion) :
    RingEquiv.cast (R := fun z : InfinitePlace K ↦ z.1.Completion) h
        (x v) = x v' := by
  subst v'
  rfl

private theorem lies_trans_base
    {K E L : Type u} [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    (v₀ v : AbsoluteValue K ℝ) (u : AbsoluteValue E ℝ)
    (w : AbsoluteValue L ℝ) (h : v₀ = v)
    (hu₀ : AbsoluteValue.LiesOver u v₀)
    (hwu : AbsoluteValue.LiesOver w u)
    (hw₀ : AbsoluteValue.LiesOver w v₀)
    (hwv : AbsoluteValue.LiesOver w v)
    (z : v₀.Completion) :
    completionLies u w hwu
        (completionLies v₀ u hu₀ z) =
      completionLies v w hwv (RingEquiv.cast h z) := by
  subst v
  simpa using RingHom.congr_fun
    (completion_lies_trans v₀ u w hu₀ hwu hw₀) z

set_option maxHeartbeats 3000000 in
-- Comparing the two infinite-coordinate extension maps requires normalizing
-- dependent completion casts through the whole field tower.
set_option maxRecDepth 100000 in
/-- Transitivity of coordinatewise extension on infinite idèles. -/
theorem infinite_monoid_trans
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    [IsGalois K E] [IsGalois E L] [IsGalois K L] :
    (infiniteMonoidHom (K := E) (L := L)).comp
        (infiniteMonoidHom (K := K) (L := E)) =
      infiniteMonoidHom (K := K) (L := L) := by
  apply MonoidHom.ext
  intro x
  apply Units.ext
  funext w
  let u := w.comap (algebraMap E L)
  let v₀ := u.comap (algebraMap K E)
  let v := w.comap (algebraMap K L)
  let hv : v₀ = v := infinite_comap_tower w
  let hu₀ := infinite_lies_comap v₀ u rfl
  let hwu := infinite_lies_comap u w rfl
  let hw₀ := infinite_lies_comap v₀ w hv.symm
  let hwv := infinite_lies_comap v w rfl
  have hcast : RingEquiv.cast hv
      ((MulEquiv.piUnits x v₀ : _) : v₀.1.Completion) =
      ((MulEquiv.piUnits x v : _) : v.1.Completion) :=
    infinite_place_dependent hv
      (fun z ↦ ((MulEquiv.piUnits x z : _) : z.1.Completion))
  change completionLies u.1 w.1 hwu
      (completionLies v₀.1 u.1 hu₀
        ((MulEquiv.piUnits x v₀ : _) : v₀.1.Completion)) =
    completionLies v.1 w.1 hwv
      ((MulEquiv.piUnits x v : _) : v.1.Completion)
  rw [← hcast]
  exact lies_trans_base
    v₀.1 v.1 u.1 w.1 (congrArg Subtype.val hv) hu₀ hwu hw₀ hwv
      ((MulEquiv.piUnits x v₀ : _) : v₀.1.Completion)

set_option maxHeartbeats 3000000 in
-- The full-idèle transitivity proof combines the dependent infinite part
-- with restricted-product coordinate extension.
set_option maxRecDepth 100000 in
/-- Transitivity of the canonical extension on full idèles. -/
theorem idele_monoid_trans
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    [IsGalois K E] [IsGalois E L] [IsGalois K L] :
    (ideleExtensionMonoid (K := E) (L := L)).comp
        (ideleExtensionMonoid (K := K) (L := E)) =
      ideleExtensionMonoid (K := K) (L := L) := by
  apply MonoidHom.ext
  intro x
  apply Prod.ext
  · exact DFunLike.congr_fun
      (infinite_monoid_trans (K := K) (E := E) (L := L)) x.1
  · exact DFunLike.congr_fun
      (extension_monoid_trans (K := K) (E := E) (L := L)) x.2

set_option synthInstance.maxHeartbeats 500000 in
-- Quotient maps retain the large dependent restricted-product expressions.
set_option maxHeartbeats 3000000 in
/-- Transitivity after passing to idèle classes. -/
theorem canonical_extension_trans
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    [IsGalois K E] [IsGalois E L] [IsGalois K L] :
    let DKE := canonicalExtensionData (K := K) (L := E)
    let DEL := canonicalExtensionData (K := E) (L := L)
    let DKL := canonicalExtensionData (K := K) (L := L)
    DEL.classMap.comp DKE.classMap = DKL.classMap := by
  let DKE := canonicalExtensionData (K := K) (L := E)
  let DEL := canonicalExtensionData (K := E) (L := L)
  let DKL := canonicalExtensionData (K := K) (L := L)
  apply MonoidHom.ext
  intro c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (principalIdeles (OK K) K) c
  change DEL.classMap (DKE.classMap
      (QuotientGroup.mk' (principalIdeles (OK K) K) x)) =
    DKL.classMap (QuotientGroup.mk' (principalIdeles (OK K) K) x)
  rw [DKE.classMap_mk, DEL.classMap_mk, DKL.classMap_mk]
  exact congrArg (QuotientGroup.mk' (principalIdeles (OK L) L))
    (DFunLike.congr_fun
      (idele_monoid_trans (K := K) (E := E) (L := L)) x)

end

end Submission.CField.KNIndex
