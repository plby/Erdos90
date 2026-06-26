import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro

/-!
# Restriction on the bar resolution

This file constructs the chain map from the bar resolution of a subgroup to the restriction of
the ambient group's bar resolution.  It proves compatibility with both the differential and the
augmentation, and hence identifies this explicit map up to homotopy with the comparison map chosen
by `ProjectiveResolution.lift`.
-/

namespace Towers.CField.COps

open CategoryTheory Rep
open Finsupp

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G]

def barRestrictionF (H : Subgroup G) (n : ℕ) :
    Rep.free k H (Fin n → H) ⟶
      Rep.res H.subtype (Rep.free k G (Fin n → G)) :=
  Rep.freeLift k H _ fun x =>
    Finsupp.single (fun i => (x i : G)) (Finsupp.single 1 1)

lemma bar_f_hom (H : Subgroup G) (n : ℕ) :
    (barRestrictionF (k := k) H n).hom =
      Representation.freeLift
        (Rep.res H.subtype (Rep.free k G (Fin n → G))).ρ
        (fun x : Fin n → H =>
          Finsupp.single (fun i => (x i : G)) (Finsupp.single 1 1)) := rfl

set_option linter.flexible false in
set_option maxHeartbeats 1000000 in
-- Unfolding the mapped bar differential is expensive.
lemma bar_f_comm (H : Subgroup G) (n : ℕ) :
    barRestrictionF (k := k) H (n + 1) ≫
        (((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (barComplex k G)).d (n + 1) n =
      (barComplex k H).d (n + 1) n ≫ barRestrictionF (k := k) H n := by
  simp only [Functor.mapHomologicalComplex_obj_d]
  apply Rep.free_ext
  intro x
  change (((Rep.resFunctor H.subtype).map ((barComplex k G).d (n + 1) n)).hom.toLinearMap
      ((barRestrictionF (k := k) H (n + 1)).hom.toLinearMap
        (single x (single 1 1))) =
    (barRestrictionF (k := k) H n).hom.toLinearMap
      (((barComplex k H).d (n + 1) n).hom.toLinearMap (single x (single 1 1))))
  rw [Rep.res_map_hom_toLinearMap]
  rw [barComplex.d_def, barComplex.d_def]
  simp only [Representation.IntertwiningMap.toLinearMap_apply]
  rw [show (barRestrictionF (k := k) H (n + 1)).hom
      (single x (single 1 1)) =
        single (fun i => (x i : G)) (single 1 1) by
      have h := Representation.freeLift_single_single
        (σ := (Rep.res H.subtype
          (Rep.free k G (Fin (n + 1) → G))).ρ)
        x 1 1 (fun x : Fin (n + 1) → H =>
          single (fun i => (x i : G)) (single 1 1))
      simpa only [barRestrictionF, one_smul, map_one,
        Module.End.one_apply] using h]
  calc
    _ = single (fun i => (x i.succ : G)) (single (x 0 : G) 1) +
        Finset.univ.sum fun j : Fin (n + 1) =>
          single (Fin.contractNth j (· * ·) (fun i => (x i : G)))
            (single 1 ((-1 : k) ^ ((j : ℕ) + 1))) :=
      barComplex.d_single (k := k) (G := G) n (fun i => (x i : G))
    _ = (barRestrictionF (k := k) H n).hom
        (single (fun i => x i.succ) (single (x 0) 1) +
          Finset.univ.sum fun j : Fin (n + 1) =>
            single (Fin.contractNth j (· * ·) x)
              (single 1 ((-1 : k) ^ ((j : ℕ) + 1)))) := by
      simp [barRestrictionF, map_add, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      congr 2
      funext i
      simp [Fin.contractNth]
      split_ifs <;> rfl
    _ = _ := congrArg (barRestrictionF (k := k) H n).hom
      (barComplex.d_single (k := k) (G := H) n x).symm

def barRestrictionMap (H : Subgroup G) :
    barComplex k H ⟶
      ((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (barComplex k G) where
  f n := barRestrictionF H n
  comm' i j hij := by
    subst i
    exact bar_f_comm H j

set_option maxHeartbeats 1000000 in
-- Type-changing representation isomorphisms make this calculation expensive.
lemma diagonal_inv_single (n : ℕ) (x : Fin n → G) (g : G) (r : k) :
    (Rep.diagonalSuccIsoFree k G n).inv.hom
        (single x (single g r)) =
      single (g • Fin.partialProd x) r := by
  change (Rep.diagonalSuccIsoTensorTrivial k G n).inv.hom
      ((Rep.leftRegularTensorTrivialIsoFree k G (Fin n → G)).inv.hom
        (single x (single g r))) = _
  rw [show (Rep.leftRegularTensorTrivialIsoFree k G (Fin n → G)).inv.hom
      (single x (single g r)) = single g 1 ⊗ₜ[k] single x r by
    change (Representation.leftRegularTensorTrivialIsoFree (Fin n → G)).symm
      (single x (single g r)) = _
    exact Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single x g r]
  change (Rep.linearizationOfMulActionIso k G (Fin (n + 1) → G)).inv.hom
    ((Rep.ofHom (Representation.linearizeMap
      (Action.diagonalSuccIsoTensorTrivial G n).inv)).hom
      ((Functor.LaxMonoidal.μ (Rep.linearization k G)
        (Action.leftRegular G) (Action.trivial G (Fin n → G))).hom
        (((Rep.linearizationOfMulActionIso k G G).inv.hom.tensor
          (Rep.linearizationTrivialIso k G (Fin n → G)).inv.hom)
            (single g 1 ⊗ₜ[k] single x r)))) = _
  rw [Representation.IntertwiningMap.tensor_apply]
  rw [show (Rep.linearizationOfMulActionIso k G G).inv.hom (single g 1) =
      single g 1 by
    change (Representation.linearizeOfMulActionIso k G G).symm (single g 1) = _
    exact Representation.linearizeOfMulActionIso_symm_apply (single g 1)]
  rw [show (Rep.linearizationTrivialIso k G (Fin n → G)).inv.hom (single x r) =
      single x r by
    change (Representation.linearizeTrivialIso k G (Fin n → G)).symm
      (single x r) = _
    exact Representation.linearizeTrivialIso_symm_apply (single x r)]
  rw [Rep.μ_hom]
  have hμ := @Representation.LinearizeMonoidal.μ_apply_single_single
    G _ (Action.leftRegular G) (Action.trivial G (Fin n → G))
    k _ g x 1 r
  calc
    _ = (Rep.linearizationOfMulActionIso k G (Fin (n + 1) → G)).inv.hom
        ((Rep.ofHom (Representation.linearizeMap
          (Action.diagonalSuccIsoTensorTrivial G n).inv)).hom
            (single (g, x) (1 * r))) := congrArg
      (fun z => (Rep.linearizationOfMulActionIso k G (Fin (n + 1) → G)).inv.hom
        ((Rep.ofHom (Representation.linearizeMap
          (Action.diagonalSuccIsoTensorTrivial G n).inv)).hom z)) hμ
    _ = (Rep.linearizationOfMulActionIso k G (Fin (n + 1) → G)).inv.hom
        (single (g • Fin.partialProd x) r) := by
      congr 1
      change Representation.linearizeMap
        (Action.diagonalSuccIsoTensorTrivial G n).inv
          (single (g, x) (1 * r)) = _
      rw [Representation.linearizeMap_single,
        Action.diagonalSuccIsoTensorTrivial_inv_hom_apply]
      simp
    _ = _ := by
      change (Representation.linearizeOfMulActionIso k G
        (Fin (n + 1) → G)).symm (single (g • Fin.partialProd x) r) = _
      exact Representation.linearizeOfMulActionIso_symm_apply _

lemma bar_resolution_f (x : Fin 0 → G) (g : G) (r : k) :
    (barResolution k G).π.f 0
        (single x (single g r)) = r := by
  change (standardComplex.ε k G).hom
    ((Rep.diagonalSuccIsoFree k G 0).inv.hom
      (single x (single g r))) = r
  rw [diagonal_inv_single]
  simp [standardComplex.ε]

set_option maxHeartbeats 1000000 in
-- Unfolding the type-changing restriction functor in degree zero is expensive.
lemma bar_restriction_zero (H : Subgroup G) :
    (barRestrictionMap (k := k) H).f 0 ≫
        (((Rep.resFunctor H.subtype).mapProjectiveResolution
          (barResolution k G)).π.f 0) =
      (barResolution k H).π.f 0 := by
  apply Rep.free_ext
  intro x
  have hx : x = default := Subsingleton.elim _ _
  subst x
  change (((Rep.resFunctor H.subtype).map ((barResolution k G).π.f 0)).hom
      ((barRestrictionF (k := k) H 0).hom
        (single default (single 1 1)))) =
    (barResolution k H).π.f 0 (single default (single 1 1))
  rw [show (barRestrictionF (k := k) H 0).hom
      (single default (single 1 1)) =
        single default (single 1 1) by
    rw [bar_f_hom]
    rw [Representation.freeLift_single_single]
    simp only [one_smul, map_one, Module.End.one_apply]
    congr
    exact Subsingleton.elim _ _]
  change (barResolution k G).π.f 0 (single default (single 1 1)) = _
  rw [bar_resolution_f, bar_resolution_f]

lemma bar_restriction_pi (H : Subgroup G) :
    barRestrictionMap (k := k) H ≫
        ((Rep.resFunctor H.subtype).mapProjectiveResolution
          (barResolution k G)).π =
      (barResolution k H).π := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero => exact bar_restriction_zero H
  | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.down ℕ) 0 (Rep.trivial k H k) (n + 1)
        (by simp)).eq_of_tgt _ _

noncomputable def bar_homotopy_lift (H : Subgroup G) :
    Homotopy (barRestrictionMap (k := k) H)
      (ProjectiveResolution.lift (𝟙 _)
        (barResolution k H)
        ((Rep.resFunctor H.subtype).mapProjectiveResolution
          (barResolution k G))) :=
  ProjectiveResolution.liftHomotopy (𝟙 _)
    (barRestrictionMap (k := k) H)
    (ProjectiveResolution.lift (𝟙 _)
      (barResolution k H)
      ((Rep.resFunctor H.subtype).mapProjectiveResolution
        (barResolution k G)))
    (by simpa using bar_restriction_pi (k := k) H)
    (ProjectiveResolution.lift_commutes (𝟙 _)
      (barResolution k H)
      ((Rep.resFunctor H.subtype).mapProjectiveResolution
        (barResolution k G)))

end

end Towers.CField.COps
