import Towers.ClassField.CohomologyOps.ShapiroCup
import Towers.ClassField.CohomologyOps.Corestriction

namespace Towers.CField.COps.CPFuncto

open CategoryTheory Rep
open Towers.CField.COps.CPBuild
open Towers.CField.COps
open scoped MonoidalCategory TensorProduct

variable {G : Type} [Group G]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

noncomputable section

theorem coind_tensor_hom (H : Subgroup G) (A : Rep ℤ H)
    (N : Rep ℤ G) (q : coind H.subtype A) (n : N) (g : G) :
    ((coindTensorHom H A N)
      (tensorElement (coind H.subtype A) N q n) :
        coind H.subtype (A ⊗ Rep.res H.subtype N : Rep ℤ H)).1 g =
      tensorElement A (Rep.res H.subtype N) (q.1 g) (N.ρ g n) := by
  rw [coindTensorHom, Rep.resCoindToHom_hom_apply_coe]
  change
    tensorElement A (Rep.res H.subtype N)
        (((resCoindAdjunction ℤ H.subtype).counit.app A)
          ((coind H.subtype A).ρ g q))
        (N.ρ g n) = _
  have hc : ((resCoindAdjunction ℤ H.subtype).counit.app A)
      ((coind H.subtype A).ρ g q) = q.1 g := by
    change (((coind H.subtype A).ρ g q) : coind H.subtype A).1 1 = q.1 g
    simp [Representation.coind]
  rw [hc]

set_option maxHeartbeats 2000000 in
-- Tensor elaboration across restriction is expensive.
theorem coind_tensor_comp
    (H : Subgroup G) [H.FiniteIndex] (M N : Rep ℤ G) :
    coindTensorHom H (Rep.res H.subtype M) N ≫
        corestrictionTrace (M ⊗ N : Rep ℤ G) H =
      corestrictionTrace M H ⊗ₘ 𝟙 N := by
  classical
  letI := (coind H.subtype (Rep.res H.subtype M) ⊗ N : Rep ℤ G).hV2
  letI := (M ⊗ N : Rep ℤ G).hV2
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw =>
      simpa only [map_add] using congrArg₂ (fun a b => a + b) hz hw
  | tmul q n =>
      change (corestrictionTrace (M ⊗ N : Rep ℤ G) H)
          (coindTensorHom H (Rep.res H.subtype M) N
            (tensorElement (coind H.subtype (Rep.res H.subtype M)) N q n)) =
        tensorElement M N (corestrictionTrace M H q) n
      rw [corestrictionTrace_apply, corestrictionTrace_apply]
      rw [tensor_sum_left]
      apply Fintype.sum_congr
      intro c
      rw [coind_tensor_hom]
      change (M ⊗ N : Rep ℤ G).ρ (Quotient.out c)⁻¹
          (tensorElement M N (q.1 (Quotient.out c))
            (N.ρ (Quotient.out c) n)) = _
      rw [tensorElement_action]
      rw [rep_action_mul]
      simp

set_option maxHeartbeats 2000000 in
-- The projection formula for the finite-index corestriction.
theorem cup_corestriction_projection
    (H : Subgroup G) [H.FiniteIndex] (M N : Rep ℤ G) (r s : ℕ)
    (x : groupCohomology (Rep.res H.subtype M) r)
    (y : groupCohomology N s) :
    corestriction (M ⊗ N : Rep ℤ G) H (r + s)
        (cupCohomology (Rep.res H.subtype M) (Rep.res H.subtype N)
          r s x (restriction N H s y)) =
      cupCohomology M N r s (corestriction M H r x) y := by
  let A := Rep.res H.subtype M
  let u := (groupCohomology.coindIso A r).inv x
  let θ := coindTensorHom H A N
  let z := cupCohomology (coind H.subtype A) N r s u y
  let eT := groupCohomology.coindIso
    (A ⊗ Rep.res H.subtype N : Rep ℤ H) (r + s)
  have hshapiro := coind_iso_cup H A N r s x y
  have hinv :
      eT.inv
          (cupCohomology A (Rep.res H.subtype N) r s x
            (restriction N H s y)) =
        groupCohomology.map (MonoidHom.id G) θ (r + s) z := by
    apply (ModuleCat.mono_iff_injective eT.hom).1 inferInstance
    rw [Iso.inv_hom_id_apply]
    exact hshapiro.symm
  dsimp only [corestriction]
  change
    groupCohomology.map (MonoidHom.id G)
        (corestrictionTrace (M ⊗ N : Rep ℤ G) H) (r + s)
        (eT.inv (cupCohomology A (Rep.res H.subtype N) r s x
          (restriction N H s y))) =
      cupCohomology M N r s
        (groupCohomology.map (MonoidHom.id G)
          (corestrictionTrace M H) r
          ((groupCohomology.coindIso A r).inv x)) y
  rw [hinv]
  have hcomp := groupCohomology.map_id_comp θ
    (corestrictionTrace (M ⊗ N : Rep ℤ G) H) (r + s)
  have hcomp_z := congrArg (fun f => f z) hcomp
  simp only [ConcreteCategory.comp_apply] at hcomp_z
  rw [← hcomp_z]
  have htrace : θ ≫ corestrictionTrace (M ⊗ N : Rep ℤ G) H =
      corestrictionTrace M H ⊗ₘ 𝟙 N := by
    dsimp only [θ, A]
    exact coind_tensor_comp H M N
  let traceComp :
      (coind H.subtype A ⊗ N : Rep ℤ G) ⟶ (M ⊗ N : Rep ℤ G) :=
    θ ≫ corestrictionTrace (M ⊗ N : Rep ℤ G) H
  let traceTensor :
      (coind H.subtype A ⊗ N : Rep ℤ G) ⟶ (M ⊗ N : Rep ℤ G) :=
    corestrictionTrace M H ⊗ₘ 𝟙 N
  have htrace' : traceComp = traceTensor := htrace
  let F := groupCohomology.functor ℤ G (r + s)
  have htraceMap := congrArg
    (fun q : (coind H.subtype A ⊗ N : Rep ℤ G) ⟶
        (M ⊗ N : Rep ℤ G) =>
      F.map q) htrace'
  have htraceZ := congrArg (fun f => f z) htraceMap
  have hnat := cupCohomology_natural
    (corestrictionTrace M H) (𝟙 N) r s u y
  have hnat' :
      groupCohomology.map (MonoidHom.id G)
          (corestrictionTrace M H ⊗ₘ 𝟙 N) (r + s) z =
        cupCohomology M N r s
          (groupCohomology.map (MonoidHom.id G)
            (corestrictionTrace M H) r u) y := by
    dsimp only [z]
    simpa using hnat
  exact htraceZ.trans hnat'

end

end Towers.CField.COps.CPFuncto
