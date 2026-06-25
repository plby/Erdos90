import Submission.ClassField.BrauerGroups.BaseChangeBrauer

/-!
# Transitivity of scalar extension on Brauer groups

Scalar extension through a tower `k → L → M` is canonically equivalent to
direct scalar extension from `k` to `M`.  Consequently the corresponding
Brauer-group homomorphisms compose.
-/

namespace Submission.CField.BGroups

noncomputable section

open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance high] Algebra.TensorProduct.leftAlgebra

private noncomputable def towerTensorCongr
    (k L A B : Type u) [Field k] [Field L] [Algebra k L]
    [Ring A] [Algebra k A] [Ring B] [Algebra k B]
    (e : A ≃ₐ[k] B) : A ⊗[k] L ≃ₐ[L] B ⊗[k] L :=
  { Algebra.TensorProduct.congr e AlgEquiv.refl with
    commutes' := by
      intro l
      rw [Algebra.TensorProduct.right_algebraMap_apply,
        Algebra.TensorProduct.right_algebraMap_apply]
      simp }

private noncomputable def towerTensorLid
    (L M : Type u) [Field L] [Field M] [Algebra L M] :
    L ⊗[L] M ≃ₐ[M] M :=
  { Algebra.TensorProduct.lid L M with
    commutes' := by
      intro m
      rw [Algebra.TensorProduct.right_algebraMap_apply]
      simp }

private noncomputable def towerTensorRid
    (L M : Type u) [Field L] [Field M] [Algebra L M] :
    M ⊗[L] L ≃ₐ[M] M :=
  (Algebra.TensorProduct.commRight L M L).trans (towerTensorLid L M)

private noncomputable def towerCancelChange
    (k L M A : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
    [Ring A] [Algebra k A] :
    (M ⊗[L] L) ⊗[k] A ≃ₐ[M] M ⊗[k] A :=
  { Algebra.TensorProduct.congr
      ((towerTensorRid L M).restrictScalars k) AlgEquiv.refl with
    commutes' := by
      intro m
      simp [towerTensorRid, towerTensorLid] }

/-- Extending an algebra first from `k` to `L` and then from `L` to `M` is
canonically equivalent to extending it directly from `k` to `M`. -/
noncomputable def scalarTowerAlg
    (k L M A : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
    [Ring A] [Algebra k A] :
    (A ⊗[k] L) ⊗[L] M ≃ₐ[M] A ⊗[k] M :=
  (towerTensorCongr L M (A ⊗[k] L) (L ⊗[k] A)
      (Algebra.TensorProduct.commRight k L A).symm).trans
    (Algebra.TensorProduct.commRight L M (L ⊗[k] A)).symm |>.trans
      (Algebra.TensorProduct.assoc k L M M L A).symm |>.trans
        (towerCancelChange k L M A) |>.trans
          (Algebra.TensorProduct.commRight k M A)

/-- Scalar extension applied to a represented Brauer class is represented by
the scalar extension of the algebra. -/
@[simp]
theorem brauer_change_class
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (A : CSA.{u, u} k) :
    brauerBaseChange k K (brauerClass k A) =
      brauerClass K (scalarExtensionCSA k K A) :=
  rfl

/-- Scalar extension on Brauer groups is transitive through a field tower. -/
theorem base_change_tower
    (k L M : Type u) [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
    (x : BrauerGroup.{u, u} k) :
    brauerBaseChange L M (brauerBaseChange k L x) =
      brauerBaseChange k M x := by
  induction x using Quotient.inductionOn with
  | _ A =>
      apply Quotient.sound
      exact brauer_equivalent_alg M _ _
        (scalarTowerAlg k L M A)

end

end Submission.CField.BGroups
