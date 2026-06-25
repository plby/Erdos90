import Submission.ClassField.Ideles.GlobalPlace

/-!
# The basic archimedean idèle subgroup

At a real place we use the positive component, and at a complex place the
whole unit group. These definitions are independent of norm maps.
-/

namespace Submission.CField.HNorm

open NumberField
open Submission.CField.Ideles

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- At a real infinite place use the positive component; at a complex place
use the whole unit group. -/
noncomputable def infiniteBasicSubgroup
    (v : InfinitePlace K) : Subgroup v.Completionˣ := by
  classical
  exact if hv : v.IsReal then
      (Units.posSubgroup ℝ).comap
        (Units.map
          (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toMonoidHom)
    else
      ⊤

/-- The product of the archimedean basic subgroups. -/
def infiniteIdeleSubgroup :
    Subgroup (InfiniteAdeleRing K)ˣ where
  carrier := {a | ∀ v : InfinitePlace K,
    MulEquiv.piUnits a v ∈ infiniteBasicSubgroup (K := K) v}
  one_mem' := by
    intro v
    rw [show MulEquiv.piUnits (1 : (InfiniteAdeleRing K)ˣ) v = 1 by
      exact congrFun (map_one (MulEquiv.piUnits :
        (InfiniteAdeleRing K)ˣ ≃* ((v : InfinitePlace K) → v.Completionˣ))) v]
    exact (infiniteBasicSubgroup (K := K) v).one_mem
  mul_mem' := by
    intro a b ha hb v
    rw [show MulEquiv.piUnits (a * b) v =
        MulEquiv.piUnits a v * MulEquiv.piUnits b v by
      exact congrFun (map_mul (MulEquiv.piUnits :
        (InfiniteAdeleRing K)ˣ ≃* ((v : InfinitePlace K) → v.Completionˣ)) a b) v]
    exact (infiniteBasicSubgroup (K := K) v).mul_mem (ha v) (hb v)
  inv_mem' := by
    intro a ha v
    have h := congrFun (map_inv (MulEquiv.piUnits :
      (InfiniteAdeleRing K)ˣ ≃* ((v : InfinitePlace K) → v.Completionˣ)) a) v
    change MulEquiv.piUnits a⁻¹ v ∈ infiniteBasicSubgroup (K := K) v
    exact h.symm ▸ (infiniteBasicSubgroup (K := K) v).inv_mem (ha v)

end

end Submission.CField.HNorm
