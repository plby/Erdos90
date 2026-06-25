import Towers.ClassField.CohomologyOps.Corestriction

/-!
# Class Field Theory, Chapter II, Remark 1.3(c)

For a finite group `G` and a `G`-representation `A`, Milne's induced-module
trace onto `A` is surjective.  Mathlib identifies finite-index coinduction
with induction; the required preimage of `x` is the induced vector supported
at the identity with value `x`.
-/

namespace Towers.CField.COps

open CategoryTheory Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- The induction/restriction counit sends the vector supported at the
identity with value `x` to `x`. -/
private lemma ind_counit_v (A : Rep k G) (x : A) :
    ((indResAdjunction k (⊥ : Subgroup G).subtype).counit.app A).hom
        (Representation.IndV.mk (⊥ : Subgroup G).subtype
          (A.ρ.comp (⊥ : Subgroup G).subtype) 1 x) = x := by
  change ((indResHomEquiv (⊥ : Subgroup G).subtype
      (res (⊥ : Subgroup G).subtype A) A).symm (𝟙 _)).hom
        (Representation.IndV.mk (⊥ : Subgroup G).subtype
          (A.ρ.comp (⊥ : Subgroup G).subtype) 1 x) = x
  simp [indResHomEquiv]

/-- **Remark II.1.3(c).** For finite `G`, the canonical trace from the
representation induced from the underlying module is surjective.  Here the
source is written as the canonically isomorphic coinduced representation,
matching Milne's function model. -/
theorem corestriction_bot_surjective
    [Finite G] (A : Rep k G) :
    Function.Surjective
      (corestrictionTrace A (⊥ : Subgroup G)).hom := by
  classical
  letI := Classical.decRel (QuotientGroup.rightRel (⊥ : Subgroup G))
  intro x
  let v : Representation.IndV (⊥ : Subgroup G).subtype
      (A.ρ.comp (⊥ : Subgroup G).subtype) :=
    Representation.IndV.mk (⊥ : Subgroup G).subtype
      (A.ρ.comp (⊥ : Subgroup G).subtype) 1 x
  refine ⟨(indCoindIso (res (⊥ : Subgroup G).subtype A)).hom.hom v, ?_⟩
  rw [corestrictionTrace, coindResAdjunction_counit_app]
  change ((indResAdjunction k (⊥ : Subgroup G).subtype).counit.app A).hom
      ((indCoindIso (res (⊥ : Subgroup G).subtype A)).inv.hom
        ((indCoindIso (res (⊥ : Subgroup G).subtype A)).hom.hom v)) = x
  rw [Iso.hom_inv_id_apply]
  exact ind_counit_v A x

end Towers.CField.COps
