import Submission.Group.PrimeBlockRecipe
import Submission.Group.PetrescoNormalClosure

open scoped commutatorElement

namespace Submission
namespace HACoeff

open PPColl
open PPColl.RCColl.RPAggreg

/-- At prime-power budgets, universal bidegree-normal-closure membership gives
the normal-closure-shaped trace target. -/
lemma bidegree_closure_trace
    (p A B : ℕ) :
    BNClos.subgroup ((p : ℤ) ^ A) ((p : ℤ) ^ B) ≤
      TNClos.subgroup p A B universalLeft universalRight := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨u, c, hpositive, hleft, hright, rfl⟩
  apply Subgroup.subset_normalClosure
  let F : RFactor UniversalGroup := {
    word := u
    multiplicity := c
    conjugator := 1 }
  refine ⟨F, ?_, ?_⟩
  · exact ⟨hpositive.left, hpositive.right, hleft, hright⟩
  · simp [F, RFactor.eval]

/-- Specialize a universal trace to an arbitrary Hall pair. -/
def specializeTrace
    {p A B : ℕ}
    {G : Type*} [Group G]
    (T :
      PPColl.Trace p universalLeft universalRight A B)
    (x y : G) :
    PPColl.Trace p x y A B where
  factors :=
    RFactor.listMapHom (specialize x y) T.factors
  eval_eq := by
    calc
      PPColl.listEval x y
          (RFactor.listMapHom (specialize x y) T.factors) =
        PPColl.listEval
          ((specialize x y) universalLeft)
          ((specialize x y) universalRight)
          (RFactor.listMapHom (specialize x y) T.factors) := by
            simp
      _ =
          specialize x y
            (PPColl.listEval
              universalLeft universalRight T.factors) := by
        exact
          RFactor.list_eval_hom
            (specialize x y) universalLeft universalRight T.factors
      _ = ⁅x ^ (p ^ A), y ^ (p ^ B)⁆ := by
        rw [T.eval_eq]
        simp [map_commutatorElement, map_pow]
  factors_good := by
    intro F hF
    rcases List.mem_map.mp hF with ⟨E, hE, rfl⟩
    exact (RFactor.good_mapHom (specialize x y) E).2 (T.factors_good E hE)

end HACoeff
end Submission
