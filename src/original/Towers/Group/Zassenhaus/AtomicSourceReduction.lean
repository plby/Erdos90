import Towers.Group.Zassenhaus.WeightOneReduction

/-!
# Exact atomic residual reduction for symbolic Hall powers

A symbolic Hall-power factor whose commutator word is already one Hall
address has no intrinsic Hall-normalization tail in its own weight layer.
This is the all-weight atomic analogue of the weight-one residual reduction.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace CCExpans

/--
The active Hall-normal layer of an atomic symbolic Hall-power factor is
exactly the factor itself.
-/
lemma active_block_atom
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factor : SPFactora H inputWeight)
    (address : HEAddres H)
    (hword : factor.word = .atom address)
    (htruncated : address.weight < n)
    (q : ℕ) :
    activeNormalValue hn H hH factor address.weight q =
      factor.eval (n := n) q := by
  rcases address with ⟨s, i⟩
  have hwordValue :
      factor.wordValue (n := n) =
        ((H s).commutator i).freeLowerTruncation := by
    unfold SPFactora.wordValue
    rw [hword]
    rfl
  change activeNormalValue hn H hH factor s q =
    factor.eval q
  unfold activeNormalValue
  rw [CCExpans.list_weight_factors]
  rw [factor.normal_coordinate_expansions hn H hH q s
    (PEAddres.weight_pos ⟨s, i⟩) htruncated]
  have hcoordinates :
      normalFormCoordinates hn H hH (factor.wordValue (n := n)) s =
        fun j => if j = i then 1 else 0 := by
    rw [hwordValue]
    exact
      BCWta.hallnormalform_coordsevalin_frelowcentru
        hn H hH (PEAddres.weight_pos ⟨s, i⟩) htruncated i
  change
    (H s).collectedWeightProduct
        (fun j =>
          normalFormCoordinates hn H hH (factor.wordValue (n := n)) s j *
            factor.exponent q) =
      factor.eval q
  rw [hcoordinates]
  rw [show
      (fun j => (if j = i then 1 else 0) * factor.exponent q) =
        fun j => if j = i then factor.exponent q else 0 by
      funext j
      split_ifs <;> simp]
  rw [(H s).collectedweight_productite_eqzpow]
  unfold SPFactora.eval
  rw [hwordValue]

end CCExpans

open CCExpans

namespace
  TSSrc

/--
An atomic symbolic Hall-power factor has trivial intrinsic residual source:
its active Hall-normal block already evaluates to the factor.
-/
noncomputable def of_atom
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factor : SPFactora H inputWeight)
    (address : HEAddres H)
    (hword : factor.word = .atom address)
    (htruncated : address.weight < n) :
    TSSrc
      (lowerWeight := address.weight) hn H hH factor where
  higherSource := []
  higher_source_truncated := by
    simp [SPFactora.IsTruncated]
  higher_least_succ := by
    simp [SPFactora.WordWeightLeast]
  list_higher_raw q := by
    rw [factor.active_raw_source
      (lowerWeight := address.weight) hn H hH q]
    unfold
      CCExpans.activeBlockValue
    rw [
      active_block_atom
        hn H hH factor address hword htruncated q]
    simp [SPFactora.listEval]

end
  TSSrc

end TCTex
end Towers
