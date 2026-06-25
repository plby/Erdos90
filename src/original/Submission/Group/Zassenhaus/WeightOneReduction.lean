import Submission.Group.Zassenhaus.SignedCorrectionSemantics
import Submission.Group.Zassenhaus.FactorSourceReduction

/-!
# Exact weight-one residual reduction for symbolic Hall powers

A symbolic Hall-power factor of ordinary word weight one is one Hall address.
Its active Hall-normal layer already evaluates exactly to the factor, so its
intrinsic residual source recollects to the empty list.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace CCExpans

/--
The active Hall-normal layer of a weight-one symbolic Hall-power factor is
exactly the factor itself.
-/
lemma active_block_value
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = 1)
    (q : ℕ) :
    activeNormalValue hn H hH factor 1 q =
      factor.eval (n := n) q := by
  obtain ⟨address, hword⟩ :=
    CWord.atom_weight_one
      PEAddres.weight PEAddres.weight_pos
        factor.word hfactorWeight
  rcases address with ⟨s, i⟩
  have hs : s = 1 := by
    rw [hword] at hfactorWeight
    simpa [PEAddres.weight] using hfactorWeight
  subst s
  have hwordValue :
      factor.wordValue (n := n) =
        ((H 1).commutator i).freeLowerTruncation := by
    unfold SPFactora.wordValue
    rw [hword]
    rfl
  unfold activeNormalValue
  rw [CCExpans.list_weight_factors]
  rw [factor.normal_coordinate_expansions hn H hH q 1 (by omega)
    (by omega)]
  have hcoordinates :
      normalFormCoordinates hn H hH (factor.wordValue (n := n)) 1 =
        fun j => if j = i then 1 else 0 := by
    rw [hwordValue]
    exact
      BCWta.hallnormalform_coordsevalin_frelowcentru
        hn H hH (by omega) (by omega) i
  change
    (H 1).collectedWeightProduct
        (fun j =>
          normalFormCoordinates hn H hH (factor.wordValue (n := n)) 1 j *
            factor.exponent q) =
      factor.eval q
  rw [hcoordinates]
  rw [show
      (fun j => (if j = i then 1 else 0) * factor.exponent q) =
        fun j => if j = i then factor.exponent q else 0 by
      funext j
      split_ifs <;> simp]
  rw [(H 1).collectedweight_productite_eqzpow]
  unfold SPFactora.eval
  rw [hwordValue]

end CCExpans

namespace
  TSSrc

open CCExpans

/--
A weight-one symbolic Hall-power factor has trivial intrinsic residual source:
its active Hall-normal block already evaluates to the factor.
-/
noncomputable def of_weight_one
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = 1) :
    TSSrc
      (lowerWeight := 1) hn H hH factor where
  higherSource := []
  higher_source_truncated := by
    simp [SPFactora.IsTruncated]
  higher_least_succ := by
    simp [SPFactora.WordWeightLeast]
  list_higher_raw q := by
    rw [factor.active_raw_source
      hn H hH 1 q]
    unfold
      CCExpans.activeBlockValue
    rw [
      active_block_value
        hn H hH factor hfactorWeight q]
    simp [SPFactora.listEval]

end
  TSSrc

end TCTex
end Submission
