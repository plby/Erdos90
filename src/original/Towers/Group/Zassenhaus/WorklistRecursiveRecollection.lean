import Towers.Group.Zassenhaus.ConjugatedHigherRouting
import Towers.Group.Zassenhaus.BracketPacketWorklist
import Towers.Group.Zassenhaus.SourceRecollectionComposition

/-!
# Recursive recollection of powered outer-bracket worklists

An outer-bracket packet worklist retains conjugating copies of each left
factor.  If the recursive tail has already been recollected one layer higher,
sharp higher-tail routing removes the wrappers around that tail.  Appending
the terminal correction packet then recollects the complete worklist.

The recursion is structural on the finite left source.  It assumes a sharp
router at the left factors' common stratum and does not assume a semantic
normalizer at that same stratum.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace PBWork

/--
Structurally recollect an exact outer-bracket worklist whose left factors all
lie in one ordinary Hall-weight stratum.
-/
noncomputable def source_recollect_normalizer
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight) H)
    (right : SPFactora H inputWeight)
    (packet :
      ∀ left : SPFactora H inputWeight,
        TCPkt n left right) :
    ∀ left : List (SPFactora H inputWeight),
      SPFactora.IsTruncated n left →
        (∀ x ∈ left,
          x.word.weight PEAddres.weight = lowerWeight) →
          TSRecol
            (n := n) (lowerWeight := lowerWeight + 1) H
            (factors right packet left)
  | [], _hleftTruncated, _hleftWeight =>
      TSRecol.empty
  | head :: tail, hleftTruncated, hleftWeight => by
      have hheadTruncated :
          head.word.weight PEAddres.weight < n :=
        hleftTruncated head (by simp)
      have htailTruncated :
          SPFactora.IsTruncated n tail := by
        intro x hx
        exact hleftTruncated x (by simp [hx])
      have hheadWeight :
          head.word.weight PEAddres.weight = lowerWeight :=
        hleftWeight head (by simp)
      have htailWeight :
          ∀ x ∈ tail,
            x.word.weight PEAddres.weight = lowerWeight := by
        intro x hx
        exact hleftWeight x (by simp [hx])
      let tailRecollection :=
        source_recollect_normalizer factory sharp right
          packet tail htailTruncated htailWeight
      let conjugated :=
        factory.conjugated_recollection_normalizer sharp
          head.neg
          (by simpa only [SPFactora.word_neg] using hheadWeight)
          (by
            simpa only [SPFactora.word_neg] using
              hheadTruncated)
          (factors right packet tail)
          tailRecollection.higherSource
          tailRecollection.higher_source_truncated
          tailRecollection.higher_weight_least
          tailRecollection.list_higher_raw
      exact
        {
          higherSource := conjugated.higherSource ++ (packet head).factors
          higher_source_truncated := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact conjugated.higher_source_truncated x hx
            · exact (packet head).word_weight_cutoff x hx
          higher_weight_least := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact conjugated.higher_least_succ x hx
            · have hterminal := (packet head).word_weight_left x hx
              omega
          list_higher_raw := by
            intro q
            rw [SPFactora.listEval_append,
              conjugated.higher_conjugated_raw]
            simp only [factors_cons,
              SPFactora.conjugatedRawSource,
              SPFactora.listEval_append,
              SPFactora.listEval_cons,
              SPFactora.listEval_nil, mul_one,
              SPFactora.eval_neg, inv_inv]
        }

end PBWork
end TCTex
end Towers
