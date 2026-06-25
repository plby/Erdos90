import Towers.Group.Zassenhaus.BracketPacketWorklist
import Towers.Group.Zassenhaus.SemanticallyHigherRecollection
import Towers.Group.Zassenhaus.SharpNormalizerFamilies

/-!
# Recollecting powered outer-bracket packet worklists

The finite outer-bracket worklist retains same-weight conjugating copies of
the left source, so it is not physically supported one stratum higher.
Nevertheless its evaluated product is exactly a commutator.  Lower-central
strong centrality places that value one layer above the common physical
support bound.  A current-stratum semantic normalizer can therefore discard
the vanishing active block and retain only a strictly higher tail.

This is the semantic adapter needed after reducing an inner Hall bracket to
its finite atomic packet and before recursing on the resulting outer
brackets.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

namespace PBWork

/--
The outer-bracket packet worklist evaluates one lower-central layer above any
common physical support bound for its left source.
-/
theorem list_factors_series
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (right : SPFactora H inputWeight)
    (packet :
      ∀ left : SPFactora H inputWeight,
        TCPkt n left right)
    (left : List (SPFactora H inputWeight))
    (hleft :
      SPFactora.WordWeightLeast lowerWeight left)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (factors right packet left) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        lowerWeight := by
  rw [listEval_factors]
  have hcommutator :
      ⁅SPFactora.listEval (n := n) q left,
        right.eval (n := n) q⁆ ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        ((lowerWeight - 1) +
          (right.word.weight PEAddres.weight - 1) + 1) :=
    element_lower_series
      (SPFactora.list_series_weight
        (n := n) q left hleft)
      (right.eval_lower_series (n := n) q)
  exact Subgroup.lowerCentralSeries_antitone (by
    have hrightPos := right.word_weight_pos
    omega) hcommutator

/--
Normalize an outer-bracket packet worklist and retain its strictly higher
coordinate tail.
-/
noncomputable def source_recollection_normalizer
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight) H)
    (right : SPFactora H inputWeight)
    (packet :
      ∀ left : SPFactora H inputWeight,
        TCPkt n left right)
    (left : List (SPFactora H inputWeight))
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n)
    (hleftTruncated : SPFactora.IsTruncated n left)
    (hleftSupported :
      SPFactora.WordWeightLeast lowerWeight left) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight + 1) H
        (factors right packet left) :=
  normalizer.source_recollection_series hn H hH
    (factors right packet left) hlowerWeightPos hlowerWeightTruncated
      (isTruncated_factors right packet hleftTruncated)
      (weight_least_factors right packet hleftSupported)
      (list_factors_series right packet left
        hleftSupported)

/-- Use a normalizer family at the common left-source support bound. -/
noncomputable def recollection_normalizer_family
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H)
    (right : SPFactora H inputWeight)
    (packet :
      ∀ left : SPFactora H inputWeight,
        TCPkt n left right)
    (left : List (SPFactora H inputWeight))
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n)
    (hleftTruncated : SPFactora.IsTruncated n left)
    (hleftSupported :
      SPFactora.WordWeightLeast lowerWeight left) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight + 1) H
        (factors right packet left) :=
  source_recollection_normalizer hn H hH
    (family.normalizer lowerWeight) right packet left hlowerWeightPos
      hlowerWeightTruncated hleftTruncated hleftSupported

end PBWork
end TCTex
end Towers
