import Towers.Group.Zassenhaus.InverseHistoryTruncation
import Towers.Group.Zassenhaus.PacketScheduling

/-!
# Evaluating truncated inverse-oriented Hall traces

The inverse-oriented trace is constructed in the labelled free group.  This
file specializes its universal collapsed identity to an arbitrary group pair,
then combines that identity with history truncation.  The result is an honest
fixed-multiplicity packet contract: a closed operational schedule produces an
ordered below-cutoff family list evaluating to `[x^M, y^N]` in every matching
nilpotent quotient.

This does not yet assert the stronger all-integral polynomial identity required
by `TAPktb`.  It is intentionally not imported by the existing
collection proof.
-/

namespace Towers
namespace TCTex
namespace ITEvalua

open scoped commutatorElement

open HACoeff
open BRSpec
open BFTrunc
open ITSched
open PHTrunc
open PHTrunc.CHSched
open PPColl.RCColl.RPAggreg

/-- Specialize the universal Hall-pair free group to an arbitrary group pair. -/
def hallPairSpecialize
    {G : Type*}
    [Group G]
    (x y : G) :
    UniversalGroup →* G :=
  FreeGroup.lift (HPAtom.eval x y)

@[simp]
lemma specialize_universal_left
    {G : Type*}
    [Group G]
    (x y : G) :
    hallPairSpecialize x y universalLeft = x := by
  simp [hallPairSpecialize, universalLeft, HPAtom.eval]

@[simp]
lemma specialize_universal_right
    {G : Type*}
    [Group G]
    (x y : G) :
    hallPairSpecialize x y universalRight = y := by
  simp [hallPairSpecialize, universalRight, HPAtom.eval]

/-- Universal collapsed-list evaluation specializes to evaluation at a group pair. -/
lemma pair_specialize_collapsed
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (words : List (CWord (LabelledAtom M N))) :
    hallPairSpecialize x y (collapsedListEval words) =
      collapsedList x y words := by
  rw [collapsedListEval, collapsedList, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro word _hword
  change
    hallPairSpecialize x y
        ((collapseWord word).eval
          (HPAtom.eval universalLeft universalRight)) =
      (collapseWord word).eval (HPAtom.eval x y)
  rw [CWord.map_eval]
  congr 1
  funext atom
  cases atom <;>
    simp [hallPairSpecialize, HPAtom.eval, universalLeft, universalRight]

/--
At every group pair, the collapsed inverse-oriented source trace evaluates to
the commutator of the corresponding natural powers.
-/
lemma collapsed_commutator_pow
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (x y : G) :
    collapsedList x y
        (inverseLeftTrace
          (labelledLeftAtoms M N)
          (labelledRightAtoms M N)) =
      ⁅x ^ M, y ^ N⁆ := by
  calc
    collapsedList x y
          (inverseLeftTrace
            (labelledLeftAtoms M N)
            (labelledRightAtoms M N)) =
        hallPairSpecialize x y
          (collapsedListEval
            (inverseLeftTrace
              (labelledLeftAtoms M N)
              (labelledRightAtoms M N))) := by
      symm
      exact pair_specialize_collapsed x y _
    _ =
        hallPairSpecialize x y
          ⁅universalLeft ^ M, universalRight ^ N⁆ := by
      rw [← collapsed_eval_pow
        (inverseLabelledCollection M N)]
      rfl
    _ = ⁅x ^ M, y ^ N⁆ := by
      simp only [map_commutatorElement, map_pow,
        specialize_universal_left, specialize_universal_right]

/--
Fixed natural-multiplicity cutoff packet extracted from an operational history
schedule.  This is the semantic endpoint available before proving the
all-integral polynomial interpolation theorem.
-/
structure TFPkt
    (M N n leftWeight rightWeight : ℕ) where
  families :
    List (BFam M N)
  collapsed_list_eval :
    ∀ {G : Type*} [Group G]
      (x y : G),
      x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1) →
      y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1) →
      Subgroup.lowerCentralSeries G (n - 1) = ⊥ →
      collapsedList x y (BFam.realizationList families) =
        ⁅x ^ M, y ^ N⁆
  weighted_weight_cutoff :
    ∀ family ∈ families,
      weightedWordWeight leftWeight rightWeight family.recipe < n

namespace CHSched

/--
Every closed inverse-oriented history schedule yields a fixed-power truncated
packet by deleting only quotient-trivial high-weight histories.
-/
def truncatedPowerPacket
    {M N n leftWeight rightWeight : ℕ}
    (schedule : CHSched M N)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    TFPkt M N n leftWeight rightWeight where
  families :=
    PHTrunc.CHSched.retainedFamilies
      n leftWeight rightWeight schedule
  collapsed_list_eval := by
    intro G _ x y hx hy hbot
    exact
      (collapsed_families_source
        schedule (n := n) hleftWeight hrightWeight hx hy hbot).trans
          (collapsed_commutator_pow x y)
  weighted_weight_cutoff := by
    intro family hfamily
    exact weighted_cutoff_families hfamily

end CHSched

namespace PPScheda

/--
A positive-positive operational scheduler, together with the checked zero
cases, supplies fixed-power truncated packets for every pair of multiplicities.
-/
noncomputable def resolveAllPacket
    (kernel : PPScheda)
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    TFPkt M N n leftWeight rightWeight :=
  ITEvalua.CHSched.truncatedPowerPacket
    (kernel.resolveAll M N) hleftWeight hrightWeight

end PPScheda

/-- The explicit first positive-positive trace gives the first fixed-power packet. -/
def truncatedFixedPacket
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    TFPkt 1 1 n leftWeight rightWeight :=
  ITEvalua.CHSched.truncatedPowerPacket
    oneOne hleftWeight hrightWeight

end ITEvalua
end TCTex
end Towers
