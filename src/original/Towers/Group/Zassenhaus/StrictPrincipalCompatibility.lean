import Towers.Group.Zassenhaus.StrictTail
import Towers.Group.Zassenhaus.ResidualPrincipalInventory

/-!
# Compatibility between strict tails and principal residual inventory

An ordered split around the basic Hall-Petresco recipe is stronger than the
unordered principal-recipe invariant.  This file connects those two
interfaces and records the exact raw residual order after inversion.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace PFSubsti.TAPkt

open BRSpec
open PTSubsti

namespace OBSplit

/-- Forget the ordered tails while retaining the principal-recipe invariant. -/
def principalRecipe
    {d n : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : OBSplit packet) :
    packet.PBRecipea where
  basic_mem := by
    rw [split.recipes_eq]
    simp
  basic_bidegree_one := by
    intro R hR hleft hright
    rw [split.recipes_eq] at hR
    rcases List.mem_append.mp hR with hR | hR
    · exact False.elim <|
        (split.before_strict_tail R hR).elim
          (fun hne => hne hleft) (fun hne => hne hright)
    · rcases List.mem_cons.mp hR with rfl | hR
      · rfl
      · exact False.elim <|
          (split.after_strict_tail R hR).elim
            (fun hne => hne hleft) (fun hne => hne hright)

end OBSplit

/--
For an ordered split, every raw residual member is the negated basic output,
a strictly heavier output, or the appended parent.
-/
theorem
    neg_basic_split
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (split : packet.OBSplit)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (nextExpansion :
      TWExp H inputWeight)
    (hnext :
      nextExpansion ∈
        packet.transientInnerReduction hinputWeight
          outerExpansion innerWord rightWord) :
    nextExpansion =
        (wordExpansion hinputWeight hallPair (outerExpansion.reword innerWord)
          (TWExp.wordUnit rightWord)).neg ∨
      outerExpansion.word.weight PEAddres.weight <
        nextExpansion.word.weight PEAddres.weight ∨
      nextExpansion = outerExpansion :=
  packet
    |>.neg_outer_source
      split.principalRecipe hinputWeight outerExpansion innerWord
        rightWord hword nextExpansion hnext

end PFSubsti.TAPkt

end TCTex
end Towers
