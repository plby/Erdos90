import Submission.Group.Zassenhaus.GeneratedFrontierRouting

/-!
# Structural restart routing for active transient frontiers

The ordered residual tails of one transient commutator frontier descend in
cutoff defect from the original outer carrier.  Its temporary classified
packet instead descends from the reworded inner carrier.  That inner carrier
has strictly smaller physical Hall-word weight because it is a proper
commutator subtree.

This file packages the second move as an explicit structural restart
interface.  The resulting adapter keeps the two recursion orders separate:
cutoff-defect recursion handles the outer tails, while a caller-supplied
strictly-smaller-root handler restarts recursion at the reworded inner word.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace
  BRRoute

/--
The inner word selected by a bifurcated transient-frontier route is strictly
lighter than its decomposable outer word.
-/
lemma inner_weight_outer
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    {outerExpansion :
      TWExp H inputWeight}
    (routing :
      BRRoute
        H packet hinputWeight outerExpansion) :
    routing.innerWord.weight PEAddres.weight <
      outerExpansion.word.weight PEAddres.weight := by
  rw [routing.word_eq, CWord.weight_commutator]
  exact
    Nat.lt_add_of_pos_right
      (CWord.weight_pos PEAddres.weight
        PEAddres.weight_pos routing.rightWord)

/--
Rewording the outer transient exponent onto the selected inner word exposes a
strictly lighter recursive root.
-/
lemma reword_inner_outer
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    {outerExpansion :
      TWExp H inputWeight}
    (routing :
      BRRoute
        H packet hinputWeight outerExpansion) :
    (outerExpansion.reword routing.innerWord).word.weight
        PEAddres.weight <
      outerExpansion.word.weight PEAddres.weight := by
  simpa only [TWExp.word_reword] using
    routing.inner_weight_outer

end
  BRRoute

/--
A restart handler for the second recursive root exposed by transient
frontier decomposition.

The handler is deliberately parameterized by a strictly lighter transient
root.  It does not claim that this root descends in cutoff defect from the
original outer root.
-/
structure
    TSRestar
    {d n inputWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (outerExpansion :
      TWExp H inputWeight) where
  sourceRecollection :
    ∀
      (smallerExpansion :
        TWExp H inputWeight),
      smallerExpansion.word.weight PEAddres.weight <
          outerExpansion.word.weight PEAddres.weight →
        ∀ lowerWeight,
          lowerWeight ≤
              outerExpansion.word.weight PEAddres.weight →
            ∀ child,
              SOTerm.FrontierDefectMultiset
                  n child [.frontier smallerExpansion] →
                TTRecol
                  n lowerWeight H child

namespace
  BRRoute

/--
Close one decomposable transient frontier from its ordinary outer
cutoff-defect callback and an explicit strictly-smaller-root restart handler.
-/
noncomputable def recollection_smaller_restart
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    {outerExpansion :
      TWExp H inputWeight}
    (routing :
      BRRoute
        H packet hinputWeight outerExpansion)
    (split :
      PFSubsti.TAPkt.OBSplit
        packet)
    (hlowerWeight :
      lowerWeight ≤
        outerExpansion.word.weight PEAddres.weight)
    (outerRecursiveResults :
      ∀ child,
        SOTerm.FrontierDefectMultiset
            n child [.frontier outerExpansion] →
          TTRecol
            n lowerWeight H child)
    (restart :
      TSRestar
        (n := n) H outerExpansion) :
    TTRecol
      n lowerWeight H [.frontier outerExpansion] :=
  routing.sourceRecollection split hlowerWeight outerRecursiveResults <|
    restart.sourceRecollection
      (outerExpansion.reword routing.innerWord)
      routing.reword_inner_outer
      lowerWeight hlowerWeight

end
  BRRoute

namespace
  TSRestar

/--
Automatically close any Hall-Petresco generated transient frontier once a
strictly-smaller-root restart handler and the outer cutoff-defect callback are
available.
-/
noncomputable def source_recollection_expansion
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (split :
      PFSubsti.TAPkt.OBSplit
        packet)
    (hinputWeight : 0 < inputWeight)
    (R : HACoeff.BRecipe)
    (B A : TWExp H inputWeight)
    (hlowerWeight :
      lowerWeight ≤
        (PTSubsti.wordExpansion
          hinputWeight R B A).word.weight PEAddres.weight)
    (outerRecursiveResults :
      ∀ child,
        SOTerm.FrontierDefectMultiset
            n child
              [.frontier
                (PTSubsti.wordExpansion
                  hinputWeight R B A)] →
          TTRecol
            n lowerWeight H child)
    (restart :
      TSRestar
        (n := n) H
          (PTSubsti.wordExpansion
            hinputWeight R B A)) :
    TTRecol
      n lowerWeight H
        [.frontier
          (PTSubsti.wordExpansion
            hinputWeight R B A)] :=
  (BRRoute.of_wordExpansion
    packet hinputWeight R B A)
      |>.recollection_smaller_restart split hlowerWeight
        outerRecursiveResults restart

end
  TSRestar

end TCTex
end Submission

