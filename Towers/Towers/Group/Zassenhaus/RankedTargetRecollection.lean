import Towers.Group.Zassenhaus.RankedTaskSource
import Towers.Group.Zassenhaus.Packet

/-!
# Ranked target recollections for concrete outer brackets

The exact powered outer-bracket worklist emitted after reducing an inner Hall
packet has two complementary properties:

* every emitted factor is a strict cutoff-defect/Hall-rank child;
* structural normalization recollects the erased source at any support target
  up to the full outer-bracket weight.

This file packages those properties together.  It is the symbolic analogue of
the inner-span branch in the classical Hall collector: recursively scheduled
outer-bracket tasks come with one exact, semantically recollected source.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

namespace SPFactora

/--
A finite strict Hall-ranked child source together with a semantic recollection
of its erased symbolic factors.
-/
structure RankedRecollectedChild
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (parent : SPFactora H inputWeight)
    (parentRankDefect : ℕ) where
  source :
    RCSrc (n := n) parent parentRankDefect
  recollection :
    TSRecol
      (n := n) (lowerWeight := lowerWeight) H source.factorSource

end SPFactora

open HEWord

namespace CBWorka

/--
Package the exact generated outer-bracket worklist as strict Hall-ranked
children recollected at a chosen support target.
-/
noncomputable def rankedTargetRecollection
    {d n inputWeight targetWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight PEAddres.weight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (hinitialTarget :
      inner.word.weight PEAddres.weight + 1 ≤ targetWeight)
    (htargetTotal :
      targetWeight ≤
        inner.word.weight PEAddres.weight +
          right.word.weight PEAddres.weight) :
    SPFactora.RankedRecollectedChild
      (n := n) (lowerWeight := targetWeight) inner
      (HallTree.bracketRankDefect
        ((tree inner.word).weight + unchanged.weight)
        originalLeft originalRight) where
  source :=
    rankedTaskSource packet hinputWeight inner right hinnerTruncated added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic
  recollection := by
    rw [factor_ranked_task]
    exact
      recollect_normalizer_above hn hH packet hinputWeight
        inner right normalizerAbove hinnerTruncated hinitialTarget htargetTotal

/--
The recollected higher source still evaluates exactly to the generated
outer bracket of the reduced inner packet.
-/
theorem ranked_target_recollection
    {d n inputWeight targetWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight PEAddres.weight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (hinitialTarget :
      inner.word.weight PEAddres.weight + 1 ≤ targetWeight)
    (htargetTotal :
      targetWeight ≤
        inner.word.weight PEAddres.weight +
          right.word.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (rankedTargetRecollection hn hH packet hinputWeight inner right
          normalizerAbove hinnerTruncated added originalRight unchanged
            originalLeft hinnerTree hRightLeft hRightUnchanged hunchangedBasic
              hinitialTarget htargetTotal).recollection.higherSource =
      ⁅SPFactora.listEval (n := n) q
          (basicReductionFactors inner),
        right.eval (n := n) q⁆ := by
  rw [(rankedTargetRecollection hn hH packet hinputWeight inner right
    normalizerAbove hinnerTruncated added originalRight unchanged originalLeft
      hinnerTree hRightLeft hRightUnchanged hunchangedBasic hinitialTarget
        htargetTotal).recollection.list_higher_raw]
  exact
    list_ranked_task packet hinputWeight inner right
      hinnerTruncated added originalRight unchanged originalLeft hinnerTree
        hRightLeft hRightUnchanged hunchangedBasic q

/--
Specialize the ranked generated outer-bracket branch to its full
lower-central support depth.
-/
noncomputable def rankedTotalRecollection
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight PEAddres.weight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    SPFactora.RankedRecollectedChild
      (n := n)
      (lowerWeight :=
        inner.word.weight PEAddres.weight +
          right.word.weight PEAddres.weight)
      inner
      (HallTree.bracketRankDefect
        ((tree inner.word).weight + unchanged.weight)
        originalLeft originalRight) :=
  rankedTargetRecollection hn hH packet hinputWeight inner right
    normalizerAbove hinnerTruncated added originalRight unchanged originalLeft
      hinnerTree hRightLeft hRightUnchanged hunchangedBasic
        (by
          have hrightPos := right.word_weight_pos
          omega)
        (Nat.le_refl _)

end CBWorka
end TCTex
end Towers
