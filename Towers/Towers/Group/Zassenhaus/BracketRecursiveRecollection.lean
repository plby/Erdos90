import Towers.Group.Zassenhaus.ResidualSingletonRecollection
import Towers.Group.Zassenhaus.RankedTaskSource

/-!
# Recursive recollection of concrete inner-packet outer brackets

The concrete inner-packet outer-bracket worklist is an exact symbolic source.
Its ranked task source strictly descends lexicographically.  Once recursive
basic residual recollections are available for every emitted task, singleton
reconstruction and finite source composition recollect the complete exact
worklist.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace CBWorka

/--
Recollect the exact outer-bracket worklist from concrete basic residual
recollections for all of its strictly descending Hall-ranked tasks.
-/
noncomputable def recollection_basic_residuals
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (residual :
      ∀ task ∈ rankedTasks packet hinputWeight inner right unchanged,
        TSRecollb
          (n := n) task.1) :
    TSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight PEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (factors packet hinputWeight inner right) := by
  let source :=
    rankedTaskSource packet hinputWeight inner right hinnerTruncated added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic
  have hsource :
      source.factorSource = factors packet hinputWeight inner right := by
    dsimp only [source]
    exact
      factor_ranked_task packet hinputWeight inner right
        hinnerTruncated added originalRight unchanged originalLeft hinnerTree
          hRightLeft hRightUnchanged hunchangedBasic
  rw [← hsource]
  apply source.recollection_basic_residuals
  · rw [hsource]
    exact isTruncated_factors packet hinputWeight inner right hinnerTruncated
  · rw [hsource]
    exact weight_least_factors packet hinputWeight inner right
  · intro task htask
    exact residual task (by simpa only [source, rankedTaskSource] using htask)

end CBWorka
end TCTex
end Towers
