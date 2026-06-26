import Submission.Group.Zassenhaus.RankedTaskInduction
import
  Submission.Group.Zassenhaus.BracketRecursiveRecollection

/-!
# Hall-ranked recursion for concrete basic residual recollections

A concrete Hall collector must recollect each atomic basic-reduction residual
into a strictly higher symbolic source.  This file isolates the remaining
local Hall-tree obligation: a scheduler emits finitely many lexicographically
smaller tasks and recollects one parent once those child residuals are
available.

Well-founded Hall-ranked recursion then constructs a residual recollection for
every factor.  The final adapter feeds those recursively constructed residuals
into the exact concrete inner-packet outer-bracket worklist recollection.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
The local data needed to recollect all concrete atomic residuals by Hall-ranked
well-founded recursion.
-/
structure RRSchedua
    {d n inputWeight : ℕ} where
  children :
    ∀ (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (rankDefect : ℕ),
      SPFactora.RCSrc
        (n := n) factor rankDefect
  recollect :
    ∀ (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (rankDefect : ℕ),
      (∀ task ∈ (children factor rankDefect).tasks,
        TSRecollb
          (n := n) task.1) →
        TSRecollb
          (n := n) factor

namespace
  RRSchedua

/--
Construct the concrete basic residual recollection for an arbitrary ranked
factor from a finite Hall-ranked scheduler.
-/
noncomputable def residualRecollection
    {d n inputWeight : ℕ}
    (scheduler :
      RRSchedua
        (d := d) (n := n) (inputWeight := inputWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ) :
    TSRecollb
      (n := n) factor :=
  Classical.choice <|
    SPFactora.induction_child_sources
      (motive := fun child _childRankDefect =>
        Nonempty
          (TSRecollb
            (n := n) child))
      scheduler.children
      (fun parent parentRankDefect ih =>
        ⟨scheduler.recollect parent parentRankDefect
          (fun task htask => Classical.choice (ih task htask))⟩)
      factor rankDefect

end
  RRSchedua

namespace CBWorka

/--
Recollect an exact concrete outer-bracket worklist using residual
recollections constructed by a global Hall-ranked scheduler.
-/
noncomputable def recollection_ranked_scheduler
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (scheduler :
      RRSchedua
        (d := d) (n := n) (inputWeight := inputWeight))
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      HEWord.tree inner.word =
        .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    TSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight PEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (factors packet hinputWeight inner right) :=
  recollection_basic_residuals packet hinputWeight inner right
    hinnerTruncated added originalRight unchanged originalLeft hinnerTree
      hRightLeft hRightUnchanged hunchangedBasic
        (fun task _htask =>
          scheduler.residualRecollection task.1 task.2)

end CBWorka
end TCTex
end Submission
