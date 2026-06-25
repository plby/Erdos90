import Submission.Group.Zassenhaus.PolynomialRankedSupport
import Submission.Group.Zassenhaus.RankedStructuralRestarts

/-!
# Hall-ranked recursion for concrete polynomial basic residual recollections

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
structure
    TRSchedu
    {d n : ℕ}
    {ι : Type} where
  children :
    ∀ (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι)
      (rankDefect : ℕ),
      SPFactor.RCSrc
        (n := n) factor rankDefect
  recollect :
    ∀ (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι)
      (rankDefect : ℕ),
      (∀ task ∈ (children factor rankDefect).tasks,
        TRRecoll
          (n := n) task.1) →
        TRRecoll
          (n := n) factor

namespace
  TRSchedu

/--
Construct the concrete basic residual recollection for an arbitrary ranked
factor from a finite Hall-ranked scheduler.
-/
noncomputable def residualRecollection
    {d n : ℕ}
    {ι : Type}
    (scheduler :
      TRSchedu
        (d := d) (n := n) (ι := ι))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ) :
    TRRecoll
      (n := n) factor :=
  Classical.choice <|
    SPFactor.induction_child_sources
      (motive := fun child _childRankDefect =>
        Nonempty
          (TRRecoll
            (n := n) child))
      scheduler.children
      (fun parent parentRankDefect ih =>
        ⟨scheduler.recollect parent parentRankDefect
          (fun task htask => Classical.choice (ih task htask))⟩)
      factor rankDefect

end
  TRSchedu

namespace IBWork

/--
Recollect an exact concrete outer-bracket worklist using residual
recollections constructed by a global Hall-ranked scheduler.
-/
noncomputable def recollection_ranked_scheduler
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (scheduler :
      TRSchedu
        (d := d) (n := n) (ι := ι))
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      CEWord.tree inner.word =
        .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    SSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight HEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (factors packet inner right) :=
  recollection_basic_residuals packet inner right hinnerTruncated
    added originalRight unchanged originalLeft hinnerTree hRightLeft
      hRightUnchanged hunchangedBasic
        (fun task _htask =>
          scheduler.residualRecollection task.1 task.2)

end IBWork
end TCTex
end Submission
