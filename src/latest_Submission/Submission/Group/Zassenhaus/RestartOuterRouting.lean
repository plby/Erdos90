import Submission.Group.Zassenhaus.StructuralActiveFactory
import Submission.Group.Zassenhaus.Contextual

/-!
# Concrete outer-residual routing from structural transient restarts

Structural restart routing compiles the first classified transient packet
into the active packet factory used by contextual powered collection.  Two
one-layer semantic recollections still remain: the Hall-child comparison and
the transient bridge quotient.

This file keeps those obligations explicit, packages them with the compiled
active factory, and feeds the result into the existing concrete Hall-ranked
outer-residual scheduler.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
Scheduler-facing structural restart inputs for contextual powered outer
residuals.

The packet-ordering and smaller-root obligations live in `activeRouting`.
The one-layer comparison and bridge recollections remain visible in `pieces`.
-/
structure
    PSRestar
    (d n inputWeight : ℕ)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight) where
  activeRouting :
    CSRestar
      d n inputWeight (concreteBasicCommutators.{u} d)
  pieces :
    CPFtry
      d n inputWeight activeRouting.toActiveFactory packet hinputWeight

namespace
  PSRestar

open OFRoute

/-- Compile structural-restart powered pieces into the ordinary outer-residual
factory consumed by Hall-ranked recursion. -/
noncomputable def outerRecollectionFactory
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    (routing :
      PSRestar
        d n inputWeight packet hinputWeight) :
    IRFtry
      d n inputWeight :=
  routing.pieces.outerRecollectionFactory

/--
Combine structural-restart powered pieces with the ordinary correction
schedule and strictly-deeper normalizers expected by Hall-ranked recursion.
-/
noncomputable def rankedFactoryRouting
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    (routing :
      PSRestar
        d n inputWeight packet hinputWeight)
    (schedule :
      TFSched
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (normalizerAbove :
      ∀ lowerWeight strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d)) :
    OFRoute
      (d := d) (n := n) (inputWeight := inputWeight) :=
  factory_powered_pieces
    schedule normalizerAbove routing.pieces

end
  PSRestar

namespace
  RRSchedua

/--
Construct one true concrete Hall-tree residual by ranked recursion from
structural-restart powered routing and indexed local branch cases.
-/
noncomputable def
    structural_factory_cases
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    (routing :
      PSRestar
        d n inputWeight packet hinputWeight)
    (schedule :
      TFSched
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (normalizerAbove :
      ∀ lowerWeight strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (cases :
      ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (rankDefect : ℕ),
        TruncatedBranchCase
          (n := n) factor rankDefect)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ) :
    TSRecollb
      (n := n) factor :=
  recollect_factory_cases hn hH
    (routing.rankedFactoryRouting schedule normalizerAbove)
      cases factor rankDefect

end
  RRSchedua

end TCTex
end Submission
