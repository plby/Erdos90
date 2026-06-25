import
  Towers.Group.Zassenhaus.GeneratedStructuralRouting
import Towers.Group.Zassenhaus.Contextual

/-!
# Outer-residual routing from generated structural restarts

Generated-child structural restart routing compiles the first classified
transient packet into the active packet factory used by contextual powered
collection.  This file packages that tighter active factory with the two
remaining one-layer powered recollections and feeds it into the Hall-ranked
outer-residual scheduler.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/--
Scheduler-facing generated structural restart inputs for contextual powered
outer residuals.
-/
structure
    CSRestara
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
      d n inputWeight activeRouting.generatedActiveFactory packet
        hinputWeight

namespace
  CSRestara

/-- Compile generated structural restart powered pieces into the ordinary
outer-residual factory consumed by Hall-ranked recursion. -/
noncomputable def outerRecollectionFactory
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    (routing :
      CSRestara
        d n inputWeight packet hinputWeight) :
    IRFtry
      d n inputWeight :=
  routing.pieces.outerRecollectionFactory

/--
Combine generated structural restart powered pieces with the ordinary
correction schedule and strictly-deeper normalizers.
-/
noncomputable def rankedFactoryRouting
    {d n inputWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {hinputWeight : 0 < inputWeight}
    (routing :
      CSRestara
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
  OFRoute.factory_powered_pieces
    schedule normalizerAbove routing.pieces

end
  CSRestara

namespace
  RRSchedua

/--
Construct one true concrete Hall-tree residual by ranked recursion from
generated structural restart powered routing and indexed local branch cases.
-/
noncomputable def
    recollect_restart_cases
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
      CSRestara
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
end Towers
