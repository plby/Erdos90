import Towers.Group.Zassenhaus.RankedResidual
import
  Towers.Group.Zassenhaus.FixedRestartRouting

/-!
# Unrestricted signed-leaf Hall-Witt retained traces from fixed-packet restarts

Fixed-packet generated structural restart routing supplies the outer residual
factory.  Unrestricted signed-leaf Hall-Witt strict-trace sources supply the
remaining positive expanded-Jacobi value packets.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


open HEWord

universe u

/--
Fixed-packet restart inputs after positive expanded-Jacobi packets have been
replaced by unrestricted signed-leaf Hall-Witt strict-trace sources.
-/
structure
    LRBuild
    {d n inputWeight : ℕ} where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  hinputWeight :
    0 < inputWeight
  routing :
    PRRouteb
      d n inputWeight packet hinputWeight
  rootCase :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TruncatedBranchCase
            (n := n) factor 0
  root_case_tree :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (hfactorWeight :
        factor.word.weight PEAddres.weight = lowerWeight)
      (hfactorTruncated :
        factor.word.weight PEAddres.weight < n)
      (innerCase :
        RankedInnerCase
          (n := n) factor 0),
      rootCase lowerWeight factor hfactorWeight hfactorTruncated =
          .innerReductionOuter innerCase →
        tree innerCase.rightWord = innerCase.unchanged
  valueStrictTrace :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          ELInput
            (n := n) factor ranked.decomposition

namespace
  LRBuild

/--
Forget fixed-packet restart routing as the outer factory of the unrestricted
signed-leaf Hall-Witt retained-trace collector.
-/
noncomputable def leafDirectBuilder
    {d n inputWeight : ℕ}
    (builder :
      LRBuild.{u}
        (d := d) (n := n) (inputWeight := inputWeight)) :
    TLBuild.{u}
      (d := d) (n := n) (inputWeight := inputWeight) where
  outerFactory :=
    builder.routing.outerRecollectionFactory
  rootCase :=
    builder.rootCase
  root_case_tree :=
    builder.root_case_tree
  valueStrictTrace :=
    builder.valueStrictTrace

end
  LRBuild

end TCTex
end Towers
