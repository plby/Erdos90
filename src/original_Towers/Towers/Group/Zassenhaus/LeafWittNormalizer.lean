import Towers.Group.Zassenhaus.RankedResidual

/-!
# Signed-leaf Hall-Witt inputs from parent-layer normalizers

The standard polynomial bound for one symbolic factor and a semantic
normalizer at its physical parent layer compile directly into the
unrestricted signed-leaf Hall-Witt strict-trace input.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


open HEWord
open
  LCSrc
open TWLeaf

universe u

namespace
  ELInput

/--
Compile the standard factor exponent polynomial using a semantic normalizer
at the expanded Jacobi packet's physical parent layer.
-/
noncomputable def ofNormalizer
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hparent :
      factor.word.weight PEAddres.weight + 1 < n)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
        (lowerWeight := factor.word.weight PEAddres.weight)
        (concreteBasicCommutators.{u} d)) :
    ELInput
      (n := n) factor decomposition := by
  have hweight := congrArg HallTree.weight decomposition.tree_eq
  simp only [HallTree.weight_commutator, tree_weight] at hweight
  exact
    {
      strictTrace :=
        headCoefficientNormalizer
          hn
          (by
            simpa only [hweight] using hparent)
          hinputWeight
          (by
            simpa only [hweight] using
                factor.exponent_valued_most
                  hinputWeight)
          (by
            simpa only [hweight] using normalizer)
    }

end
  ELInput

end TCTex
end Towers
