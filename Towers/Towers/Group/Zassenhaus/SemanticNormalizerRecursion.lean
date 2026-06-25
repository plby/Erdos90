import Towers.Group.Zassenhaus.SemanticCorrectionDelegation

/-!
# Filtration recursion for semantic symbolic Hall power normalizers

Correction packets rise strictly in ordinary Hall weight.  Consequently, a
collector for stratum `lowerWeight` may recursively call a normalizer for
`lowerWeight + 1`.  Once `n ≤ 2 * lowerWeight`, the remaining stratum is
commutative and the semantic high-weight normalizer closes the recursion.

This file isolates the remaining local scheduler obligation and proves the
well-founded filtration recursion around it.  A universal Claim 5 constructor
is reduced to building the one-stratum insertion step.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
The local scheduler obligation at one support stratum: assuming correction
packets can be normalized one stratum higher, insert one factor into a
normalized endpoint at the current stratum.
-/
structure RIStep
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) : Prop where
  insert :
    ∀ lowerWeight : ℕ,
      TSNormalb
          (n := n) (inputWeight := inputWeight)
            (lowerWeight := lowerWeight + 1) H →
        TSInserta
          (n := n) (inputWeight := inputWeight)
            (lowerWeight := lowerWeight) H

namespace TSNormalb

/--
Successive-stratum insertion plus the commutative high-weight terminal case
constructs a semantic normalizer at every support stratum.
-/
noncomputable def recInsertionStep
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (step :
      RIStep
        (n := n) (inputWeight := inputWeight) H)
    (lowerWeight : ℕ) :
    TSNormalb
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H :=
  if hterminal : n ≤ 2 * lowerWeight then
    of_highWeight hn H hH hterminal
  else
    ofInsertionKernel
      (step.insert lowerWeight
        (recInsertionStep hn H hH step (lowerWeight + 1)))
termination_by n - lowerWeight
decreasing_by omega

end TSNormalb

namespace TSInput

/--
The filtration-recursion reduction for Claim 5.  It remains to construct the
one-stratum scheduler step for the chosen repeated-block source.
-/
theorem recursiveSemanticInsertion
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (step :
      RIStep
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.supportedSemanticNormalizer
    hsourceSupported
    (TSNormalb.recInsertionStep
      hn H hH step inputWeight)
    hinputWeight

end TSInput

end TCTex
end Towers
