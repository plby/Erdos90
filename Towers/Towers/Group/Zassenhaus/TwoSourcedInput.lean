import Towers.Group.Zassenhaus.ClassTwo
import Towers.Group.Zassenhaus.ReachableUniversalReduction
import Towers.Group.Zassenhaus.RestrictedSharp

/-!
# Explicit class-two sources for recursive symbolic Hall-power collectors

In the class-two region `n ≤ 3 * inputWeight`, the finite powered-block source
is already explicit: original Hall atoms carry `choose q 1`, and ordered pairs
carry their commutator corrections with `choose q 2`.

This file packages that source for the semantic recursive collectors.  The
class-two scheduler proves the support invariant needed to start recursion.
The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace TSInput

/--
The explicit truncated class-two powered source is a correctly sourced input
for semantic coordinate collection.
-/
noncomputable def classTwoSource
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0) :
    TSInput
      (n := n) (inputWeight := inputWeight) H e where
  source :=
    truncatedSourceFactors
      (n := n) (inputWeight := inputWeight) e
  source_isTruncated :=
    truncated_source_factors e
  list_eval_source :=
    list_truncated_factors
      hinputWeight hcutoff e heBelow

/--
Every retained factor in the explicit class-two source remains above the
initial Hall weight.
-/
lemma least_two_source
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (e : HEFam H)
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0) :
    SPFactora.WordWeightLeast inputWeight
      ((classTwoSource hinputWeight hcutoff e heBelow).source) := by
  intro factor hfactor
  exact
    SSAtom.input_truncate_factors
      (collectedHallAtoms (n := n) (inputWeight := inputWeight) e)
      hfactor

/--
In the class-two source region, a reachable universal collector constructs
the Claim 5 coordinate polynomials.
-/
theorem
    reachable_universal_builder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    {e : HEFam H}
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (builder :
      TDBuild
        (n := n) (inputWeight := inputWeight) H) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  reachableDerivationBuilder
    hn H hH (classTwoSource hinputWeight hcutoff e heBelow)
      (least_two_source hinputWeight hcutoff e heBelow)
        builder hinputWeight

/--
In the class-two source region, restricted sharp recursive data constructs
the Claim 5 coordinate polynomials.
-/
theorem
    sharp_recursive_builder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    {e : HEFam H}
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (builder :
      RSRec
        (n := n) (inputWeight := inputWeight) hn H hH) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  restrictedSharpRecursive
    hn H hH (classTwoSource hinputWeight hcutoff e heBelow)
      (least_two_source hinputWeight hcutoff e heBelow)
        builder hinputWeight

/--
In the class-two source region, correction expansions and singleton
recollections construct the Claim 5 coordinate polynomials.
-/
theorem
    sharp_singleton_builder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    {e : HEFam H}
    (heBelow : ∀ s : ℕ, s < inputWeight → e s = 0)
    (builder :
      TSBuildd
        (n := n) (inputWeight := inputWeight) hn H hH) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  restrictedSingletonBuilder
    hn H hH (classTwoSource hinputWeight hcutoff e heBelow)
      (least_two_source hinputWeight hcutoff e heBelow)
        builder hinputWeight

end TSInput

end TCTex
end Towers
