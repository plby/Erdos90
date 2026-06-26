import Submission.Group.Zassenhaus.ReductionOuterFactory
import Submission.Group.Zassenhaus.ResidualBranchCases

/-!
# Ranked residual cases with a full-weight outer-residual factory

The non-circular inner-reduction branch consumes an explicit factory for the
full-weight child-to-parent quotient.  Its other local inputs are the
correction factory, sharp active-atomic router, and next-stratum normalizer.

This file packages those inputs and compiles indexed local cases into the
global well-founded residual scheduler.  A complete normalizer family still
implements the interface as a compatibility path, but the scheduler no longer
requires a parent-stratum normalizer directly.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/-- Non-circular local routing inputs for every concrete symbolic factor. -/
structure OFRoute
    {d n inputWeight : ℕ} where
  factory :
    ∀ factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight,
      TSFtrya
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)
            (factor.word.weight PEAddres.weight)
  sharp :
    ∀ factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight,
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight)
          (concreteBasicCommutators.{u} d)
  nextNormalizer :
    ∀ factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight,
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight + 1)
          (concreteBasicCommutators.{u} d)
  outerFactory :
    IRFtry
      d n inputWeight

namespace
  OFRoute

/--
A correction schedule, strictly deeper normalizers, and the explicit
full-weight outer-residual factory supply every local input used by the
non-circular ranked scheduler.
-/
noncomputable def factory_above_outer
    {d n inputWeight : ℕ}
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
    (outerFactory :
      IRFtry
        d n inputWeight) :
    OFRoute
      (d := d) (n := n) (inputWeight := inputWeight) where
  factory factor :=
    schedule.factory
      (factor.word.weight PEAddres.weight)
  sharp factor :=
    SSNormal.ofNormalizerAbove
      (normalizerAbove
        (factor.word.weight PEAddres.weight))
  nextNormalizer factor :=
    normalizerAbove
      (factor.word.weight PEAddres.weight)
      (factor.word.weight PEAddres.weight + 1) (by omega)
  outerFactory := outerFactory

/--
A complete normalizer family and correction-factory schedule implement the
outer-factory routing interface.  This is the compatibility path for existing
global constructions.
-/
noncomputable def normalizers_factory_schedule
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (schedule :
      TFSched
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)) :
    OFRoute
      (d := d) (n := n) (inputWeight := inputWeight) :=
  factory_above_outer schedule
    (fun _lowerWeight strongerWeight _hstronger =>
      family.normalizer strongerWeight)
    (family.concreteRecollectionFactory hn hH)

end
  OFRoute

namespace RRBrancha

/-- Compile one indexed inner-reduction case through outer-factory routing. -/
noncomputable def innerOuterFactory
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      OFRoute
        (d := d) (n := n) (inputWeight := inputWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (branchCase :
      RankedInnerCase
        (n := n) factor rankDefect) :
    RRBrancha
      (n := n) factor rankDefect := by
  rcases branchCase with
    ⟨innerWord, rightWord, hword, hfactorTruncated, added, originalRight,
      unchanged, originalLeft, hinnerTree, hRightLeft, hRightUnchanged,
      hunchangedBasic, rankDefect_eq⟩
  subst rankDefect
  exact
    innerComparisonFactory hn hH factor
      (routing.factory factor) (routing.sharp factor)
        (routing.nextNormalizer factor) routing.outerFactory innerWord rightWord
          hword hfactorTruncated added originalRight unchanged originalLeft
            hinnerTree hRightLeft hRightUnchanged hunchangedBasic

/-- Compile either a leaf or an outer-factory inner-reduction local case. -/
noncomputable def outerFactoryCase
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      OFRoute
        (d := d) (n := n) (inputWeight := inputWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (branchCase :
      TruncatedBranchCase
        (n := n) factor rankDefect) :
    RRBrancha
      (n := n) factor rankDefect := by
  cases branchCase with
  | leaf leafCase =>
      exact ofLeafCase factor rankDefect leafCase
  | innerReductionOuter innerCase =>
      exact
        innerOuterFactory hn hH routing factor rankDefect
          innerCase

end RRBrancha

namespace
  RRSchedua

/-- Compile outer-factory routed indexed cases into a global residual scheduler. -/
noncomputable def outerFactoryCases
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      OFRoute
        (d := d) (n := n) (inputWeight := inputWeight))
    (cases :
      ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (rankDefect : ℕ),
        TruncatedBranchCase
          (n := n) factor rankDefect) :
    RRSchedua
      (d := d) (n := n) (inputWeight := inputWeight) :=
  ofBranches fun factor rankDefect =>
    RRBrancha.outerFactoryCase
      hn hH routing factor rankDefect (cases factor rankDefect)

/--
Run well-founded residual recursion directly from outer-factory routed indexed
local cases.
-/
noncomputable def recollect_factory_cases
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      OFRoute
        (d := d) (n := n) (inputWeight := inputWeight))
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
  (outerFactoryCases hn hH routing cases).residualRecollection
    factor rankDefect

end
  RRSchedua

end TCTex
end Submission
