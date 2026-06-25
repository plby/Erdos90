import Submission.Group.Zassenhaus.ConcreteAutomaticComparison
import Submission.Group.Zassenhaus.FactoryBranchCases
import Submission.Group.Zassenhaus.ResidualBranchCases
import Submission.Group.Zassenhaus.SharpComparisonRecollection
import Submission.Group.Zassenhaus.HallSupportMonotonicity
import Submission.Group.Zassenhaus.RetainedInsertionCollection
import Submission.Group.Zassenhaus.ResidualBasicChildren
import Submission.Group.Zassenhaus.Jacobi
import Submission.Group.Zassenhaus.CanonicalHallRecollection
import Submission.Group.Zassenhaus.ValueNamedNormalization
import Submission.Group.Zassenhaus.ConcreteValueNormalization
import
  Submission.Group.Zassenhaus.FixedRestartRouting
import Submission.Group.Zassenhaus.EndpointInterpolationNormalizer
import Submission.Group.Zassenhaus.IntegralStrictTail


-- Merged from ResidualRestrictedSharpFactorResidual.lean

/-!
# Ranked Hall-power residuals as restricted-sharp factor tails

The ranked concrete residual scheduler constructs the true basic-reduction
residual without a parent-stratum normalizer. Restricted-sharp atomic
normalization independently recollects the concrete-to-semantic comparison.
Composing those two higher sources gives the intrinsic factor tail consumed by
direct Hall-power recursion.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace
  OFRoute

/--
Compile ranked outer-factory cases into the intrinsic restricted-sharp factor
tail at one active support weight.
-/
noncomputable def outer_factory_cases
    {d n inputWeight lowerWeight : ℕ}
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
    (rankDefect : ℕ)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSExp
      (lowerWeight := lowerWeight) hn (concreteBasicCommutators.{u} d) hH
        factor := by
  subst lowerWeight
  exact
    ((RRSchedua.recollect_factory_cases
        hn hH routing cases factor rankDefect).intrinsicResidualSource
          (TCRecoll.of_atomicNorm
            hn hH factor rfl hfactorTruncated
              (routing.factory factor) (routing.sharp factor)
                (routing.nextNormalizer factor))
          rfl).factorExpansion

end
  OFRoute

end TCTex
end Submission

-- Merged from ResidualSharpComparisonBranchCases.lean

/-!
# Ranked residual cases with sharp inner-reduction comparison

The sharp inner-reduction branch uses only local routing data: a normalizer
for its child-to-parent quotient, a correction factory and sharp router for
its active atomic comparison, and a next-stratum normalizer.  This file
packages those inputs and compiles indexed local branch cases into the global
well-founded residual scheduler.

A normalizer family and correction-factory schedule provide the routing data
automa.  Keeping the local structure explicit also records the
strictly smaller interface needed by the recursive inner-reduction branch.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/-- Local sharp routing inputs for every concrete symbolic factor. -/
structure SCRoutea
    {d n inputWeight : ℕ} where
  normalizer :
    ∀ factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight,
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight)
          (concreteBasicCommutators.{u} d)
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

namespace
  SCRoutea

/--
A complete normalizer family and correction-factory schedule provide every
local routing input used by the sharp inner-reduction branch.
-/
noncomputable def normalizers_factory_schedule
    {d n inputWeight : ℕ}
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (schedule :
      TFSched
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)) :
    SCRoutea
      (d := d) (n := n) (inputWeight := inputWeight) where
  normalizer factor :=
    family.normalizer
      (factor.word.weight PEAddres.weight)
  factory factor :=
    schedule.factory
      (factor.word.weight PEAddres.weight)
  sharp _factor :=
    SSNormal.ofNormalizerAbove
      (fun strongerWeight _hstronger => family.normalizer strongerWeight)
  nextNormalizer factor :=
    family.normalizer
      (factor.word.weight PEAddres.weight + 1)

end
  SCRoutea

namespace RRBrancha

/-- Compile one indexed inner-reduction case through sharp comparison routing. -/
noncomputable def sharpComparisonCase
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      SCRoutea
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
    inner_sharp_comparison hn hH factor
      (routing.normalizer factor) (routing.factory factor)
        (routing.sharp factor) (routing.nextNormalizer factor)
          innerWord rightWord hword hfactorTruncated added originalRight
            unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
              hunchangedBasic

/-- Compile either a leaf or a sharply routed inner-reduction local case. -/
noncomputable def sharpCase
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      SCRoutea
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
        sharpComparisonCase hn hH routing factor
          rankDefect innerCase

end RRBrancha

namespace
  RRSchedua

/-- Compile sharply routed indexed cases into a global residual scheduler. -/
noncomputable def sharpComparisonCases
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      SCRoutea
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
    RRBrancha.sharpCase
      hn hH routing factor rankDefect (cases factor rankDefect)

/--
Run well-founded residual recursion directly from sharply routed indexed
local cases.
-/
noncomputable def sharp_comparison_cases
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      SCRoutea
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
  (sharpComparisonCases hn hH routing cases).residualRecollection
    factor rankDefect

end
  RRSchedua

end TCTex
end Submission

-- Merged from ResidualSupportedOuterFactoryCollection.lean

/-!
# Support-local ranked Hall-power residual collection

The original ranked outer-factory routing record asks for normalizers above
every symbolic factor. Direct filtration recursion only has to route factors
reachable from one active support stratum. This file narrows the routing
interface accordingly and runs the Hall-ranked residual recursion while
preserving that support bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/-- Outer-factory routing restricted to factors supported in one active stratum. -/
structure
    SFRoute
    {d n inputWeight lowerWeight : ℕ} where
  factory :
    ∀ factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight,
      lowerWeight ≤ factor.word.weight PEAddres.weight →
        TSFtrya
          (n := n) (inputWeight := inputWeight)
            (concreteBasicCommutators.{u} d)
              (factor.word.weight PEAddres.weight)
  sharp :
    ∀ factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight,
      lowerWeight ≤ factor.word.weight PEAddres.weight →
        SSNormal
          (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight)
          (concreteBasicCommutators.{u} d)
  nextNormalizer :
    ∀ factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight,
      lowerWeight ≤ factor.word.weight PEAddres.weight →
        TSNormalb
          (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight + 1)
          (concreteBasicCommutators.{u} d)
  outerFactory :
    IRFtry
      d n inputWeight

namespace
  SFRoute

/--
A correction schedule, normalizers strictly above the active support bound,
and a full-weight outer residual factory supply support-local ranked routing.
-/
noncomputable def factory_above_outer
    {d n inputWeight lowerWeight : ℕ}
    (schedule :
      TFSched
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (outerFactory :
      IRFtry
        d n inputWeight) :
    SFRoute
      (d := d) (n := n) (inputWeight := inputWeight)
        (lowerWeight := lowerWeight) where
  factory factor _hfactorSupported :=
    schedule.factory
      (factor.word.weight PEAddres.weight)
  sharp factor hfactorSupported :=
    SSNormal.ofNormalizerAbove
      (fun strongerWeight hstronger =>
        normalizerAbove strongerWeight
          (hfactorSupported.trans_lt hstronger))
  nextNormalizer factor hfactorSupported :=
    normalizerAbove
      (factor.word.weight PEAddres.weight + 1)
      (by omega)
  outerFactory := outerFactory

end
  SFRoute

namespace RRBrancha

/-- Compile one support-local leaf or inner-reduction case. -/
noncomputable def supported_factory_case
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      SFRoute
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (hfactorSupported :
      lowerWeight ≤ factor.word.weight PEAddres.weight)
    (branchCase :
      TruncatedBranchCase
        (n := n) factor rankDefect) :
    RRBrancha
      (n := n) factor rankDefect := by
  cases branchCase with
  | leaf leafCase =>
      exact ofLeafCase factor rankDefect leafCase
  | innerReductionOuter innerCase =>
      rcases innerCase with
        ⟨innerWord, rightWord, hword, hfactorTruncated, added, originalRight,
          unchanged, originalLeft, hinnerTree, hRightLeft, hRightUnchanged,
          hunchangedBasic, rankDefect_eq⟩
      subst rankDefect
      exact
        innerComparisonFactory hn hH factor
          (routing.factory factor hfactorSupported)
          (routing.sharp factor hfactorSupported)
          (routing.nextNormalizer factor hfactorSupported)
          routing.outerFactory innerWord rightWord hword hfactorTruncated added
          originalRight unchanged originalLeft hinnerTree hRightLeft
          hRightUnchanged hunchangedBasic

/-- Every recursive task emitted by a support-local branch preserves full weight. -/
lemma word_outer_factory
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      SFRoute
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (hfactorSupported :
      lowerWeight ≤ factor.word.weight PEAddres.weight)
    (branchCase :
      TruncatedBranchCase
        (n := n) factor rankDefect)
    {task :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight ×
        ℕ}
    (htask :
      task ∈
        (supported_factory_case hn hH routing factor rankDefect
          hfactorSupported branchCase).children.tasks) :
    task.1.word.weight PEAddres.weight =
      factor.word.weight PEAddres.weight := by
  cases branchCase with
  | leaf leafCase =>
      cases leafCase <;>
        simp [supported_factory_case, ofLeafCase, leaf_of_terminal,
          leaf_tree_basic, leaf_commutator_self,
          leaf_reversed_basic, leaf_weight_one,
          ofResidRecollect,
          SPFactora.RCSrc.empty] at htask
  | innerReductionOuter innerCase =>
      rcases innerCase with
        ⟨innerWord, rightWord, hword, hfactorTruncated, added, originalRight,
          unchanged, originalLeft, hinnerTree, hRightLeft, hRightUnchanged,
          hunchangedBasic, rankDefect_eq⟩
      subst rankDefect
      have htask' :
          task ∈
            CIChildr.rankedTasks
              factor innerWord rightWord hword unchanged := by
        simpa only [supported_factory_case,
          innerComparisonFactory,
          CIChildr.tasks_ranked_task]
          using htask
      rcases
          CIChildr.index_ranked_tasks
            factor innerWord rightWord hword unchanged htask' with
        ⟨i, rfl⟩
      exact
        HEWord.inner_outer_factor
          factor innerWord rightWord hword i

end RRBrancha

namespace
  SFRoute

/--
Run Hall-ranked recursion using only routing data supported in the active
stratum.
-/
noncomputable def residual_recollection_cases
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      SFRoute
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight))
    (cases :
      ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (rankDefect : ℕ),
        lowerWeight ≤ factor.word.weight PEAddres.weight →
          factor.word.weight PEAddres.weight < n →
            TruncatedBranchCase
              (n := n) factor rankDefect)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (hfactorSupported :
      lowerWeight ≤ factor.word.weight PEAddres.weight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecollb
      (n := n) factor :=
  Classical.choice <|
    SPFactora.ranked_descends_induction
      (motive := fun child childRankDefect =>
        lowerWeight ≤ child.word.weight PEAddres.weight →
          child.word.weight PEAddres.weight < n →
            Nonempty
              (TSRecollb
                (n := n) child))
      (fun parent parentRankDefect ih hparentSupported hparentTruncated =>
        let branch :=
          RRBrancha.supported_factory_case
            hn hH routing parent parentRankDefect hparentSupported
              (cases parent parentRankDefect hparentSupported hparentTruncated)
        ⟨branch.recollect fun task htask =>
          Classical.choice <|
            ih task.1 task.2 (branch.children.tasks_descend task htask)
              (by
                rw [
                  RRBrancha.word_outer_factory
                    hn hH routing parent parentRankDefect hparentSupported
                      (cases parent parentRankDefect hparentSupported
                        hparentTruncated) htask]
                exact hparentSupported)
              (by
                rw [
                  RRBrancha.word_outer_factory
                    hn hH routing parent parentRankDefect hparentSupported
                      (cases parent parentRankDefect hparentSupported
                        hparentTruncated) htask]
                exact hparentTruncated)⟩)
      factor rankDefect hfactorSupported hfactorTruncated

/--
Compile support-local ranked residual recursion and atomic comparison into
the intrinsic restricted-sharp factor tail.
-/
noncomputable def factor_expansion_cases
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      SFRoute
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight))
    (cases :
      ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (rankDefect : ℕ),
        lowerWeight ≤ factor.word.weight PEAddres.weight →
          factor.word.weight PEAddres.weight < n →
            TruncatedBranchCase
              (n := n) factor rankDefect)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSExp
      (lowerWeight := lowerWeight) hn (concreteBasicCommutators.{u} d) hH
        factor := by
  subst lowerWeight
  exact
    ((routing.residual_recollection_cases hn hH cases factor rankDefect le_rfl
        hfactorTruncated).intrinsicResidualSource
          (TCRecoll.of_atomicNorm
            hn hH factor rfl hfactorTruncated
              (routing.factory factor le_rfl) (routing.sharp factor le_rfl)
                (routing.nextNormalizer factor le_rfl))
          rfl).factorExpansion

/--
Run support-local Hall-ranked recursion from classifiers restricted to the
active full weight. Every emitted child preserves that exact word weight.
-/
noncomputable def recollection_exact_cases
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      SFRoute
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight))
    (cases :
      ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (rankDefect : ℕ),
        factor.word.weight PEAddres.weight = lowerWeight →
          factor.word.weight PEAddres.weight < n →
            TruncatedBranchCase
              (n := n) factor rankDefect)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecollb
      (n := n) factor :=
  Classical.choice <|
    SPFactora.ranked_descends_induction
      (motive := fun child childRankDefect =>
        child.word.weight PEAddres.weight = lowerWeight →
          child.word.weight PEAddres.weight < n →
            Nonempty
              (TSRecollb
                (n := n) child))
      (fun parent parentRankDefect ih hparentWeight hparentTruncated =>
        let branch :=
          RRBrancha.supported_factory_case
            hn hH routing parent parentRankDefect (by omega)
              (cases parent parentRankDefect hparentWeight hparentTruncated)
        ⟨branch.recollect fun task htask =>
          Classical.choice <|
            ih task.1 task.2 (branch.children.tasks_descend task htask)
              (by
                rw [
                  RRBrancha.word_outer_factory
                    hn hH routing parent parentRankDefect (by omega)
                      (cases parent parentRankDefect hparentWeight
                        hparentTruncated) htask]
                exact hparentWeight)
              (by
                rw [
                  RRBrancha.word_outer_factory
                    hn hH routing parent parentRankDefect (by omega)
                      (cases parent parentRankDefect hparentWeight
                        hparentTruncated) htask]
                exact hparentTruncated)⟩)
      factor rankDefect hfactorWeight hfactorTruncated

/--
Compile exact-active-weight ranked classifiers and atomic comparison into the
intrinsic restricted-sharp factor tail.
-/
noncomputable def expansion_exact_cases
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      SFRoute
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight))
    (cases :
      ∀ (factor :
          SPFactora
            (concreteBasicCommutators.{u} d) inputWeight)
        (rankDefect : ℕ),
        factor.word.weight PEAddres.weight = lowerWeight →
          factor.word.weight PEAddres.weight < n →
            TruncatedBranchCase
              (n := n) factor rankDefect)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSExp
      (lowerWeight := lowerWeight) hn (concreteBasicCommutators.{u} d) hH
        factor := by
  subst lowerWeight
  exact
    ((routing.recollection_exact_cases hn hH cases factor
        rankDefect rfl hfactorTruncated).intrinsicResidualSource
          (TCRecoll.of_atomicNorm
            hn hH factor rfl hfactorTruncated
              (routing.factory factor le_rfl) (routing.sharp factor le_rfl)
                (routing.nextNormalizer factor le_rfl))
          rfl).factorExpansion

end
  SFRoute

end TCTex
end Submission

-- Merged from ResidualRetainedRecipeCoefficientTraceCollection.lean

/-!
# Hall-power collection from retained recipe traces and ranked outer factories

The retained recipe-coefficient law supplies the powered correction packet at
every support stratum. Support-local Hall-ranked residual recursion supplies
the remaining exact-weight factor tail from a full-weight outer residual
factory and branch classifications.

This file compiles those inputs directly to global Hall-power recollection
polynomials. It is intentionally not imported by the existing collection
proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  CCThree
open
  CPSplita

/--
The remaining concrete powered inputs after retained recipe packets and
support-local ranked recursion have been compiled into the collector.
-/
structure
    TCBuildb
    {d n inputWeight : ℕ} where
  outerFactory :
    IRFtry
      d n inputWeight
  cases :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (rankDefect : ℕ),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TruncatedBranchCase
            (n := n) factor rankDefect

namespace
  TCBuildb

open
  TAExp
open
  TAResolua

/-- Compile retained recipe coefficients to a powered packet at every stratum. -/
noncomputable def supportedFactorySchedule
    {d n inputWeight : ℕ}
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n) :
    TFSched
      (n := n) (inputWeight := inputWeight)
        (concreteBasicCommutators.{u} d) where
  factory lowerWeight :=
    TDBuild.retainedRecipeFactory
      (lowerWeight := lowerWeight) hinputWeight hrecipes

/--
Construct the global Hall-power semantic normalizer by support recursion.
Recursive uses occur only at strictly larger support weights, including the
normalizers used inside support-local Hall-ranked residual collection.
-/
noncomputable def semanticCoordinateNormalizer
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (builder :
      TCBuildb.{u}
        (d := d) (n := n) (inputWeight := inputWeight))
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowerWeight : ℕ) :
    TSNormalb
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight)
        (concreteBasicCommutators.{u} d) :=
  if hterminal : n ≤ 2 * lowerWeight then
    TSNormalb.of_highWeight
      hn (concreteBasicCommutators.{u} d)
        (fun r hr hrn =>
          concrete_forms_associated d n r hr
            hrn)
        hterminal
  else
    TSNormalb.ofInsertionKernel
      { insert := by
          intro coordinates factor hcoordinates hfactorSupported
            hfactorTruncated
          let hH :=
            fun r hr hrn =>
              concrete_forms_associated d n r hr
                hrn
          let nextNormalizer :=
            builder.semanticCoordinateNormalizer
              hn hinputWeight hrecipes (lowerWeight + 1)
          by_cases hfactorStrict :
              lowerWeight <
                factor.word.weight PEAddres.weight
          · exact
              nextNormalizer.insertion_word_weight coordinates
                factor hcoordinates hfactorStrict hfactorTruncated
          · have hfactorWeight :
                factor.word.weight PEAddres.weight =
                  lowerWeight := by
              omega
            let schedule :=
              supportedFactorySchedule
                hinputWeight hrecipes
            let normalizerAbove :=
              fun strongerWeight
                  (_hstronger : lowerWeight < strongerWeight) =>
                builder.semanticCoordinateNormalizer
                  hn hinputWeight hrecipes strongerWeight
            let routing :=
              SFRoute.factory_above_outer
                schedule normalizerAbove builder.outerFactory
            let packetFactory := schedule.factory lowerWeight
            let sharp :
                SSNormal
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight)
                      (concreteBasicCommutators.{u} d) :=
              SSNormal.ofNormalizerAbove
                normalizerAbove
            let factorTail :=
              routing.expansion_exact_cases hn hH
                (builder.cases lowerWeight) factor 0 hfactorWeight
                  hfactorTruncated
            let merge :=
              (packetFactory
                |>.semantic_merge_sharp
                  hn (concreteBasicCommutators.{u} d) hH sharp coordinates
                    factor)
                |>.mergeResidualExpansion hfactorWeight hfactorTruncated
            let block :=
              mergeFactor merge factorTail
            let tail :=
              (packetFactory
                |>.supported_route_sharp
                  sharp coordinates factor hfactorWeight)
                |>.higherTailResolution hfactorWeight hfactorTruncated
            exact
              (active_block_tail
                hcoordinates hfactorWeight hfactorTruncated
                  (block.activeBlockResolution hcoordinates
                    hfactorWeight)
                  tail)
                |>.exists_insertion nextNormalizer hfactorWeight
                  hfactorTruncated }
termination_by n - lowerWeight
decreasing_by
  all_goals
    have hlowerWeightCutoff : lowerWeight < n := by
      omega
    omega

end
  TCBuildb

namespace TSInput

/--
Retained recipe traces and support-local ranked outer residual data construct
the canonical Claim 5 polynomials for a supported sourced input.
-/
theorem
    coordCoeffBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (builder :
      TCBuildb.{u}
        (d := d) (n := n) (inputWeight := inputWeight)) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.supportedSemanticNormalizer
    hsourceSupported
      (builder.semanticCoordinateNormalizer
        hn hinputWeight hrecipes inputWeight)
      hinputWeight

end TSInput

/--
In the automatic class-two source range, retained recipe traces and
support-local ranked outer residual data construct the canonical Claim 5
power package.
-/
theorem
    commutators_ranked_below
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (builder :
      TCBuildb.{u}
        (d := d) (n := n) (inputWeight := inputWeight))
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)} :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e
        inputWeight := by
  intro heBelow
  let e' : HEFam (concreteBasicCommutators.{u} d) :=
    HEFam.zeroBelow e inputWeight
  have he'Below :
      ∀ s : ℕ, s < inputWeight → e' s = 0 := by
    intro s hs
    simp [e', hs]
  have he'Product :
      collectedHallProduct
          (n := n) (concreteBasicCommutators.{u} d) e' =
        collectedHallProduct
          (n := n) (concreteBasicCommutators.{u} d) e := by
    simpa [e'] using collected_below_self e heBelow
  rcases
      (TSInput.coordCoeffBuilder
          hn
          (TSInput.classTwoSource
            hinputWeight hcutoff e' he'Below)
          (TSInput.least_two_source
            hinputWeight hcutoff e' he'Below)
          hinputWeight hrecipes builder)
        (fun s _hs hs _hsn => he'Below s hs) with
    ⟨E, hEproduct, hEpolynomial⟩
  refine ⟨E, ?_, hEpolynomial⟩
  intro q
  exact (hEproduct q).trans (congrArg (fun x => x ^ q) he'Product)

/--
Retained recipe traces construct the full canonical Claim 5 power input once
supported low-weight sources and ranked outer residual builders are supplied.
-/
theorem
    commutators_poly_builders
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (builders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          TCBuildb.{u}
            (d := d) (n := n) (inputWeight := inputWeight)) :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) (concreteCommutatorsWeight.{u} d) e
            inputWeight := by
  intro e inputWeight hinputWeight
  by_cases hclassTwoRange : n ≤ 3 * inputWeight
  · exact
      commutators_ranked_below
        hn hinputWeight hclassTwoRange hrecipes
          (builders inputWeight hinputWeight)
  · exact
      TSInput.coordCoeffBuilder
        hn
          (lowWeightSource e inputWeight hinputWeight hclassTwoRange)
          (lowWeightSupported e inputWeight hinputWeight hclassTwoRange)
          hinputWeight hrecipes (builders inputWeight hinputWeight)

end TCTex
end Submission

-- Merged from ResidualSupportedBasicChildrenCollection.lean

/-!
# Support-local reachable scheduling for Hall-power residuals

An arbitrary active-stratum factor needs one root classification. After a
recipe-correct inner reduction, every recursive task is a bracket of two
Hall-basic trees. This file combines support-local outer-factory routing with
the structural two-basic-child scheduler: recursive children are classified
internally, while the caller supplies only Jacobi value residuals and swap
residuals at the active weight.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HEWord

/--
Support-local outer routing together with the two semantic residuals exposed
by structural Jacobi orientation.
-/
structure
    RCRoute
    {d n inputWeight lowerWeight : ℕ} where
  outerRouting :
    SFRoute.{u}
      (d := d) (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight)
  valueResidual :
    ∀
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TJRecoll
            (n := n) factor ranked.decomposition
  swapValueInverse :
    ∀
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (left right : HallTree (FreeGenerator.{u} d))
      (hleftBasic : left.IsBasic)
      (hrightBasic : right.IsBasic)
      (htree : tree factor.word = .commutator left right),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TIRecoll
            (n := n) factor left right hleftBasic hrightBasic htree

namespace
  RCRoute

/-- Recursive reachable tasks remain inside the active full-weight stratum. -/
def Reachable
    {d n inputWeight lowerWeight : ℕ}
    (_routing :
      RCRoute
        (d := d) (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ) : Prop :=
  factor.word.weight PEAddres.weight = lowerWeight ∧
    Nonempty
      (TCReacha
        (n := n) factor rankDefect)

end
  RCRoute

namespace
  TCReacha

/--
Every child emitted by a support-local indexed branch is a reachable
two-basic-child task.
-/
noncomputable def children_factory_case
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      SFRoute
        (d := d) (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (hfactorSupported :
      lowerWeight ≤ factor.word.weight PEAddres.weight)
    (branchCase :
      TruncatedBranchCase
        (n := n) factor rankDefect)
    (hrightTree :
      ∀ innerCase,
        branchCase = .innerReductionOuter innerCase →
          tree innerCase.rightWord = innerCase.unchanged)
    {task :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight ×
        ℕ}
    (htask :
      task ∈
        (RRBrancha.supported_factory_case
          hn hH routing factor rankDefect hfactorSupported branchCase).children.tasks) :
    TCReacha
      (n := n) task.1 task.2 := by
  cases branchCase with
  | leaf leafCase =>
      cases leafCase <;>
        simp [
          RRBrancha.supported_factory_case,
          RRBrancha.ofLeafCase,
          RRBrancha.leaf_of_terminal,
          RRBrancha.leaf_tree_basic,
          RRBrancha.leaf_commutator_self,
          RRBrancha.leaf_reversed_basic,
          RRBrancha.leaf_weight_one,
          RRBrancha.ofResidRecollect,
          SPFactora.RCSrc.empty] at htask
  | innerReductionOuter innerCase =>
      have hrightTree' := hrightTree innerCase rfl
      rcases innerCase with
        ⟨innerWord, rightWord, hword, hfactorTruncated, added, originalRight,
          unchanged, originalLeft, hinnerTree, hRightLeft, hRightUnchanged,
          hunchangedBasic, rankDefect_eq⟩
      subst rankDefect
      exact
        ranked_tasks factor innerWord rightWord hword unchanged
          hrightTree' hunchangedBasic hfactorTruncated (by
            simpa only [
              RRBrancha.supported_factory_case,
              RRBrancha.innerComparisonFactory,
              CIChildr.tasks_ranked_task]
              using htask)

end
  TCReacha

namespace
  RRBrancha

/--
Flatten one support-local expanded Jacobi root and the inner reductions of its
two descendants into a single strict branch.
-/
noncomputable def supported_ranked_decomp
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      RCRoute
        (d := d) (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (ranked :
      TRDecomp
        factor)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    RRBrancha
      (n := n) factor
        (expandedParentDefect ranked.decomposition) := by
  let first :=
    supported_factory_case hn hH routing.outerRouting
      (expandedJacobiFactor factor ranked.decomposition)
      (expandedParentDefect ranked.decomposition)
      (by
        simpa only [expanded_jacobi_factor, hfactorWeight] using
          (le_refl lowerWeight))
      (.innerReductionOuter (ranked.firstCase hfactorTruncated))
  let second :=
    supported_factory_case hn hH routing.outerRouting
      (expandedJacobiSecond factor ranked.decomposition)
      (expandedParentDefect ranked.decomposition)
      (by
        simpa only [expanded_second_factor, hfactorWeight] using
          (le_refl lowerWeight))
      (.innerReductionOuter (ranked.secondCase hfactorTruncated))
  exact
    {
      children :=
        (first.children.reparent
          (expanded_jacobi_factor
            factor ranked.decomposition)).append
          (second.children.reparent
            (expanded_second_factor
              factor ranked.decomposition))
      recollect := fun residual =>
        let firstResidual :=
          first.recollect fun task htask =>
            residual task (List.mem_append_left _ htask)
        let secondResidual :=
          second.recollect fun task htask =>
            residual task (List.mem_append_right _ htask)
        let continuation :=
          CDRecoll.of_routedFirst
            (routing.outerRouting.factory factor (by omega))
            (routing.outerRouting.sharp factor (by omega))
            factor ranked.decomposition rfl hfactorTruncated
            firstResidual secondResidual
              (routing.valueResidual factor ranked hfactorWeight
                hfactorTruncated).toInverseRecollection
        TSRecollb.expanded_reduction
          hn hH
          (routing.outerRouting.factory factor (by omega))
          (routing.outerRouting.sharp factor (by omega))
          (routing.outerRouting.nextNormalizer factor (by omega))
          factor ranked.decomposition rfl hfactorTruncated
          continuation.expandedContinuationRecollection
    }

/-- Every child of the flattened support-local Jacobi branch has full weight. -/
lemma word_expanded_jacobi
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      RCRoute
        (d := d) (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (ranked :
      TRDecomp
        factor)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    {task :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight ×
        ℕ}
    (htask :
      task ∈
        (supported_ranked_decomp hn hH routing factor
          ranked hfactorWeight hfactorTruncated).children.tasks) :
    task.1.word.weight PEAddres.weight =
      factor.word.weight PEAddres.weight := by
  let first :=
    supported_factory_case hn hH routing.outerRouting
      (expandedJacobiFactor factor ranked.decomposition)
      (expandedParentDefect ranked.decomposition)
      (by
        simpa only [expanded_jacobi_factor, hfactorWeight] using
          (le_refl lowerWeight))
      (.innerReductionOuter (ranked.firstCase hfactorTruncated))
  let second :=
    supported_factory_case hn hH routing.outerRouting
      (expandedJacobiSecond factor ranked.decomposition)
      (expandedParentDefect ranked.decomposition)
      (by
        simpa only [expanded_second_factor, hfactorWeight] using
          (le_refl lowerWeight))
      (.innerReductionOuter (ranked.secondCase hfactorTruncated))
  have htask' : task ∈ first.children.tasks ++ second.children.tasks := by
    simpa only [supported_ranked_decomp,
      SPFactora.RCSrc.tasks_append,
      SPFactora.RCSrc.tasks_reparent]
      using htask
  classical
  by_cases htaskFirst : task ∈ first.children.tasks
  · calc
      task.1.word.weight PEAddres.weight =
          (expandedJacobiFactor factor ranked.decomposition).word.weight
            PEAddres.weight := by
        exact
          word_outer_factory
            hn hH routing.outerRouting
              (expandedJacobiFactor factor ranked.decomposition)
              (expandedParentDefect ranked.decomposition)
              (by
                simpa only [expanded_jacobi_factor,
                  hfactorWeight] using (le_refl lowerWeight))
              (.innerReductionOuter (ranked.firstCase hfactorTruncated))
              htaskFirst
      _ = factor.word.weight PEAddres.weight :=
        expanded_jacobi_factor factor ranked.decomposition
  · have htaskSecond : task ∈ second.children.tasks :=
      (List.mem_append.mp htask').resolve_left htaskFirst
    calc
      task.1.word.weight PEAddres.weight =
          (expandedJacobiSecond factor ranked.decomposition).word.weight
            PEAddres.weight := by
        exact
          word_outer_factory
            hn hH routing.outerRouting
              (expandedJacobiSecond factor ranked.decomposition)
              (expandedParentDefect ranked.decomposition)
              (by
                simpa only [expanded_second_factor,
                  hfactorWeight] using (le_refl lowerWeight))
              (.innerReductionOuter (ranked.secondCase hfactorTruncated))
              htaskSecond
      _ = factor.word.weight PEAddres.weight :=
        expanded_second_factor factor ranked.decomposition

end
  RRBrancha

namespace
  TCReacha

/-- Every child of a flattened support-local Jacobi branch is reachable. -/
noncomputable def supported_jacobi_children
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      RCRoute
        (d := d) (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (ranked :
      TRDecomp
        factor)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    {task :
      SPFactora
          (concreteBasicCommutators.{u} d) inputWeight ×
        ℕ}
    (htask :
      task ∈
        (RRBrancha.supported_ranked_decomp
          hn hH routing factor ranked hfactorWeight
            hfactorTruncated).children.tasks) :
    TCReacha
      (n := n) task.1 task.2 := by
  let first :=
    RRBrancha.supported_factory_case
      hn hH routing.outerRouting
        (expandedJacobiFactor factor ranked.decomposition)
        (expandedParentDefect ranked.decomposition)
        (by
          simpa only [expanded_jacobi_factor, hfactorWeight] using
            (le_refl lowerWeight))
        (.innerReductionOuter (ranked.firstCase hfactorTruncated))
  let second :=
    RRBrancha.supported_factory_case
      hn hH routing.outerRouting
        (expandedJacobiSecond factor ranked.decomposition)
        (expandedParentDefect ranked.decomposition)
        (by
          simpa only [expanded_second_factor, hfactorWeight] using
            (le_refl lowerWeight))
        (.innerReductionOuter (ranked.secondCase hfactorTruncated))
  have htask' : task ∈ first.children.tasks ++ second.children.tasks := by
    simpa only [
      RRBrancha.supported_ranked_decomp,
      SPFactora.RCSrc.tasks_append,
      SPFactora.RCSrc.tasks_reparent]
      using htask
  classical
  by_cases htaskFirst : task ∈ first.children.tasks
  · exact
      children_factory_case hn hH routing.outerRouting
        (expandedJacobiFactor factor ranked.decomposition)
        (expandedParentDefect ranked.decomposition)
        (by
          simpa only [expanded_jacobi_factor, hfactorWeight] using
            (le_refl lowerWeight))
        (.innerReductionOuter (ranked.firstCase hfactorTruncated))
          (fun _ hinnerCase => by
            cases hinnerCase
            rfl)
          htaskFirst
  · exact
      children_factory_case hn hH routing.outerRouting
        (expandedJacobiSecond factor ranked.decomposition)
        (expandedParentDefect ranked.decomposition)
        (by
          simpa only [expanded_second_factor, hfactorWeight] using
            (le_refl lowerWeight))
        (.innerReductionOuter (ranked.secondCase hfactorTruncated))
          (fun _ hinnerCase => by
            cases hinnerCase
            rfl)
        ((List.mem_append.mp htask').resolve_left htaskFirst)

end
  TCReacha

namespace
  RRBranch

/-- Flatten one exact-weight expanded Jacobi root as a reachable branch. -/
noncomputable def childrenRankedDecomposition
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      RCRoute
        (d := d) (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (ranked :
      TRDecomp
        factor)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    RRBranch
      (n := n) routing.Reachable factor
        (expandedParentDefect ranked.decomposition) where
  branch :=
    RRBrancha.supported_ranked_decomp
      hn hH routing factor ranked hfactorWeight hfactorTruncated
  children_reachable := by
    intro task htask
    exact
      ⟨by
        rw [
          RRBrancha.word_expanded_jacobi
            hn hH routing factor ranked hfactorWeight hfactorTruncated htask]
        exact hfactorWeight,
       ⟨TCReacha.supported_jacobi_children
          hn hH routing factor ranked hfactorWeight hfactorTruncated htask⟩⟩

/-- Compile either Hall orientation as an exact-weight reachable branch. -/
noncomputable def childrenRankedDispatch
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      RCRoute
        (d := d) (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (dispatch :
      CRDispat factor left right hleftBasic
        hrightBasic htree) :
    RRBranch
      (n := n) routing.Reachable factor
        (HallTree.bracketRankDefect
          (left.weight + right.weight) left right) := by
  cases dispatch with
  | forward ranked =>
      rw [←
        CRDispat.forward_rank_defect
          factor left right hleftBasic hrightBasic htree ranked]
      exact
        childrenRankedDecomposition hn hH routing
          factor ranked hfactorWeight hfactorTruncated
  | swapped ranked =>
      rw [←
        CRDispat.swapped_rank_defect
          factor left right hleftBasic hrightBasic htree ranked]
      let swappedFactor :=
        childrenSwapFactor factor left right hleftBasic hrightBasic htree
      have hswappedWeight :
          swappedFactor.word.weight PEAddres.weight =
            lowerWeight := by
        simpa only [swappedFactor, basic_children_swap] using
          hfactorWeight
      have hswappedTruncated :
          swappedFactor.word.weight PEAddres.weight < n := by
        simpa only [swappedFactor, basic_children_swap] using
          hfactorTruncated
      let reversed :=
        childrenRankedDecomposition hn hH
          routing swappedFactor ranked hswappedWeight hswappedTruncated
      exact
        { branch :=
            RRBrancha.childrenSwap
              factor left right hleftBasic hrightBasic htree
                (expandedParentDefect ranked.decomposition)
                reversed.branch
                (routing.swapValueInverse factor left right hleftBasic
                  hrightBasic htree hfactorWeight hfactorTruncated)
          children_reachable := by
            intro task htask
            exact reversed.children_reachable task (by
              simpa only [
                RRBrancha.childrenSwap,
                SPFactora.RCSrc.tasks_reparent]
                using htask) }

/-- Choose the ranked Hall orientation of an exact-weight reachable frontier. -/
noncomputable def childrenRankedJacobi
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      RCRoute
        (d := d) (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hchildrenNe : left ≠ right)
    (hforwardNonbasic : ¬(HallTree.commutator left right).IsBasic)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    RRBranch
      (n := n) routing.Reachable factor
        (HallTree.bracketRankDefect
          (left.weight + right.weight) left right) :=
  childrenRankedDispatch hn hH routing factor left right
    hleftBasic hrightBasic htree hfactorWeight hfactorTruncated
      (childrenJacobiDispatch factor left right hleftBasic
        hrightBasic htree hchildrenNe hforwardNonbasic hreverseNonbasic)

/--
Classify one exact-weight reachable two-basic-child task. All non-leaf roots
flatten one Jacobi frontier.
-/
noncomputable def supported_basic_children
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      RCRoute
        (d := d) (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (hreachable : routing.Reachable factor rankDefect) :
    RRBranch
      (n := n) routing.Reachable factor rankDefect := by
  rcases hreachable with ⟨hfactorWeight, hreachable⟩
  let reachable := Classical.choice hreachable
  rcases reachable with
    ⟨left, right, hleftBasic, hrightBasic, htree, hfactorTruncated,
      rankDefect_eq⟩
  subst rankDefect
  by_cases hcutoff :
      n ≤ factor.word.weight PEAddres.weight + 1
  · exact
      ofResidRecollect factor
        (HallTree.bracketRankDefect
          (left.weight + right.weight) left right)
        (TSRecollb.of_terminal
          factor hcutoff)
  · by_cases hforwardBasic : (HallTree.commutator left right).IsBasic
    · exact
        ofResidRecollect factor
          (HallTree.bracketRankDefect
            (left.weight + right.weight) left right)
          (TSRecollb.tree_basic
            factor (by
              rw [htree]
              exact hforwardBasic))
    · by_cases hchildrenEq : left = right
      · exact
          ofResidRecollect factor
            (HallTree.bracketRankDefect
              (left.weight + right.weight) left right)
            (TSRecollb.tree_commutator_self
              factor left (by simpa only [hchildrenEq] using htree))
      · by_cases hreverseBasic : (HallTree.commutator right left).IsBasic
        · exact
            ofResidRecollect factor
              (HallTree.bracketRankDefect
                (left.weight + right.weight) left right)
              (TSRecollb.tree_swap_basic
                factor right left htree hreverseBasic)
        · exact
            childrenRankedJacobi hn hH routing factor left
              right hleftBasic hrightBasic htree hchildrenEq hforwardBasic
                hreverseBasic hfactorWeight hfactorTruncated

end
  RRBranch

namespace
  RCRoute

/-- Compile support-local structural branches into a reachable scheduler. -/
noncomputable def scheduler
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      RCRoute
        (d := d) (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight)) :
    TRSchedua
      (n := n) routing.Reachable :=
  TRSchedua.ofBranches
    fun factor rankDefect hreachable =>
      RRBranch.supported_basic_children
        hn hH routing factor rankDefect hreachable

/-- Recollect one certified two-basic-child task in the active stratum. -/
noncomputable def residualRecollection
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      RCRoute
        (d := d) (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (rankDefect : ℕ)
    (hreachable : routing.Reachable factor rankDefect) :
    TSRecollb
      (n := n) factor :=
  (routing.scheduler hn hH).residualRecollection factor rankDefect hreachable

/--
Recollect one arbitrary exact-weight root. Recursive children are discharged
by the structural two-basic-child scheduler.
-/
noncomputable def residual_recollection_case
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      RCRoute
        (d := d) (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (_hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (rootCase :
      TruncatedBranchCase
        (n := n) factor 0)
    (childrenReachable :
      ∀ task ∈
          (RRBrancha.supported_factory_case
            hn hH routing.outerRouting factor 0 (by omega) rootCase).children.tasks,
        TCReacha
          (n := n) task.1 task.2) :
    TSRecollb
      (n := n) factor :=
  let branch :=
    RRBrancha.supported_factory_case
      hn hH routing.outerRouting factor 0 (by omega) rootCase
  branch.recollect fun task htask =>
    routing.residualRecollection hn hH task.1 task.2
      ⟨by
        rw [
          RRBrancha.word_outer_factory
            hn hH routing.outerRouting factor 0 (by omega) rootCase htask]
        exact hfactorWeight,
       ⟨childrenReachable task htask⟩⟩

/--
Compile one root case, structural descendant scheduling, and atomic
comparison into the intrinsic restricted-sharp factor tail.
-/
noncomputable def factor_expansion_case
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      RCRoute
        (d := d) (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (rootCase :
      TruncatedBranchCase
        (n := n) factor 0)
    (childrenReachable :
      ∀ task ∈
          (RRBrancha.supported_factory_case
            hn hH routing.outerRouting factor 0 (by omega) rootCase).children.tasks,
        TCReacha
          (n := n) task.1 task.2) :
    TSExp
      (lowerWeight := lowerWeight) hn (concreteBasicCommutators.{u} d) hH
        factor := by
  subst lowerWeight
  exact
    ((routing.residual_recollection_case hn hH factor rfl
        hfactorTruncated rootCase childrenReachable).intrinsicResidualSource
          (TCRecoll.of_atomicNorm
            hn hH factor rfl hfactorTruncated
              (routing.outerRouting.factory factor le_rfl)
              (routing.outerRouting.sharp factor le_rfl)
              (routing.outerRouting.nextNormalizer factor le_rfl))
          rfl).factorExpansion

end
  RCRoute

end TCTex
end Submission

-- Merged from ResidualHallWittDirectRouting.lean

/-!
# Direct Hall-Witt routing for ranked concrete residuals

The positive Jacobi callback in support-local ranked residual collection can be
supplied directly by a fixed higher Hall-Witt strict-trace source.  This avoids
the same-stratum factor-residual callback exposed by recursive value routing.

The current Hall-Witt substitution encodes inverse letters by swapping a
commutator root.  The direct input therefore records the three syntactic
commutator witnesses explicitly.  Signed two-basic-child swaps cancel exactly
and need no callback.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open HEWord
open
  PCSrc

universe u


/--
A fixed higher Hall-Witt strict-trace source for one expanded Jacobi packet,
together with the witnesses required by the current signed substitution.
-/
structure EJInput
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) where
  left_isCommutator :
    ∃ left right, decomposition.left = .commutator left right
  middle_isCommutator :
    ∃ left right, decomposition.middle = .commutator left right
  right_isCommutator :
    ∃ left right, decomposition.right = .commutator left right
  strictTrace :
    TWSrc
      (n := n) (inputWeight := inputWeight)
      decomposition.left decomposition.middle decomposition.right
        factor.exponent

namespace
  EJInput

/-- Compile a direct strict-trace input into the positive Jacobi recollection. -/
noncomputable def valueResidualRecollection
    {d n inputWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    {decomposition : ExpandedJacobiDecomposition factor.word}
    (input :
      EJInput
        (n := n) factor decomposition) :
    TJRecoll
      (n := n) factor decomposition :=
  TJRecoll.witt_strict_source
    decomposition input.left_isCommutator input.middle_isCommutator
      input.right_isCommutator input.strictTrace

end
  EJInput

/--
Support-local routing whose only positive value-packet obligation is a direct
higher Hall-Witt strict-trace source.
-/
structure
    RDRoute
    {d n inputWeight lowerWeight : ℕ} where
  outerRouting :
    SFRoute.{u}
      (d := d) (n := n) (inputWeight := inputWeight)
        (lowerWeight := lowerWeight)
  valueStrictTrace :
    ∀
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          EJInput
            (n := n) factor ranked.decomposition

namespace
  RDRoute

/--
Compile direct Hall-Witt value inputs and exact empty swap packets into the
support-local ranked residual router.
-/
noncomputable def supportedChildrenRouting
    {d n inputWeight lowerWeight : ℕ}
    (routing :
      RDRoute
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight)) :
    RCRoute
      (d := d) (n := n) (inputWeight := inputWeight)
        (lowerWeight := lowerWeight) where
  outerRouting := routing.outerRouting
  valueResidual factor ranked hfactorWeight hfactorTruncated :=
    (routing.valueStrictTrace factor ranked hfactorWeight
      hfactorTruncated).valueResidualRecollection
  swapValueInverse factor left right hleftBasic hrightBasic htree
      _hfactorWeight _hfactorTruncated :=
    TIRecoll.empty
      factor left right hleftBasic hrightBasic htree

/-- Recollect one exact-weight root from direct Hall-Witt value inputs. -/
noncomputable def residual_recollection_case
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      RDRoute
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (rootCase :
      TruncatedBranchCase
        (n := n) factor 0)
    (childrenReachable :
      ∀ task ∈
          (RRBrancha.supported_factory_case
            hn hH routing.outerRouting factor 0 (by omega) rootCase).children.tasks,
        TCReacha
          (n := n) task.1 task.2) :
    TSRecollb
      (n := n) factor :=
  routing.supportedChildrenRouting
    |>.residual_recollection_case hn hH factor hfactorWeight
      hfactorTruncated rootCase childrenReachable

/-- Compile direct Hall-Witt routing into the intrinsic factor-tail endpoint. -/
noncomputable def factor_expansion_case
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      RDRoute
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (rootCase :
      TruncatedBranchCase
        (n := n) factor 0)
    (childrenReachable :
      ∀ task ∈
          (RRBrancha.supported_factory_case
            hn hH routing.outerRouting factor 0 (by omega) rootCase).children.tasks,
        TCReacha
          (n := n) task.1 task.2) :
    TSExp
      (lowerWeight := lowerWeight) hn (concreteBasicCommutators.{u} d) hH
        factor :=
  routing.supportedChildrenRouting
    |>.factor_expansion_case hn hH factor hfactorWeight
      hfactorTruncated rootCase childrenReachable

end
  RDRoute

end TCTex
end Submission

-- Merged from ResidualSupportedBasicChildrenNamedRecursiveValueRouting.lean

/-!
# Named recursive value routing for support-local Hall-power residuals

The finite-factor recursive value router still exposes raw list-membership
callbacks.  This file narrows that boundary to named residual recollections.

For each forward Jacobi packet, callers supply the positive root and its two
ordinary descendants.  For each inverse two-basic-child swap packet, callers
supply the positive root and the sign-corrected reversed factor.  Coefficient
negation and packet membership are discharged internally.

The positive root obligations intentionally remain explicit: they identify
the exact same-stratum cycle which a global symbolic value-packet theorem
must break.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open HEWord

/-- Support-local outer routing with named recursive value-packet residuals. -/
structure
    TRRoute
    {d n inputWeight lowerWeight : ℕ} where
  outerRouting :
    SFRoute.{u}
      (d := d) (n := n) (inputWeight := inputWeight)
        (lowerWeight := lowerWeight)
  valueResidualFactor :
    ∀
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (_ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n) factor
  valueResidualFirst :
    ∀
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n)
            (expandedJacobiFactor factor ranked.decomposition)
  valueResidualSecond :
    ∀
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n)
            (expandedJacobiSecond factor ranked.decomposition)
  swapValueFactor :
    ∀
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (left right : HallTree (FreeGenerator.{u} d))
      (_hleftBasic : left.IsBasic)
      (_hrightBasic : right.IsBasic)
      (_htree : tree factor.word = .commutator left right),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n) factor
  swapValueResidual :
    ∀
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (left right : HallTree (FreeGenerator.{u} d))
      (hleftBasic : left.IsBasic)
      (hrightBasic : right.IsBasic)
      (htree : tree factor.word = .commutator left right),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n)
            (childrenSwapFactor factor left right hleftBasic hrightBasic
              htree)

namespace
  TRRoute

/-- Compile named packet inputs into the semantic support-local router. -/
noncomputable def supportedChildrenRouting
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      TRRoute
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight)) :
    RCRoute
      (d := d) (n := n) (inputWeight := inputWeight)
        (lowerWeight := lowerWeight) where
  outerRouting := routing.outerRouting
  valueResidual factor ranked hfactorWeight hfactorTruncated :=
    TJRecoll.namedBasicResids
      hn hH
      (routing.outerRouting.factory factor (by omega))
      (routing.outerRouting.sharp factor (by omega))
      (routing.outerRouting.nextNormalizer factor (by omega))
      factor ranked.decomposition rfl hfactorTruncated
      (routing.valueResidualFactor factor ranked hfactorWeight
        hfactorTruncated)
      (routing.valueResidualFirst factor ranked hfactorWeight
        hfactorTruncated)
      (routing.valueResidualSecond factor ranked hfactorWeight
        hfactorTruncated)
  swapValueInverse factor left right hleftBasic hrightBasic htree
      hfactorWeight hfactorTruncated :=
    TIRecoll.namedBasicResids
      hn hH
      (routing.outerRouting.factory factor (by omega))
      (routing.outerRouting.sharp factor (by omega))
      (routing.outerRouting.nextNormalizer factor (by omega))
      factor left right hleftBasic hrightBasic htree rfl
      hfactorTruncated
      (routing.swapValueFactor factor left right hleftBasic
        hrightBasic htree hfactorWeight hfactorTruncated)
      (routing.swapValueResidual factor left right hleftBasic
        hrightBasic htree hfactorWeight hfactorTruncated)

/-- Recollect one exact-weight root from named value-packet obligations. -/
noncomputable def residual_recollection_case
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      TRRoute
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (rootCase :
      TruncatedBranchCase
        (n := n) factor 0)
    (childrenReachable :
      ∀ task ∈
          (RRBrancha.supported_factory_case
            hn hH routing.outerRouting factor 0 (by omega) rootCase).children.tasks,
        TCReacha
          (n := n) task.1 task.2) :
    TSRecollb
      (n := n) factor :=
  (routing.supportedChildrenRouting hn hH)
    |>.residual_recollection_case hn hH factor hfactorWeight
      hfactorTruncated rootCase childrenReachable

/-- Compile the named route into the intrinsic factor-tail endpoint. -/
noncomputable def factor_expansion_case
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      TRRoute
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (rootCase :
      TruncatedBranchCase
        (n := n) factor 0)
    (childrenReachable :
      ∀ task ∈
          (RRBrancha.supported_factory_case
            hn hH routing.outerRouting factor 0 (by omega) rootCase).children.tasks,
        TCReacha
          (n := n) task.1 task.2) :
    TSExp
      (lowerWeight := lowerWeight) hn (concreteBasicCommutators.{u} d) hH
        factor :=
  (routing.supportedChildrenRouting hn hH)
    |>.factor_expansion_case hn hH factor hfactorWeight
      hfactorTruncated rootCase childrenReachable

end
  TRRoute

end TCTex
end Submission

-- Merged from ResidualSupportedBasicChildrenRecursiveValueRouting.lean

/-!
# Recursive value routing for support-local Hall-power residuals

The support-local two-basic-child scheduler consumes two semantic value
residuals at the active Hall weight. Direct normalization of those packets asks
for a semantic normalizer at the same stratum.

This file replaces that circular input by finite concrete residual obligations.
Each factor in a value packet is reduced to its atomic Hall packet and an
already recollected intrinsic residual. The remaining active atoms are routed
using only the support-local correction factory, sharp router, and next-stratum
normalizer already carried by outer-factory routing.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open HEWord

/--
Support-local outer routing together with recursive concrete residuals for the
finite factors exposed by forward Jacobi and inverse swap value packets.
-/
structure
    CRRoute
    {d n inputWeight lowerWeight : ℕ} where
  outerRouting :
    SFRoute.{u}
      (d := d) (n := n) (inputWeight := inputWeight)
        (lowerWeight := lowerWeight)
  valueResidualBasic :
    ∀
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          ∀ child ∈
              expandedJacobiRaw factor ranked.decomposition,
            TSRecollb
              (n := n) child
  swapInverseBasic :
    ∀
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (left right : HallTree (FreeGenerator.{u} d))
      (hleftBasic : left.IsBasic)
      (hrightBasic : right.IsBasic)
      (htree : tree factor.word = .commutator left right),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          ∀ child ∈
              basicChildrenSwap factor left right
                hleftBasic hrightBasic htree,
            TSRecollb
              (n := n) child

namespace
  CRRoute

/--
Compile finite recursive value-packet obligations into the semantic value
residuals consumed by the support-local structural scheduler.
-/
noncomputable def supportedChildrenRouting
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      CRRoute
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight)) :
    RCRoute
      (d := d) (n := n) (inputWeight := inputWeight)
        (lowerWeight := lowerWeight) where
  outerRouting := routing.outerRouting
  valueResidual factor ranked hfactorWeight hfactorTruncated :=
    TJRecoll.ofBasicResiduals
      hn hH
      (routing.outerRouting.factory factor (by omega))
      (routing.outerRouting.sharp factor (by omega))
      (routing.outerRouting.nextNormalizer factor (by omega))
      factor ranked.decomposition rfl hfactorTruncated
      (routing.valueResidualBasic factor ranked hfactorWeight
        hfactorTruncated)
  swapValueInverse factor left right hleftBasic hrightBasic htree
      hfactorWeight hfactorTruncated :=
    TIRecoll.ofBasicResiduals
      hn hH
      (routing.outerRouting.factory factor (by omega))
      (routing.outerRouting.sharp factor (by omega))
      (routing.outerRouting.nextNormalizer factor (by omega))
      factor left right hleftBasic hrightBasic htree rfl
      hfactorTruncated
      (routing.swapInverseBasic factor left right
        hleftBasic hrightBasic htree hfactorWeight hfactorTruncated)

/--
Recollect one arbitrary exact-weight root from a root classifier, reachable
children, and finite recursive value-packet obligations.
-/
noncomputable def residual_recollection_case
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      CRRoute
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (rootCase :
      TruncatedBranchCase
        (n := n) factor 0)
    (childrenReachable :
      ∀ task ∈
          (RRBrancha.supported_factory_case
            hn hH routing.outerRouting factor 0 (by omega) rootCase).children.tasks,
        TCReacha
          (n := n) task.1 task.2) :
    TSRecollb
      (n := n) factor :=
  (routing.supportedChildrenRouting hn hH)
    |>.residual_recollection_case hn hH factor hfactorWeight
      hfactorTruncated rootCase childrenReachable

/--
Compile the recursive value-packet route into the intrinsic factor tail used by
the restricted-sharp active-block collector.
-/
noncomputable def factor_expansion_case
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      CRRoute
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (rootCase :
      TruncatedBranchCase
        (n := n) factor 0)
    (childrenReachable :
      ∀ task ∈
          (RRBrancha.supported_factory_case
            hn hH routing.outerRouting factor 0 (by omega) rootCase).children.tasks,
        TCReacha
          (n := n) task.1 task.2) :
    TSExp
      (lowerWeight := lowerWeight) hn (concreteBasicCommutators.{u} d) hH
        factor :=
  (routing.supportedChildrenRouting hn hH)
    |>.factor_expansion_case hn hH factor hfactorWeight
      hfactorTruncated rootCase childrenReachable

end
  CRRoute

end TCTex
end Submission

-- Merged from ResidualSupportedBasicChildrenRetainedRecipeCoefficientTraceCollection.lean

/-!
# Hall-power retained-trace collection with structural ranked descendants

The retained recipe-coefficient law supplies the powered correction packet at
every support stratum. An arbitrary active-block factor is classified once at
rank zero. Its recursive children are certified as two-basic-child tasks and
then recollected by the support-local structural Hall-ranked scheduler.

This narrows the powered retained-trace boundary from classifiers for every
ranked descendant to one root classifier, one retained-right certificate, and
the two semantic residuals exposed by Jacobi orientation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open HEWord
open
  CCThree
open
  CPSplita

/--
The powered structural inputs remaining after retained recipe packets and
support-local two-basic-child scheduling have been compiled.
-/
structure
    CCBuilda
    {d n inputWeight : ℕ} where
  outerFactory :
    IRFtry
      d n inputWeight
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
  valueResidual :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TJRecoll
            (n := n) factor ranked.decomposition
  swapValueInverse :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (left right : HallTree (FreeGenerator.{u} d))
      (hleftBasic : left.IsBasic)
      (hrightBasic : right.IsBasic)
      (htree : tree factor.word = .commutator left right),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TIRecoll
            (n := n) factor left right hleftBasic hrightBasic htree

namespace
  CCBuilda

open
  TAExp
open
  TAResolua

/-- Compile retained recipe coefficients to a powered packet at every stratum. -/
noncomputable def supportedFactorySchedule
    {d n inputWeight : ℕ}
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n) :
    TFSched
      (n := n) (inputWeight := inputWeight)
        (concreteBasicCommutators.{u} d) where
  factory lowerWeight :=
    TDBuild.retainedRecipeFactory
      (lowerWeight := lowerWeight) hinputWeight hrecipes

/--
Construct the global Hall-power semantic normalizer by support recursion.
Recursive uses occur only at strictly larger support weights, including the
normalizers used inside support-local Hall-ranked residual collection.
-/
noncomputable def semanticCoordinateNormalizer
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (builder :
      CCBuilda.{u}
        (d := d) (n := n) (inputWeight := inputWeight))
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowerWeight : ℕ) :
    TSNormalb
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight)
        (concreteBasicCommutators.{u} d) :=
  if hterminal : n ≤ 2 * lowerWeight then
    TSNormalb.of_highWeight
      hn (concreteBasicCommutators.{u} d)
        (fun r hr hrn =>
          concrete_forms_associated d n r hr
            hrn)
        hterminal
  else
    TSNormalb.ofInsertionKernel
      { insert := by
          intro coordinates factor hcoordinates hfactorSupported
            hfactorTruncated
          let hH :=
            fun r hr hrn =>
              concrete_forms_associated d n r hr
                hrn
          let nextNormalizer :=
            builder.semanticCoordinateNormalizer
              hn hinputWeight hrecipes (lowerWeight + 1)
          by_cases hfactorStrict :
              lowerWeight <
                factor.word.weight PEAddres.weight
          · exact
              nextNormalizer.insertion_word_weight coordinates
                factor hcoordinates hfactorStrict hfactorTruncated
          · have hfactorWeight :
                factor.word.weight PEAddres.weight =
                  lowerWeight := by
              omega
            let schedule :=
              supportedFactorySchedule
                hinputWeight hrecipes
            let normalizerAbove :=
              fun strongerWeight
                  (_hstronger : lowerWeight < strongerWeight) =>
                builder.semanticCoordinateNormalizer
                  hn hinputWeight hrecipes strongerWeight
            let outerRouting :=
              SFRoute.factory_above_outer
                schedule normalizerAbove builder.outerFactory
            let routing :
                RCRoute
                  (d := d) (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight) :=
              {
                outerRouting := outerRouting
                valueResidual :=
                  fun child ranked hchildWeight hchildTruncated =>
                    builder.valueResidual lowerWeight child ranked
                      hchildWeight hchildTruncated
                swapValueInverse :=
                  fun child left right hleftBasic hrightBasic htree
                      hchildWeight hchildTruncated =>
                    builder.swapValueInverse lowerWeight child left
                      right hleftBasic hrightBasic htree hchildWeight
                        hchildTruncated
              }
            let rootCase :=
              builder.rootCase lowerWeight factor hfactorWeight
                hfactorTruncated
            let hrootCaseRightTree :=
              fun innerCase hinnerCase =>
                builder.root_case_tree lowerWeight factor hfactorWeight
                  hfactorTruncated innerCase (by
                    simpa only [rootCase] using hinnerCase)
            let packetFactory := schedule.factory lowerWeight
            let sharp :
                SSNormal
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight)
                      (concreteBasicCommutators.{u} d) :=
              SSNormal.ofNormalizerAbove
                normalizerAbove
            let factorTail :=
              routing.factor_expansion_case hn hH factor
                hfactorWeight hfactorTruncated rootCase
                  (fun task htask =>
                    TCReacha.children_factory_case
                      hn hH outerRouting factor 0 (by omega) rootCase
                        hrootCaseRightTree htask)
            let merge :=
              (packetFactory
                |>.semantic_merge_sharp
                  hn (concreteBasicCommutators.{u} d) hH sharp coordinates
                    factor)
                |>.mergeResidualExpansion hfactorWeight hfactorTruncated
            let block :=
              mergeFactor merge factorTail
            let tail :=
              (packetFactory
                |>.supported_route_sharp
                  sharp coordinates factor hfactorWeight)
                |>.higherTailResolution hfactorWeight hfactorTruncated
            exact
              (active_block_tail
                hcoordinates hfactorWeight hfactorTruncated
                  (block.activeBlockResolution hcoordinates
                    hfactorWeight)
                  tail)
                |>.exists_insertion nextNormalizer hfactorWeight
                  hfactorTruncated }
termination_by n - lowerWeight
decreasing_by
  all_goals
    have hlowerWeightCutoff : lowerWeight < n := by
      omega
    omega

end
  CCBuilda

namespace TSInput

/--
Retained recipe traces and support-local ranked outer residual data construct
the canonical Claim 5 polynomials for a supported sourced input.
-/
theorem
    coordSupportedBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (builder :
      CCBuilda.{u}
        (d := d) (n := n) (inputWeight := inputWeight)) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.supportedSemanticNormalizer
    hsourceSupported
      (builder.semanticCoordinateNormalizer
        hn hinputWeight hrecipes inputWeight)
      hinputWeight

end TSInput

/--
In the automatic class-two source range, retained recipe traces and
support-local ranked outer residual data construct the canonical Claim 5
power package.
-/
theorem
    commutators_supported_below
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (builder :
      CCBuilda.{u}
        (d := d) (n := n) (inputWeight := inputWeight))
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)} :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e
        inputWeight := by
  intro heBelow
  let e' : HEFam (concreteBasicCommutators.{u} d) :=
    HEFam.zeroBelow e inputWeight
  have he'Below :
      ∀ s : ℕ, s < inputWeight → e' s = 0 := by
    intro s hs
    simp [e', hs]
  have he'Product :
      collectedHallProduct
          (n := n) (concreteBasicCommutators.{u} d) e' =
        collectedHallProduct
          (n := n) (concreteBasicCommutators.{u} d) e := by
    simpa [e'] using collected_below_self e heBelow
  rcases
      (TSInput.coordSupportedBuilder
          hn
          (TSInput.classTwoSource
            hinputWeight hcutoff e' he'Below)
          (TSInput.least_two_source
            hinputWeight hcutoff e' he'Below)
          hinputWeight hrecipes builder)
        (fun s _hs hs _hsn => he'Below s hs) with
    ⟨E, hEproduct, hEpolynomial⟩
  refine ⟨E, ?_, hEpolynomial⟩
  intro q
  exact (hEproduct q).trans (congrArg (fun x => x ^ q) he'Product)

/--
Retained recipe traces construct the full canonical Claim 5 power input once
supported low-weight sources and ranked outer residual builders are supplied.
-/
theorem
    commutators_forall_builders
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (builders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          CCBuilda.{u}
            (d := d) (n := n) (inputWeight := inputWeight)) :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) (concreteCommutatorsWeight.{u} d) e
            inputWeight := by
  intro e inputWeight hinputWeight
  by_cases hclassTwoRange : n ≤ 3 * inputWeight
  · exact
      commutators_supported_below
        hn hinputWeight hclassTwoRange hrecipes
          (builders inputWeight hinputWeight)
  · exact
      TSInput.coordSupportedBuilder
        hn
          (lowWeightSource e inputWeight hinputWeight hclassTwoRange)
          (lowWeightSupported e inputWeight hinputWeight hclassTwoRange)
          hinputWeight hrecipes (builders inputWeight hinputWeight)

end TCTex
end Submission

-- Merged from ResidualSupportedBasicChildrenJacobiOnlyValueRouting.lean

/-!
# Jacobi-only value routing for support-local Hall-power residuals

Signed bracket swaps cancel exactly, so support-local ranked residual
collection does not need recursive inputs for two-basic-child swap packets.
Only the forward Jacobi value packet remains semantic.

This file threads the exact empty swap recollection into the support-local
router and leaves three named Jacobi residual obligations: the positive root
and its two ordinary descendants.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open HEWord

/-- Support-local outer routing with only named Jacobi value-packet inputs. -/
structure
    TORouteb
    {d n inputWeight lowerWeight : ℕ} where
  outerRouting :
    SFRoute.{u}
      (d := d) (n := n) (inputWeight := inputWeight)
        (lowerWeight := lowerWeight)
  valueResidualFactor :
    ∀
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (_ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n) factor
  valueResidualFirst :
    ∀
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n)
            (expandedJacobiFactor factor ranked.decomposition)
  valueResidualSecond :
    ∀
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n)
            (expandedJacobiSecond factor ranked.decomposition)

namespace
  TORouteb

/-- Compile named Jacobi inputs and exact empty swap packets into the router. -/
noncomputable def supportedChildrenRouting
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      TORouteb
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight)) :
    RCRoute
      (d := d) (n := n) (inputWeight := inputWeight)
        (lowerWeight := lowerWeight) where
  outerRouting := routing.outerRouting
  valueResidual factor ranked hfactorWeight hfactorTruncated :=
    TJRecoll.namedBasicResids
      hn hH
      (routing.outerRouting.factory factor (by omega))
      (routing.outerRouting.sharp factor (by omega))
      (routing.outerRouting.nextNormalizer factor (by omega))
      factor ranked.decomposition rfl hfactorTruncated
      (routing.valueResidualFactor factor ranked hfactorWeight
        hfactorTruncated)
      (routing.valueResidualFirst factor ranked hfactorWeight
        hfactorTruncated)
      (routing.valueResidualSecond factor ranked hfactorWeight
        hfactorTruncated)
  swapValueInverse factor left right hleftBasic hrightBasic htree
      _hfactorWeight _hfactorTruncated :=
    TIRecoll.empty
      factor left right hleftBasic hrightBasic htree

/-- Recollect one exact-weight root from Jacobi-only value obligations. -/
noncomputable def residual_recollection_case
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      TORouteb
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (rootCase :
      TruncatedBranchCase
        (n := n) factor 0)
    (childrenReachable :
      ∀ task ∈
          (RRBrancha.supported_factory_case
            hn hH routing.outerRouting factor 0 (by omega) rootCase).children.tasks,
        TCReacha
          (n := n) task.1 task.2) :
    TSRecollb
      (n := n) factor :=
  (routing.supportedChildrenRouting hn hH)
    |>.residual_recollection_case hn hH factor hfactorWeight
      hfactorTruncated rootCase childrenReachable

/-- Compile the Jacobi-only route into the intrinsic factor-tail endpoint. -/
noncomputable def factor_expansion_case
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      TORouteb
        (d := d) (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight))
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (rootCase :
      TruncatedBranchCase
        (n := n) factor 0)
    (childrenReachable :
      ∀ task ∈
          (RRBrancha.supported_factory_case
            hn hH routing.outerRouting factor 0 (by omega) rootCase).children.tasks,
        TCReacha
          (n := n) task.1 task.2) :
    TSExp
      (lowerWeight := lowerWeight) hn (concreteBasicCommutators.{u} d) hH
        factor :=
  (routing.supportedChildrenRouting hn hH)
    |>.factor_expansion_case hn hH factor hfactorWeight
      hfactorTruncated rootCase childrenReachable

end
  TORouteb

end TCTex
end Submission

-- Merged from ResidualHallWittDirectRetainedTraceCollection.lean

/-!
# Retained-trace collection from direct Hall-Witt sources

The retained recipe-coefficient collector already accepts a direct positive
Jacobi value recollection.  A fixed higher Hall-Witt strict-trace source
supplies that recollection, while signed two-basic-child swaps recollect to the
empty source.

This adapter removes the same-stratum positive-root callback from the global
retained-trace builder without duplicating its support recursion.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open HEWord
open
  CCThree
open
  CPSplita

universe u


/--
Global retained-trace inputs whose positive Jacobi packets are supplied by
direct higher Hall-Witt strict-trace sources.
-/
structure
    SCBuildc
    {d n inputWeight : ℕ} where
  outerFactory :
    IRFtry
      d n inputWeight
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
          EJInput
            (n := n) factor ranked.decomposition

namespace
  SCBuildc

/--
Compile direct Hall-Witt inputs into the general retained recipe-coefficient
collector.
-/
noncomputable def
    supportedChildrenBuilder
    {d n inputWeight : ℕ}
    (builder :
      SCBuildc.{u}
        (d := d) (n := n) (inputWeight := inputWeight)) :
    CCBuilda.{u}
      (d := d) (n := n) (inputWeight := inputWeight) where
  outerFactory :=
    builder.outerFactory
  rootCase :=
    builder.rootCase
  root_case_tree :=
    builder.root_case_tree
  valueResidual :=
    fun lowerWeight factor ranked hfactorWeight hfactorTruncated =>
      (builder.valueStrictTrace lowerWeight factor ranked hfactorWeight
        hfactorTruncated).valueResidualRecollection
  swapValueInverse :=
    fun _lowerWeight factor left right hleftBasic hrightBasic htree
        _hfactorWeight _hfactorTruncated =>
      TIRecoll.empty
        factor left right hleftBasic hrightBasic htree

/--
The terminating direct Hall-Witt retained-trace collector supplies a semantic
normalizer at every support bound.
-/
noncomputable def supportedSemanticFamily
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (builder :
      SCBuildc.{u}
        (d := d) (n := n) (inputWeight := inputWeight))
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n) :
    SSNormala
      (n := n) (inputWeight := inputWeight)
        (concreteBasicCommutators.{u} d) where
  normalizer lowerWeight :=
    builder.supportedChildrenBuilder
      |>.semanticCoordinateNormalizer
        hn hinputWeight hrecipes lowerWeight

end
  SCBuildc

end TCTex
end Submission

-- Merged from ResidualSignedLeafHallWittDirectRetainedTraceCollection.lean

/-!
# Retained-trace collection from unrestricted signed-leaf Hall-Witt sources

The signed-leaf Hall-Witt source compiler accepts compressed atomic branches.
Supply one such direct higher source for every positive expanded-Jacobi packet;
signed two-basic-child swaps still cancel exactly to the empty source.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


open HEWord
open
  CCThree
open
  CPSplita
open
  LCSrc

universe u

/--
An unrestricted fixed higher signed-leaf Hall-Witt source for one expanded
Jacobi packet.
-/
structure
    ELInput
    {d n inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (decomposition : ExpandedJacobiDecomposition factor.word) where
  strictTrace :
    TWLeaf
      (n := n) (inputWeight := inputWeight)
      decomposition.left decomposition.middle decomposition.right
        factor.exponent

namespace
  ELInput

/-- Compile an unrestricted signed-leaf strict-trace input into the positive
Jacobi recollection. -/
noncomputable def valueResidualRecollection
    {d n inputWeight : ℕ}
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    {decomposition : ExpandedJacobiDecomposition factor.word}
    (input :
      ELInput
        (n := n) factor decomposition) :
    TJRecoll
      (n := n) factor decomposition :=
  TJRecoll.signed_leaf_witt
    decomposition input.strictTrace

end
  ELInput

/--
Global retained-trace inputs whose positive Jacobi packets are supplied by
unrestricted signed-leaf Hall-Witt sources.
-/
structure
    TLBuild
    {d n inputWeight : ℕ} where
  outerFactory :
    IRFtry
      d n inputWeight
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
  TLBuild

/-- Compile unrestricted signed-leaf Hall-Witt inputs into the general
retained recipe-coefficient collector. -/
noncomputable def
    supportedChildrenBuilder
    {d n inputWeight : ℕ}
    (builder :
      TLBuild.{u}
        (d := d) (n := n) (inputWeight := inputWeight)) :
    CCBuilda.{u}
      (d := d) (n := n) (inputWeight := inputWeight) where
  outerFactory :=
    builder.outerFactory
  rootCase :=
    builder.rootCase
  root_case_tree :=
    builder.root_case_tree
  valueResidual :=
    fun lowerWeight factor ranked hfactorWeight hfactorTruncated =>
      (builder.valueStrictTrace lowerWeight factor ranked hfactorWeight
        hfactorTruncated).valueResidualRecollection
  swapValueInverse :=
    fun _lowerWeight factor left right hleftBasic hrightBasic htree
        _hfactorWeight _hfactorTruncated =>
      TIRecoll.empty
        factor left right hleftBasic hrightBasic htree

/-- The terminating unrestricted signed-leaf retained-trace collector
supplies a semantic normalizer at every support bound. -/
noncomputable def supportedSemanticFamily
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (builder :
      TLBuild.{u}
        (d := d) (n := n) (inputWeight := inputWeight))
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n) :
    SSNormala
      (n := n) (inputWeight := inputWeight)
        (concreteBasicCommutators.{u} d) where
  normalizer lowerWeight :=
    builder.supportedChildrenBuilder
      |>.semanticCoordinateNormalizer
        hn hinputWeight hrecipes lowerWeight

end
  TLBuild

end TCTex
end Submission

-- Merged from
-- ResidualSupportedBasicChildrenNamedRecursiveValueRetainedRecipeCoefficientTraceCollection.lean

/-!
# Retained-trace Hall-power collection with named recursive value routing

Support-local structural collection exposes two same-stratum semantic value
packets.  Named recursive value routing reduces those packets to positive roots
and their ordinary descendants, constructing coefficient-negated residuals
internally.

This file threads that narrower interface through filtration recursion.
Retained recipe coefficients supply the correction packet schedule, recursive
support calls supply only strictly deeper normalizers, and the remaining
same-stratum positive-root cycle is explicit in the builder fields.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open HEWord
open
  CCThree
open
  CPSplita

/--
The powered retained-trace inputs after semantic value packets have been
reduced to named recursive concrete residual obligations.
-/
structure
    NRBuild
    {d n inputWeight : ℕ} where
  outerFactory :
    IRFtry
      d n inputWeight
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
  valueResidualFactor :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (_ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n) factor
  valueResidualFirst :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n)
            (expandedJacobiFactor factor ranked.decomposition)
  valueResidualSecond :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n)
            (expandedJacobiSecond factor ranked.decomposition)
  swapValueFactor :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (left right : HallTree (FreeGenerator.{u} d))
      (_hleftBasic : left.IsBasic)
      (_hrightBasic : right.IsBasic)
      (_htree : tree factor.word = .commutator left right),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n) factor
  swapValueResidual :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (left right : HallTree (FreeGenerator.{u} d))
      (hleftBasic : left.IsBasic)
      (hrightBasic : right.IsBasic)
      (htree : tree factor.word = .commutator left right),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n)
            (childrenSwapFactor factor left right hleftBasic hrightBasic
              htree)

namespace
  NRBuild

open
  TAExp
open
  TAResolua

/--
Construct the global Hall-power semantic normalizer by support recursion.
Recursive normalizer calls occur only at strictly larger support weights.
-/
noncomputable def semanticCoordinateNormalizer
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (builder :
      NRBuild.{u}
        (d := d) (n := n) (inputWeight := inputWeight))
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowerWeight : ℕ) :
    TSNormalb
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight)
        (concreteBasicCommutators.{u} d) :=
  if hterminal : n ≤ 2 * lowerWeight then
    TSNormalb.of_highWeight
      hn (concreteBasicCommutators.{u} d)
        (fun r hr hrn =>
          concrete_forms_associated d n r hr hrn)
        hterminal
  else
    TSNormalb.ofInsertionKernel
      { insert := by
          intro coordinates factor hcoordinates hfactorSupported
            hfactorTruncated
          let hH :=
            fun r hr hrn =>
              concrete_forms_associated d n r hr
                hrn
          let nextNormalizer :=
            builder.semanticCoordinateNormalizer
              hn hinputWeight hrecipes (lowerWeight + 1)
          by_cases hfactorStrict :
              lowerWeight <
                factor.word.weight PEAddres.weight
          · exact
              nextNormalizer.insertion_word_weight coordinates
                factor hcoordinates hfactorStrict hfactorTruncated
          · have hfactorWeight :
                factor.word.weight PEAddres.weight =
                  lowerWeight := by
              omega
            let schedule :=
              CCBuilda.supportedFactorySchedule
                hinputWeight hrecipes
            let normalizerAbove :=
              fun strongerWeight
                  (_hstronger : lowerWeight < strongerWeight) =>
                builder.semanticCoordinateNormalizer
                  hn hinputWeight hrecipes strongerWeight
            let outerRouting :=
              SFRoute.factory_above_outer
                schedule normalizerAbove builder.outerFactory
            let routing :
                TRRoute
                  (d := d) (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight) :=
              {
                outerRouting := outerRouting
                valueResidualFactor :=
                  fun child ranked hchildWeight hchildTruncated =>
                    builder.valueResidualFactor lowerWeight child
                      ranked hchildWeight hchildTruncated
                valueResidualFirst :=
                  fun child ranked hchildWeight hchildTruncated =>
                    builder.valueResidualFirst lowerWeight child ranked
                      hchildWeight hchildTruncated
                valueResidualSecond :=
                  fun child ranked hchildWeight hchildTruncated =>
                    builder.valueResidualSecond lowerWeight child ranked
                      hchildWeight hchildTruncated
                swapValueFactor :=
                  fun child left right hleftBasic hrightBasic htree
                      hchildWeight hchildTruncated =>
                    builder.swapValueFactor lowerWeight child
                      left right hleftBasic hrightBasic htree hchildWeight
                        hchildTruncated
                swapValueResidual :=
                  fun child left right hleftBasic hrightBasic htree
                      hchildWeight hchildTruncated =>
                    builder.swapValueResidual lowerWeight child
                      left right hleftBasic hrightBasic htree hchildWeight
                        hchildTruncated
              }
            let rootCase :=
              builder.rootCase lowerWeight factor hfactorWeight
                hfactorTruncated
            let hrootCaseRightTree :=
              fun innerCase hinnerCase =>
                builder.root_case_tree lowerWeight factor hfactorWeight
                  hfactorTruncated innerCase (by
                    simpa only [rootCase] using hinnerCase)
            let packetFactory := schedule.factory lowerWeight
            let sharp :
                SSNormal
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight)
                      (concreteBasicCommutators.{u} d) :=
              SSNormal.ofNormalizerAbove
                normalizerAbove
            let factorTail :=
              routing.factor_expansion_case hn hH factor
                hfactorWeight hfactorTruncated rootCase
                  (fun task htask =>
                    TCReacha.children_factory_case
                      hn hH outerRouting factor 0 (by omega) rootCase
                        hrootCaseRightTree htask)
            let merge :=
              (packetFactory
                |>.semantic_merge_sharp
                  hn (concreteBasicCommutators.{u} d) hH sharp coordinates
                    factor)
                |>.mergeResidualExpansion hfactorWeight hfactorTruncated
            let block :=
              mergeFactor merge factorTail
            let tail :=
              (packetFactory
                |>.supported_route_sharp
                  sharp coordinates factor hfactorWeight)
                |>.higherTailResolution hfactorWeight hfactorTruncated
            exact
              (active_block_tail
                hcoordinates hfactorWeight hfactorTruncated
                  (block.activeBlockResolution hcoordinates
                    hfactorWeight)
                  tail)
                |>.exists_insertion nextNormalizer hfactorWeight
                  hfactorTruncated }
termination_by n - lowerWeight
decreasing_by
  all_goals
    have hlowerWeightCutoff : lowerWeight < n := by
      omega
    omega

end
  NRBuild

namespace TSInput

/--
Retained recipe traces and named recursive value-packet residual obligations
construct the canonical Claim 5 polynomials for a supported sourced input.
-/
theorem
    childrenRecBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (builder :
      NRBuild.{u}
        (d := d) (n := n) (inputWeight := inputWeight)) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.supportedSemanticNormalizer
    hsourceSupported
      (builder.semanticCoordinateNormalizer
        hn hinputWeight hrecipes inputWeight)
      hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from
-- ResidualSupportedBasicChildrenRecursiveValueRetainedRecipeCoefficientTraceCollection.lean

/-!
# Retained-trace Hall-power collection with recursive value routing

Support-local structural collection exposes two same-stratum semantic value
packets. The recursive value-routing adapter replaces those opaque packets by
finite concrete residual obligations for their factors.

This file threads that adapter through filtration recursion. Retained recipe
coefficients supply the correction packet schedule, recursive support calls
supply only strictly deeper normalizers, and the remaining same-stratum input
is an explicit finite family of concrete factor residual recollections.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open HEWord
open
  CCThree
open
  CPSplita

/--
The powered retained-trace inputs after semantic value packets have been
reduced to finite recursive concrete residual obligations.
-/
structure
    CRBuild
    {d n inputWeight : ℕ} where
  outerFactory :
    IRFtry
      d n inputWeight
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
  valueResidualBasic :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          ∀ child ∈
              expandedJacobiRaw factor ranked.decomposition,
            TSRecollb
              (n := n) child
  swapInverseBasic :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (left right : HallTree (FreeGenerator.{u} d))
      (hleftBasic : left.IsBasic)
      (hrightBasic : right.IsBasic)
      (htree : tree factor.word = .commutator left right),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          ∀ child ∈
              basicChildrenSwap factor left right
                hleftBasic hrightBasic htree,
            TSRecollb
              (n := n) child

namespace
  CRBuild

open
  TAExp
open
  TAResolua

/--
Construct the global Hall-power semantic normalizer by support recursion.
Recursive normalizer calls occur only at strictly larger support weights.
-/
noncomputable def semanticCoordinateNormalizer
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (builder :
      CRBuild.{u}
        (d := d) (n := n) (inputWeight := inputWeight))
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowerWeight : ℕ) :
    TSNormalb
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight)
        (concreteBasicCommutators.{u} d) :=
  if hterminal : n ≤ 2 * lowerWeight then
    TSNormalb.of_highWeight
      hn (concreteBasicCommutators.{u} d)
        (fun r hr hrn =>
          concrete_forms_associated d n r hr hrn)
        hterminal
  else
    TSNormalb.ofInsertionKernel
      { insert := by
          intro coordinates factor hcoordinates hfactorSupported
            hfactorTruncated
          let hH :=
            fun r hr hrn =>
              concrete_forms_associated d n r hr
                hrn
          let nextNormalizer :=
            builder.semanticCoordinateNormalizer
              hn hinputWeight hrecipes (lowerWeight + 1)
          by_cases hfactorStrict :
              lowerWeight <
                factor.word.weight PEAddres.weight
          · exact
              nextNormalizer.insertion_word_weight coordinates
                factor hcoordinates hfactorStrict hfactorTruncated
          · have hfactorWeight :
                factor.word.weight PEAddres.weight =
                  lowerWeight := by
              omega
            let schedule :=
              CCBuilda.supportedFactorySchedule
                hinputWeight hrecipes
            let normalizerAbove :=
              fun strongerWeight
                  (_hstronger : lowerWeight < strongerWeight) =>
                builder.semanticCoordinateNormalizer
                  hn hinputWeight hrecipes strongerWeight
            let outerRouting :=
              SFRoute.factory_above_outer
                schedule normalizerAbove builder.outerFactory
            let routing :
                CRRoute
                  (d := d) (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight) :=
              {
                outerRouting := outerRouting
                valueResidualBasic :=
                  fun child ranked hchildWeight hchildTruncated =>
                    builder.valueResidualBasic lowerWeight child ranked
                      hchildWeight hchildTruncated
                swapInverseBasic :=
                  fun child left right hleftBasic hrightBasic htree
                      hchildWeight hchildTruncated =>
                    builder.swapInverseBasic lowerWeight
                      child left right hleftBasic hrightBasic htree hchildWeight
                        hchildTruncated
              }
            let rootCase :=
              builder.rootCase lowerWeight factor hfactorWeight
                hfactorTruncated
            let hrootCaseRightTree :=
              fun innerCase hinnerCase =>
                builder.root_case_tree lowerWeight factor hfactorWeight
                  hfactorTruncated innerCase (by
                    simpa only [rootCase] using hinnerCase)
            let packetFactory := schedule.factory lowerWeight
            let sharp :
                SSNormal
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight)
                      (concreteBasicCommutators.{u} d) :=
              SSNormal.ofNormalizerAbove
                normalizerAbove
            let factorTail :=
              routing.factor_expansion_case hn hH factor
                hfactorWeight hfactorTruncated rootCase
                  (fun task htask =>
                    TCReacha.children_factory_case
                      hn hH outerRouting factor 0 (by omega) rootCase
                        hrootCaseRightTree htask)
            let merge :=
              (packetFactory
                |>.semantic_merge_sharp
                  hn (concreteBasicCommutators.{u} d) hH sharp coordinates
                    factor)
                |>.mergeResidualExpansion hfactorWeight hfactorTruncated
            let block :=
              mergeFactor merge factorTail
            let tail :=
              (packetFactory
                |>.supported_route_sharp
                  sharp coordinates factor hfactorWeight)
                |>.higherTailResolution hfactorWeight hfactorTruncated
            exact
              (active_block_tail
                hcoordinates hfactorWeight hfactorTruncated
                  (block.activeBlockResolution hcoordinates
                    hfactorWeight)
                  tail)
                |>.exists_insertion nextNormalizer hfactorWeight
                  hfactorTruncated }
termination_by n - lowerWeight
decreasing_by
  all_goals
    have hlowerWeightCutoff : lowerWeight < n := by
      omega
    omega

end
  CRBuild

namespace TSInput

/--
Retained recipe traces and finite recursive value-packet residual obligations
construct the canonical Claim 5 polynomials for a supported sourced input.
-/
theorem
    coordRecBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (builder :
      CRBuild.{u}
        (d := d) (n := n) (inputWeight := inputWeight)) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.supportedSemanticNormalizer
    hsourceSupported
      (builder.semanticCoordinateNormalizer
        hn hinputWeight hrecipes inputWeight)
      hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from
-- ResidualSupportedBasicChildrenJacobiOnlyValueRetainedRecipeCoefficientTraceCollection.lean

/-!
# Retained-trace Hall-power collection with Jacobi-only value routing

Exact signed-swap cancellation removes both swap-packet recursive inputs from
support-local structural collection.  This file threads the resulting
Jacobi-only interface through filtration recursion.

Retained recipe coefficients supply the correction packet schedule, recursive
support calls supply only strictly deeper normalizers, and the only remaining
same-stratum semantic cycle is the positive root of a forward Jacobi packet.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open HEWord
open
  CCThree
open
  CPSplita

/--
The powered retained-trace inputs after exact swap cancellation and named
Jacobi recursive value routing.
-/
structure
    JCBuild
    {d n inputWeight : ℕ} where
  outerFactory :
    IRFtry
      d n inputWeight
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
  valueResidualFactor :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (_ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n) factor
  valueResidualFirst :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n)
            (expandedJacobiFactor factor ranked.decomposition)
  valueResidualSecond :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n)
            (expandedJacobiSecond factor ranked.decomposition)

namespace
  JCBuild

open
  TAExp
open
  TAResolua

/--
Construct the global Hall-power semantic normalizer by support recursion.
Recursive normalizer calls occur only at strictly larger support weights.
-/
noncomputable def semanticCoordinateNormalizer
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (builder :
      JCBuild.{u}
        (d := d) (n := n) (inputWeight := inputWeight))
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowerWeight : ℕ) :
    TSNormalb
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight)
        (concreteBasicCommutators.{u} d) :=
  if hterminal : n ≤ 2 * lowerWeight then
    TSNormalb.of_highWeight
      hn (concreteBasicCommutators.{u} d)
        (fun r hr hrn =>
          concrete_forms_associated d n r hr hrn)
        hterminal
  else
    TSNormalb.ofInsertionKernel
      { insert := by
          intro coordinates factor hcoordinates hfactorSupported
            hfactorTruncated
          let hH :=
            fun r hr hrn =>
              concrete_forms_associated d n r hr
                hrn
          let nextNormalizer :=
            builder.semanticCoordinateNormalizer
              hn hinputWeight hrecipes (lowerWeight + 1)
          by_cases hfactorStrict :
              lowerWeight <
                factor.word.weight PEAddres.weight
          · exact
              nextNormalizer.insertion_word_weight coordinates
                factor hcoordinates hfactorStrict hfactorTruncated
          · have hfactorWeight :
                factor.word.weight PEAddres.weight =
                  lowerWeight := by
              omega
            let schedule :=
              CCBuilda.supportedFactorySchedule
                hinputWeight hrecipes
            let normalizerAbove :=
              fun strongerWeight
                  (_hstronger : lowerWeight < strongerWeight) =>
                builder.semanticCoordinateNormalizer
                  hn hinputWeight hrecipes strongerWeight
            let outerRouting :=
              SFRoute.factory_above_outer
                schedule normalizerAbove builder.outerFactory
            let routing :
                TORouteb
                  (d := d) (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight) :=
              {
                outerRouting := outerRouting
                valueResidualFactor :=
                  fun child ranked hchildWeight hchildTruncated =>
                    builder.valueResidualFactor lowerWeight child
                      ranked hchildWeight hchildTruncated
                valueResidualFirst :=
                  fun child ranked hchildWeight hchildTruncated =>
                    builder.valueResidualFirst lowerWeight child ranked
                      hchildWeight hchildTruncated
                valueResidualSecond :=
                  fun child ranked hchildWeight hchildTruncated =>
                    builder.valueResidualSecond lowerWeight child
                      ranked hchildWeight hchildTruncated
              }
            let rootCase :=
              builder.rootCase lowerWeight factor hfactorWeight
                hfactorTruncated
            let hrootCaseRightTree :=
              fun innerCase hinnerCase =>
                builder.root_case_tree lowerWeight factor hfactorWeight
                  hfactorTruncated innerCase (by
                    simpa only [rootCase] using hinnerCase)
            let packetFactory := schedule.factory lowerWeight
            let sharp :
                SSNormal
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight)
                      (concreteBasicCommutators.{u} d) :=
              SSNormal.ofNormalizerAbove
                normalizerAbove
            let factorTail :=
              routing.factor_expansion_case hn hH factor
                hfactorWeight hfactorTruncated rootCase
                  (fun task htask =>
                    TCReacha.children_factory_case
                      hn hH outerRouting factor 0 (by omega) rootCase
                        hrootCaseRightTree htask)
            let merge :=
              (packetFactory
                |>.semantic_merge_sharp
                  hn (concreteBasicCommutators.{u} d) hH sharp coordinates
                    factor)
                |>.mergeResidualExpansion hfactorWeight hfactorTruncated
            let block :=
              mergeFactor merge factorTail
            let tail :=
              (packetFactory
                |>.supported_route_sharp
                  sharp coordinates factor hfactorWeight)
                |>.higherTailResolution hfactorWeight hfactorTruncated
            exact
              (active_block_tail
                hcoordinates hfactorWeight hfactorTruncated
                  (block.activeBlockResolution hcoordinates
                    hfactorWeight)
                  tail)
                |>.exists_insertion nextNormalizer hfactorWeight
                  hfactorTruncated }
termination_by n - lowerWeight
decreasing_by
  all_goals
    have hlowerWeightCutoff : lowerWeight < n := by
      omega
    omega

end
  JCBuild

namespace TSInput

/--
Retained recipe traces and three named Jacobi residual obligations construct
the canonical Claim 5 polynomials for a supported sourced input.
-/
theorem
    jacobiCollectBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight)
          (concreteCommutatorsWeight.{u} d) e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (builder :
      JCBuild.{u}
        (d := d) (n := n) (inputWeight := inputWeight)) :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e inputWeight :=
  input.supportedSemanticNormalizer
    hsourceSupported
      (builder.semanticCoordinateNormalizer
        hn hinputWeight hrecipes inputWeight)
      hinputWeight

end TSInput

/--
In the automatic class-two source range, retained recipe traces and
Jacobi-only ranked outer residual data construct the canonical Claim 5 power
package.
-/
theorem
    commutators_builder_below
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hinputWeight : 1 ≤ inputWeight)
    (hcutoff : n ≤ 3 * inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (builder :
      JCBuild.{u}
        (d := d) (n := n) (inputWeight := inputWeight))
    {e :
      HEFam
        (concreteCommutatorsWeight.{u} d)} :
    CollectedPolynomialData
      (n := n) (concreteCommutatorsWeight.{u} d) e
        inputWeight := by
  intro heBelow
  let e' : HEFam (concreteBasicCommutators.{u} d) :=
    HEFam.zeroBelow e inputWeight
  have he'Below :
      ∀ s : ℕ, s < inputWeight → e' s = 0 := by
    intro s hs
    simp [e', hs]
  have he'Product :
      collectedHallProduct
          (n := n) (concreteBasicCommutators.{u} d) e' =
        collectedHallProduct
          (n := n) (concreteBasicCommutators.{u} d) e := by
    simpa [e'] using collected_below_self e heBelow
  rcases
      (TSInput.jacobiCollectBuilder
          hn
          (TSInput.classTwoSource
            hinputWeight hcutoff e' he'Below)
          (TSInput.least_two_source
            hinputWeight hcutoff e' he'Below)
          hinputWeight hrecipes builder)
        (fun s _hs hs _hsn => he'Below s hs) with
    ⟨E, hEproduct, hEpolynomial⟩
  refine ⟨E, ?_, hEpolynomial⟩
  intro q
  exact (hEproduct q).trans (congrArg (fun x => x ^ q) he'Product)

/--
Retained recipe traces construct the full canonical Claim 5 power input once
supported low-weight sources and Jacobi-only ranked residual builders are
supplied.
-/
theorem
    commutators_collect_builders
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowWeightSource :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ),
        1 ≤ inputWeight →
          ¬n ≤ 3 * inputWeight →
            TSInput
              (n := n) (inputWeight := inputWeight)
                (concreteCommutatorsWeight.{u} d) e)
    (lowWeightSupported :
      ∀ (e :
          HEFam
            (concreteCommutatorsWeight.{u} d))
        (inputWeight : ℕ)
        (hinputWeight : 1 ≤ inputWeight)
        (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
          SPFactora.WordWeightLeast inputWeight
            (lowWeightSource e inputWeight hinputWeight
              hbelowClassTwoRange).source)
    (builders :
      ∀ inputWeight : ℕ,
        1 ≤ inputWeight →
          JCBuild.{u}
            (d := d) (n := n) (inputWeight := inputWeight)) :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        CollectedPolynomialData
          (n := n) (concreteCommutatorsWeight.{u} d) e
            inputWeight := by
  intro e inputWeight hinputWeight
  by_cases hclassTwoRange : n ≤ 3 * inputWeight
  · exact
      commutators_builder_below
        hn hinputWeight hclassTwoRange hrecipes
          (builders inputWeight hinputWeight)
  · exact
      TSInput.jacobiCollectBuilder
        hn
          (lowWeightSource e inputWeight hinputWeight hclassTwoRange)
          (lowWeightSupported e inputWeight hinputWeight hclassTwoRange)
          hinputWeight hrecipes (builders inputWeight hinputWeight)

end TCTex
end Submission

-- Merged from ResidualHallWittDirectFixedPacketRestartCollection.lean

/-!
# Direct Hall-Witt retained traces from fixed-packet structural restarts

Fixed-packet generated structural restart routing supplies the outer residual
factory.  Direct higher Hall-Witt strict-trace sources supply the remaining
positive Jacobi value packets.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open HEWord

universe u


/--
Fixed-packet restart inputs after the positive Jacobi cycle has been replaced
by direct higher Hall-Witt strict-trace sources.
-/
structure
    TRBuildb
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
          EJInput
            (n := n) factor ranked.decomposition

namespace
  TRBuildb

/--
Forget fixed-packet restart routing as the outer factory of the direct
Hall-Witt retained-trace collector.
-/
noncomputable def wittDirectBuilder
    {d n inputWeight : ℕ}
    (builder :
      TRBuildb.{u}
        (d := d) (n := n) (inputWeight := inputWeight)) :
    SCBuildc.{u}
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
  TRBuildb

end TCTex
end Submission

-- Merged from ResidualSupportedBasicChildrenJacobiOnlyValueFixedPacketGeneratedStructuralRestartRet
-- ainedRecipeCoefficientTraceCollection.lean

/-!
# Jacobi-only retained-trace collection from fixed-packet structural restarts

Fixed-packet generated structural restart routing constructs the outer
residual recollection factory consumed by support-local Hall-ranked
collection.  This file threads that concrete transient route into the
Jacobi-only retained-trace builder.

The remaining same-stratum obligations are kept visible: root
classification, retained-right evidence, and the three named forward-Jacobi
residual recollections.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open HEWord

/--
Powered retained-trace inputs after fixed-packet generated structural
restarts have discharged the outer residual factory.
-/
structure
    TFBuilda
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
  valueResidualFactor :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (_ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n) factor
  valueResidualFirst :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n)
            (expandedJacobiFactor factor ranked.decomposition)
  valueResidualSecond :
    ∀ (lowerWeight : ℕ)
      (factor :
        SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)
      (ranked :
        TRDecomp
          factor),
      factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          TSRecollb
            (n := n)
            (expandedJacobiSecond factor ranked.decomposition)

namespace
  TFBuilda

/--
Forget fixed-packet generated restart routing as the outer residual factory
used by Jacobi-only support recursion.
-/
noncomputable def
    jacobiOnlyBuilder
    {d n inputWeight : ℕ}
    (builder :
      TFBuilda.{u}
        (d := d) (n := n) (inputWeight := inputWeight)) :
    JCBuild.{u}
      (d := d) (n := n) (inputWeight := inputWeight) where
  outerFactory :=
    builder.routing.outerRecollectionFactory
  rootCase :=
    builder.rootCase
  root_case_tree :=
    builder.root_case_tree
  valueResidualFactor :=
    builder.valueResidualFactor
  valueResidualFirst :=
    builder.valueResidualFirst
  valueResidualSecond :=
    builder.valueResidualSecond

end
  TFBuilda

end TCTex
end Submission

-- Merged from ResidualSupportedBasicChildrenJacobiOnlyValueRetainedRecipeCoefficientTraceNormalizer
-- Families.lean

/-!
# Normalizer families from Jacobi-only ranked Hall-power collection

The Jacobi-only ranked residual collector constructs a semantic normalizer at
every support bound by terminating filtration recursion.  This file packages
those normalizers as one family and exposes the two consumers needed by the
cutoff-aware Hall-power route:

* concrete basic-reduction endpoint residual recollections; and
* signed physical Hall-Witt branch recollections.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open
  CCThree
open
  CPSplita
open
  RFPhysic

namespace
  JCBuild

/--
The terminating Jacobi-only ranked collector supplies a semantic normalizer
at every support bound.
-/
noncomputable def supportedSemanticFamily
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (builder :
      JCBuild.{u}
        (d := d) (n := n) (inputWeight := inputWeight))
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n) :
    SSNormala
      (n := n) (inputWeight := inputWeight)
        (concreteBasicCommutators.{u} d) where
  normalizer lowerWeight :=
    builder.semanticCoordinateNormalizer
      hn hinputWeight hrecipes lowerWeight

/--
The Jacobi-only ranked collector supplies both concrete Hall-tree residual
recollections required by endpoint interpolation.
-/
noncomputable def
    endpointInterpolationBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (builder :
      JCBuild.{u}
        (d := d) (n := n) (inputWeight := inputWeight))
    (hinputWeight : 1 ≤ inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n) :
    TSBuildc
      (inputWeight := inputWeight) hn
        (forms_associated_below
          d n) :=
  TSBuildc.ofNormalizerFamily
    hn
      (forms_associated_below
        d n)
      (builder.supportedSemanticFamily
        hn hinputWeight hrecipes)

/--
The same Jacobi-only ranked collector supplies both integral Hall-Witt
strict-tail recollections for every admissible physical branch.
-/
noncomputable def branchRecollectionFactory
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (builder :
      JCBuild.{u}
        (d := d) (n := n) (inputWeight := inputWeight))
    (hinputWeight : 0 < inputWeight)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n) :
    BRFtry
      (d := d) (n := n) (inputWeight := inputWeight) hn hinputWeight :=
  BRFtry.ofNormalizerFamily
    hn hinputWeight
      (builder.supportedSemanticFamily
        hn hinputWeight hrecipes)

end
  JCBuild

end TCTex
end Submission
