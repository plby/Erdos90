import Towers.Group.Zassenhaus.OuterResidualInterfaces
import Towers.Group.Zassenhaus.LocalResidualBranches
import Towers.Group.Zassenhaus.SignedReductionFactors
import Towers.Group.Zassenhaus.HallSupportMonotonicity

/-!
# Ranked polynomial residual cases with a full-weight outer-residual factory

The non-circular inner-reduction branch consumes an explicit factory for the
full-weight child-to-parent quotient. Its other local inputs are the
correction factory, sharp active-atomic router, and next-stratum normalizer.

This file packages those inputs and compiles indexed local cases into the
global well-founded residual scheduler. A complete normalizer family still
implements the interface as a compatibility path, but the scheduler no longer
requires a parent-stratum normalizer directly.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/-- Non-circular local routing inputs for every concrete polynomial factor. -/
structure
    RFRoute
    {d n : ℕ}
    (ι : Type) where
  factory :
    ∀ factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι,
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d)
          (factor.word.weight HEAddres.weight)
  sharp :
    ∀ factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι,
      TSNormala
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d)
  nextNormalizer :
    ∀ factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι,
      TSNormal
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
  outerFactory :
    TRFtrya
      (d := d) (n := n) ι

namespace
  RFRoute

/--
A correction schedule, strictly deeper normalizers, and the explicit
full-weight outer-residual factory supply every local input used by the
non-circular ranked scheduler.
-/
noncomputable def factory_above_outer
    {d n : ℕ}
    {ι : Type}
    (schedule :
      SFSched
        (n := n) (concreteBasicCommutators.{u} d))
    (normalizerAbove :
      ∀ lowerWeight strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (outerFactory :
      TRFtrya
        (d := d) (n := n) ι) :
    RFRoute
      (d := d) (n := n) ι where
  factory factor :=
    schedule.factory
      (factor.word.weight HEAddres.weight)
  sharp factor :=
    TSNormala.ofNormalizerAbove
      (normalizerAbove
        (factor.word.weight HEAddres.weight))
  nextNormalizer factor :=
    normalizerAbove
      (factor.word.weight HEAddres.weight)
      (factor.word.weight HEAddres.weight + 1) (by omega)
  outerFactory := outerFactory

/--
A complete normalizer family and correction-factory schedule implement the
outer-factory routing interface. This is the compatibility path for existing
global constructions.
-/
noncomputable def normalizers_factory_schedule
    {d n : ℕ}
    {ι : Type}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (family :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d))
    (schedule :
      SFSched
        (n := n) (concreteBasicCommutators.{u} d)) :
    RFRoute
      (d := d) (n := n) ι :=
  factory_above_outer schedule
    (fun _lowerWeight strongerWeight _hstronger =>
      family.normalizer strongerWeight)
    (family.concreteRecollectionFactory hn hH)

end
  RFRoute

namespace TRBrancha

/-- Compile one indexed inner-reduction case through outer-factory routing. -/
noncomputable def innerOuterFactory
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (routing :
      RFRoute
        (d := d) (n := n) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (branchCase :
      TruncatedRankedCase
        (n := n) factor rankDefect) :
    TRBrancha
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
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (routing :
      RFRoute
        (d := d) (n := n) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (branchCase :
      RankedBranchCase
        (n := n) factor rankDefect) :
    TRBrancha
      (n := n) factor rankDefect := by
  cases branchCase with
  | leaf leafCase =>
      exact ofLeafCase factor rankDefect leafCase
  | innerReductionOuter innerCase =>
      exact
        innerOuterFactory hn hH routing factor rankDefect
          innerCase

end TRBrancha

namespace
  TRSchedu

/-- Compile outer-factory routed indexed cases into a global residual scheduler. -/
noncomputable def outerFactoryCases
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (routing :
      RFRoute
        (d := d) (n := n) ι)
    (cases :
      ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (rankDefect : ℕ),
        RankedBranchCase
          (n := n) factor rankDefect) :
    TRSchedu
      (d := d) (n := n) (ι := ι) :=
  ofBranches fun factor rankDefect =>
    TRBrancha.outerFactoryCase
      hn hH routing factor rankDefect (cases factor rankDefect)

/--
Run well-founded residual recursion directly from outer-factory routed indexed
local cases.
-/
noncomputable def recollect_factory_cases
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (routing :
      RFRoute
        (d := d) (n := n) ι)
    (cases :
      ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (rankDefect : ℕ),
        RankedBranchCase
          (n := n) factor rankDefect)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ) :
    TRRecoll
      (n := n) factor :=
  (outerFactoryCases hn hH routing cases).residualRecollection
    factor rankDefect

end
  TRSchedu

end TCTex
end Towers

/-!
# Ranked residual cases with sharp inner-reduction comparison

The sharp branch uses local routing data: a normalizer for the child-to-parent
quotient, a correction factory and sharp router for the active comparison, and
a next-stratum normalizer.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/-- Local sharp routing inputs for every concrete polynomial factor. -/
structure RSRoute
    {d n : ℕ}
    (ι : Type) where
  normalizer :
    ∀ factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι,
      TSNormal
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d)
  factory :
    ∀ factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι,
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d)
          (factor.word.weight HEAddres.weight)
  sharp :
    ∀ factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι,
      TSNormala
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d)
  nextNormalizer :
    ∀ factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι,
      TSNormal
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)

namespace
  RSRoute

/-- A normalizer family and factory schedule provide every local routing input. -/
noncomputable def normalizers_factory_schedule
    {d n : ℕ}
    {ι : Type}
    (family :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d))
    (schedule :
      SFSched
        (n := n) (concreteBasicCommutators.{u} d)) :
    RSRoute
      (d := d) (n := n) ι where
  normalizer factor :=
    family.normalizer
      (factor.word.weight HEAddres.weight)
  factory factor :=
    schedule.factory
      (factor.word.weight HEAddres.weight)
  sharp _factor :=
    TSNormala.ofNormalizerAbove
      (fun strongerWeight _hstronger => family.normalizer strongerWeight)
  nextNormalizer factor :=
    family.normalizer
      (factor.word.weight HEAddres.weight + 1)

end
  RSRoute

namespace TRBrancha

/-- Compile one indexed inner-reduction case through sharp comparison routing. -/
noncomputable def sharpComparisonCase
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (routing :
      RSRoute
        (d := d) (n := n) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (branchCase :
      TruncatedRankedCase
        (n := n) factor rankDefect) :
    TRBrancha
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

/-- Compile either a leaf or a sharply routed inner-reduction case. -/
noncomputable def sharpCase
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (routing :
      RSRoute
        (d := d) (n := n) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (branchCase :
      RankedBranchCase
        (n := n) factor rankDefect) :
    TRBrancha
      (n := n) factor rankDefect := by
  cases branchCase with
  | leaf leafCase =>
      exact ofLeafCase factor rankDefect leafCase
  | innerReductionOuter innerCase =>
      exact
        sharpComparisonCase hn hH routing factor
          rankDefect innerCase

end TRBrancha

namespace
  TRSchedu

/-- Compile sharply routed indexed cases into a global scheduler. -/
noncomputable def sharpComparisonCases
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (routing :
      RSRoute
        (d := d) (n := n) ι)
    (cases :
      ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (rankDefect : ℕ),
        RankedBranchCase
          (n := n) factor rankDefect) :
    TRSchedu
      (d := d) (n := n) (ι := ι) :=
  ofBranches fun factor rankDefect =>
    TRBrancha.sharpCase
      hn hH routing factor rankDefect (cases factor rankDefect)

/-- Run recursion directly from sharply routed indexed local cases. -/
noncomputable def sharp_comparison_cases
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (routing :
      RSRoute
        (d := d) (n := n) ι)
    (cases :
      ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (rankDefect : ℕ),
        RankedBranchCase
          (n := n) factor rankDefect)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ) :
    TRRecoll
      (n := n) factor :=
  (sharpComparisonCases hn hH routing cases).residualRecollection
    factor rankDefect

end
  TRSchedu

end TCTex
end Towers

/-!
# Reachable polynomial Hall-ranked residual scheduling

The unrestricted residual scheduler requests a local branch for every pair of
a symbolic factor and a numerical Hall-rank defect. Recipe-correct inner
reduction naturally supplies branches only for tasks reached from the
collector's worklists.

This file records a restricted scheduler indexed by a reachability predicate.
Every emitted child must remain reachable, so well-founded Hall-ranked
recursion constructs residual recollections from local branches only along
the actual recursive task graph.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/--
A reachable Hall-ranked branch is an ordinary branch whose emitted children
remain inside the recursive task predicate.
-/
structure TRBranch
    {d n : ℕ}
    {ι : Type}
    (Reachable :
      SPFactor
          (concreteBasicCommutators.{u} d) ι →
        ℕ → Prop)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ) where
  branch :
    TRBrancha
      (n := n) factor rankDefect
  children_reachable :
    ∀ task ∈ branch.children.tasks,
      Reachable task.1 task.2

/--
A Hall-ranked residual scheduler whose local obligations are restricted to
reachable tasks.
-/
structure RRSchedu
    {d n : ℕ}
    {ι : Type}
    (Reachable :
      SPFactor
          (concreteBasicCommutators.{u} d) ι →
        ℕ → Prop) where
  branches :
    ∀
      (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι)
      (rankDefect : ℕ),
      Reachable factor rankDefect →
        TRBranch
          (n := n) Reachable factor rankDefect

namespace
  RRSchedu

/--
Run Hall-ranked well-founded recursion from branches supplied only for
reachable tasks.
-/
noncomputable def residualRecollection
    {d n : ℕ}
    {ι : Type}
    {Reachable :
      SPFactor
          (concreteBasicCommutators.{u} d) ι →
        ℕ → Prop}
    (scheduler :
      RRSchedu
        (n := n) Reachable)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (hreachable : Reachable factor rankDefect) :
    TRRecoll
      (n := n) factor :=
  Classical.choice <|
    SPFactor.ranked_descends_induction
      (motive := fun child childRankDefect =>
        Reachable child childRankDefect →
          Nonempty
            (TRRecoll
              (n := n) child))
      (fun parent parentRankDefect ih hparent =>
        let branch := scheduler.branches parent parentRankDefect hparent
        ⟨branch.branch.recollect fun task htask =>
          Classical.choice <|
            ih task.1 task.2
              (branch.branch.children.tasks_descend task htask)
              (branch.children_reachable task htask)⟩)
      factor rankDefect hreachable

/-- Compile reachable local branches directly into a restricted scheduler. -/
noncomputable def ofBranches
    {d n : ℕ}
    {ι : Type}
    {Reachable :
      SPFactor
          (concreteBasicCommutators.{u} d) ι →
        ℕ → Prop}
    (branches :
      ∀
        (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (rankDefect : ℕ),
        Reachable factor rankDefect →
          TRBranch
            (n := n) Reachable factor rankDefect) :
    RRSchedu
      (n := n) Reachable where
  branches := branches

end
  RRSchedu

namespace
  TRBranch

/--
Compile one reachable outer-factory case, provided its emitted children
remain reachable.
-/
noncomputable def outerFactoryCase
    {d n : ℕ}
    {ι : Type}
    {Reachable :
      SPFactor
          (concreteBasicCommutators.{u} d) ι →
        ℕ → Prop}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      RFRoute
        (d := d) (n := n) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (branchCase :
      RankedBranchCase
        (n := n) factor rankDefect)
    (children_reachable :
      ∀ task ∈
          (TRBrancha.outerFactoryCase
            hn hH routing factor rankDefect branchCase).children.tasks,
        Reachable task.1 task.2) :
    TRBranch
      (n := n) Reachable factor rankDefect where
  branch :=
    TRBrancha.outerFactoryCase
      hn hH routing factor rankDefect branchCase
  children_reachable := children_reachable

end
  TRBranch

namespace
  RRSchedu

/-- Compile outer-factory cases only along a reachable ranked task graph. -/
noncomputable def outerFactoryCases
    {d n : ℕ}
    {ι : Type}
    {Reachable :
      SPFactor
          (concreteBasicCommutators.{u} d) ι →
        ℕ → Prop}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      RFRoute
        (d := d) (n := n) ι)
    (cases :
      ∀
        (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (rankDefect : ℕ),
        Reachable factor rankDefect →
          RankedBranchCase
            (n := n) factor rankDefect)
    (children_reachable :
      ∀
        (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (rankDefect : ℕ)
        (hreachable : Reachable factor rankDefect)
        (task :
          SPFactor
              (concreteBasicCommutators.{u} d) ι ×
            ℕ),
        task ∈
            (TRBrancha.outerFactoryCase
              hn hH routing factor rankDefect
                (cases factor rankDefect hreachable)).children.tasks →
          Reachable task.1 task.2) :
    RRSchedu
      (n := n) Reachable :=
  ofBranches fun factor rankDefect hreachable =>
    TRBranch.outerFactoryCase
      hn hH routing factor rankDefect (cases factor rankDefect hreachable)
        (children_reachable factor rankDefect hreachable)

/--
Run well-founded residual recursion directly from reachable outer-factory
cases.
-/
noncomputable def recollect_factory_cases
    {d n : ℕ}
    {ι : Type}
    {Reachable :
      SPFactor
          (concreteBasicCommutators.{u} d) ι →
        ℕ → Prop}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (routing :
      RFRoute
        (d := d) (n := n) ι)
    (cases :
      ∀
        (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (rankDefect : ℕ),
        Reachable factor rankDefect →
          RankedBranchCase
            (n := n) factor rankDefect)
    (children_reachable :
      ∀
        (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (rankDefect : ℕ)
        (hreachable : Reachable factor rankDefect)
        (task :
          SPFactor
              (concreteBasicCommutators.{u} d) ι ×
            ℕ),
        task ∈
            (TRBrancha.outerFactoryCase
              hn hH routing factor rankDefect
                (cases factor rankDefect hreachable)).children.tasks →
          Reachable task.1 task.2)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (hreachable : Reachable factor rankDefect) :
    TRRecoll
      (n := n) factor :=
  (outerFactoryCases hn hH routing cases children_reachable)
    |>.residualRecollection factor rankDefect hreachable

end
  RRSchedu

namespace IBWork

/--
Recollect an exact concrete outer-bracket worklist using a Hall-ranked
scheduler restricted to reachable recursive tasks.
-/
noncomputable def recollection_reachable_scheduler
    {d n : ℕ}
    {ι : Type}
    {Reachable :
      SPFactor
          (concreteBasicCommutators.{u} d) ι →
        ℕ → Prop}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (scheduler :
      RRSchedu
        (n := n) Reachable)
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
    (hunchangedBasic : unchanged.IsBasic)
    (tasks_reachable :
      ∀ task ∈ rankedTasks packet inner right unchanged,
        Reachable task.1 task.2) :
    SSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight HEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (factors packet inner right) :=
  recollection_basic_residuals packet inner right hinnerTruncated
    added originalRight unchanged originalLeft hinnerTree hRightLeft
      hRightUnchanged hunchangedBasic
        (fun task htask =>
          scheduler.residualRecollection task.1 task.2
            (tasks_reachable task htask))

end IBWork

end TCTex
end Towers

/-!
# Ranked polynomial residuals as restricted-sharp factor tails

The ranked concrete residual scheduler constructs the true basic-reduction
residual without a parent-stratum normalizer. Restricted-sharp atomic
normalization independently recollects the concrete-to-semantic comparison.
Composing those two higher sources gives the intrinsic factor tail consumed by
direct signed Hall recursion.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace
  RFRoute

/--
Compile ranked outer-factory cases into the intrinsic restricted-sharp factor
tail at one active support weight.
-/
noncomputable def outer_factory_cases
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (routing :
      RFRoute
        (d := d) (n := n) ι)
    (cases :
      ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (rankDefect : ℕ),
        RankedBranchCase
          (n := n) factor rankDefect)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TPExp
      (lowerWeight := lowerWeight) hn (concreteBasicCommutators.{u} d) hH
        ι factor := by
  subst lowerWeight
  exact
    ((TRSchedu.recollect_factory_cases
        hn hH routing cases factor rankDefect).intrinsicResidualSource
          (TPRecoll.of_atomicNorm
            hn hH factor rfl hfactorTruncated
              (routing.factory factor) (routing.sharp factor)
                (routing.nextNormalizer factor))
          rfl).factorExpansion

end
  RFRoute

end TCTex
end Towers

/-!
# Ranked polynomial residual routing from comparison recollections

The reachable Hall-ranked scheduler consumes a factory for child-to-parent
outer residuals. Such a factory can be recovered from independently
recollected atomic-to-child comparisons and full basic residuals.

This file packages those smaller inputs as routing data and connects the
quotient construction directly to ranked scheduling. It is intentionally not
imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/--
Local ranked-routing inputs with outer residuals represented by independently
recollected atomic-to-child comparisons and full basic residuals.
-/
structure
    TFRoute
    {d n : ℕ}
    (ι : Type) where
  factory :
    ∀ factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι,
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d)
          (factor.word.weight HEAddres.weight)
  sharp :
    ∀ factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι,
      TSNormala
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight)
        (concreteBasicCommutators.{u} d)
  nextNormalizer :
    ∀ factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι,
      TSNormal
        (n := n)
        (lowerWeight :=
          factor.word.weight HEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
  comparisonFactory :
    ComparisonRecollectionFactory
      (d := d) (n := n) ι
  residualFactory :
    ConcreteRecollectionFactory
      (d := d) (n := n) ι

namespace
  TFRoute

open
  TRFtrya

/--
Recover the ordinary outer-factory routing data consumed by both unrestricted
and reachable ranked schedulers.
-/
noncomputable def outerFactoryRouting
    {d n : ℕ}
    {ι : Type}
    (routing :
      TFRoute
        (d := d) (n := n) ι) :
    RFRoute
      (d := d) (n := n) ι where
  factory := routing.factory
  sharp := routing.sharp
  nextNormalizer := routing.nextNormalizer
  outerFactory :=
    comparisonResidualFactories routing.comparisonFactory
      routing.residualFactory

/--
A correction schedule and strictly deeper normalizers supply the operational
part of comparison-factory routing.
-/
noncomputable def
    schedule_residual_factories
    {d n : ℕ}
    {ι : Type}
    (schedule :
      SFSched
        (n := n) (concreteBasicCommutators.{u} d))
    (normalizerAbove :
      ∀ lowerWeight strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (comparisonFactory :
      ComparisonRecollectionFactory
        (d := d) (n := n) ι)
    (residualFactory :
      ConcreteRecollectionFactory
        (d := d) (n := n) ι) :
    TFRoute
      (d := d) (n := n) ι where
  factory factor :=
    schedule.factory
      (factor.word.weight HEAddres.weight)
  sharp factor :=
    TSNormala.ofNormalizerAbove
      (normalizerAbove
        (factor.word.weight HEAddres.weight))
  nextNormalizer factor :=
    normalizerAbove
      (factor.word.weight HEAddres.weight)
      (factor.word.weight HEAddres.weight + 1) (by omega)
  comparisonFactory := comparisonFactory
  residualFactory := residualFactory

end
  TFRoute

end TCTex
end Towers

/-!
# Support-local ranked polynomial residual collection

The original ranked outer-factory routing record asks for normalizers above
every symbolic factor. Direct filtration recursion only has to route factors
reachable from one active support stratum. This file narrows the routing
interface accordingly and runs the Hall-ranked residual recursion while
preserving that support bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

/-- Outer-factory routing restricted to factors supported in one active stratum. -/
structure
    PFRoute
    {d n lowerWeight : ℕ}
    (ι : Type) where
  factory :
    ∀ factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι,
      lowerWeight ≤ factor.word.weight HEAddres.weight →
        TSFtry
          (n := n) (concreteBasicCommutators.{u} d)
            (factor.word.weight HEAddres.weight)
  sharp :
    ∀ factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι,
      lowerWeight ≤ factor.word.weight HEAddres.weight →
        TSNormala
          (n := n)
          (lowerWeight :=
            factor.word.weight HEAddres.weight)
          (concreteBasicCommutators.{u} d)
  nextNormalizer :
    ∀ factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι,
      lowerWeight ≤ factor.word.weight HEAddres.weight →
        TSNormal
          (n := n)
          (lowerWeight :=
            factor.word.weight HEAddres.weight + 1)
          (concreteBasicCommutators.{u} d)
  outerFactory :
    TRFtrya
      (d := d) (n := n) ι

namespace
  PFRoute

/--
A correction schedule, normalizers strictly above the active support bound,
and a full-weight outer residual factory supply support-local ranked routing.
-/
noncomputable def factory_above_outer
    {d n lowerWeight : ℕ}
    {ι : Type}
    (schedule :
      SFSched
        (n := n) (concreteBasicCommutators.{u} d))
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (outerFactory :
      TRFtrya
        (d := d) (n := n) ι) :
    PFRoute
      (d := d) (n := n) (lowerWeight := lowerWeight) ι where
  factory factor _hfactorSupported :=
    schedule.factory
      (factor.word.weight HEAddres.weight)
  sharp factor hfactorSupported :=
    TSNormala.ofNormalizerAbove
      (fun strongerWeight hstronger =>
        normalizerAbove strongerWeight
          (hfactorSupported.trans_lt hstronger))
  nextNormalizer factor hfactorSupported :=
    normalizerAbove
      (factor.word.weight HEAddres.weight + 1)
      (by omega)
  outerFactory := outerFactory

end
  PFRoute

namespace TRBrancha

/-- Compile one support-local leaf or inner-reduction case. -/
noncomputable def supported_factory_case
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (routing :
      PFRoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (hfactorSupported :
      lowerWeight ≤ factor.word.weight HEAddres.weight)
    (branchCase :
      RankedBranchCase
        (n := n) factor rankDefect) :
    TRBrancha
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
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (routing :
      PFRoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (hfactorSupported :
      lowerWeight ≤ factor.word.weight HEAddres.weight)
    (branchCase :
      RankedBranchCase
        (n := n) factor rankDefect)
    {task :
      SPFactor
          (concreteBasicCommutators.{u} d) ι ×
        ℕ}
    (htask :
      task ∈
        (supported_factory_case hn hH routing factor rankDefect
          hfactorSupported branchCase).children.tasks) :
    task.1.word.weight HEAddres.weight =
      factor.word.weight HEAddres.weight := by
  cases branchCase with
  | leaf leafCase =>
      cases leafCase <;>
        simp [supported_factory_case, ofLeafCase, leaf_of_terminal,
          leaf_tree_basic, leaf_commutator_self,
          leaf_reversed_basic, leaf_weight_one,
          ofResidRecollect,
          SPFactor.RCSrc.empty] at htask
  | innerReductionOuter innerCase =>
      rcases innerCase with
        ⟨innerWord, rightWord, hword, hfactorTruncated, added, originalRight,
          unchanged, originalLeft, hinnerTree, hRightLeft, hRightUnchanged,
          hunchangedBasic, rankDefect_eq⟩
      subst rankDefect
      have htask' :
          task ∈
            IRChildr.rankedTasks
              factor innerWord rightWord hword unchanged := by
        simpa only [supported_factory_case,
          innerComparisonFactory,
          IRChildr.tasks_ranked_task]
          using htask
      rcases
          IRChildr.index_ranked_tasks
            factor innerWord rightWord hword unchanged htask' with
        ⟨i, rfl⟩
      exact
        CEWord.inner_outer_factor
          factor innerWord rightWord hword i

end TRBrancha

namespace
  PFRoute

/--
Run Hall-ranked recursion using only routing data supported in the active
stratum.
-/
noncomputable def residual_recollection_cases
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (routing :
      PFRoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (cases :
      ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (rankDefect : ℕ),
        lowerWeight ≤ factor.word.weight HEAddres.weight →
          factor.word.weight HEAddres.weight < n →
            RankedBranchCase
              (n := n) factor rankDefect)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (hfactorSupported :
      lowerWeight ≤ factor.word.weight HEAddres.weight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRRecoll
      (n := n) factor :=
  Classical.choice <|
    SPFactor.ranked_descends_induction
      (motive := fun child childRankDefect =>
        lowerWeight ≤ child.word.weight HEAddres.weight →
          child.word.weight HEAddres.weight < n →
            Nonempty
              (TRRecoll
                (n := n) child))
      (fun parent parentRankDefect ih hparentSupported hparentTruncated =>
        let branch :=
          TRBrancha.supported_factory_case
            hn hH routing parent parentRankDefect hparentSupported
              (cases parent parentRankDefect hparentSupported hparentTruncated)
        ⟨branch.recollect fun task htask =>
          Classical.choice <|
            ih task.1 task.2 (branch.children.tasks_descend task htask)
              (by
                rw [
                  TRBrancha.word_outer_factory
                    hn hH routing parent parentRankDefect hparentSupported
                      (cases parent parentRankDefect hparentSupported
                        hparentTruncated) htask]
                exact hparentSupported)
              (by
                rw [
                  TRBrancha.word_outer_factory
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
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (routing :
      PFRoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (cases :
      ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (rankDefect : ℕ),
        lowerWeight ≤ factor.word.weight HEAddres.weight →
          factor.word.weight HEAddres.weight < n →
            RankedBranchCase
              (n := n) factor rankDefect)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TPExp
      (lowerWeight := lowerWeight) hn (concreteBasicCommutators.{u} d) hH
        ι factor := by
  subst lowerWeight
  exact
    ((routing.residual_recollection_cases hn hH cases factor rankDefect le_rfl
        hfactorTruncated).intrinsicResidualSource
          (TPRecoll.of_atomicNorm
            hn hH factor rfl hfactorTruncated
              (routing.factory factor le_rfl) (routing.sharp factor le_rfl)
                (routing.nextNormalizer factor le_rfl))
          rfl).factorExpansion

/--
Run support-local Hall-ranked recursion from classifiers restricted to the
active full weight. Every emitted child preserves that exact word weight.
-/
noncomputable def recollection_exact_cases
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (routing :
      PFRoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (cases :
      ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (rankDefect : ℕ),
        factor.word.weight HEAddres.weight = lowerWeight →
          factor.word.weight HEAddres.weight < n →
            RankedBranchCase
              (n := n) factor rankDefect)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRRecoll
      (n := n) factor :=
  Classical.choice <|
    SPFactor.ranked_descends_induction
      (motive := fun child childRankDefect =>
        child.word.weight HEAddres.weight = lowerWeight →
          child.word.weight HEAddres.weight < n →
            Nonempty
              (TRRecoll
                (n := n) child))
      (fun parent parentRankDefect ih hparentWeight hparentTruncated =>
        let branch :=
          TRBrancha.supported_factory_case
            hn hH routing parent parentRankDefect (by omega)
              (cases parent parentRankDefect hparentWeight hparentTruncated)
        ⟨branch.recollect fun task htask =>
          Classical.choice <|
            ih task.1 task.2 (branch.children.tasks_descend task htask)
              (by
                rw [
                  TRBrancha.word_outer_factory
                    hn hH routing parent parentRankDefect (by omega)
                      (cases parent parentRankDefect hparentWeight
                        hparentTruncated) htask]
                exact hparentWeight)
              (by
                rw [
                  TRBrancha.word_outer_factory
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
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (routing :
      PFRoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (cases :
      ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (rankDefect : ℕ),
        factor.word.weight HEAddres.weight = lowerWeight →
          factor.word.weight HEAddres.weight < n →
            RankedBranchCase
              (n := n) factor rankDefect)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TPExp
      (lowerWeight := lowerWeight) hn (concreteBasicCommutators.{u} d) hH
        ι factor := by
  subst lowerWeight
  exact
    ((routing.recollection_exact_cases hn hH cases factor
        rankDefect rfl hfactorTruncated).intrinsicResidualSource
          (TPRecoll.of_atomicNorm
            hn hH factor rfl hfactorTruncated
              (routing.factory factor le_rfl) (routing.sharp factor le_rfl)
                (routing.nextNormalizer factor le_rfl))
          rfl).factorExpansion

end
  PFRoute

end TCTex
end Towers
