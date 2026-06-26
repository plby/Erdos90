import Submission.Group.Zassenhaus.ReverseOrientationResiduals
import Submission.Group.Zassenhaus.RootSwapNormalization
import Submission.Group.Zassenhaus.OuterBracketRecollection
import Submission.Group.Zassenhaus.FullWeightFactory
import Submission.Group.Zassenhaus.SignedReductionFactors
import Submission.Group.Zassenhaus.CoefficientNegationRouting
import Submission.Group.HallBasic.JacobiFrontierWeight
import Submission.Group.Zassenhaus.PolynomialRankedSupport
import Submission.Group.HallBasic.JacobiValueScaling
import Submission.Group.Zassenhaus.JacobiContinuationBuilders
import Submission.Group.Zassenhaus.JacobiFrontierRouting
import Submission.Group.Zassenhaus.SignCorrectedSwaps
import Submission.Group.HallBasic.AssociatedGradedSpanning
import Submission.Group.Zassenhaus.PolynomialConcreteSemantic
import Submission.Group.Zassenhaus.PolynomialBracketSupport
import Submission.Group.Zassenhaus.RankedStructuralRestarts
import Submission.Group.Zassenhaus.HallRankDescent
import Submission.Group.HallBasic.StandardSequence


-- Merged from PolynomialConcreteBasic.lean

/-!
# Ranked Hall orientation for polynomial Jacobi frontiers with basic children

The ordinary two-basic-child orientation layer remembers only which child is
an exposed commutator. Ranked descendant scheduling needs the inequalities
proved at the same time: after choosing the left-normed orientation
`[[a, b], v]`, one has `v < b < a`.

This file preserves that stronger Hall certificate and compiles either
orientation into the ranked expanded-Jacobi decomposition consumed by
reachable descendant scheduling.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open CEWord

universe u

/--
A two-basic-child Jacobi frontier oriented as `[[a, b], v]`, retaining the
strict inequalities needed by ranked descendant recursion.
-/
inductive BasicChildrenOrientation
    {d : ℕ}
    (left right : HallTree (FreeGenerator.{u} d)) where
  | left
      (left₁ left₂ : HallTree (FreeGenerator.{u} d))
      (tree_eq : left = .commutator left₁ left₂)
      (right_lt_left₂ : right < left₂)
      (left₂_lt_left₁ : left₂ < left₁)
      (left₁_isBasic : left₁.IsBasic)
      (left₂_isBasic : left₂.IsBasic)
  | right
      (right₁ right₂ : HallTree (FreeGenerator.{u} d))
      (tree_eq : right = .commutator right₁ right₂)
      (left_lt_right₂ : left < right₂)
      (right₂_lt_right₁ : right₂ < right₁)
      (right₁_isBasic : right₁.IsBasic)
      (right₂_isBasic : right₂.IsBasic)

/--
Hall admissibility orients every two-basic-child frontier while preserving
the inequalities discarded by the earlier shape-only dispatcher.
-/
theorem children_ranked_orientation
    {d : ℕ}
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (hchildrenNe : left ≠ right)
    (hforwardNonbasic : ¬(HallTree.commutator left right).IsBasic)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic) :
    Nonempty (BasicChildrenOrientation left right) := by
  rcases
      HallTree.inadmissible_orientation_children
        left right hleftBasic hrightBasic hchildrenNe hforwardNonbasic
          hreverseNonbasic with
    hleft | hright
  · rcases hleft with ⟨left₁, left₂, hleft, _hrightLeft, hbad⟩
    have hleftBasic' : (HallTree.commutator left₁ left₂).IsBasic := by
      simpa only [hleft] using hleftBasic
    rcases (HallTree.isBasic_commutator left₁ left₂).mp hleftBasic' with
      ⟨hleft₁Basic, hleft₂Basic, hleft₂Left₁, _hadmissible⟩
    exact
      ⟨.left left₁ left₂ hleft (lt_of_not_ge hbad) hleft₂Left₁
        hleft₁Basic hleft₂Basic⟩
  · rcases hright with ⟨right₁, right₂, hright, _hleftRight, hbad⟩
    have hrightBasic' : (HallTree.commutator right₁ right₂).IsBasic := by
      simpa only [hright] using hrightBasic
    rcases (HallTree.isBasic_commutator right₁ right₂).mp hrightBasic' with
      ⟨hright₁Basic, hright₂Basic, hright₂Right₁, _hadmissible⟩
    exact
      ⟨.right right₁ right₂ hright (lt_of_not_ge hbad) hright₂Right₁
        hright₁Basic hright₂Basic⟩

/-- Choose the ranked Hall orientation of a two-basic-child frontier. -/
noncomputable def childrenJacobiOrientation
    {d : ℕ}
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (hchildrenNe : left ≠ right)
    (hforwardNonbasic : ¬(HallTree.commutator left right).IsBasic)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic) :
    BasicChildrenOrientation left right :=
  Classical.choice
    (children_ranked_orientation left right hleftBasic
      hrightBasic hchildrenNe hforwardNonbasic hreverseNonbasic)

/--
Ranked expanded-Jacobi data after orienting a two-basic-child frontier.
The reversed case carries the sign-corrected swapped factor.
-/
inductive CJDispat
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right) where
  | forward
      (ranked :
        ERDecomp
          factor)
  | swapped
      (ranked :
        ERDecomp
          (childrenSwapFactor factor left right hleftBasic hrightBasic
            htree))

namespace CJDispat

/-- Forward dispatch retains the incoming symmetric bracket-rank defect. -/
theorem forward_rank_defect
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (_hleftBasic : left.IsBasic)
    (_hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (ranked :
      ERDecomp
        factor) :
    expandedJacobiParent ranked.decomposition =
      HallTree.bracketRankDefect
        (left.weight + right.weight) left right := by
  have hroot :
      HallTree.commutator left right =
        .commutator
          (.commutator
            (tree ranked.decomposition.left)
            (tree ranked.decomposition.middle))
          (tree ranked.decomposition.right) := by
    rw [← htree, ranked.decomposition.tree_eq]
  injection hroot with hleft hright
  simp only [expandedJacobiParent]
  rw [← hleft, ← hright]
  simp only [tree_commutator, ← hleft]

/-- Swapped dispatch retains the incoming symmetric bracket-rank defect. -/
theorem swapped_rank_defect
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (ranked :
      ERDecomp
        (childrenSwapFactor factor left right hleftBasic hrightBasic
          htree)) :
    expandedJacobiParent ranked.decomposition =
      HallTree.bracketRankDefect
        (left.weight + right.weight) left right := by
  have hroot :
      HallTree.commutator right left =
        .commutator
          (.commutator
            (tree ranked.decomposition.left)
            (tree ranked.decomposition.middle))
          (tree ranked.decomposition.right) := by
    rw [← tree_children_swap factor left right hleftBasic
      hrightBasic htree, ranked.decomposition.tree_eq]
  injection hroot with hright hleft
  simp only [expandedJacobiParent]
  rw [← hright, ← hleft]
  simp only [tree_commutator, ← hright,
    HallTree.bracketRankDefect, min_comm, add_comm]

end CJDispat

/--
Compile the ranked Hall orientation into forward or sign-corrected swapped
expanded-Jacobi data.
-/
noncomputable def rankedJacobiDispatch
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hchildrenNe : left ≠ right)
    (hforwardNonbasic : ¬(HallTree.commutator left right).IsBasic)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic) :
    CJDispat factor left right hleftBasic hrightBasic
      htree := by
  let orientation :=
    childrenJacobiOrientation left right hleftBasic hrightBasic
      hchildrenNe hforwardNonbasic hreverseNonbasic
  cases orientation with
  | left left₁ left₂ hleft hrightLeft₂ hleft₂Left₁ hleft₁Basic
      hleft₂Basic =>
      exact
        .forward
          (ERDecomp.nonbasic_commutator_tree
            factor left₁ left₂ right
              (by simpa only [hleft] using htree)
              (by simpa only [hleft] using hforwardNonbasic)
              hrightLeft₂ hleft₂Left₁ hleft₁Basic hleft₂Basic)
  | right right₁ right₂ hright hleftRight₂ hright₂Right₁ hright₁Basic
      hright₂Basic =>
      exact
        .swapped
          (ERDecomp.nonbasic_commutator_tree
            (childrenSwapFactor factor left right hleftBasic hrightBasic
              htree)
            right₁ right₂ left
              (by simp only [tree_children_swap, hright])
              (by simpa only [hright] using hreverseNonbasic)
              hleftRight₂ hright₂Right₁ hright₁Basic hright₂Basic)

end TCTex
end Submission

-- Merged from PolynomialConcreteInner.lean

/-!
# Reachable routing through polynomial outer-bracket structural restarts

Support-local signed collection constructs residual recollections only for
tasks reachable from the active source.  A reconstruction structural restart
emits the same finite ranked task list as the atomic outer-bracket worklist,
followed by a normalized strictly higher quotient.

This file feeds a reachable ranked scheduler through that restart boundary.
The result recollects the exact reconstructed outer bracket while keeping the
recursive obligations restricted to its emitted tasks.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open scoped commutatorElement

open CEWord

namespace IBRecons

/--
Recollect an exact reconstruction outer bracket through a ranked scheduler
restricted to reachable tasks.
-/
noncomputable def
    structural_restart_reachable
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
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
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (tasks_reachable :
      ∀ task ∈
          IBWork.rankedTasks
            packet inner right unchanged,
        Reachable task.1 task.2) :
    SSRecol
      (n := n)
      (lowerWeight := inner.word.weight HEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (factors packet inner right) :=
  recollect_restart_residuals
    hn hH packet inner right normalizerAbove hinnerTruncated added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic
          (fun task htask =>
            scheduler.residualRecollection task.1 task.2
              (tasks_reachable task htask))

/--
The reachable structural-restart route still evaluates exactly to the
original outer commutator.
-/
theorem
    reachable_ranked_scheduler
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
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
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (tasks_reachable :
      ∀ task ∈
          IBWork.rankedTasks
            packet inner right unchanged,
        Reachable task.1 task.2)
    (e :
      ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (structural_restart_reachable
          hn hH packet scheduler inner right normalizerAbove hinnerTruncated
            added originalRight unchanged originalLeft hinnerTree hRightLeft
              hRightUnchanged hunchangedBasic tasks_reachable).higherSource =
      ⁅inner.eval (n := n) e, right.eval (n := n) e⁆ :=
  higher_restart_residuals
    hn hH packet inner right normalizerAbove hinnerTruncated added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic
          (fun task htask =>
            scheduler.residualRecollection task.1 task.2
              (tasks_reachable task htask))
          e

end IBRecons

end TCTex
end Submission

/-!
# Callbacks for polynomial outer-bracket structural restarts

The reconstruction structural restart has a deliberately small recursive
boundary: every ranked child emitted by its atomic outer-bracket worklist
must have a concrete basic-residual recollection.  The normalized quotient is
then appended automa at strictly greater total weight.

This file packages that boundary as callbacks.  It also records constructors
from unrestricted and reachability-local Hall-ranked schedulers.  A future
signed collection builder can target these callbacks directly instead of the
same-layer outer-residual factory.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open scoped commutatorElement

open CEWord

/--
Recursive child recollections required by reconstruction structural
restarts.
-/
structure
    RRCallba
    {d n : ℕ}
    (ι : Type) where
  basicResidual :
    ∀
      (packet :
        PFSubsti.TAPkt.{u}
          d n)
      (inner right :
        SPFactor
          (concreteBasicCommutators.{u} d) ι)
      (_hinnerTruncated :
        inner.word.weight HEAddres.weight < n)
      (added originalRight unchanged originalLeft :
        HallTree (FreeGenerator.{u} d))
      (_hinnerTree :
        tree inner.word = .commutator added originalRight)
      (_hRightLeft : originalRight < originalLeft)
      (_hRightUnchanged : originalRight < unchanged)
      (_hunchangedBasic : unchanged.IsBasic)
      (task :
        SPFactor
              (concreteBasicCommutators.{u} d) ι ×
          ℕ),
      task ∈
          IBWork.rankedTasks
            packet inner right unchanged →
        TRRecoll
          (n := n) task.1

namespace
  RRCallba

/--
Run one exact reconstruction structural restart from its recursive child
callbacks.
-/
noncomputable def sourceRecollection
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (callbacks :
      RRCallba
        (d := d) (n := n) ι)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    SSRecol
      (n := n)
      (lowerWeight := inner.word.weight HEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (IBRecons.factors
        packet inner right) :=
  IBRecons.recollect_restart_residuals
    hn hH packet inner right normalizerAbove hinnerTruncated added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic
          (callbacks.basicResidual packet inner right hinnerTruncated added
            originalRight unchanged originalLeft hinnerTree hRightLeft
              hRightUnchanged hunchangedBasic)

/--
The callback-driven restart recollection evaluates to the original outer
commutator.
-/
theorem higher_source_recollection
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (callbacks :
      RRCallba
        (d := d) (n := n) ι)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (e :
      ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (callbacks.sourceRecollection hn hH packet inner right normalizerAbove
          hinnerTruncated added originalRight unchanged originalLeft hinnerTree
            hRightLeft hRightUnchanged hunchangedBasic).higherSource =
      ⁅inner.eval (n := n) e, right.eval (n := n) e⁆ :=
  IBRecons.higher_restart_residuals
    hn hH packet inner right normalizerAbove hinnerTruncated added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic
          (callbacks.basicResidual packet inner right hinnerTruncated added
            originalRight unchanged originalLeft hinnerTree hRightLeft
              hRightUnchanged hunchangedBasic)
          e

/-- Every unrestricted ranked residual scheduler supplies restart callbacks. -/
noncomputable def rankedResidualScheduler
    {d n : ℕ}
    {ι : Type}
    (scheduler :
      TRSchedu
        (d := d) (n := n) (ι := ι)) :
    RRCallba
      (d := d) (n := n) ι where
  basicResidual _packet _inner _right _hinnerTruncated _added _originalRight
      _unchanged _originalLeft _hinnerTree _hRightLeft _hRightUnchanged
      _hunchangedBasic task _htask :=
    scheduler.residualRecollection task.1 task.2

/--
Every reachable scheduler supplies restart callbacks once its emitted
outer-bracket tasks are certified reachable.
-/
noncomputable def reachableRankedScheduler
    {d n : ℕ}
    {ι : Type}
    {Reachable :
      SPFactor
          (concreteBasicCommutators.{u} d) ι →
        ℕ → Prop}
    (scheduler :
      RRSchedu
        (n := n) Reachable)
    (tasks_reachable :
      ∀
        (packet :
          PFSubsti.TAPkt.{u}
            d n)
        (inner right :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (_hinnerTruncated :
          inner.word.weight HEAddres.weight < n)
        (added originalRight unchanged originalLeft :
          HallTree (FreeGenerator.{u} d))
        (_hinnerTree :
          tree inner.word = .commutator added originalRight)
        (_hRightLeft : originalRight < originalLeft)
        (_hRightUnchanged : originalRight < unchanged)
        (_hunchangedBasic : unchanged.IsBasic)
        (task :
          SPFactor
                (concreteBasicCommutators.{u} d) ι ×
            ℕ),
        task ∈
            IBWork.rankedTasks
              packet inner right unchanged →
          Reachable task.1 task.2) :
    RRCallba
      (d := d) (n := n) ι where
  basicResidual packet inner right hinnerTruncated added originalRight
      unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
      hunchangedBasic task htask :=
    scheduler.residualRecollection task.1 task.2
      (tasks_reachable packet inner right hinnerTruncated added originalRight
        unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
          hunchangedBasic task htask)

end
  RRCallba

end TCTex
end Submission

/-!
# Correction-packet routing through polynomial structural restarts

The exact reconstruction outer worklist and the concrete Hall-Petresco
correction packet evaluate to the same outer commutator.  Consequently, a
callback-driven structural restart for the reconstruction worklist transports
directly to the correction packet source.

This is the packet-facing endpoint needed by signed collection: recursive
ranked atomic children are handled by callbacks, while the reconstruction
quotient is appended as a normalized strictly higher block.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open scoped commutatorElement

namespace
  RRCallba

/--
Transport callback-driven reconstruction recollection to the concrete
Hall-Petresco correction packet.
-/
noncomputable def correctionSourceRecollection
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (callbacks :
      RRCallba
        (d := d) (n := n) ι)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
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
      (lowerWeight := inner.word.weight HEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (IBWork.correctionPacket
        packet inner right).factors :=
  (callbacks.sourceRecollection hn hH packet inner right normalizerAbove
    hinnerTruncated added originalRight unchanged originalLeft hinnerTree
      hRightLeft hRightUnchanged hunchangedBasic)
    |>.of_list_eq
      (IBRecons.list_factors_packet
        packet inner right)

/--
The packet-facing callback route evaluates exactly to the original outer
commutator.
-/
theorem list_higher_recollection
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (callbacks :
      RRCallba
        (d := d) (n := n) ι)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
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
    (e :
      ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (callbacks.correctionSourceRecollection hn hH packet inner right
          normalizerAbove hinnerTruncated added originalRight unchanged
            originalLeft hinnerTree hRightLeft hRightUnchanged
              hunchangedBasic).higherSource =
      ⁅inner.eval (n := n) e, right.eval (n := n) e⁆ :=
  callbacks.higher_source_recollection hn hH packet inner right
    normalizerAbove hinnerTruncated added originalRight unchanged originalLeft
      hinnerTree hRightLeft hRightUnchanged hunchangedBasic e

end
  RRCallba

end TCTex
end Submission

/-!
# Automatic routing through polynomial outer-bracket structural restarts

The atomic outer-bracket worklist emitted by a reconstruction restart has two
kinds of factors:

* retained wrappers from the inner basic-reduction packet; and
* Hall-Petresco terminal corrections strictly heavier than the inner factor.

The wrappers have basic expanded Hall trees, so their concrete residuals are
trivial.  The heavier corrections can be recollected by a strictly deeper
signed semantic normalizer at their own weights.  Thus one restart requires
no external child callbacks once deeper normalizers are available.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open scoped commutatorElement

open CEWord

namespace IBWork

/--
Every ranked child emitted by an atomic outer-bracket worklist has an
automatic concrete residual recollection from strictly deeper normalizers.
-/
noncomputable def
    tasks_normalizer_above
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (unchanged : HallTree (FreeGenerator.{u} d))
    (task :
      SPFactor
            (concreteBasicCommutators.{u} d) ι ×
        ℕ)
    (htask : task ∈ rankedTasks packet inner right unchanged) :
    TRRecoll
      (n := n) task.1 := by
  classical
  apply Classical.choice
  have hfactor : task.1 ∈ factors packet inner right := by
    rcases factor_ranked_tasks packet inner right unchanged htask with
      ⟨factor, hfactor, htaskEq⟩
    rw [htaskEq]
    exact hfactor
  rcases
      or_neg_factors
        packet inner right hfactor with
    hwrapped | hhigher
  · rcases hwrapped with ⟨left, hleft, hfactorEq⟩
    rcases hfactorEq with hfactorEq | hfactorEq
    · rw [hfactorEq]
      exact
        ⟨TRRecoll.tree_basic
          left (tree_basic_factors inner hleft)⟩
    · rw [hfactorEq]
      exact
        ⟨TRRecoll.tree_basic
          left.neg (by
            simpa only [SPFactor.word_neg] using
              (tree_basic_factors inner hleft))⟩
  · exact
      ⟨TRRecoll.ofNormalizer
        hn hH (normalizerAbove _ hhigher) task.1 rfl
          (isTruncated_factors packet inner right hinnerTruncated task.1
            hfactor)⟩

end IBWork

namespace IBRecons

/--
Automatically recollect an exact reconstruction outer bracket using only
normalizers strictly above the inner factor's weight.
-/
noncomputable def
    structural_restart_normalizer
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    SSRecol
      (n := n)
      (lowerWeight := inner.word.weight HEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (factors packet inner right) :=
  recollect_restart_residuals
    hn hH packet inner right normalizerAbove hinnerTruncated added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic
          (fun task htask =>
            IBWork.tasks_normalizer_above
              hn hH packet inner right normalizerAbove hinnerTruncated
                unchanged task htask)

/--
The automatic structural-restart route evaluates exactly to the original
outer commutator.
-/
theorem
    structural_restart_above
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (e :
      ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (structural_restart_normalizer
          hn hH packet inner right normalizerAbove hinnerTruncated added
            originalRight unchanged originalLeft hinnerTree hRightLeft
              hRightUnchanged hunchangedBasic).higherSource =
      ⁅inner.eval (n := n) e, right.eval (n := n) e⁆ :=
  higher_restart_residuals
    hn hH packet inner right normalizerAbove hinnerTruncated added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic
          (fun task htask =>
            IBWork.tasks_normalizer_above
              hn hH packet inner right normalizerAbove hinnerTruncated
                unchanged task htask)
          e

/--
Automatically route the concrete Hall-Petresco correction packet through a
reconstruction structural restart.
-/
noncomputable def
    ranked_structural_restart
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    SSRecol
      (n := n)
      (lowerWeight := inner.word.weight HEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (IBWork.correctionPacket
        packet inner right).factors :=
  (structural_restart_normalizer
    hn hH packet inner right normalizerAbove hinnerTruncated added
      originalRight unchanged originalLeft hinnerTree hRightLeft
        hRightUnchanged hunchangedBasic)
    |>.of_list_eq
      (list_factors_packet packet inner right)

end IBRecons

end TCTex
end Submission

-- Merged from PolynomialConcreteJacobiFrontierLowCutoffCollection.lean

/-!
# Automatic signed-polynomial residual collection below the Jacobi frontier

At cutoff at most six, every nonterminal true Hall-tree quotient residual has
weight at most two.  The Jacobi frontier starts in weight three, so a supplied
truncated Hall-Petresco packet automa yields product and inverse
coordinate polynomials.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace
  JFBuild

/--
At cutoff at most six, a truncated Hall-Petresco packet has no remaining
Jacobi-frontier residual obligations.
-/
noncomputable def automatic_n_six
    {d n : ℕ}
    {hn : 2 ≤ n}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hn6 : n ≤ 6) :
    JFBuild.{u}
      (d := d) (n := n) hn where
  packet := packet
  jacobiFrontierResidual lowerWeight hnonterminal factor hfactorWeight
      _hfactorTruncated htreeNonbasic left right htree hne hreverse := by
    exfalso
    apply
      HallTree.false_swap_not
        left right
    · rw [← htree, CEWord.tree_weight,
        hfactorWeight]
      omega
    · exact hne
    · exact fun hbasic => htreeNonbasic (htree.symm ▸ hbasic)
    · exact hreverse

end
  JFBuild

open
  JFBuild

/--
For canonical Hall families at cutoff at most six, a supplied truncated
Hall-Petresco packet constructs product coordinate polynomials.
-/
theorem
    frontier_automatic_collect
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn6 : n ≤ 6)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d))) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_frontier_collect
    hn e (automatic_n_six packet hn6)

/--
For canonical Hall families at cutoff at most six, a supplied truncated
Hall-Petresco packet constructs inverse coordinate polynomials.
-/
theorem
    commutators_automatic_collect
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn6 : n ≤ 6)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d)) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_reduction_builder
    hn e (automatic_n_six packet hn6)

/--
For canonical Hall families at cutoff at most six, a universal Hall-Petresco
packet constructs product coordinate polynomials.
-/
theorem
    commutators_automatic_univ
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn6 : n ≤ 6)
    (packet :
      PFSubsti.UAInt.{u})
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d))) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  frontier_automatic_collect
    hn hn6 (packet.truncatedAll (d := d) (n := n)) e

/--
For canonical Hall families at cutoff at most six, a universal Hall-Petresco
packet constructs inverse coordinate polynomials.
-/
theorem
    automatic_univ_collect
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn6 : n ≤ 6)
    (packet :
      PFSubsti.UAInt.{u})
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d)) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_automatic_collect
    hn hn6 (packet.truncatedAll (d := d) (n := n)) e

end TCTex
end Submission

-- Merged from PolynomialConcreteJacobiValueResidual.lean

/-!
# Signed-polynomial Jacobi value residuals

The atomic Jacobi coordinate packet compares explicit Hall reductions.  The
companion packet in this file compares the original powered nested
commutator value with the two powered Jacobi descendant values.  Its
evaluation lies one lower-central stratum higher and is therefore the
recursive value-level correction left by the Jacobi rewrite.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace CEWord

universe u

/--
Value-level Jacobi residual: original nested factor inverse, followed by the
two signed Jacobi descendants.
-/
noncomputable def jacobiValueSource
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  [factor.neg,
    jacobiFirstFactor factor left middle right hword,
    jacobiSecondFactor factor left middle right hword]

/-- Truncation of the original factor physically truncates its value residual. -/
theorem truncated_jacobi_raw
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (hfactor :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (jacobiValueSource factor left middle right hword) := by
  intro x hx
  simp only [jacobiValueSource, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · simpa only [SPFactor.word_neg] using hfactor
  · simpa only [jacobi_first_factor] using hfactor
  · simpa only [word_jacobi_second] using hfactor

/-- The symbolic Jacobi value residual evaluates one lower-central stratum higher. -/
theorem jacobi_value_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (jacobiValueSource factor left middle right hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  have hfree :=
    HallTree.jacobi_zpow_series
      (tree left) (tree middle) (tree right) (factor.coefficient.eval e)
  have hmap :=
    Subgroup.lowerCentralSeries.map
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight HEAddres.weight)
      (Subgroup.mem_map_of_mem
        (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (by
          rw [hword, CWord.weight_commutator,
            CWord.weight_commutator, ← tree_weight, ← tree_weight,
            ← tree_weight]
          exact hfree))
  rw [jacobiValueSource,
    SPFactor.listEval_cons,
    SPFactor.listEval_cons,
    SPFactor.listEval_cons,
    SPFactor.listEval_nil, mul_one]
  rw [← tree_commutator left middle,
    ← tree_commutator (.commutator left middle) right,
    ← tree_commutator left right,
    ← tree_commutator (.commutator left right) middle,
    ← tree_commutator middle right,
    ← tree_commutator (.commutator middle right) left] at hmap
  rw [map_mul, map_inv, map_zpow, map_mul, map_zpow, map_zpow,
    lower_truncation_tree,
    lower_truncation_tree,
    lower_truncation_tree] at hmap
  rw [SPFactor.eval_neg,
    SPFactor.eval, SPFactor.eval,
    SPFactor.eval,
    coefficient_jacobi_factor,
    jacobi_second_factor]
  simpa only [map_mul, map_inv, map_zpow,
    SPFactor.eval,
    SPFactor.wordValue,
    jacobiFirstFactor, jacobiSecondFactor,
    SPFactor.word_neg,
    SPFactor.word_reword, hword, zpow_neg] using hmap

/--
Inverse orientation of the value-level Jacobi residual.  This is convenient
when it appears at the tail of a continuation packet.
-/
noncomputable def jacobiRawSource
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  SPFactor.inverseList
    (jacobiValueSource factor left middle right hword)

/-- Truncation is preserved by inversion of the Jacobi value residual. -/
theorem truncated_jacobi_source
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (hfactor :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (jacobiRawSource factor left middle right hword) := by
  exact
    SPFactor.truncated_inverse_list
      (truncated_jacobi_raw
        factor left middle right hword hfactor)

/-- The inverse Jacobi value residual also lies one lower-central stratum higher. -/
theorem jacobi_raw_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (jacobiRawSource factor left middle right hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  rw [jacobiRawSource,
    SPFactor.list_eval_inverse]
  exact
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight HEAddres.weight)).inv_mem
        (jacobi_value_series
          factor left middle right hword e)

end CEWord
end TCTex
end Submission

-- Merged from PolynomialConcreteNonbasicNonselfReductionCollection.lean

/-!
# Signed-polynomial collection reduced to non-basic non-self expanded trees

Basic expanded Hall trees and symbolic self-commutators have automatic true
residual recollections.  This file packages both eliminations: an arbitrary
cutoff collector now needs explicit residual recollection only for non-basic
words that are not syntactic self-commutators.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
A cutoff Hall-Petresco packet and upward recollection of true residuals only
for non-basic factors that are not symbolic self-commutators.
-/
structure
    NNBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  nonbasicNonselfResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ¬(CEWord.tree factor.word).IsBasic →
                (∀ word :
                  CWord
                    (HEAddres
                      (concreteBasicCommutators.{u} d)),
                    factor.word ≠ .commutator word word) →
                  TRRecoll
                    (n := n) factor

namespace
  NNBuild

open
  TRRecoll

/--
Fill every symbolic self-commutator residual with the empty recollection and
leave only non-basic non-self residuals to the caller.
-/
noncomputable def nonbasicReductionBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      NNBuild.{u}
        (d := d) (n := n) hn) :
    TNBuilda.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  nonbasicResidual lowerWeight hnonterminal factor hfactorWeight
      hfactorTruncated htreeNonbasic := by
    classical
    by_cases hself :
        ∃ word :
          CWord
            (HEAddres (concreteBasicCommutators.{u} d)),
          factor.word = .commutator word word
    · exact
        word_commutator_self factor (Classical.choose hself)
          (Classical.choose_spec hself)
    · exact
        builder.nonbasicNonselfResidual lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated htreeNonbasic (by
            intro word hword
            exact hself ⟨word, hword⟩)

end
  NNBuild

/--
For canonical Hall families, a cutoff packet and true residual recollections
for non-basic non-self words construct product coordinate polynomials.
-/
theorem
    nonself_collect_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      NNBuild.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  nonbasic_collect_builder
    hn e builder.nonbasicReductionBuilder

/--
For canonical Hall families, a cutoff packet and true residual recollections
for non-basic non-self words construct inverse coordinate polynomials.
-/
theorem
    commutators_nonself_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      NNBuild.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_nonbasic_builder
    hn e builder.nonbasicReductionBuilder

end TCTex
end Submission

-- Merged from PolynomialConcreteRoutedJacobiFrontierCollection.lean

/-!
# Routed polynomial recollection at every concrete Jacobi frontier

This module combines the expanded-Jacobi continuation route with the
expanded-root frontier route.  Recursive callers supply ordinary descendant
recollections, forward Jacobi value-packet recollections, inverse
two-basic-child swap-packet recollections, and forward generic root-swap
packet recollections.  Conjugation routing, source inversion, and orientation
dispatch are compiled internally.
-/

noncomputable section

namespace Submission
namespace TCTex

open CEWord

universe u

/-- Recursive data after every concrete polynomial Jacobi route is compiled. -/
structure
    RJBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  expandedJacobi :
    EFBuild.{u}
      (d := d) (n := n) hn
  basicChildrenInverse :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (left right : HallTree (FreeGenerator.{u} d))
          (hleftBasic : left.IsBasic)
          (hrightBasic : right.IsBasic)
          (htree : tree factor.word = .commutator left right),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TVRecoll
                (n := n) factor left right hleftBasic hrightBasic htree
  rootSwapResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              PSRecoll
                (n := n) factor left right hword

namespace
  RJBuild

/-- Compile routed expanded continuations into two-basic-child orientation. -/
noncomputable def childrenOrientationBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      RJBuild.{u}
        (d := d) (n := n) hn) :
    COBuild.{u}
      (d := d) (n := n) hn where
  expandedJacobi :=
    builder.expandedJacobi
      |>.expandedContinuationBuilder
  swapValueInverse :=
    builder.basicChildrenInverse

/-- Compile all routed cases into the expanded-root frontier builder. -/
noncomputable def expandedFrontierBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      RJBuild.{u}
        (d := d) (n := n) hn) :
    EFBuilda.{u}
      (d := d) (n := n) hn where
  basicChildren :=
    builder.childrenOrientationBuilder
  normalizerAbove :=
    fun _lowerWeight strongerWeight _ =>
      builder.expandedJacobi.normalizerFamily.normalizer strongerWeight
  rootSwapResidual := builder.rootSwapResidual

/-- Compile all routed cases into the arbitrary Jacobi-frontier collector. -/
noncomputable def jacobiCollectionBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      RJBuild.{u}
        (d := d) (n := n) hn) :
    JFBuild.{u}
      (d := d) (n := n) hn :=
  builder.expandedFrontierBuilder
    |>.jacobiCollectionBuilder

end
  RJBuild

/--
For canonical Hall families, routed recursive Jacobi data constructs product
coordinate polynomials.
-/
theorem
    routed_jacobi_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      RJBuild.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_frontier_collect
    hn e builder.jacobiCollectionBuilder

/--
For canonical Hall families, routed recursive Jacobi data constructs inverse
coordinate polynomials.
-/
theorem
    commutators_routed_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      RJBuild.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_reduction_builder
    hn e builder.jacobiCollectionBuilder

end TCTex
end Submission

-- Merged from PolynomialConcreteSwapValueResidualExactCancellation.lean

/-!
# Exact cancellation of signed polynomial swap residuals

Reversing a commutator is exactly inversion for the commutator convention
used by mathlib.  Negating the symbolic coefficient therefore makes the
reversed polynomial factor evaluate exactly like the original factor.  The
associated skew-value packets recollect to the empty source.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open CEWord

universe u

namespace CEWord

/-- A signed swap of two basic children has inverse unpowered word value. -/
theorem children_swap_inv
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right) :
    (childrenSwapFactor factor left right hleftBasic hrightBasic
        htree).wordValue (n := n) =
      (factor.wordValue (n := n))⁻¹ := by
  change
    (childrenSwapFactor factor left right hleftBasic hrightBasic
        htree).word.eval
        HEAddres.freeLowerTruncation =
      (factor.word.eval HEAddres.freeLowerTruncation)⁻¹
  rw [←
    lower_truncation_tree
      (childrenSwapFactor factor left right hleftBasic hrightBasic
        htree).word,
    ← lower_truncation_tree factor.word,
    tree_children_swap, htree]
  simp only [HallTree.to_commutator_commutator,
    CWord.eval_commutator]
  exact congrArg
    (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (commutatorElement_inv
      (left.toCWord.eval FreeGroup.of)
      (right.toCWord.eval FreeGroup.of)).symm

/-- A signed swap of two basic children preserves polynomial evaluation. -/
theorem eval_children_swap
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    (childrenSwapFactor factor left right hleftBasic hrightBasic
        htree).eval (n := n) e =
      factor.eval (n := n) e := by
  rw [SPFactor.eval, SPFactor.eval,
    coefficient_children_swap,
    children_swap_inv, zpow_neg, inv_zpow, inv_inv]

/-- The forward two-basic-child swap value packet cancels exactly. -/
theorem children_swap_raw
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (childrenSwapSource factor left right hleftBasic
          hrightBasic htree) =
      1 := by
  simp only [childrenSwapSource,
    SPFactor.listEval_cons,
    SPFactor.listEval_nil, mul_one,
    SPFactor.eval_neg,
    eval_children_swap, inv_mul_cancel]

/-- The inverse two-basic-child swap value packet also cancels exactly. -/
theorem list_children_inverse
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (basicChildrenSwap factor left right
          hleftBasic hrightBasic htree) =
      1 := by
  rw [basicChildrenSwap,
    SPFactor.list_eval_inverse,
    children_swap_raw]
  simp

/-- A signed expanded-root swap has inverse unpowered word value. -/
theorem expanded_swap_inv
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) :
    (expandedSwapFactor factor left right hword).wordValue (n := n) =
      (factor.wordValue (n := n))⁻¹ := by
  rw [SPFactor.wordValue,
    SPFactor.wordValue, word_expanded_swap,
    hword]
  exact (commutatorElement_inv _ _).symm

/-- A signed expanded-root swap preserves polynomial evaluation. -/
theorem eval_expanded_swap
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    (expandedSwapFactor factor left right hword).eval (n := n) e =
      factor.eval (n := n) e := by
  rw [SPFactor.eval, SPFactor.eval,
    coefficient_expanded_swap,
    expanded_swap_inv, zpow_neg, inv_zpow, inv_inv]

/-- The forward expanded-root swap value packet cancels exactly. -/
theorem expanded_root_swap
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (expandedSwapRaw factor left right hword) =
      1 := by
  simp only [expandedSwapRaw,
    SPFactor.listEval_cons,
    SPFactor.listEval_nil, mul_one,
    SPFactor.eval_neg, eval_expanded_swap,
    inv_mul_cancel]

/-- The inverse expanded-root swap value packet also cancels exactly. -/
theorem expanded_swap_raw
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (expandedSwapSource factor left right
          hword) =
      1 := by
  rw [expandedSwapSource,
    SPFactor.list_eval_inverse,
    expanded_root_swap]
  simp

end CEWord

namespace
  TVRecoll

/-- The inverse two-basic-child swap packet recollects to the empty source. -/
noncomputable def empty
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : CEWord.tree factor.word =
      .commutator left right) :
    TVRecoll
      (n := n) factor left right hleftBasic hrightBasic htree where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    contradiction
  higher_least_succ := by
    intro x hx
    contradiction
  list_higher_raw := by
    intro e
    simpa only [SPFactor.listEval_nil] using
      (CEWord.list_children_inverse
        factor left right hleftBasic hrightBasic htree e).symm

end
  TVRecoll

namespace
  PSRecoll

/-- The forward expanded-root swap packet recollects to the empty source. -/
noncomputable def empty
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator left right) :
    PSRecoll
      (n := n) factor left right hword where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    contradiction
  higher_least_succ := by
    intro x hx
    contradiction
  list_higher_raw := by
    intro e
    simpa only [SPFactor.listEval_nil] using
      (CEWord.expanded_root_swap
        factor left right hword e).symm

end
  PSRecoll

end TCTex
end Submission

-- Merged from PolynomialConcreteExpanded.lean

/-!
# Flattened Hall-ranked branches for expanded polynomial Jacobi residuals

The two ordinary descendants of one expanded Jacobi root inherit the root
Hall-rank defect, so they are not themselves strict recursive tasks.  Each
descendant is, however, a recipe-correct inner-reduction case.  This file
flattens those two reductions into one branch whose exposed grandchildren
strictly descend.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

namespace SPFactor
namespace RCSrc

/--
Transport a strict child source to a parent with the same ordinary word
weight and the same Hall-rank defect.
-/
def reparent
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {oldParent newParent : SPFactor H ι}
    {parentRankDefect : ℕ}
    (source :
      RCSrc (n := n) oldParent parentRankDefect)
    (hweight :
      oldParent.word.weight HEAddres.weight =
        newParent.word.weight HEAddres.weight) :
    RCSrc (n := n) newParent parentRankDefect where
  tasks := source.tasks
  tasks_descend := by
    intro task htask
    simpa only [HallRankedDescends, hallRankedMeasure, cutoffDefect, hweight] using
      source.tasks_descend task htask

@[simp]
theorem tasks_reparent
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {oldParent newParent : SPFactor H ι}
    {parentRankDefect : ℕ}
    (source :
      RCSrc (n := n) oldParent parentRankDefect)
    (hweight :
      oldParent.word.weight HEAddres.weight =
        newParent.word.weight HEAddres.weight) :
    (source.reparent hweight).tasks = source.tasks :=
  rfl

/-- Concatenate two strict child sources for the same ranked parent. -/
def append
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    (left right :
      RCSrc (n := n) parent parentRankDefect) :
    RCSrc (n := n) parent parentRankDefect where
  tasks := left.tasks ++ right.tasks
  tasks_descend := by
    intro task htask
    rcases List.mem_append.mp htask with htask | htask
    · exact left.tasks_descend task htask
    · exact right.tasks_descend task htask

@[simp]
theorem tasks_append
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    (left right :
      RCSrc (n := n) parent parentRankDefect) :
    (left.append right).tasks = left.tasks ++ right.tasks :=
  rfl

end RCSrc
end SPFactor

namespace TRBrancha

open
  TRRecoll
  TDRecoll
  TRRecolla

/--
Transport a reversed two-basic-child branch back to the original signed
factor while preserving its strict child source.
-/
noncomputable def childrenSwap
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : CEWord.tree factor.word =
      .commutator left right)
    (rankDefect : ℕ)
    (reversed :
      TRBrancha
        (n := n)
        (childrenSwapFactor factor left right hleftBasic hrightBasic
          htree)
        rankDefect)
    (valueResidualInverse :
      TVRecoll
        (n := n) factor left right hleftBasic hrightBasic htree) :
    TRBrancha
      (n := n) factor rankDefect where
  children :=
    reversed.children.reparent
      (basic_children_swap factor left right hleftBasic
        hrightBasic htree)
  recollect := fun residual =>
    TRRecoll.children_swap
      factor left right hleftBasic hrightBasic htree
        (reversed.recollect fun task htask => residual task htask)
        valueResidualInverse

/--
Flatten an expanded Jacobi root and the inner reductions of both descendants
into a single strictly descending Hall-ranked branch.
-/
noncomputable def expanded_ranked_decomp
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
    (ranked :
      ERDecomp
        factor)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (valueResidual :
      TRRecolla
        (n := n) factor ranked.decomposition) :
    TRBrancha
      (n := n) factor
        (expandedJacobiParent ranked.decomposition) := by
  let first :=
    innerOuterFactory hn hH routing
      (expandedJacobiFactor factor ranked.decomposition)
      (expandedJacobiParent ranked.decomposition)
      (ranked.firstCase hfactorTruncated)
  let second :=
    innerOuterFactory hn hH routing
      (expandedJacobiSecond factor ranked.decomposition)
      (expandedJacobiParent ranked.decomposition)
      (ranked.secondCase hfactorTruncated)
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
          of_routedFirst
            (routing.factory factor) (routing.sharp factor)
            factor ranked.decomposition rfl hfactorTruncated
            firstResidual secondResidual valueResidual.toInverseRecollection
        expanded_reduction hn hH
          (routing.factory factor) (routing.sharp factor)
          (routing.nextNormalizer factor)
          factor ranked.decomposition rfl hfactorTruncated
          continuation.expandedContinuationRecollection
    }

/--
Compile either ranked Hall orientation of a two-basic-child Jacobi frontier
into one strict branch.
-/
noncomputable def basicChildrenDispatch
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
    (valueResidual :
      ∀
        (childFactor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (ranked :
          ERDecomp
            childFactor),
        childFactor.word.weight HEAddres.weight < n →
          TRRecolla
            (n := n) childFactor ranked.decomposition)
    (swapValueInverse :
      ∀
        (childFactor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (left right : HallTree (FreeGenerator.{u} d))
        (hleftBasic : left.IsBasic)
        (hrightBasic : right.IsBasic)
        (htree : tree childFactor.word = .commutator left right),
        childFactor.word.weight HEAddres.weight < n →
          TVRecoll
            (n := n) childFactor left right hleftBasic hrightBasic htree)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (dispatch :
      CJDispat factor left right hleftBasic
        hrightBasic htree) :
    TRBrancha
      (n := n) factor
        (HallTree.bracketRankDefect
          (left.weight + right.weight) left right) := by
  cases dispatch with
  | forward ranked =>
      rw [←
        CJDispat.forward_rank_defect
          factor left right hleftBasic hrightBasic htree ranked]
      exact
        expanded_ranked_decomp hn hH routing factor ranked
          hfactorTruncated (valueResidual factor ranked hfactorTruncated)
  | swapped ranked =>
      rw [←
        CJDispat.swapped_rank_defect
          factor left right hleftBasic hrightBasic htree ranked]
      exact
        childrenSwap factor left right hleftBasic hrightBasic htree
          (expandedJacobiParent ranked.decomposition)
          (expanded_ranked_decomp hn hH routing
            (childrenSwapFactor factor left right hleftBasic hrightBasic
              htree)
            ranked
            (by
              simpa only [basic_children_swap] using
                hfactorTruncated)
            (valueResidual
              (childrenSwapFactor factor left right hleftBasic
                hrightBasic htree)
              ranked
              (by
                simpa only [basic_children_swap] using
                  hfactorTruncated)))
          (swapValueInverse factor left right hleftBasic hrightBasic
            htree hfactorTruncated)

/--
Choose the ranked Hall orientation and compile one two-basic-child Jacobi
frontier into a strict branch.
-/
noncomputable def basicChildrenJacobi
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
    (valueResidual :
      ∀
        (childFactor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (ranked :
          ERDecomp
            childFactor),
        childFactor.word.weight HEAddres.weight < n →
          TRRecolla
            (n := n) childFactor ranked.decomposition)
    (swapValueInverse :
      ∀
        (childFactor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (left right : HallTree (FreeGenerator.{u} d))
        (hleftBasic : left.IsBasic)
        (hrightBasic : right.IsBasic)
        (htree : tree childFactor.word = .commutator left right),
        childFactor.word.weight HEAddres.weight < n →
          TVRecoll
            (n := n) childFactor left right hleftBasic hrightBasic htree)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hchildrenNe : left ≠ right)
    (hforwardNonbasic : ¬(HallTree.commutator left right).IsBasic)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRBrancha
      (n := n) factor
        (HallTree.bracketRankDefect
          (left.weight + right.weight) left right) :=
  basicChildrenDispatch hn hH routing valueResidual
    swapValueInverse factor left right hleftBasic hrightBasic htree
      hfactorTruncated
        (rankedJacobiDispatch factor left right hleftBasic
          hrightBasic htree hchildrenNe hforwardNonbasic hreverseNonbasic)

end TRBrancha

end TCTex
end Submission

-- Merged from PolynomialConcreteJacobiContinuationDecomposition.lean

/-!
# Recursive decomposition of the signed-polynomial Jacobi continuation

After the atomic Jacobi coordinate packet is peeled from a true concrete
factor residual, the remaining continuation can be decomposed into:

* the true residual of the second Jacobi descendant;
* the true residual of the first descendant, conjugated by the second
  descendant value; and
* the inverse value-level Jacobi residual.

This is an exact symbolic-list identity.  It exposes the recursive obligations
that remain after the associated-graded Jacobi correction has been routed
upward.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace CEWord

universe u

/--
Recursive source whose evaluation is the remaining Jacobi continuation.

The singleton factors surrounding the first descendant residual encode its
conjugation by the second descendant value.
-/
noncomputable def jacobiContinuationSource
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  basicRawSource
      (jacobiSecondFactor factor left middle right hword) ++
    [(jacobiSecondFactor factor left middle right hword).neg] ++
      basicRawSource
          (jacobiFirstFactor factor left middle right hword) ++
        [jacobiSecondFactor factor left middle right hword] ++
          jacobiRawSource factor left middle right hword

/-- A truncated original factor gives a physically truncated recursive continuation. -/
theorem truncated_continuation_decomposition
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (hfactor :
      factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (jacobiContinuationSource
        factor left middle right hword) := by
  have hfirst :
      (jacobiFirstFactor factor left middle right hword).word.weight
          HEAddres.weight < n := by
    simpa only [jacobi_first_factor] using hfactor
  have hsecond :
      (jacobiSecondFactor factor left middle right hword).word.weight
          HEAddres.weight < n := by
    simpa only [word_jacobi_second] using hfactor
  intro x hx
  simp only [jacobiContinuationSource, List.mem_append] at hx
  rcases hx with (((hx | hx) | hx) | hx) | hx
  · exact
      truncated_reduction_source
        (jacobiSecondFactor factor left middle right hword) hsecond x hx
  · simp only [List.mem_singleton] at hx
    subst x
    simpa only [SPFactor.word_neg] using hsecond
  · exact
      truncated_reduction_source
        (jacobiFirstFactor factor left middle right hword) hfirst x hx
  · simp only [List.mem_singleton] at hx
    subst x
    exact hsecond
  · exact
      truncated_jacobi_source
        factor left middle right hword hfactor x hx

/--
The recursive decomposition evaluates exactly to the continuation left after
the atomic Jacobi coordinate correction.
-/
theorem
    jacobi_continuation_decomposition
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (jacobiContinuationSource
          factor left middle right hword) =
      SPFactor.listEval e
        (jacobiContinuationRaw factor left middle right hword) := by
  simp only [jacobiContinuationSource,
    jacobiContinuationRaw, jacobiRawSource,
    jacobiValueSource, SPFactor.listEval_append,
    SPFactor.list_eval_inverse,
    reduction_raw_source,
    SPFactor.listEval_cons,
    SPFactor.listEval_nil, mul_one,
    SPFactor.eval_neg]
  group

/-- The recursive decomposition inherits next-stratum membership. -/
theorem
    continuation_decomposition_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (jacobiContinuationSource
          factor left middle right hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  rw [
    jacobi_continuation_decomposition
      factor left middle right hword e]
  exact
    continuation_raw_series
      factor left middle right hword e

end CEWord
end TCTex
end Submission

-- Merged from PolynomialConcreteUnresolvedReductionCollection.lean

/-!
# Signed-polynomial collection reduced past exact skew cases

Basic expanded Hall trees, symbolic self-commutators, and reversed-basic
brackets all have automatic true residual recollections.  This file packages
those eliminations and exposes the remaining arbitrary-cutoff collector
boundary.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
A cutoff Hall-Petresco packet and upward recollection of only the unresolved
true residuals after basic, self-bracket, and reversed-basic cases are removed.
-/
structure TUBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  unresolvedResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ¬(CEWord.tree factor.word).IsBasic →
                (∀ word :
                  CWord
                    (HEAddres
                      (concreteBasicCommutators.{u} d)),
                    factor.word ≠ .commutator word word) →
                  ¬CEWord.IsReversedBasic
                      factor.word →
                    TRRecoll
                      (n := n) factor

namespace
  TUBuild

open
  TRRecoll

/--
Fill every reversed-basic residual with the empty recollection and leave only
the unresolved true residuals to the caller.
-/
noncomputable def nonbasicNonselfCollection
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      TUBuild.{u}
        (d := d) (n := n) hn) :
    NNBuild.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  nonbasicNonselfResidual lowerWeight hnonterminal factor hfactorWeight
      hfactorTruncated htreeNonbasic hnonself := by
    classical
    by_cases hreversed :
        CEWord.IsReversedBasic factor.word
    · exact reversed_basic factor hreversed
    · exact
        builder.unresolvedResidual lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated htreeNonbasic hnonself hreversed

end
  TUBuild

/--
For canonical Hall families, a cutoff packet and recollections of only the
unresolved true residuals construct product coordinate polynomials.
-/
theorem
    unresolved_collect_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      TUBuild.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  nonself_collect_builder
    hn e builder.nonbasicNonselfCollection

/--
For canonical Hall families, a cutoff packet and recollections of only the
unresolved true residuals construct inverse coordinate polynomials.
-/
theorem
    commutators_unresolved_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      TUBuild.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_nonself_builder
    hn e builder.nonbasicNonselfCollection

end TCTex
end Submission

-- Merged from PolynomialConcreteValueResidualRecursiveNormalization.lean

/-!
# Recursive normalization of concrete signed-polynomial value residuals

The direct expanded-Jacobi value-residual normalizer consumes a semantic
normalizer at the current Hall-weight stratum.  This file exposes a recursive
alternative.

Replace every factor in a semantically higher packet by its concrete atomic
Hall reduction and already recollected intrinsic residual.  The remaining
active factors are atomic, while every non-atomic factor is strictly higher.
Restricted-sharp routing then lifts the whole packet using only a correction
factory, a sharp router, and the next-stratum normalizer.

Signed swap packets are simpler: they cancel exactly and already have empty
recollection constructors.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open CEWord

namespace
  TRRecoll

/--
Fold independently recollected concrete residuals over an arbitrary finite
signed-polynomial source while retaining the active-atoms-or-higher invariant.
-/
noncomputable def atoms_or_residuals
    {d n lowerWeight : ℕ}
    {ι : Type}
    (source :
      List
        (SPFactor
          (concreteBasicCommutators.{u} d) ι))
    (hsourceTruncated :
      SPFactor.IsTruncated n source)
    (hsourceSupported :
      SPFactor.WordWeightLeast lowerWeight source)
    (residual :
      ∀ factor ∈ source,
        TRRecoll
          (n := n) factor) :
    TORecoll
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d) source := by
  have hsource :
      source.flatMap
          (fun factor :
              SPFactor
                (concreteBasicCommutators.{u} d) ι =>
            [factor]) =
        source := by
    clear hsourceTruncated hsourceSupported residual
    induction source with
    | nil =>
        rfl
    | cons factor source ih =>
        simp only [List.flatMap_cons, List.singleton_append, ih]
  rw [← hsource]
  exact
    TORecoll.flatMap
      source
      (fun factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι =>
        [factor])
      (fun factor hfactor =>
        (residual factor hfactor).atomsOrRecollection
          (hsourceTruncated factor hfactor)
          (hsourceSupported factor hfactor))

/--
Lift a semantically higher concrete source from recursive residual
recollections of its factors.  No current-stratum normalizer is required.
-/
noncomputable def recollect_higher_residuals
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factory :
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1)
          (concreteBasicCommutators.{u} d))
    (source :
      List
        (SPFactor
          (concreteBasicCommutators.{u} d) ι))
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n)
    (hsourceTruncated :
      SPFactor.IsTruncated n source)
    (hsourceSupported :
      SPFactor.WordWeightLeast lowerWeight source)
    (hsourceMem :
      ∀ e : ι → HEFam (concreteBasicCommutators.{u} d),
        SPFactor.listEval (n := n) e source ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            lowerWeight)
    (residual :
      ∀ factor ∈ source,
        TRRecoll
          (n := n) factor) :
    SSRecol
      (n := n) (lowerWeight := lowerWeight + 1)
      (concreteBasicCommutators.{u} d) source :=
  (atoms_or_residuals
    source hsourceTruncated hsourceSupported residual)
    |>.recollectionSemanticallyHigher hn hH factory sharp
      nextNormalizer hlowerWeightPos hlowerWeightTruncated hsourceMem

end
  TRRecoll

namespace
  TRRecolla

/--
Normalize an expanded-Jacobi value packet from recursive recollections of its
three concrete factors.
-/
noncomputable def ofBasicResiduals
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factory :
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (residual :
      ∀ child ∈ expandedJacobiRaw factor decomposition,
        TRRecoll
          (n := n) child) :
    TRRecolla
      (n := n) factor decomposition := by
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    rw [← hfactorWeight]
    exact factor.word_weight_pos
  let recollection :=
    TRRecoll.recollect_higher_residuals
      hn hH factory sharp nextNormalizer
      (expandedJacobiRaw factor decomposition)
      hlowerWeightPos (by omega)
      (expanded_jacobi_source factor decomposition
        hfactorTruncated)
      (by
        intro x hx
        simp only [expandedJacobiRaw, List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · simpa only [SPFactor.word_neg] using
            hfactorWeight.ge
        · simpa only [expanded_jacobi_factor] using
            hfactorWeight.ge
        · simpa only [expanded_second_factor] using
            hfactorWeight.ge)
      (by
        intro e
        simpa only [hfactorWeight] using
          list_expanded_series
            factor decomposition e)
      residual
  exact
    {
      higherSource := recollection.higherSource
      higher_source_truncated := recollection.higher_source_truncated
      higher_least_succ := by
        simpa only [hfactorWeight] using
          recollection.higher_weight_least
      list_higher_raw :=
        recollection.list_higher_raw
    }

end
  TRRecolla

end TCTex
end Submission

-- Merged from PolynomialConcreteJacobiContinuationRecursion.lean

/-!
# Recursive interface for the signed-polynomial Jacobi continuation

The exact Jacobi-continuation decomposition is the collector-facing recursive
boundary:

* the two descendant true residuals remain recursive calls;
* the first descendant residual is conjugated by the second descendant value;
* the inverse value-level Jacobi packet lies one lower-central stratum higher.

This file packages recollection of that decomposition as recollection of the
original continuation.  It also records the common-total-weight rank decrease
for all four eventual right factors in the two descendant branches.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission

namespace TCTex

open CEWord

universe u

/--
Recollection data for the explicit recursive decomposition of a Jacobi
continuation.
-/
structure
    JCRecol
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right) where
  higherSource :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_least_succ :
    SPFactor.WordWeightLeast
      (factor.word.weight HEAddres.weight + 1) higherSource
  list_decomposition_raw :
    ∀ e : ι → HEFam (concreteBasicCommutators.{u} d),
      SPFactor.listEval (n := n) e higherSource =
        SPFactor.listEval e
          (jacobiContinuationSource
            factor left middle right hword)

namespace
  JCRecol

/--
An upward recollection of the explicit recursive decomposition is an upward
recollection of the original Jacobi continuation.
-/
noncomputable def jacobiContinuationRecollection
    {d n : ℕ}
    {ι : Type}
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    {left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d))}
    {hword : factor.word = .commutator (.commutator left middle) right}
    (recollection :
      JCRecol
        (n := n) factor left middle right hword) :
    ConcreteContinuationRecollection
      (n := n) factor left middle right hword where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_least_succ :=
    recollection.higher_least_succ
  list_higher_raw := by
    intro e
    rw [recollection.list_decomposition_raw e,
      jacobi_continuation_decomposition]

end
  JCRecol

/--
A decomposition-aware refinement of the syntactic Jacobi continuation
builder.  Its remaining obligation is exactly the recursive decomposition
rather than the opaque continuation source.
-/
structure
    SCDecompa
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  jacobiContinuationDecomposition :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (left middle right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator (.commutator left middle) right),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              JCRecol
                (n := n) factor left middle right hword

namespace
  SCDecompa

/--
Forget the explicit recursive shape after compiling it into the continuation
boundary consumed by the existing Jacobi collector.
-/
noncomputable def syntacticContinuationBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      SCDecompa.{u}
        (d := d) (n := n) hn) :
    SJContin
      (d := d) (n := n) hn where
  packet := builder.packet
  jacobiContinuation := by
    intro ι lowerWeight hnonterminal factor left middle right hword
      hfactorWeight hfactorTruncated
    let recollection :=
      builder.jacobiContinuationDecomposition lowerWeight hnonterminal
        factor left middle right hword hfactorWeight hfactorTruncated
    exact recollection.jacobiContinuationRecollection

/--
Lift one syntactically exposed Jacobi factor from recollection of its explicit
recursive continuation decomposition.
-/
noncomputable def jacobiResidual
    {d n : ℕ}
    {hn : 2 ≤ n}
    {ι : Type}
    (builder :
      SCDecompa.{u}
        (d := d) (n := n) hn)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator (.commutator left middle) right)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRRecoll
      (n := n) factor :=
  builder.syntacticContinuationBuilder.jacobiResidual
    lowerWeight hnonterminal normalizerAbove factor left middle right hword
      hfactorWeight hfactorTruncated

/--
Lift an expanded Jacobi root whose inner bracket is nonbasic from recollection
of its explicit recursive continuation decomposition.
-/
noncomputable def jacobiTreeNonbasic
    {d n : ℕ}
    {hn : 2 ≤ n}
    {ι : Type}
    (builder :
      SCDecompa.{u}
        (d := d) (n := n) hn)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left middle right : HallTree (FreeGenerator.{u} d))
    (htree :
      CEWord.tree factor.word =
        .commutator (.commutator left middle) right)
    (houterNonbasic :
      ¬(HallTree.commutator (.commutator left middle) right).IsBasic)
    (hinnerNonbasic :
      ¬(HallTree.commutator left middle).IsBasic)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRRecoll
      (n := n) factor :=
  builder.syntacticContinuationBuilder
    |>.jacobiTreeNonbasic lowerWeight
      hnonterminal normalizerAbove factor left middle right htree
        houterNonbasic hinnerNonbasic hfactorWeight hfactorTruncated

end
  SCDecompa
end TCTex
end Submission

-- Merged from PolynomialConcreteValueResidualNamedRecursiveNormalization.lean

/-!
# Named recursive inputs for concrete signed-polynomial value residuals

The finite-factor value normalizer accepts one concrete residual recollection
for every member of a short raw packet.  This file replaces that membership
callback by named inputs.

For a forward Jacobi packet, the inverse parent factor is derived from the
positive parent residual by the atomic sign-order router.  The remaining
inputs are the two ordinary descendants.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open CEWord

universe u


namespace
  TRRecolla

/--
Normalize a forward expanded-Jacobi value packet from named residuals of the
positive parent and its two ordinary descendants.
-/
noncomputable def namedBasicResids
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (factory :
      TSFtry
        (n := n) (concreteBasicCommutators.{u} d) lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (decomposition : ExpandedJacobiDecomposition factor.word)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (factorResidual :
      TRRecoll
        (n := n) factor)
    (firstResidual :
      TRRecoll
        (n := n) (expandedJacobiFactor factor decomposition))
    (secondResidual :
      TRRecoll
        (n := n) (expandedJacobiSecond factor decomposition)) :
    TRRecolla
      (n := n) factor decomposition :=
  ofBasicResiduals hn hH factory sharp nextNormalizer factor decomposition
    hfactorWeight hfactorTruncated fun child hchild => by
      exact Classical.choice (by
        simp only [expandedJacobiRaw, List.mem_cons,
          List.not_mem_nil, or_false] at hchild
        rcases hchild with rfl | rfl | rfl
        · exact
            ⟨TRRecoll.neg_of_recollection
              hn hH factory sharp nextNormalizer factor hfactorWeight
                hfactorTruncated factorResidual⟩
        · exact ⟨firstResidual⟩
        · exact ⟨secondResidual⟩)

end
  TRRecolla

end TCTex
end Submission

-- Merged from PolynomialConcreteRanked.lean

/-!
# Reachable two-basic-child polynomial Hall-ranked residual tasks

After one recipe-correct inner reduction, every exposed recursive task is a
bracket of two Hall-basic trees.  Its numerical rank defect is the canonical
symmetric bracket defect and its symbolic factor remains physically
truncated.  This file records that reachable task predicate and derives it
directly from membership in an inner-reduction child packet.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

/--
A reachable ranked residual task exposed by inner Hall reduction has two
basic children and carries their canonical symmetric bracket-rank defect.
-/
structure
    PCReach
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ) where
  left : HallTree (FreeGenerator.{u} d)
  right : HallTree (FreeGenerator.{u} d)
  left_isBasic : left.IsBasic
  right_isBasic : right.IsBasic
  tree_eq :
    tree factor.word = .commutator left right
  factor_truncated :
    factor.word.weight HEAddres.weight < n
  rankDefect_eq :
    rankDefect =
      HallTree.bracketRankDefect
        (left.weight + right.weight) left right

namespace
  PCReach

/--
Every member of a recipe-correct ranked inner-reduction packet is a reachable
two-basic-child task, provided the retained right word expands to the basic
unchanged tree recorded by the recipe.
-/
noncomputable def ranked_tasks
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (unchanged : HallTree (FreeGenerator.{u} d))
    (hrightTree : tree rightWord = unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    {task :
      SPFactor
          (concreteBasicCommutators.{u} d) ι ×
        ℕ}
    (htask :
      task ∈
        IRChildr.rankedTasks
          factor innerWord rightWord hword unchanged) :
    PCReach
      (n := n) task.1 task.2 := by
  let indexExists :=
    IRChildr.index_ranked_tasks
      factor innerWord rightWord hword unchanged htask
  let i := Classical.choose indexExists
  have htask_eq := Classical.choose_spec indexExists
  rw [htask_eq]
  refine
    { left := HallTree.indexedBasicTree i
      right := unchanged
      left_isBasic := HallTree.indexed_tree i
      right_isBasic := hunchangedBasic
      tree_eq := ?_
      factor_truncated := ?_
      rankDefect_eq := ?_ }
  · rw [inner_reduction_factor, tree_commutator, tree_atom,
      basicReductionAddress, concreteBasicTree, hrightTree]
  · rw [inner_outer_factor]
    exact hfactorTruncated
  · rw [HallTree.indexed_tree_weight]

end
  PCReach

end TCTex
end Submission

/-!
# Reachable scheduling for two-basic-child polynomial Hall residuals

Every strict task exposed by a flattened Jacobi frontier is again a bracket
of two basic trees.  This file proves that closure property and uses it to
classify reachable tasks: terminal, basic, self, and reversed-basic roots
close immediately, while the remaining roots flatten one Jacobi step and
schedule only their strictly descending grandchildren.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

namespace
  PCReach

/--
Children emitted by one compiled recipe-correct inner reduction are again
reachable two-basic-child tasks when the retained right word expands to the
recorded unchanged tree.
-/
noncomputable def reduction_factory_children
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
        (n := n) factor rankDefect)
    (hrightTree : tree branchCase.rightWord = branchCase.unchanged)
    {task :
      SPFactor
          (concreteBasicCommutators.{u} d) ι ×
        ℕ}
    (htask :
      task ∈
        (TRBrancha.innerOuterFactory
          hn hH routing factor rankDefect branchCase).children.tasks) :
    PCReach
      (n := n) task.1 task.2 := by
  rcases branchCase with
    ⟨innerWord, rightWord, hword, hfactorTruncated, added, originalRight,
      unchanged, originalLeft, hinnerTree, hRightLeft, hRightUnchanged,
      hunchangedBasic, rankDefect_eq⟩
  subst rankDefect
  exact
    ranked_tasks factor innerWord rightWord hword unchanged hrightTree
      hunchangedBasic hfactorTruncated (by
        simpa only [
          TRBrancha.innerOuterFactory,
          TRBrancha.innerComparisonFactory,
          IRChildr.tasks_ranked_task]
          using htask)

/--
The children exposed by one flattened ranked Jacobi decomposition are
reachable two-basic-child tasks.
-/
noncomputable def expanded_jacobi_children
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
    (ranked :
      ERDecomp
        factor)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (valueResidual :
      TRRecolla
        (n := n) factor ranked.decomposition)
    {task :
      SPFactor
          (concreteBasicCommutators.{u} d) ι ×
        ℕ}
    (htask :
      task ∈
        (TRBrancha.expanded_ranked_decomp
          hn hH routing factor ranked hfactorTruncated valueResidual).children.tasks) :
    PCReach
      (n := n) task.1 task.2 := by
  let firstCase := ranked.firstCase hfactorTruncated
  let secondCase := ranked.secondCase hfactorTruncated
  let first :=
    TRBrancha.innerOuterFactory
      hn hH routing
        (expandedJacobiFactor factor ranked.decomposition)
        (expandedJacobiParent ranked.decomposition) firstCase
  let second :=
    TRBrancha.innerOuterFactory
      hn hH routing
        (expandedJacobiSecond factor ranked.decomposition)
        (expandedJacobiParent ranked.decomposition) secondCase
  have htask' : task ∈ first.children.tasks ++ second.children.tasks := by
    simpa only [
      TRBrancha.expanded_ranked_decomp,
      SPFactor.RCSrc.tasks_append,
      SPFactor.RCSrc.tasks_reparent]
      using htask
  classical
  by_cases htaskFirst : task ∈ first.children.tasks
  · exact
      reduction_factory_children hn hH routing
        (expandedJacobiFactor factor ranked.decomposition)
        (expandedJacobiParent ranked.decomposition) firstCase
          (by rfl) htaskFirst
  · have htaskSecond : task ∈ second.children.tasks :=
      (List.mem_append.mp htask').resolve_left htaskFirst
    exact
      reduction_factory_children hn hH routing
        (expandedJacobiSecond factor ranked.decomposition)
        (expandedJacobiParent ranked.decomposition) secondCase
          (by rfl) htaskSecond

end
  PCReach

namespace
  TRBranch

/-- Lift an already closed residual recollection to any reachable predicate. -/
noncomputable def ofResidRecollect
    {d n : ℕ}
    {ι : Type}
    {Reachable :
      SPFactor
          (concreteBasicCommutators.{u} d) ι →
        ℕ → Prop}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (residual :
      TRRecoll
        (n := n) factor) :
    TRBranch
      (n := n) Reachable factor rankDefect where
  branch :=
    TRBrancha.ofResidRecollect
      factor rankDefect residual
  children_reachable := by
    simp [
      TRBrancha.ofResidRecollect,
      SPFactor.RCSrc.empty]

/--
A flattened ranked Jacobi decomposition is a reachable branch for the
two-basic-child task predicate.
-/
noncomputable def basic_children_jacobi
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
    (ranked :
      ERDecomp
        factor)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (valueResidual :
      TRRecolla
        (n := n) factor ranked.decomposition) :
    TRBranch
      (n := n)
      (fun child childRankDefect =>
        Nonempty
          (PCReach
            (n := n) child childRankDefect))
      factor (expandedJacobiParent ranked.decomposition) where
  branch :=
    TRBrancha.expanded_ranked_decomp
      hn hH routing factor ranked hfactorTruncated valueResidual
  children_reachable := by
    intro task htask
    exact
      ⟨PCReach.expanded_jacobi_children
        hn hH routing factor ranked hfactorTruncated valueResidual htask⟩

/--
Compile either ranked Hall orientation directly as a reachable branch.  The
rank rewrite happens outside the child-source projections, so the closure
proof remains at the decomposition's native rank.
-/
noncomputable def basicChildrenDispatch
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
    (valueResidual :
      ∀
        (childFactor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (ranked :
          ERDecomp
            childFactor),
        childFactor.word.weight HEAddres.weight < n →
          TRRecolla
            (n := n) childFactor ranked.decomposition)
    (swapValueInverse :
      ∀
        (childFactor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (left right : HallTree (FreeGenerator.{u} d))
        (hleftBasic : left.IsBasic)
        (hrightBasic : right.IsBasic)
        (htree : tree childFactor.word = .commutator left right),
        childFactor.word.weight HEAddres.weight < n →
          TVRecoll
            (n := n) childFactor left right hleftBasic hrightBasic htree)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (dispatch :
      CJDispat factor left right hleftBasic
        hrightBasic htree) :
    TRBranch
      (n := n)
      (fun child childRankDefect =>
        Nonempty
          (PCReach
            (n := n) child childRankDefect))
      factor
        (HallTree.bracketRankDefect
          (left.weight + right.weight) left right) := by
  cases dispatch with
  | forward ranked =>
      rw [←
        CJDispat.forward_rank_defect
          factor left right hleftBasic hrightBasic htree ranked]
      exact
        basic_children_jacobi hn hH routing factor
          ranked hfactorTruncated (valueResidual factor ranked hfactorTruncated)
  | swapped ranked =>
      rw [←
        CJDispat.swapped_rank_defect
          factor left right hleftBasic hrightBasic htree ranked]
      let swappedFactor :=
        childrenSwapFactor factor left right hleftBasic hrightBasic htree
      have hswappedTruncated :
          swappedFactor.word.weight HEAddres.weight < n := by
        simpa only [swappedFactor, basic_children_swap] using
          hfactorTruncated
      let reversed :=
        basic_children_jacobi hn hH routing
          swappedFactor ranked hswappedTruncated
            (valueResidual swappedFactor ranked hswappedTruncated)
      exact
        { branch :=
            TRBrancha.childrenSwap
              factor left right hleftBasic hrightBasic htree
                (expandedJacobiParent ranked.decomposition)
                reversed.branch
                (swapValueInverse factor left right hleftBasic
                  hrightBasic htree hfactorTruncated)
          children_reachable := by
            intro task htask
            exact reversed.children_reachable task (by
              simpa only [
                TRBrancha.childrenSwap,
                SPFactor.RCSrc.tasks_reparent]
                using htask) }

/-- Choose the Hall orientation and compile its reachable flattened branch. -/
noncomputable def basicChildrenJacobi
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
    (valueResidual :
      ∀
        (childFactor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (ranked :
          ERDecomp
            childFactor),
        childFactor.word.weight HEAddres.weight < n →
          TRRecolla
            (n := n) childFactor ranked.decomposition)
    (swapValueInverse :
      ∀
        (childFactor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (left right : HallTree (FreeGenerator.{u} d))
        (hleftBasic : left.IsBasic)
        (hrightBasic : right.IsBasic)
        (htree : tree childFactor.word = .commutator left right),
        childFactor.word.weight HEAddres.weight < n →
          TVRecoll
            (n := n) childFactor left right hleftBasic hrightBasic htree)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hchildrenNe : left ≠ right)
    (hforwardNonbasic : ¬(HallTree.commutator left right).IsBasic)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRBranch
      (n := n)
      (fun child childRankDefect =>
        Nonempty
          (PCReach
            (n := n) child childRankDefect))
      factor
        (HallTree.bracketRankDefect
          (left.weight + right.weight) left right) :=
  basicChildrenDispatch hn hH routing valueResidual
    swapValueInverse factor left right hleftBasic hrightBasic htree
      hfactorTruncated
        (rankedJacobiDispatch factor left right hleftBasic
          hrightBasic htree hchildrenNe hforwardNonbasic hreverseNonbasic)

/--
Classify one reachable two-basic-child task.  Immediate endpoints close with
no recursive children; every remaining root is a flattened ranked Jacobi
frontier.
-/
noncomputable def basicChildrenReachable
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
    (valueResidual :
      ∀
        (childFactor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (ranked :
          ERDecomp
            childFactor),
        childFactor.word.weight HEAddres.weight < n →
          TRRecolla
            (n := n) childFactor ranked.decomposition)
    (swapValueInverse :
      ∀
        (childFactor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (left right : HallTree (FreeGenerator.{u} d))
        (hleftBasic : left.IsBasic)
        (hrightBasic : right.IsBasic)
        (htree : tree childFactor.word = .commutator left right),
        childFactor.word.weight HEAddres.weight < n →
          TVRecoll
            (n := n) childFactor left right hleftBasic hrightBasic htree)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (reachable :
      PCReach
        (n := n) factor rankDefect) :
    TRBranch
      (n := n)
      (fun child childRankDefect =>
        Nonempty
          (PCReach
            (n := n) child childRankDefect))
      factor rankDefect := by
  rcases reachable with
    ⟨left, right, hleftBasic, hrightBasic, htree, hfactorTruncated,
      rankDefect_eq⟩
  subst rankDefect
  by_cases hcutoff :
      n ≤ factor.word.weight HEAddres.weight + 1
  · exact
      ofResidRecollect factor
        (HallTree.bracketRankDefect
          (left.weight + right.weight) left right)
        (TRRecoll.of_terminal
          factor hcutoff)
  · by_cases hforwardBasic : (HallTree.commutator left right).IsBasic
    · exact
        ofResidRecollect factor
          (HallTree.bracketRankDefect
            (left.weight + right.weight) left right)
          (TRRecoll.tree_basic
            factor (by
              rw [htree]
              exact hforwardBasic))
    · by_cases hchildrenEq : left = right
      · exact
          ofResidRecollect factor
            (HallTree.bracketRankDefect
              (left.weight + right.weight) left right)
            (TRRecoll.tree_commutator_self
              factor left (by simpa only [hchildrenEq] using htree))
      · by_cases hreverseBasic : (HallTree.commutator right left).IsBasic
        · exact
            ofResidRecollect factor
              (HallTree.bracketRankDefect
                (left.weight + right.weight) left right)
              (TRRecoll.tree_swap_basic
                factor right left htree hreverseBasic)
        · exact
            basicChildrenJacobi hn hH routing valueResidual
              swapValueInverse factor left right hleftBasic
                hrightBasic htree hchildrenEq hforwardBasic hreverseBasic
                  hfactorTruncated

end
  TRBranch

namespace
  RRSchedu

/--
Compile the reachable two-basic-child classifier into a restricted
well-founded Hall-ranked scheduler.
-/
noncomputable def ofBasicChildren
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
    (valueResidual :
      ∀
        (childFactor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (ranked :
          ERDecomp
            childFactor),
        childFactor.word.weight HEAddres.weight < n →
          TRRecolla
            (n := n) childFactor ranked.decomposition)
    (swapValueInverse :
      ∀
        (childFactor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (left right : HallTree (FreeGenerator.{u} d))
        (hleftBasic : left.IsBasic)
        (hrightBasic : right.IsBasic)
        (htree : tree childFactor.word = .commutator left right),
        childFactor.word.weight HEAddres.weight < n →
          TVRecoll
            (n := n) childFactor left right hleftBasic hrightBasic htree) :
    RRSchedu
      (d := d) (n := n) (ι := ι)
      (fun
        (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        rankDefect =>
        Nonempty
          (PCReach
            (n := n) factor rankDefect)) :=
  RRSchedu.ofBranches
    fun factor rankDefect hreachable =>
      TRBranch.basicChildrenReachable
        hn hH routing valueResidual swapValueInverse factor rankDefect
          (Classical.choice hreachable)

/--
Run restricted Hall-ranked recursion from one reachable two-basic-child task.
-/
noncomputable def residual_recollection_children
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
    (valueResidual :
      ∀
        (childFactor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (ranked :
          ERDecomp
            childFactor),
        childFactor.word.weight HEAddres.weight < n →
          TRRecolla
            (n := n) childFactor ranked.decomposition)
    (swapValueInverse :
      ∀
        (childFactor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        (left right : HallTree (FreeGenerator.{u} d))
        (hleftBasic : left.IsBasic)
        (hrightBasic : right.IsBasic)
        (htree : tree childFactor.word = .commutator left right),
        childFactor.word.weight HEAddres.weight < n →
          TVRecoll
            (n := n) childFactor left right hleftBasic hrightBasic htree)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (hreachable :
      Nonempty
        (PCReach
          (n := n) factor rankDefect)) :
    TRRecoll
      (n := n) factor :=
  (ofBasicChildren hn hH routing valueResidual swapValueInverse)
    |>.residualRecollection factor rankDefect hreachable

end
  RRSchedu

end TCTex
end Submission

/-!
# Canonical routing for reachable two-basic-child polynomial Hall residuals

The reachable scheduler needs outer-residual routing and semantic
normalization of the two value residuals introduced by forward and swapped
Jacobi orientations.  A single signed semantic normalizer family supplies
both value normalizations.

This file packages those inputs and exposes the canonical endpoints:
well-founded recollection of an individual reachable two-basic-child task,
and recollection of an oriented expanded-Jacobi root after flattening its two
ordinary descendants into strictly descending grandchildren.

The comparison-routing constructor keeps the outer-factory input
non-circular: child-to-parent outer residuals are recovered as quotients of
independently recollected atomic comparisons and full basic residuals.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

/--
Canonical routing inputs for the reachable two-basic-child ranked residual
scheduler.
-/
structure
    PCRoute
    {d n : ℕ}
    (ι : Type) where
  outerRouting :
    RFRoute.{u}
      (d := d) (n := n) ι
  normalizerFamily :
    SNFam
      (n := n) (concreteBasicCommutators.{u} d)

namespace
  PCRoute

/--
Recover canonical routing from independently recollected atomic comparisons
and full basic residuals.
-/
noncomputable def comparison_factory_routing
    {d n : ℕ}
    {ι : Type}
    (routing :
      TFRoute
        (d := d) (n := n) ι)
    (normalizerFamily :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d)) :
    PCRoute
      (d := d) (n := n) ι where
  outerRouting := routing.outerFactoryRouting
  normalizerFamily := normalizerFamily

/-- Normalize the forward expanded-Jacobi value residual at its own weight. -/
noncomputable def valueResidual
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
      PCRoute
        (d := d) (n := n) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (ranked :
      ERDecomp
        factor)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRRecolla
      (n := n) factor ranked.decomposition :=
  TRRecolla.ofNormalizerFamily
    hn hH routing.normalizerFamily factor ranked.decomposition rfl
      hfactorTruncated

/-- Normalize the inverse skew-value residual at its own weight. -/
noncomputable def swapValueInverse
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
      PCRoute
        (d := d) (n := n) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TVRecoll
      (n := n) factor left right hleftBasic hrightBasic htree :=
  TVRecoll.ofNormalizerFamily
    hn hH routing.normalizerFamily factor left right hleftBasic hrightBasic
      htree rfl hfactorTruncated

/-- Compile canonical routing into the restricted ranked residual scheduler. -/
noncomputable def scheduler
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
      PCRoute
        (d := d) (n := n) ι) :
    RRSchedu
      (d := d) (n := n) (ι := ι)
      (fun
        (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
        rankDefect =>
        Nonempty
          (PCReach
            (n := n) factor rankDefect)) :=
  RRSchedu.ofBasicChildren
    hn hH routing.outerRouting (routing.valueResidual hn hH)
      (routing.swapValueInverse hn hH)

/-- Recollect one certified reachable two-basic-child residual task. -/
noncomputable def residualRecollection
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
      PCRoute
        (d := d) (n := n) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (hreachable :
      Nonempty
        (PCReach
          (n := n) factor rankDefect)) :
    TRRecoll
      (n := n) factor :=
  (routing.scheduler hn hH).residualRecollection factor rankDefect hreachable

/--
Flatten one ranked expanded-Jacobi root and recollect its certified strict
grandchildren with the canonical scheduler.
-/
noncomputable def expanded_ranked_decomposition
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
      PCRoute
        (d := d) (n := n) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (ranked :
      ERDecomp
        factor)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRRecoll
      (n := n) factor :=
  let branch :=
    TRBranch.basic_children_jacobi
      hn hH routing.outerRouting factor ranked hfactorTruncated
        (routing.valueResidual hn hH factor ranked hfactorTruncated)
  branch.branch.recollect fun task htask =>
    routing.residualRecollection hn hH task.1 task.2
      (branch.children_reachable task htask)

end
  PCRoute

end TCTex
end Submission

/-!
# Support-local reachable scheduling for polynomial Hall residuals

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

open CEWord

/--
Support-local outer routing together with the two semantic residuals exposed
by structural Jacobi orientation.
-/
structure
    TCRoute
    {d n lowerWeight : ℕ}
    (ι : Type) where
  outerRouting :
    PFRoute.{u}
      (d := d) (n := n) (lowerWeight := lowerWeight) ι
  valueResidual :
    ∀
      (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι)
      (ranked :
        ERDecomp
          factor),
      factor.word.weight HEAddres.weight = lowerWeight →
        factor.word.weight HEAddres.weight < n →
          TRRecolla
            (n := n) factor ranked.decomposition
  swapValueInverse :
    ∀
      (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι)
      (left right : HallTree (FreeGenerator.{u} d))
      (hleftBasic : left.IsBasic)
      (hrightBasic : right.IsBasic)
      (htree : tree factor.word = .commutator left right),
      factor.word.weight HEAddres.weight = lowerWeight →
        factor.word.weight HEAddres.weight < n →
          TVRecoll
            (n := n) factor left right hleftBasic hrightBasic htree

namespace
  TCRoute

/-- Recursive reachable tasks remain inside the active full-weight stratum. -/
def Reachable
    {d n lowerWeight : ℕ}
    {ι : Type}
    (_routing :
      TCRoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ) : Prop :=
  factor.word.weight HEAddres.weight = lowerWeight ∧
    Nonempty
      (PCReach
        (n := n) factor rankDefect)

end
  TCRoute

namespace
  PCReach

/--
Every child emitted by a support-local indexed branch is a reachable
two-basic-child task.
-/
noncomputable def children_factory_case
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
    (hrightTree :
      ∀ innerCase,
        branchCase = .innerReductionOuter innerCase →
          tree innerCase.rightWord = innerCase.unchanged)
    {task :
      SPFactor
          (concreteBasicCommutators.{u} d) ι ×
        ℕ}
    (htask :
      task ∈
        (TRBrancha.supported_factory_case
          hn hH routing factor rankDefect hfactorSupported branchCase).children.tasks) :
    PCReach
      (n := n) task.1 task.2 := by
  cases branchCase with
  | leaf leafCase =>
      cases leafCase <;>
        simp [
          TRBrancha.supported_factory_case,
          TRBrancha.ofLeafCase,
          TRBrancha.leaf_of_terminal,
          TRBrancha.leaf_tree_basic,
          TRBrancha.leaf_commutator_self,
          TRBrancha.leaf_reversed_basic,
          TRBrancha.leaf_weight_one,
          TRBrancha.ofResidRecollect,
          SPFactor.RCSrc.empty] at htask
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
              TRBrancha.supported_factory_case,
              TRBrancha.innerComparisonFactory,
              IRChildr.tasks_ranked_task]
              using htask)

end
  PCReach

namespace
  TRBrancha

/--
Flatten one support-local expanded Jacobi root and the inner reductions of its
two descendants into a single strict branch.
-/
noncomputable def supported_ranked_decomp
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
      TCRoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (ranked :
      ERDecomp
        factor)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRBrancha
      (n := n) factor
        (expandedJacobiParent ranked.decomposition) := by
  let first :=
    supported_factory_case hn hH routing.outerRouting
      (expandedJacobiFactor factor ranked.decomposition)
      (expandedJacobiParent ranked.decomposition)
      (by
        simpa only [expanded_jacobi_factor, hfactorWeight] using
          (le_refl lowerWeight))
      (.innerReductionOuter (ranked.firstCase hfactorTruncated))
  let second :=
    supported_factory_case hn hH routing.outerRouting
      (expandedJacobiSecond factor ranked.decomposition)
      (expandedJacobiParent ranked.decomposition)
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
          TDRecoll.of_routedFirst
            (routing.outerRouting.factory factor (by omega))
            (routing.outerRouting.sharp factor (by omega))
            factor ranked.decomposition rfl hfactorTruncated
            firstResidual secondResidual
              (routing.valueResidual factor ranked hfactorWeight
                hfactorTruncated).toInverseRecollection
        TRRecoll.expanded_reduction
          hn hH
          (routing.outerRouting.factory factor (by omega))
          (routing.outerRouting.sharp factor (by omega))
          (routing.outerRouting.nextNormalizer factor (by omega))
          factor ranked.decomposition rfl hfactorTruncated
          continuation.expandedContinuationRecollection
    }

/-- Every child of the flattened support-local Jacobi branch has full weight. -/
lemma word_expanded_jacobi
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
      TCRoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (ranked :
      ERDecomp
        factor)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    {task :
      SPFactor
          (concreteBasicCommutators.{u} d) ι ×
        ℕ}
    (htask :
      task ∈
        (supported_ranked_decomp hn hH routing factor
          ranked hfactorWeight hfactorTruncated).children.tasks) :
    task.1.word.weight HEAddres.weight =
      factor.word.weight HEAddres.weight := by
  let first :=
    supported_factory_case hn hH routing.outerRouting
      (expandedJacobiFactor factor ranked.decomposition)
      (expandedJacobiParent ranked.decomposition)
      (by
        simpa only [expanded_jacobi_factor, hfactorWeight] using
          (le_refl lowerWeight))
      (.innerReductionOuter (ranked.firstCase hfactorTruncated))
  let second :=
    supported_factory_case hn hH routing.outerRouting
      (expandedJacobiSecond factor ranked.decomposition)
      (expandedJacobiParent ranked.decomposition)
      (by
        simpa only [expanded_second_factor, hfactorWeight] using
          (le_refl lowerWeight))
      (.innerReductionOuter (ranked.secondCase hfactorTruncated))
  have htask' : task ∈ first.children.tasks ++ second.children.tasks := by
    simpa only [supported_ranked_decomp,
      SPFactor.RCSrc.tasks_append,
      SPFactor.RCSrc.tasks_reparent]
      using htask
  classical
  by_cases htaskFirst : task ∈ first.children.tasks
  · calc
      task.1.word.weight HEAddres.weight =
          (expandedJacobiFactor factor ranked.decomposition).word.weight
            HEAddres.weight := by
        exact
          word_outer_factory
            hn hH routing.outerRouting
              (expandedJacobiFactor factor ranked.decomposition)
              (expandedJacobiParent ranked.decomposition)
              (by
                simpa only [expanded_jacobi_factor,
                  hfactorWeight] using (le_refl lowerWeight))
              (.innerReductionOuter (ranked.firstCase hfactorTruncated))
              htaskFirst
      _ = factor.word.weight HEAddres.weight :=
        expanded_jacobi_factor factor ranked.decomposition
  · have htaskSecond : task ∈ second.children.tasks :=
      (List.mem_append.mp htask').resolve_left htaskFirst
    calc
      task.1.word.weight HEAddres.weight =
          (expandedJacobiSecond factor ranked.decomposition).word.weight
            HEAddres.weight := by
        exact
          word_outer_factory
            hn hH routing.outerRouting
              (expandedJacobiSecond factor ranked.decomposition)
              (expandedJacobiParent ranked.decomposition)
              (by
                simpa only [expanded_second_factor,
                  hfactorWeight] using (le_refl lowerWeight))
              (.innerReductionOuter (ranked.secondCase hfactorTruncated))
              htaskSecond
      _ = factor.word.weight HEAddres.weight :=
        expanded_second_factor factor ranked.decomposition

end
  TRBrancha

namespace
  PCReach

/-- Every child of a flattened support-local Jacobi branch is reachable. -/
noncomputable def supported_jacobi_children
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
      TCRoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (ranked :
      ERDecomp
        factor)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    {task :
      SPFactor
          (concreteBasicCommutators.{u} d) ι ×
        ℕ}
    (htask :
      task ∈
        (TRBrancha.supported_ranked_decomp
          hn hH routing factor ranked hfactorWeight
            hfactorTruncated).children.tasks) :
    PCReach
      (n := n) task.1 task.2 := by
  let first :=
    TRBrancha.supported_factory_case
      hn hH routing.outerRouting
        (expandedJacobiFactor factor ranked.decomposition)
        (expandedJacobiParent ranked.decomposition)
        (by
          simpa only [expanded_jacobi_factor, hfactorWeight] using
            (le_refl lowerWeight))
        (.innerReductionOuter (ranked.firstCase hfactorTruncated))
  let second :=
    TRBrancha.supported_factory_case
      hn hH routing.outerRouting
        (expandedJacobiSecond factor ranked.decomposition)
        (expandedJacobiParent ranked.decomposition)
        (by
          simpa only [expanded_second_factor, hfactorWeight] using
            (le_refl lowerWeight))
        (.innerReductionOuter (ranked.secondCase hfactorTruncated))
  have htask' : task ∈ first.children.tasks ++ second.children.tasks := by
    simpa only [
      TRBrancha.supported_ranked_decomp,
      SPFactor.RCSrc.tasks_append,
      SPFactor.RCSrc.tasks_reparent]
      using htask
  classical
  by_cases htaskFirst : task ∈ first.children.tasks
  · exact
      children_factory_case hn hH routing.outerRouting
        (expandedJacobiFactor factor ranked.decomposition)
        (expandedJacobiParent ranked.decomposition)
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
        (expandedJacobiParent ranked.decomposition)
        (by
          simpa only [expanded_second_factor, hfactorWeight] using
            (le_refl lowerWeight))
        (.innerReductionOuter (ranked.secondCase hfactorTruncated))
          (fun _ hinnerCase => by
            cases hinnerCase
            rfl)
        ((List.mem_append.mp htask').resolve_left htaskFirst)

end
  PCReach

namespace
  TRBranch

/-- Flatten one exact-weight expanded Jacobi root as a reachable branch. -/
noncomputable def childrenRankedDecomposition
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
      TCRoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (ranked :
      ERDecomp
        factor)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRBranch
      (n := n) routing.Reachable factor
        (expandedJacobiParent ranked.decomposition) where
  branch :=
    TRBrancha.supported_ranked_decomp
      hn hH routing factor ranked hfactorWeight hfactorTruncated
  children_reachable := by
    intro task htask
    exact
      ⟨by
        rw [
          TRBrancha.word_expanded_jacobi
            hn hH routing factor ranked hfactorWeight hfactorTruncated htask]
        exact hfactorWeight,
       ⟨PCReach.supported_jacobi_children
          hn hH routing factor ranked hfactorWeight hfactorTruncated htask⟩⟩

/-- Compile either Hall orientation as an exact-weight reachable branch. -/
noncomputable def childrenRankedDispatch
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
      TCRoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (dispatch :
      CJDispat factor left right hleftBasic
        hrightBasic htree) :
    TRBranch
      (n := n) routing.Reachable factor
        (HallTree.bracketRankDefect
          (left.weight + right.weight) left right) := by
  cases dispatch with
  | forward ranked =>
      rw [←
        CJDispat.forward_rank_defect
          factor left right hleftBasic hrightBasic htree ranked]
      exact
        childrenRankedDecomposition hn hH routing
          factor ranked hfactorWeight hfactorTruncated
  | swapped ranked =>
      rw [←
        CJDispat.swapped_rank_defect
          factor left right hleftBasic hrightBasic htree ranked]
      let swappedFactor :=
        childrenSwapFactor factor left right hleftBasic hrightBasic htree
      have hswappedWeight :
          swappedFactor.word.weight HEAddres.weight =
            lowerWeight := by
        simpa only [swappedFactor, basic_children_swap] using
          hfactorWeight
      have hswappedTruncated :
          swappedFactor.word.weight HEAddres.weight < n := by
        simpa only [swappedFactor, basic_children_swap] using
          hfactorTruncated
      let reversed :=
        childrenRankedDecomposition hn hH
          routing swappedFactor ranked hswappedWeight hswappedTruncated
      exact
        { branch :=
            TRBrancha.childrenSwap
              factor left right hleftBasic hrightBasic htree
                (expandedJacobiParent ranked.decomposition)
                reversed.branch
                (routing.swapValueInverse factor left right hleftBasic
                  hrightBasic htree hfactorWeight hfactorTruncated)
          children_reachable := by
            intro task htask
            exact reversed.children_reachable task (by
              simpa only [
                TRBrancha.childrenSwap,
                SPFactor.RCSrc.tasks_reparent]
                using htask) }

/-- Choose the ranked Hall orientation of an exact-weight reachable frontier. -/
noncomputable def childrenRankedJacobi
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
      TCRoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (left right : HallTree (FreeGenerator.{u} d))
    (hleftBasic : left.IsBasic)
    (hrightBasic : right.IsBasic)
    (htree : tree factor.word = .commutator left right)
    (hchildrenNe : left ≠ right)
    (hforwardNonbasic : ¬(HallTree.commutator left right).IsBasic)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRBranch
      (n := n) routing.Reachable factor
        (HallTree.bracketRankDefect
          (left.weight + right.weight) left right) :=
  childrenRankedDispatch hn hH routing factor left right
    hleftBasic hrightBasic htree hfactorWeight hfactorTruncated
      (rankedJacobiDispatch factor left right hleftBasic
        hrightBasic htree hchildrenNe hforwardNonbasic hreverseNonbasic)

/--
Classify one exact-weight reachable two-basic-child task. All non-leaf roots
flatten one Jacobi frontier.
-/
noncomputable def supported_basic_children
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
      TCRoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (hreachable : routing.Reachable factor rankDefect) :
    TRBranch
      (n := n) routing.Reachable factor rankDefect := by
  rcases hreachable with ⟨hfactorWeight, hreachable⟩
  let reachable := Classical.choice hreachable
  rcases reachable with
    ⟨left, right, hleftBasic, hrightBasic, htree, hfactorTruncated,
      rankDefect_eq⟩
  subst rankDefect
  by_cases hcutoff :
      n ≤ factor.word.weight HEAddres.weight + 1
  · exact
      ofResidRecollect factor
        (HallTree.bracketRankDefect
          (left.weight + right.weight) left right)
        (TRRecoll.of_terminal
          factor hcutoff)
  · by_cases hforwardBasic : (HallTree.commutator left right).IsBasic
    · exact
        ofResidRecollect factor
          (HallTree.bracketRankDefect
            (left.weight + right.weight) left right)
          (TRRecoll.tree_basic
            factor (by
              rw [htree]
              exact hforwardBasic))
    · by_cases hchildrenEq : left = right
      · exact
          ofResidRecollect factor
            (HallTree.bracketRankDefect
              (left.weight + right.weight) left right)
            (TRRecoll.tree_commutator_self
              factor left (by simpa only [hchildrenEq] using htree))
      · by_cases hreverseBasic : (HallTree.commutator right left).IsBasic
        · exact
            ofResidRecollect factor
              (HallTree.bracketRankDefect
                (left.weight + right.weight) left right)
              (TRRecoll.tree_swap_basic
                factor right left htree hreverseBasic)
        · exact
            childrenRankedJacobi hn hH routing factor left
              right hleftBasic hrightBasic htree hchildrenEq hforwardBasic
                hreverseBasic hfactorWeight hfactorTruncated

end
  TRBranch

namespace
  TCRoute

/-- Compile support-local structural branches into a reachable scheduler. -/
noncomputable def scheduler
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
      TCRoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι) :
    RRSchedu
      (n := n) routing.Reachable :=
  RRSchedu.ofBranches
    fun factor rankDefect hreachable =>
      TRBranch.supported_basic_children
        hn hH routing factor rankDefect hreachable

/-- Recollect one certified two-basic-child task in the active stratum. -/
noncomputable def residualRecollection
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
      TCRoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (rankDefect : ℕ)
    (hreachable : routing.Reachable factor rankDefect) :
    TRRecoll
      (n := n) factor :=
  (routing.scheduler hn hH).residualRecollection factor rankDefect hreachable

/--
Recollect one arbitrary exact-weight root. Recursive children are discharged
by the structural two-basic-child scheduler.
-/
noncomputable def residual_recollection_case
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
      TCRoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (_hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (rootCase :
      RankedBranchCase
        (n := n) factor 0)
    (childrenReachable :
      ∀ task ∈
          (TRBrancha.supported_factory_case
            hn hH routing.outerRouting factor 0 (by omega) rootCase).children.tasks,
        PCReach
          (n := n) task.1 task.2) :
    TRRecoll
      (n := n) factor :=
  let branch :=
    TRBrancha.supported_factory_case
      hn hH routing.outerRouting factor 0 (by omega) rootCase
  branch.recollect fun task htask =>
    routing.residualRecollection hn hH task.1 task.2
      ⟨by
        rw [
          TRBrancha.word_outer_factory
            hn hH routing.outerRouting factor 0 (by omega) rootCase htask]
        exact hfactorWeight,
       ⟨childrenReachable task htask⟩⟩

/--
Compile one root case, structural descendant scheduling, and atomic
comparison into the intrinsic restricted-sharp factor tail.
-/
noncomputable def factor_expansion_case
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
      TCRoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (rootCase :
      RankedBranchCase
        (n := n) factor 0)
    (childrenReachable :
      ∀ task ∈
          (TRBrancha.supported_factory_case
            hn hH routing.outerRouting factor 0 (by omega) rootCase).children.tasks,
        PCReach
          (n := n) task.1 task.2) :
    TPExp
      (lowerWeight := lowerWeight) hn (concreteBasicCommutators.{u} d) hH
        ι factor := by
  subst lowerWeight
  exact
    ((routing.residual_recollection_case hn hH factor rfl
        hfactorTruncated rootCase childrenReachable).intrinsicResidualSource
          (TPRecoll.of_atomicNorm
            hn hH factor rfl hfactorTruncated
              (routing.outerRouting.factory factor le_rfl)
              (routing.outerRouting.sharp factor le_rfl)
              (routing.outerRouting.nextNormalizer factor le_rfl))
          rfl).factorExpansion

end
  TCRoute

end TCTex
end Submission

/-!
# Ranked collection at polynomial Jacobi frontiers with two basic children

The older Jacobi-frontier adapter routes a two-basic-child obstruction
through raw expanded-Jacobi descendants.  Those descendants retain the
parent rank, so they are not suitable recursive tasks themselves.

The reachable ranked scheduler instead flattens each oriented Jacobi step:
it reduces both ordinary descendants immediately and recursively schedules
only the strictly descending grandchildren.  This file installs that route
at the collector-facing Jacobi frontier.  Frontiers with a genuinely
nonbasic child remain explicit for the next layer.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

/--
Canonical ranked routing for two-basic-child frontiers, with only
nonbasic-child frontiers left to the caller.
-/
structure
    RCBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    ∀ ι : Type,
      PCRoute.{u}
        (d := d) (n := n) ι
  nonbasicChildResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ¬(tree factor.word).IsBasic →
                ∀ left right : HallTree (FreeGenerator.{u} d),
                  tree factor.word = .commutator left right →
                    left ≠ right →
                      ¬(HallTree.commutator right left).IsBasic →
                        (¬left.IsBasic ∨ ¬right.IsBasic) →
                          TRRecoll
                            (n := n) factor

namespace
  RCBuild

/--
Compile reachable ranked collection for two-basic-child frontiers into the
ordinary Jacobi-frontier collector.
-/
noncomputable def jacobiCollectionBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      RCBuild.{u}
        (d := d) (n := n) hn) :
    JFBuild.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  jacobiFrontierResidual := by
    intro ι lowerWeight hnonterminal factor _hfactorWeight hfactorTruncated
      _htreeNonbasic left right htree _hchildrenNe _hreverseNonbasic
    by_cases hleftBasic : left.IsBasic
    · by_cases hrightBasic : right.IsBasic
      · exact
          (builder.routing ι).residualRecollection hn
            (fun s hs hsn =>
              concrete_forms_associated
                d n s hs hsn)
            factor
              (HallTree.bracketRankDefect
                (left.weight + right.weight) left right)
              ⟨{
                left := left
                right := right
                left_isBasic := hleftBasic
                right_isBasic := hrightBasic
                tree_eq := htree
                factor_truncated := hfactorTruncated
                rankDefect_eq := rfl
              }⟩
      · exact
          builder.nonbasicChildResidual lowerWeight hnonterminal factor
            _hfactorWeight hfactorTruncated _htreeNonbasic left right htree
              _hchildrenNe _hreverseNonbasic (Or.inr hrightBasic)
    · exact
        builder.nonbasicChildResidual lowerWeight hnonterminal factor
          _hfactorWeight hfactorTruncated _htreeNonbasic left right htree
            _hchildrenNe _hreverseNonbasic (Or.inl hleftBasic)

end
  RCBuild

/--
For canonical Hall families, ranked two-basic-child scheduling and explicit
nonbasic-child residuals construct product coordinate polynomials.
-/
theorem
    commutators_jacobi_frontier
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      RCBuild.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_frontier_collect
    hn e builder.jacobiCollectionBuilder

/--
For canonical Hall families, ranked two-basic-child scheduling and explicit
nonbasic-child residuals construct inverse coordinate polynomials.
-/
theorem
    commutators_poly_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      RCBuild.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_reduction_builder
    hn e builder.jacobiCollectionBuilder

end TCTex
end Submission

/-!
# Jacobi-only value routing for support-local signed-polynomial residuals

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


open CEWord

/-- Support-local outer routing with only named Jacobi value-packet inputs. -/
structure
    JORoute
    {d n lowerWeight : ℕ}
    (ι : Type) where
  outerRouting :
    PFRoute.{u}
      (d := d) (n := n) (lowerWeight := lowerWeight) ι
  valueResidualFactor :
    ∀
      (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι)
      (_ranked :
        ERDecomp
          factor),
      factor.word.weight HEAddres.weight = lowerWeight →
        factor.word.weight HEAddres.weight < n →
          TRRecoll
            (n := n) factor
  valueResidualFirst :
    ∀
      (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι)
      (ranked :
        ERDecomp
          factor),
      factor.word.weight HEAddres.weight = lowerWeight →
        factor.word.weight HEAddres.weight < n →
          TRRecoll
            (n := n)
            (expandedJacobiFactor factor ranked.decomposition)
  valueResidualSecond :
    ∀
      (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι)
      (ranked :
        ERDecomp
          factor),
      factor.word.weight HEAddres.weight = lowerWeight →
        factor.word.weight HEAddres.weight < n →
          TRRecoll
            (n := n)
            (expandedJacobiSecond factor ranked.decomposition)

namespace
  JORoute

/-- Compile named Jacobi inputs and exact empty swap packets into the router. -/
noncomputable def supportedChildrenRouting
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
      JORoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι) :
    TCRoute
      (d := d) (n := n) (lowerWeight := lowerWeight) ι where
  outerRouting := routing.outerRouting
  valueResidual factor ranked hfactorWeight hfactorTruncated :=
    TRRecolla.namedBasicResids
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
    TVRecoll.empty
      factor left right hleftBasic hrightBasic htree

/-- Recollect one exact-weight root from Jacobi-only value obligations. -/
noncomputable def residual_recollection_case
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
      JORoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (rootCase :
      RankedBranchCase
        (n := n) factor 0)
    (childrenReachable :
      ∀ task ∈
          (TRBrancha.supported_factory_case
            hn hH routing.outerRouting factor 0 (by omega) rootCase).children.tasks,
        PCReach
          (n := n) task.1 task.2) :
    TRRecoll
      (n := n) factor :=
  (routing.supportedChildrenRouting hn hH)
    |>.residual_recollection_case hn hH factor hfactorWeight
      hfactorTruncated rootCase childrenReachable

/-- Compile the Jacobi-only route into the intrinsic factor-tail endpoint. -/
noncomputable def factor_expansion_case
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
      JORoute
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (rootCase :
      RankedBranchCase
        (n := n) factor 0)
    (childrenReachable :
      ∀ task ∈
          (TRBrancha.supported_factory_case
            hn hH routing.outerRouting factor 0 (by omega) rootCase).children.tasks,
        PCReach
          (n := n) task.1 task.2) :
    TPExp
      (lowerWeight := lowerWeight) hn (concreteBasicCommutators.{u} d) hH
        ι factor :=
  (routing.supportedChildrenRouting hn hH)
    |>.factor_expansion_case hn hH factor hfactorWeight
      hfactorTruncated rootCase childrenReachable

end
  JORoute

end TCTex
end Submission

/-!
# Recursive value routing for support-local polynomial Hall residuals

The support-local signed-polynomial scheduler consumes a semantic value
residual at the active Hall weight.  Direct normalization of that packet asks
for a semantic normalizer at the same stratum.

This file replaces that circular input by finite concrete residual
obligations.  Each factor in a forward Jacobi value packet is reduced to its
atomic Hall packet and an already recollected intrinsic residual.  Signed
swap packets cancel exactly and therefore recollect to the empty source.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open CEWord

/--
Support-local outer routing together with recursive concrete residuals for
the finite factors exposed by forward Jacobi value packets.
-/
structure
    TCRec
    {d n lowerWeight : ℕ}
    (ι : Type) where
  outerRouting :
    PFRoute.{u}
      (d := d) (n := n) (lowerWeight := lowerWeight) ι
  valueResidualBasic :
    ∀
      (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι)
      (ranked :
        ERDecomp
          factor),
      factor.word.weight HEAddres.weight = lowerWeight →
        factor.word.weight HEAddres.weight < n →
          ∀ child ∈
              expandedJacobiRaw factor ranked.decomposition,
            TRRecoll
              (n := n) child

namespace
  TCRec

/--
Compile finite recursive value-packet obligations into the semantic value
residuals consumed by the support-local structural scheduler.
-/
noncomputable def supportedChildrenRouting
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
      TCRec
        (d := d) (n := n) (lowerWeight := lowerWeight) ι) :
    TCRoute
      (d := d) (n := n) (lowerWeight := lowerWeight) ι where
  outerRouting := routing.outerRouting
  valueResidual factor ranked hfactorWeight hfactorTruncated :=
    TRRecolla.ofBasicResiduals
      hn hH
      (routing.outerRouting.factory factor (by omega))
      (routing.outerRouting.sharp factor (by omega))
      (routing.outerRouting.nextNormalizer factor (by omega))
      factor ranked.decomposition rfl hfactorTruncated
      (routing.valueResidualBasic factor ranked hfactorWeight
        hfactorTruncated)
  swapValueInverse factor left right hleftBasic hrightBasic htree
      _hfactorWeight _hfactorTruncated :=
    TVRecoll.empty
      factor left right hleftBasic hrightBasic htree

/--
Recollect one arbitrary exact-weight root from a root classifier, reachable
children, and finite recursive value-packet obligations.
-/
noncomputable def residual_recollection_case
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
      TCRec
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (rootCase :
      RankedBranchCase
        (n := n) factor 0)
    (childrenReachable :
      ∀ task ∈
          (TRBrancha.supported_factory_case
            hn hH routing.outerRouting factor 0 (by omega) rootCase).children.tasks,
        PCReach
          (n := n) task.1 task.2) :
    TRRecoll
      (n := n) factor :=
  (routing.supportedChildrenRouting hn hH)
    |>.residual_recollection_case hn hH factor hfactorWeight
      hfactorTruncated rootCase childrenReachable

/--
Compile the recursive value-packet route into the intrinsic factor tail used
by the restricted-sharp active-block collector.
-/
noncomputable def factor_expansion_case
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
      TCRec
        (d := d) (n := n) (lowerWeight := lowerWeight) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (rootCase :
      RankedBranchCase
        (n := n) factor 0)
    (childrenReachable :
      ∀ task ∈
          (TRBrancha.supported_factory_case
            hn hH routing.outerRouting factor 0 (by omega) rootCase).children.tasks,
        PCReach
          (n := n) task.1 task.2) :
    TPExp
      (lowerWeight := lowerWeight) hn (concreteBasicCommutators.{u} d) hH
        ι factor :=
  (routing.supportedChildrenRouting hn hH)
    |>.factor_expansion_case hn hH factor hfactorWeight
      hfactorTruncated rootCase childrenReachable

end
  TCRec

end TCTex
end Submission

/-!
# Canonical collection from reachable two-basic-child polynomial routing

The restricted ranked scheduler closes every frontier whose two children are
Hall basic.  A complete signed semantic normalizer family also supplies the
broader fallback for frontiers with a genuinely nonbasic child.  This file
packages that compatibility endpoint and exports the resulting Claim 8 product
and inverse coordinate polynomials.

The fallback remains explicit in the preceding frontier interface so a later
outer-induction construction can replace current-stratum normalization without
changing the reachable two-basic-child scheduler.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
Canonical reachable routing for every exponent-variable type, together with
the Hall-Petresco packet consumed by the collector.
-/
structure
    CCBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    ∀ ι : Type,
      PCRoute.{u}
        (d := d) (n := n) ι

namespace
  CCBuild

open
  TRRecoll

/--
Build canonical collection routing from comparison-factory routing and one
signed semantic normalizer family.
-/
noncomputable def comparison_factory_routing
    {d n : ℕ}
    {hn : 2 ≤ n}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (routing :
      ∀ ι : Type,
        TFRoute.{u}
          (d := d) (n := n) ι)
    (normalizerFamily :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d)) :
    CCBuild.{u}
      (d := d) (n := n) hn where
  packet := packet
  routing ι :=
    PCRoute.comparison_factory_routing
      (routing ι) normalizerFamily

/--
Fill the remaining nonbasic-child frontier fallback from the bundled
normalizer family while preserving ranked scheduling at every two-basic-child
frontier.
-/
noncomputable def rankedChildrenJacobi
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      CCBuild.{u}
        (d := d) (n := n) hn) :
    RCBuild.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  routing := builder.routing
  nonbasicChildResidual := by
    intro ι lowerWeight _hnonterminal factor hfactorWeight hfactorTruncated
      _htreeNonbasic _left _right _htree _hchildrenNe _hreverseNonbasic _hchild
    exact
      ofNormalizerFamily hn
        (fun s hs hsn =>
          concrete_forms_associated d n s hs hsn)
        (builder.routing ι).normalizerFamily factor hfactorWeight
          hfactorTruncated

end
  CCBuild

/--
Canonical reachable two-basic-child routing constructs product coordinate
polynomials, with arbitrary nonbasic-child frontiers normalized by the bundled
compatibility family.
-/
theorem
    children_collect_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      CCBuild.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_jacobi_frontier
    hn e builder.rankedChildrenJacobi

/--
Canonical reachable two-basic-child routing constructs inverse coordinate
polynomials, with arbitrary nonbasic-child frontiers normalized by the bundled
compatibility family.
-/
theorem
    commutators_children_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      CCBuild.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_poly_builder
    hn e builder.rankedChildrenJacobi

end TCTex
end Submission

/-!
# Ranked polynomial frontiers reduced to nonbasic left children

The reachable scheduler closes every Jacobi frontier with two basic children.
For a remaining frontier, a nonbasic left child is already in the orientation
needed by outer induction.  If only the right child is nonbasic, an exact
sign-corrected root swap exposes it on the left and contributes one separately
recollected skew-value residual.

This file packages that orientation step.  The only remaining recursive
boundary is a frontier with an explicitly nonbasic left child.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open CEWord

universe u

/--
Reachable ranked routing for two-basic-child frontiers, root-swap value
recollections, and residuals for frontiers with a nonbasic left child.
-/
structure
    PFBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    ∀ ι : Type,
      PCRoute.{u}
        (d := d) (n := n) ι
  rootSwapResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              PSRecoll
                (n := n) factor left right hword
  leftNonbasicResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ left right : HallTree (FreeGenerator.{u} d),
                tree factor.word = .commutator left right →
                  ¬left.IsBasic →
                    left ≠ right →
                      ¬(HallTree.commutator right left).IsBasic →
                        TRRecoll
                          (n := n) factor

namespace
  PFBuild

open
  TRRecoll

/--
Orient every genuinely nonbasic-child frontier so that its nonbasic child is
on the left, using one exact root swap when necessary.
-/
noncomputable def nonbasicChildResidual
    {d n : ℕ}
    {hn : 2 ≤ n}
    {ι : Type}
    (builder :
      PFBuild.{u}
        (d := d) (n := n) hn)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (htreeNonbasic : ¬(tree factor.word).IsBasic)
    (left right : HallTree (FreeGenerator.{u} d))
    (htree : tree factor.word = .commutator left right)
    (hchildrenNe : left ≠ right)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic)
    (hchild : ¬left.IsBasic ∨ ¬right.IsBasic) :
    TRRecoll
      (n := n) factor := by
  by_cases hleftBasic : left.IsBasic
  · have hrightNonbasic : ¬right.IsBasic := by
      intro hrightBasic
      exact hchild.elim (fun h => h hleftBasic) (fun h => h hrightBasic)
    cases right with
    | atom generator =>
        exact False.elim (hrightNonbasic (HallTree.isBasic_atom generator))
    | commutator right₁ right₂ =>
        cases hword : factor.word with
        | atom address =>
            exfalso
            apply htreeNonbasic
            rw [hword]
            exact concrete_hall_tree address.2
        | commutator leftWord rightWord =>
            have htree' := htree
            rw [hword, tree_commutator] at htree'
            injection htree' with hleftTree hrightTree
            let reversed :=
              expandedSwapFactor factor leftWord rightWord hword
            exact
              expanded_swap factor leftWord rightWord hword
                (builder.leftNonbasicResidual lowerWeight hnonterminal
                  reversed
                    (by
                      dsimp only [reversed]
                      simpa only [expanded_root_factor] using
                        hfactorWeight)
                    (by
                      dsimp only [reversed]
                      simpa only [expanded_root_factor] using
                        hfactorTruncated)
                  (.commutator right₁ right₂) left
                    (by
                      dsimp only [reversed]
                      rw [tree_expanded_swap, hrightTree,
                        hleftTree])
                    hrightNonbasic hchildrenNe.symm
                    (by
                      rw [← htree]
                      exact htreeNonbasic))
                (builder.rootSwapResidual lowerWeight hnonterminal factor
                  leftWord rightWord hword hfactorWeight hfactorTruncated)
  · exact
      builder.leftNonbasicResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated left right htree hleftBasic hchildrenNe
          hreverseNonbasic

/--
Compile nonbasic-left orientation into the collector-facing frontier
interface.
-/
noncomputable def rankedChildrenJacobi
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      PFBuild.{u}
        (d := d) (n := n) hn) :
    RCBuild.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  routing := builder.routing
  nonbasicChildResidual :=
    fun lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
        htreeNonbasic left right htree hchildrenNe hreverseNonbasic hchild =>
      builder.nonbasicChildResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated htreeNonbasic left right htree
          hchildrenNe hreverseNonbasic hchild

end
  PFBuild

/--
For canonical Hall families, ranked two-basic-child scheduling, root-swap
orientation, and explicit nonbasic-left residuals construct product
coordinate polynomials.
-/
theorem
    jacobi_collect_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      PFBuild.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_jacobi_frontier
    hn e builder.rankedChildrenJacobi

/--
For canonical Hall families, ranked two-basic-child scheduling, root-swap
orientation, and explicit nonbasic-left residuals construct inverse
coordinate polynomials.
-/
theorem
    jacobi_frontier_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      PFBuild.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_poly_builder
    hn e builder.rankedChildrenJacobi

end TCTex
end Submission

/-!
# Canonical ranked polynomial collection from normalizer families

A complete signed semantic normalizer family supplies the two independent
recollections used by comparison-factory routing: atomic-to-child comparisons
and full basic-reduction residuals.  Together with the correction-packet
schedule, these factories instantiate the canonical reachable two-basic-child
collector.

The resulting path is a compatibility constructor.  Its comparison quotient
still records the non-circular outer-residual interface, while the supplied
normalizer family discharges the broader current-stratum obligations.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

namespace
  SNFam

/--
Normalize every atomic-to-child comparison into the next support layer.
-/
noncomputable def
    comparisonRecollectionFactory
    {d n : ℕ}
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
    (ι : Type) :
    ComparisonRecollectionFactory
      (d := d) (n := n) ι where
  sourceRecollection factor innerWord rightWord hword hfactorTruncated :=
    (family.normalizer
      (factor.word.weight HEAddres.weight))
      |>.source_recollection_series hn
        (concreteBasicCommutators.{u} d) hH
        (innerComparisonSource
          factor innerWord rightWord hword)
        factor.word_weight_pos hfactorTruncated
        (truncated_inner_comparison
          factor innerWord rightWord hword hfactorTruncated)
        (least_inner_comparison
          factor innerWord rightWord hword)
        (inner_comparison_series
          factor innerWord rightWord hword)

/-- Normalize every full basic-reduction residual into its higher tail. -/
noncomputable def concreteReductionFactory
    {d n : ℕ}
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
    (ι : Type) :
    ConcreteRecollectionFactory
      (d := d) (n := n) ι where
  residualRecollection factor hfactorTruncated :=
    TRRecoll.ofNormalizerFamily
      hn hH family factor rfl hfactorTruncated

end
  SNFam

namespace
  CCBuild

/--
Instantiate canonical ranked collection from a correction schedule and a
complete semantic normalizer family.
-/
noncomputable def normalizers_factory_schedule
    {d n : ℕ}
    {hn : 2 ≤ n}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (schedule :
      SFSched
        (n := n) (concreteBasicCommutators.{u} d))
    (family :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d)) :
    CCBuild.{u}
      (d := d) (n := n) hn :=
  comparison_factory_routing packet
    (fun ι =>
      TFRoute.schedule_residual_factories
        schedule
        (fun _lowerWeight strongerWeight _hstronger =>
          family.normalizer strongerWeight)
        (family.comparisonRecollectionFactory
          hn
          (forms_graded_below d n)
          ι)
        (family.concreteReductionFactory
          hn
          (forms_graded_below d n)
          ι))
    family

/--
The reachable signed-semantic builder supplies the schedule and normalizer
family used by canonical ranked collection.
-/
noncomputable def ofReachableBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CCBuild.{u}
      (d := d) (n := n) hn :=
  normalizers_factory_schedule packet
    (builder.supportedCorrectionFactory
      (concreteCommutatorsWeight.{u} d))
    (builder.supportedNormalizerFamily hn
      (concreteCommutatorsWeight.{u} d)
      (forms_graded_below d n))

end
  CCBuild

/--
Route a reachable signed-semantic builder through canonical ranked
two-basic-child collection to construct product coordinate polynomials.
-/
theorem
    commutators_children_collect
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  children_collect_builder
    hn e
      (CCBuild.ofReachableBuilder
        packet builder)

/--
Route a reachable signed-semantic builder through canonical ranked
two-basic-child collection to construct inverse coordinate polynomials.
-/
theorem
    ranked_children_collect
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_children_builder
    hn e
      (CCBuild.ofReachableBuilder
        packet builder)

end TCTex
end Submission

/-!
# Ranked polynomial frontiers with exposed nested words

After root-swap orientation, every remaining frontier has a nonbasic left
child.  Such a child cannot be an atom.  Both nonbasic layers therefore come
from commutator-shaped symbolic words, and the existing syntactic Jacobi
decomposition chooser exposes those words.

This file packages that exposure step.  The remaining boundary receives an
explicit left-normed symbolic decomposition suitable for structural
outer-induction classification.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open CEWord

universe u

/-- A left-normed nonbasic frontier together with its exposed symbolic words. -/
structure
    NWCase
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) where
  left :
    HallTree (FreeGenerator.{u} d)
  middle :
    HallTree (FreeGenerator.{u} d)
  right :
    HallTree (FreeGenerator.{u} d)
  tree_eq :
    tree factor.word = .commutator (.commutator left middle) right
  outer_nonbasic :
    ¬(HallTree.commutator (.commutator left middle) right).IsBasic
  inner_nonbasic :
    ¬(HallTree.commutator left middle).IsBasic
  children_ne :
    HallTree.commutator left middle ≠ right
  reverse_nonbasic :
    ¬(HallTree.commutator right (.commutator left middle)).IsBasic
  decomposition :
    SyntacticJacobiDecomposition factor.word

/--
Reachable ranked routing and residuals for explicitly exposed nested symbolic
frontiers.
-/
structure
    CNBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    ∀ ι : Type,
      PCRoute.{u}
        (d := d) (n := n) ι
  rootSwapResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              PSRecoll
                (n := n) factor left right hword
  nestedWordsResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              NWCase
                  factor →
                TRRecoll
                  (n := n) factor

namespace
  CNBuild

/-- Expose nested words at one explicitly nonbasic-left frontier. -/
noncomputable def leftNonbasicResidual
    {d n : ℕ}
    {hn : 2 ≤ n}
    {ι : Type}
    (builder :
      CNBuild.{u}
        (d := d) (n := n) hn)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (left right : HallTree (FreeGenerator.{u} d))
    (htree : tree factor.word = .commutator left right)
    (hleftNonbasic : ¬left.IsBasic)
    (hchildrenNe : left ≠ right)
    (hreverseNonbasic : ¬(HallTree.commutator right left).IsBasic) :
    TRRecoll
      (n := n) factor := by
  cases left with
  | atom generator =>
      exact False.elim (hleftNonbasic (HallTree.isBasic_atom generator))
  | commutator left middle =>
      have houterNonbasic :
          ¬(HallTree.commutator (.commutator left middle) right).IsBasic := by
        intro hbasic
        exact
          hleftNonbasic
            ((HallTree.isBasic_commutator (.commutator left middle) right).mp
              hbasic).1
      let decomposition :=
        syntacticTreeNonbasic
          factor.word left middle right (by simpa only using htree)
            houterNonbasic hleftNonbasic
      exact
        builder.nestedWordsResidual lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated
            {
              left := left
              middle := middle
              right := right
              tree_eq := by simpa only using htree
              outer_nonbasic := houterNonbasic
              inner_nonbasic := hleftNonbasic
              children_ne := hchildrenNe
              reverse_nonbasic := hreverseNonbasic
              decomposition := decomposition
            }

/-- Compile nested-word exposure into the nonbasic-left frontier interface. -/
noncomputable def
    rankedChildrenExpanded
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      CNBuild.{u}
        (d := d) (n := n) hn) :
    PFBuild.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  leftNonbasicResidual :=
    fun lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
        left right htree hleftNonbasic hchildrenNe hreverseNonbasic =>
      builder.leftNonbasicResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated left right htree hleftNonbasic
          hchildrenNe hreverseNonbasic

end
  CNBuild

/--
For canonical Hall families, ranked two-basic-child scheduling, root-swap
orientation, and explicit nested-word residuals construct product coordinate
polynomials.
-/
theorem
    commutators_ranked_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      CNBuild.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  jacobi_collect_builder
    hn e builder.rankedChildrenExpanded

/--
For canonical Hall families, ranked two-basic-child scheduling, root-swap
orientation, and explicit nested-word residuals construct inverse coordinate
polynomials.
-/
theorem
    ranked_expanded_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      CNBuild.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  jacobi_frontier_builder
    hn e builder.rankedChildrenExpanded

end TCTex
end Submission

/-!
# Ranked nonbasic-left polynomial frontiers from normalizer families

A complete signed semantic normalizer family supplies a compatibility
implementation of the two residual obligations left by expanded-left frontier
orientation: generic root-swap skew packets and explicitly left-nonbasic
residuals.

The latter field is the remaining current-stratum fallback.  Keeping this
adapter separate makes it possible to replace that field with structural
outer induction without changing reachable ranked scheduling or root-swap
orientation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace
  PFBuild

open
  TRRecoll
  PSRecoll

/--
Fill root-swap packets and the remaining nonbasic-left fallback from one
complete normalizer family.
-/
noncomputable def builderNormalizerFamily
    {d n : ℕ}
    {hn : 2 ≤ n}
    (canonical :
      CCBuild.{u}
        (d := d) (n := n) hn)
    (family :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d)) :
    PFBuild.{u}
      (d := d) (n := n) hn where
  packet := canonical.packet
  routing := canonical.routing
  rootSwapResidual :=
    fun _lowerWeight _hnonterminal factor left right hword hfactorWeight
        hfactorTruncated =>
      ofNormalizerFamily hn
        (forms_graded_below d n)
        family factor left right hword hfactorWeight hfactorTruncated
  leftNonbasicResidual :=
    fun _lowerWeight _hnonterminal factor hfactorWeight hfactorTruncated
        _left _right _htree _hleftNonbasic _hchildrenNe _hreverseNonbasic =>
      ofNormalizerFamily hn
        (forms_graded_below d n)
        family factor hfactorWeight hfactorTruncated

/--
The reachable signed-semantic builder supplies the schedule and normalizer
family for the compatibility expanded-left route.
-/
noncomputable def ofReachableBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    PFBuild.{u}
      (d := d) (n := n) hn :=
  let family :=
    builder.supportedNormalizerFamily hn
      (concreteCommutatorsWeight.{u} d)
      (forms_graded_below d n)
  builderNormalizerFamily
    (CCBuild.ofReachableBuilder
      packet builder)
    family

end
  PFBuild

/--
Route a reachable signed-semantic builder through explicit expanded-left
orientation to construct product coordinate polynomials.
-/
theorem
    commutators_collected_frontier
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  jacobi_collect_builder
    hn e
      (PFBuild.ofReachableBuilder
        packet builder)

/--
Route a reachable signed-semantic builder through explicit expanded-left
orientation to construct inverse coordinate polynomials.
-/
theorem
    collected_frontier_collect
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  jacobi_frontier_builder
    hn e
      (PFBuild.ofReachableBuilder
        packet builder)

end TCTex
end Submission

/-!
# Structural inner-span cases for exposed nested polynomial frontiers

An explicitly nested frontier does not carry enough Hall inequalities to
choose a recursive branch automa.  Once a caller supplies the
recipe-correct inner-span case, however, the existing outer-factory branch
emits only reachable two-basic-child tasks.  The canonical restricted
scheduler therefore recollects every strict child without a parent-stratum
fallback.

This file packages that local structural certificate and compiles a family of
such certificates into the exposed nested-word frontier interface.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

/--
A recipe-correct structural inner-span branch for one exposed nested-word
frontier.  The retained right-word equality is exactly the extra fact needed
to prove that every generated child is a reachable two-basic-child task.
-/
structure
    EWCase
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) where
  rankDefect : ℕ
  innerReductionOuter :
    TruncatedRankedCase
      (n := n) factor rankDefect
  right_tree :
    tree innerReductionOuter.rightWord = innerReductionOuter.unchanged

namespace
  EWCase

/--
When the exposed inner right tree is smaller than the retained outer basic
tree, the nested frontier is a direct structural inner-span case.
-/
noncomputable def inner_right_outer
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (frontier :
      NWCase
        factor)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (hinnerRightOuterRight : frontier.middle < frontier.right)
    (houterRightBasic : frontier.right.IsBasic) :
    EWCase
      (n := n) factor := by
  have hdecompositionTree :
      tree factor.word =
        HallTree.commutator
          (.commutator
            (tree frontier.decomposition.left)
            (tree frontier.decomposition.middle))
          (tree frontier.decomposition.right) := by
    have htree := congrArg tree frontier.decomposition.word_eq
    simpa only [tree_commutator] using htree
  have hroot :
      HallTree.commutator
          (.commutator
            (tree frontier.decomposition.left)
            (tree frontier.decomposition.middle))
          (tree frontier.decomposition.right) =
        .commutator (.commutator frontier.left frontier.middle)
          frontier.right := by
    exact hdecompositionTree.symm.trans frontier.tree_eq
  injection hroot with hinner hright
  injection hinner with hleft hmiddle
  exact
    {
      rankDefect :=
        HallTree.bracketRankDefect
          ((tree (.commutator frontier.decomposition.left
              frontier.decomposition.middle)).weight +
            frontier.right.weight)
          (.commutator frontier.left frontier.middle) frontier.middle
      innerReductionOuter :=
        {
          innerWord :=
            .commutator frontier.decomposition.left
              frontier.decomposition.middle
          rightWord := frontier.decomposition.right
          hword := frontier.decomposition.word_eq
          hfactorTruncated := hfactorTruncated
          added := frontier.left
          originalRight := frontier.middle
          unchanged := frontier.right
          originalLeft := .commutator frontier.left frontier.middle
          hinnerTree := by
            simp only [tree_commutator, hleft, hmiddle]
          hRightLeft :=
            HallTree.weight_add_left frontier.left frontier.middle
              (.commutator frontier.left frontier.middle) rfl
          hRightUnchanged := hinnerRightOuterRight
          hunchangedBasic := houterRightBasic
          rankDefect_eq := rfl
        }
      right_tree := hright
    }

/--
Compile one admissible structural inner-span case and recursively recollect
its strict two-basic-child tasks with the canonical reachable scheduler.
-/
noncomputable def residualRecollection
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
      PCRoute
        (d := d) (n := n) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (structural :
      EWCase
        (n := n) factor) :
    TRRecoll
      (n := n) factor :=
  let branch :=
    TRBrancha.innerOuterFactory
      hn hH routing.outerRouting factor structural.rankDefect
        structural.innerReductionOuter
  branch.recollect fun task htask =>
    routing.residualRecollection hn hH task.1 task.2
      ⟨PCReach.reduction_factory_children
        hn hH routing.outerRouting factor structural.rankDefect
          structural.innerReductionOuter structural.right_tree htask⟩

end
  EWCase

/--
Reachable ranked routing plus a structural Hall-algorithm classification for
every exposed nested-word frontier.
-/
structure
    ENBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    ∀ ι : Type,
      PCRoute.{u}
        (d := d) (n := n) ι
  rootSwapResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              PSRecoll
                (n := n) factor left right hword
  nestedStructuralCase :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              NWCase
                  factor →
                EWCase
                  (n := n) factor

namespace
  ENBuild

/--
Compile structural nested-word classification into the residual-valued
nested-word frontier interface.
-/
noncomputable def
    rankedWordsBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      ENBuild.{u}
        (d := d) (n := n) hn) :
    CNBuild.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  nestedWordsResidual :=
    fun lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
        frontier =>
      let structural :=
        builder.nestedStructuralCase lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated frontier
      structural.residualRecollection hn
        (fun s hs hsn =>
          concrete_forms_associated d n s hs
            hsn)
        (builder.routing _) factor

end
  ENBuild

/--
Reachable ranked routing plus direct inner-span inequalities for every
exposed nested-word frontier.
-/
structure
    TJBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    ∀ ι : Type,
      PCRoute.{u}
        (d := d) (n := n) ι
  rootSwapResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              PSRecoll
                (n := n) factor left right hword
  nestedInnerOuter :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.middle < frontier.right
  nestedOuterBasic :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic

namespace
  TJBuild

/--
Compile local direct-inner-span inequalities into structural nested-word
classification.
-/
noncomputable def
    rankedWordsStructural
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      TJBuild.{u}
        (d := d) (n := n) hn) :
    ENBuild.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  nestedStructuralCase :=
    fun lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
        frontier =>
      EWCase.inner_right_outer
        factor frontier hfactorTruncated
          (builder.nestedInnerOuter lowerWeight hnonterminal
            factor hfactorWeight hfactorTruncated frontier)
          (builder.nestedOuterBasic lowerWeight hnonterminal factor
            hfactorWeight hfactorTruncated frontier)

end
  TJBuild

/--
Structural classification of exposed nested-word frontiers constructs product
coordinate polynomials.
-/
theorem
    children_expanded_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      ENBuild.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_ranked_builder
    hn e
      builder.rankedWordsBuilder

/--
Structural classification of exposed nested-word frontiers constructs inverse
coordinate polynomials.
-/
theorem
    ranked_children_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      ENBuild.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  ranked_expanded_builder
    hn e
      builder.rankedWordsBuilder

end TCTex
end Submission

/-!
# Direct inner-span collection for exposed nested polynomial frontiers

The structural nested-word case applies automa when the retained
outer-right tree is basic and the inner-right tree is smaller.  These are the
local inequalities inherited by ordinary descendants of a Hall-oriented
Jacobi step.

This file installs that direct branch automa and narrows the remaining
frontier boundary to nested roots where either inequality is unavailable.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
Reachable ranked routing, root-swap residuals, and a fallback only for nested
frontiers outside the direct structural inner-span case.
-/
structure
    TCBuildc
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    ∀ ι : Type,
      PCRoute.{u}
        (d := d) (n := n) ι
  rootSwapResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              PSRecoll
                (n := n) factor left right hword
  nestedWordsFallback :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                (¬frontier.middle < frontier.right ∨
                    ¬frontier.right.IsBasic) →
                  TRRecoll
                    (n := n) factor

namespace
  TCBuildc

/--
Use direct structural inner-span recollection whenever its local inequalities
hold, leaving only the complementary nested cases to the caller.
-/
noncomputable def
    rankedWordsBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      TCBuildc.{u}
        (d := d) (n := n) hn) :
    CNBuild.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  nestedWordsResidual := by
    intro ι lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
      frontier
    by_cases hinnerRightOuterRight : frontier.middle < frontier.right
    · by_cases houterRightBasic : frontier.right.IsBasic
      · exact
          (EWCase.inner_right_outer
            factor frontier hfactorTruncated hinnerRightOuterRight
              houterRightBasic).residualRecollection hn
                (fun s hs hsn =>
                  concrete_forms_associated
                    d n s hs hsn)
                (builder.routing ι) factor
      · exact
          builder.nestedWordsFallback lowerWeight hnonterminal factor
            hfactorWeight hfactorTruncated frontier (Or.inr houterRightBasic)
    · exact
        builder.nestedWordsFallback lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated frontier
            (Or.inl hinnerRightOuterRight)

end
  TCBuildc

/--
Direct nested inner-span collection with an explicit complementary fallback
constructs product coordinate polynomials.
-/
theorem
    commutators_inner_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      TCBuildc.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_ranked_builder
    hn e
      builder.rankedWordsBuilder

/--
Direct nested inner-span collection with an explicit complementary fallback
constructs inverse coordinate polynomials.
-/
theorem
    commutators_jacobi_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      TCBuildc.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  ranked_expanded_builder
    hn e
      builder.rankedWordsBuilder

end TCTex
end Submission

/-!
# Direct nested inner-span polynomial collection from normalizer families

A complete signed semantic normalizer family supplies compatibility
implementations of the residual obligations left after direct nested
inner-span collection: generic root-swap skew packets and the complementary
nested frontiers where either local structural inequality is unavailable.

The latter field is still a current-stratum fallback, but it is now invoked
only outside the direct structural inner-span branch.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace
  TCBuildc

/--
Fill root-swap packets and the complementary nested-word fallback from one
complete normalizer family.
-/
noncomputable def builderNormalizerFamily
    {d n : ℕ}
    {hn : 2 ≤ n}
    (canonical :
      CCBuild.{u}
        (d := d) (n := n) hn)
    (family :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d)) :
    TCBuildc.{u}
      (d := d) (n := n) hn where
  packet := canonical.packet
  routing := canonical.routing
  rootSwapResidual :=
    fun _lowerWeight _hnonterminal factor left right hword hfactorWeight
        hfactorTruncated =>
      PSRecoll.ofNormalizerFamily
        hn
        (forms_graded_below d n)
        family factor left right hword hfactorWeight hfactorTruncated
  nestedWordsFallback :=
    fun _lowerWeight _hnonterminal factor hfactorWeight hfactorTruncated
        _frontier _hcomplement =>
      TRRecoll.ofNormalizerFamily
        hn
        (forms_graded_below d n)
        family factor hfactorWeight hfactorTruncated

/--
The reachable signed-semantic builder supplies the schedule and normalizer
family for compatibility direct nested inner-span collection.
-/
noncomputable def ofReachableBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    TCBuildc.{u}
      (d := d) (n := n) hn :=
  let family :=
    builder.supportedNormalizerFamily hn
      (concreteCommutatorsWeight.{u} d)
      (forms_graded_below d n)
  builderNormalizerFamily
    (CCBuild.ofReachableBuilder
      packet builder)
    family

end
  TCBuildc

/--
Route a reachable signed-semantic builder through direct nested inner-span
collection to construct product coordinate polynomials.
-/
theorem
    span_frontier_collect
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_inner_builder
    hn e
      (TCBuildc.ofReachableBuilder
        packet builder)

/--
Route a reachable signed-semantic builder through direct nested inner-span
collection to construct inverse coordinate polynomials.
-/
theorem
    commutators_span_collect
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_jacobi_builder
    hn e
      (TCBuildc.ofReachableBuilder
        packet builder)

end TCTex
end Submission

/-!
# Recursive boundaries after direct nested inner-span collection

Direct inner-span collection closes an exposed nested frontier whenever the
retained outer-right tree is basic and the inner-right tree is smaller.  The
complement naturally separates into two recursive Hall-algorithm boundaries:

* a nonbasic retained outer-right tree must be normalized before it can serve
  as the unchanged outer factor;
* a basic retained outer-right tree with failed inner-span order carries the
  reverse inequality needed for a Jacobi recursion step.

This file packages that classification while leaving the two recursive
recollections explicit.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
Reachable ranked routing, root-swap residuals, and the two recursive
boundaries left after direct nested inner-span collection.
-/
structure
    BJBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    ∀ ι : Type,
      PCRoute.{u}
        (d := d) (n := n) ι
  rootSwapResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              PSRecoll
                (n := n) factor left right hword
  retainedNonbasicResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                ¬frontier.right.IsBasic →
                  TRRecoll
                    (n := n) factor
  failedInnerOrder :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right ≤ frontier.middle →
                    TRRecoll
                      (n := n) factor

namespace
  BJBuild

/--
Classify every complement of the direct inner-span branch into retained-right
normalization or failed-order Jacobi recursion.
-/
noncomputable def
    rankedChildrenWords
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      BJBuild.{u}
        (d := d) (n := n) hn) :
    TCBuildc.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  nestedWordsFallback := by
    intro ι lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
      frontier hcomplement
    by_cases hrightBasic : frontier.right.IsBasic
    · have hfailedOrder : ¬frontier.middle < frontier.right := by
        intro hinnerRightOuterRight
        exact
          hcomplement.elim
            (fun h => h hinnerRightOuterRight)
            (fun h => h hrightBasic)
      exact
        builder.failedInnerOrder lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated frontier hrightBasic
            (le_of_not_gt hfailedOrder)
    · exact
        builder.retainedNonbasicResidual lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated frontier hrightBasic

end
  BJBuild

/--
Recursive-boundary classification after direct nested inner-span collection
constructs product coordinate polynomials.
-/
theorem
    boundary_jacobi_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      BJBuild.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_inner_builder
    hn e
      builder.rankedChildrenWords

/--
Recursive-boundary classification after direct nested inner-span collection
constructs inverse coordinate polynomials.
-/
theorem
    commutators_boundary_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      BJBuild.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_jacobi_builder
    hn e
      builder.rankedChildrenWords

end TCTex
end Submission

/-!
# Strict Jacobi recursion for failed nested inner-span order

When direct inner-span collection fails with a basic retained outer-right
tree, the reverse inequality `right ≤ middle` is available.  In the strict
Hall-oriented subcase

`right < middle < left`

with basic inner children, the exposed nested root is exactly a ranked
expanded-Jacobi decomposition.  Canonical routing flattens its two ordinary
descendants and recollects only strict grandchildren.

This file installs that branch automa and leaves four smaller
recursive boundaries explicit.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
Reachable ranked routing and the recursive boundaries left after installing
the strict basic-right failed-order Jacobi branch.
-/
structure
    FJBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    ∀ ι : Type,
      PCRoute.{u}
        (d := d) (n := n) ι
  rootSwapResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              PSRecoll
                (n := n) factor left right hword
  retainedNonbasicResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                ¬frontier.right.IsBasic →
                  TRRecoll
                    (n := n) factor
  repeatedRightResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right = frontier.middle →
                    TRRecoll
                      (n := n) factor
  leftNonbasicResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    ¬frontier.left.IsBasic →
                      TRRecoll
                        (n := n) factor
  middleNonbasicResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    frontier.left.IsBasic →
                      ¬frontier.middle.IsBasic →
                        TRRecoll
                          (n := n) factor
  failedInnerChildren :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    frontier.left.IsBasic →
                      frontier.middle.IsBasic →
                        ¬frontier.middle < frontier.left →
                          TRRecoll
                            (n := n) factor

namespace
  FJBuild

/--
Install strict basic-right failed-order Jacobi recursion and leave only its
smaller complementary boundaries explicit.
-/
noncomputable def
    rankedChildrenFrontier
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      FJBuild.{u}
        (d := d) (n := n) hn) :
    BJBuild.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  retainedNonbasicResidual := builder.retainedNonbasicResidual
  failedInnerOrder := by
    intro ι lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
      frontier hrightBasic hrightMiddle
    by_cases hrightEqMiddle : frontier.right = frontier.middle
    · exact
        builder.repeatedRightResidual lowerWeight hnonterminal factor
          hfactorWeight hfactorTruncated frontier hrightBasic hrightEqMiddle
    · have hrightLtMiddle : frontier.right < frontier.middle :=
        lt_of_le_of_ne hrightMiddle hrightEqMiddle
      by_cases hleftBasic : frontier.left.IsBasic
      · by_cases hmiddleBasic : frontier.middle.IsBasic
        · by_cases hmiddleLtLeft : frontier.middle < frontier.left
          · let ranked :=
              ERDecomp.nonbasic_commutator_tree
                factor frontier.left frontier.middle frontier.right
                  frontier.tree_eq frontier.outer_nonbasic hrightLtMiddle
                    hmiddleLtLeft hleftBasic hmiddleBasic
            exact
              (builder.routing ι)
                |>.expanded_ranked_decomposition
                  hn
                  (fun s hs hsn =>
                    concrete_forms_associated
                      d n s hs hsn)
                  factor ranked hfactorTruncated
          · exact
              builder.failedInnerChildren lowerWeight
                hnonterminal factor hfactorWeight hfactorTruncated frontier
                  hrightBasic hrightLtMiddle hleftBasic hmiddleBasic
                    hmiddleLtLeft
        · exact
            builder.middleNonbasicResidual lowerWeight hnonterminal factor
              hfactorWeight hfactorTruncated frontier hrightBasic
                hrightLtMiddle hleftBasic hmiddleBasic
      · exact
          builder.leftNonbasicResidual lowerWeight hnonterminal factor
            hfactorWeight hfactorTruncated frontier hrightBasic
              hrightLtMiddle hleftBasic

end
  FJBuild

/--
Strict failed-order Jacobi collection with explicit smaller boundaries
constructs product coordinate polynomials.
-/
theorem
    failed_jacobi_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      FJBuild.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  boundary_jacobi_builder
    hn e
      builder.rankedChildrenFrontier

/--
Strict failed-order Jacobi collection with explicit smaller boundaries
constructs inverse coordinate polynomials.
-/
theorem
    commutators_failed_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      FJBuild.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_boundary_builder
    hn e
      builder.rankedChildrenFrontier

end TCTex
end Submission

/-!
# Recursive nested-word boundaries from normalizer families

A complete signed semantic normalizer family supplies compatibility
implementations of the two explicit recursive boundaries left after direct
nested inner-span collection: nonbasic retained-right normalization and
basic-right failed-order Jacobi recursion.

Both fields remain visible so they can be replaced independently by
structural recursion.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace
  BJBuild

/--
Fill root-swap packets and both remaining recursive boundaries from one
complete normalizer family.
-/
noncomputable def builderNormalizerFamily
    {d n : ℕ}
    {hn : 2 ≤ n}
    (canonical :
      CCBuild.{u}
        (d := d) (n := n) hn)
    (family :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d)) :
    BJBuild.{u}
      (d := d) (n := n) hn where
  packet := canonical.packet
  routing := canonical.routing
  rootSwapResidual :=
    fun _lowerWeight _hnonterminal factor left right hword hfactorWeight
        hfactorTruncated =>
      PSRecoll.ofNormalizerFamily
        hn
        (forms_graded_below d n)
        family factor left right hword hfactorWeight hfactorTruncated
  retainedNonbasicResidual :=
    fun _lowerWeight _hnonterminal factor hfactorWeight hfactorTruncated
        _frontier _hrightNonbasic =>
      TRRecoll.ofNormalizerFamily
        hn
        (forms_graded_below d n)
        family factor hfactorWeight hfactorTruncated
  failedInnerOrder :=
    fun _lowerWeight _hnonterminal factor hfactorWeight hfactorTruncated
        _frontier _hrightBasic _hrightMiddle =>
      TRRecoll.ofNormalizerFamily
        hn
        (forms_graded_below d n)
        family factor hfactorWeight hfactorTruncated

/--
The reachable signed-semantic builder supplies the schedule and normalizer
family for compatibility recursive-boundary collection.
-/
noncomputable def ofReachableBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    BJBuild.{u}
      (d := d) (n := n) hn :=
  let family :=
    builder.supportedNormalizerFamily hn
      (concreteCommutatorsWeight.{u} d)
      (forms_graded_below d n)
  builderNormalizerFamily
    (CCBuild.ofReachableBuilder
      packet builder)
    family

end
  BJBuild

/--
Route a reachable signed-semantic builder through classified nested-word
recursive boundaries to construct product coordinate polynomials.
-/
theorem
    boundary_frontier_collect
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  boundary_jacobi_builder
    hn e
      (BJBuild.ofReachableBuilder
        packet builder)

/--
Route a reachable signed-semantic builder through classified nested-word
recursive boundaries to construct inverse coordinate polynomials.
-/
theorem
    commutators_boundary_collect
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_boundary_builder
    hn e
      (BJBuild.ofReachableBuilder
        packet builder)

end TCTex
end Submission

/-!
# Strict failed-order Jacobi collection from normalizer families

A complete signed semantic normalizer family supplies compatibility
implementations of the recursive boundaries left after automatic strict
failed-order Jacobi collection.

This adapter keeps the finer route immediately usable while each remaining
field is replaced independently by structural recursion.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace
  FJBuild

/--
Fill root-swap packets and the remaining failed-order boundaries from one
complete normalizer family.
-/
noncomputable def builderNormalizerFamily
    {d n : ℕ}
    {hn : 2 ≤ n}
    (canonical :
      CCBuild.{u}
        (d := d) (n := n) hn)
    (family :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d)) :
    FJBuild.{u}
      (d := d) (n := n) hn where
  packet := canonical.packet
  routing := canonical.routing
  rootSwapResidual :=
    fun _lowerWeight _hnonterminal factor left right hword hfactorWeight
        hfactorTruncated =>
      PSRecoll.ofNormalizerFamily
        hn
        (forms_graded_below d n)
        family factor left right hword hfactorWeight hfactorTruncated
  retainedNonbasicResidual :=
    fun _lowerWeight _hnonterminal factor hfactorWeight hfactorTruncated
        _frontier _hrightNonbasic =>
      TRRecoll.ofNormalizerFamily
        hn
        (forms_graded_below d n)
        family factor hfactorWeight hfactorTruncated
  repeatedRightResidual :=
    fun _lowerWeight _hnonterminal factor hfactorWeight hfactorTruncated
        _frontier _hrightBasic _hrightEqMiddle =>
      TRRecoll.ofNormalizerFamily
        hn
        (forms_graded_below d n)
        family factor hfactorWeight hfactorTruncated
  leftNonbasicResidual :=
    fun _lowerWeight _hnonterminal factor hfactorWeight hfactorTruncated
        _frontier _hrightBasic _hrightLtMiddle _hleftNonbasic =>
      TRRecoll.ofNormalizerFamily
        hn
        (forms_graded_below d n)
        family factor hfactorWeight hfactorTruncated
  middleNonbasicResidual :=
    fun _lowerWeight _hnonterminal factor hfactorWeight hfactorTruncated
        _frontier _hrightBasic _hrightLtMiddle _hleftBasic
          _hmiddleNonbasic =>
      TRRecoll.ofNormalizerFamily
        hn
        (forms_graded_below d n)
        family factor hfactorWeight hfactorTruncated
  failedInnerChildren :=
    fun _lowerWeight _hnonterminal factor hfactorWeight hfactorTruncated
        _frontier _hrightBasic _hrightLtMiddle _hleftBasic _hmiddleBasic
          _hfailedInnerChildrenOrder =>
      TRRecoll.ofNormalizerFamily
        hn
        (forms_graded_below d n)
        family factor hfactorWeight hfactorTruncated

/--
The reachable signed-semantic builder supplies the schedule and normalizer
family for compatibility strict failed-order collection.
-/
noncomputable def ofReachableBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    FJBuild.{u}
      (d := d) (n := n) hn :=
  let family :=
    builder.supportedNormalizerFamily hn
      (concreteCommutatorsWeight.{u} d)
      (forms_graded_below d n)
  builderNormalizerFamily
    (CCBuild.ofReachableBuilder
      packet builder)
    family

end
  FJBuild

/--
Route a reachable signed-semantic builder through strict failed-order Jacobi
collection to construct product coordinate polynomials.
-/
theorem
    jacobi_frontier_collect
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  failed_jacobi_builder
    hn e
      (FJBuild.ofReachableBuilder
        packet builder)

/--
Route a reachable signed-semantic builder through strict failed-order Jacobi
collection to construct inverse coordinate polynomials.
-/
theorem
    commutators_jacobi_collect
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_failed_builder
    hn e
      (FJBuild.ofReachableBuilder
        packet builder)

end TCTex
end Submission

/-!
# Structural recursion for nonbasic retained-right polynomial frontiers

An exposed nested frontier `[[left, middle], right]` cannot use direct
inner-span collection when `right` is nonbasic.  Swapping the root once gives
`[right, [left, middle]]`.  Exposing `right = [rightLeft, rightMiddle]` and
applying Jacobi produces two descendants whose retained outer-right trees are
the proper subtrees `rightMiddle` and `rightLeft`.

This file packages that structural step.  The old opaque retained-right
residual callback is replaced by recollections of those two descendants.
Their strict subtree inequalities are recorded for the later well-founded
scheduler.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open CEWord

universe u

/-- Swap an exposed nested frontier so that its retained right tree is on the left. -/
noncomputable def retainedSwapFactor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (frontier :
      NWCase
        factor) :
    SPFactor
      (concreteBasicCommutators.{u} d) ι :=
  expandedSwapFactor factor
    (.commutator frontier.decomposition.left frontier.decomposition.middle)
    frontier.decomposition.right frontier.decomposition.word_eq

@[simp]
theorem word_swap_factor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (frontier :
      NWCase
        factor) :
    (retainedSwapFactor factor frontier).word.weight
        HEAddres.weight =
      factor.word.weight HEAddres.weight := by
  exact
    expanded_root_factor factor
      (.commutator frontier.decomposition.left frontier.decomposition.middle)
      frontier.decomposition.right frontier.decomposition.word_eq

/-- The symbolic words exposed by a nested frontier have the advertised trees. -/
theorem trees_frontier
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (frontier :
      NWCase
        factor) :
    tree frontier.decomposition.left = frontier.left ∧
      tree frontier.decomposition.middle = frontier.middle ∧
        tree frontier.decomposition.right = frontier.right := by
  have htree := congrArg tree frontier.decomposition.word_eq
  simp only [tree_commutator] at htree
  have hroot := htree.symm.trans frontier.tree_eq
  injection hroot with hinner hright
  injection hinner with hleft hmiddle
  exact ⟨hleft, hmiddle, hright⟩

@[simp]
theorem tree_root_swap
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (frontier :
      NWCase
        factor) :
    tree (retainedSwapFactor factor frontier).word =
      .commutator frontier.right (.commutator frontier.left frontier.middle) := by
  rcases trees_frontier factor frontier with
    ⟨hleft, hmiddle, hright⟩
  simp only [retainedSwapFactor,
    tree_expanded_swap, tree_commutator, hleft, hmiddle, hright]

/--
The reversed retained-right frontier together with the exposed children of
its nonbasic left root.
-/
structure
    RCDecomp
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (frontier :
      NWCase
        factor) where
  left :
    HallTree (FreeGenerator.{u} d)
  middle :
    HallTree (FreeGenerator.{u} d)
  right_eq : frontier.right = .commutator left middle
  decomposition :
    ExpandedJacobiDecomposition (retainedSwapFactor factor frontier).word
  left_tree : tree decomposition.left = left
  middle_tree : tree decomposition.middle = middle
  right_tree :
    tree decomposition.right = .commutator frontier.left frontier.middle

namespace
  RCDecomp

/-- Expose the two children of a nonbasic retained-right tree after one root swap. -/
noncomputable def ofNonbasic
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (frontier :
      NWCase
        factor)
    (hrightNonbasic : ¬frontier.right.IsBasic) :
    RCDecomp
      factor frontier := by
  cases hright : frontier.right with
  | atom generator =>
      exfalso
      apply hrightNonbasic
      rw [hright]
      exact HallTree.isBasic_atom generator
  | commutator left middle =>
      have htree :
          tree (retainedSwapFactor factor frontier).word =
            .commutator (.commutator left middle)
              (.commutator frontier.left frontier.middle) := by
        rw [tree_root_swap, hright]
      have houterNonbasic :
          ¬(HallTree.commutator (.commutator left middle)
              (.commutator frontier.left frontier.middle)).IsBasic := by
        intro hbasic
        apply hrightNonbasic
        rw [hright]
        exact (HallTree.isBasic_commutator _ _).mp hbasic |>.1
      let decomposition :=
        expandedTreeNonbasic
          (retainedSwapFactor factor frontier).word left middle
            (.commutator frontier.left frontier.middle) htree houterNonbasic
      have hroot :
          HallTree.commutator
              (.commutator (tree decomposition.left)
                (tree decomposition.middle))
              (tree decomposition.right) =
            .commutator (.commutator left middle)
              (.commutator frontier.left frontier.middle) :=
        decomposition.tree_eq.symm.trans htree
      injection hroot with hinner hrightTree
      injection hinner with hleftTree hmiddleTree
      exact
        {
          left := left
          middle := middle
          right_eq := hright
          decomposition := decomposition
          left_tree := hleftTree
          middle_tree := hmiddleTree
          right_tree := hrightTree
        }

/-- The first retained-right descendant ends in the second proper subtree. -/
@[simp]
theorem tree_first_factor
    {d : ℕ}
    {ι : Type}
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    {frontier :
      NWCase
        factor}
    (retained :
      RCDecomp
        factor frontier) :
    tree
        (expandedJacobiFactor
          (retainedSwapFactor factor frontier)
          retained.decomposition).word =
      .commutator
        (.commutator retained.left
          (.commutator frontier.left frontier.middle))
        retained.middle := by
  rw [tree_expanded_factor]
  simp only [HallTree.jacobiFirstDescendant, retained.left_tree,
    retained.middle_tree, retained.right_tree]

/-- The second retained-right descendant ends in the first proper subtree. -/
@[simp]
theorem tree_second_factor
    {d : ℕ}
    {ι : Type}
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    {frontier :
      NWCase
        factor}
    (retained :
      RCDecomp
        factor frontier) :
    tree
        (expandedJacobiSecond
          (retainedSwapFactor factor frontier)
          retained.decomposition).word =
      .commutator
        (.commutator retained.middle
          (.commutator frontier.left frontier.middle))
        retained.left := by
  rw [tree_expanded_jacobi]
  simp only [HallTree.jacobiSecondDescendant, retained.left_tree,
    retained.middle_tree, retained.right_tree]

/-- The first child exposed from the retained right root is strictly smaller. -/
theorem left_lt_right
    {d : ℕ}
    {ι : Type}
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    {frontier :
      NWCase
        factor}
    (retained :
      RCDecomp
        factor frontier) :
    retained.left < frontier.right := by
  rw [retained.right_eq]
  exact HallTree.lt_commutator_left retained.left retained.middle

/-- The second child exposed from the retained right root is strictly smaller. -/
theorem middle_lt_right
    {d : ℕ}
    {ι : Type}
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    {frontier :
      NWCase
        factor}
    (retained :
      RCDecomp
        factor frontier) :
    retained.middle < frontier.right := by
  rw [retained.right_eq]
  exact HallTree.lt_commutator_right retained.left retained.middle

end
  RCDecomp

open
  RCDecomp

/--
Reachable ranked routing and the recursive boundaries left after replacing a
nonbasic retained right root by its two proper-subtree Jacobi descendants.
-/
structure
    JCBuilda
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    ∀ ι : Type,
      PCRoute.{u}
        (d := d) (n := n) ι
  rootSwapResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              PSRecoll
                (n := n) factor left right hword
  retainedFirstResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ (frontier :
                NWCase
                  factor)
                (hrightNonbasic : ¬frontier.right.IsBasic),
                let retained :=
                  ofNonbasic factor frontier hrightNonbasic
                TRRecoll
                  (n := n)
                  (expandedJacobiFactor
                    (retainedSwapFactor factor frontier)
                    retained.decomposition)
  retainedSecondResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ (frontier :
                NWCase
                  factor)
                (hrightNonbasic : ¬frontier.right.IsBasic),
                let retained :=
                  ofNonbasic factor frontier hrightNonbasic
                TRRecoll
                  (n := n)
                  (expandedJacobiSecond
                    (retainedSwapFactor factor frontier)
                    retained.decomposition)
  repeatedRightResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right = frontier.middle →
                    TRRecoll
                      (n := n) factor
  leftNonbasicResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    ¬frontier.left.IsBasic →
                      TRRecoll
                        (n := n) factor
  middleNonbasicResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    frontier.left.IsBasic →
                      ¬frontier.middle.IsBasic →
                        TRRecoll
                          (n := n) factor
  failedInnerChildren :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    frontier.left.IsBasic →
                      frontier.middle.IsBasic →
                        ¬frontier.middle < frontier.left →
                          TRRecoll
                            (n := n) factor

namespace
  JCBuilda

open
  TRRecoll

/--
Swap one nonbasic retained-right frontier, recurse on its two proper-subtree
Jacobi descendants, and reconstruct the original residual.
-/
noncomputable def retainedNonbasicResidual
    {d n : ℕ}
    {hn : 2 ≤ n}
    {ι : Type}
    (builder :
      JCBuilda.{u}
        (d := d) (n := n) hn)
    (lowerWeight : ℕ)
    (hnonterminal : ¬n ≤ 2 * lowerWeight)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (frontier :
      NWCase
        factor)
    (hrightNonbasic : ¬frontier.right.IsBasic) :
    TRRecoll
      (n := n) factor :=
  let retained :=
    ofNonbasic factor frontier hrightNonbasic
  let reversed := retainedSwapFactor factor frontier
  let reversedResidual :=
    expanded_normalizer_family hn builder.packet
      (builder.routing ι).normalizerFamily reversed retained.decomposition
      (by simpa only [reversed, word_swap_factor] using
        hfactorWeight)
      (by
        simpa only [reversed, word_swap_factor] using
          hfactorTruncated)
      (builder.retainedFirstResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated frontier hrightNonbasic)
      (builder.retainedSecondResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated frontier hrightNonbasic)
  expanded_swap factor
    (.commutator frontier.decomposition.left frontier.decomposition.middle)
    frontier.decomposition.right frontier.decomposition.word_eq
      reversedResidual
      (builder.rootSwapResidual lowerWeight hnonterminal factor
        (.commutator frontier.decomposition.left frontier.decomposition.middle)
        frontier.decomposition.right frontier.decomposition.word_eq
          hfactorWeight hfactorTruncated)

/-- Compile structural retained-right recursion into the strict failed-order builder. -/
noncomputable def
    expandedWordsFailed
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      JCBuilda.{u}
        (d := d) (n := n) hn) :
    FJBuild.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  retainedNonbasicResidual :=
    fun lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
        frontier hrightNonbasic =>
      builder.retainedNonbasicResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated frontier hrightNonbasic
  repeatedRightResidual := builder.repeatedRightResidual
  leftNonbasicResidual := builder.leftNonbasicResidual
  middleNonbasicResidual := builder.middleNonbasicResidual
  failedInnerChildren := builder.failedInnerChildren

end
  JCBuilda

/--
Structural retained-right Jacobi recursion with explicit smaller boundaries
constructs product coordinate polynomials.
-/
theorem
    commutators_collect_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      JCBuilda.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  failed_jacobi_builder
    hn e builder.expandedWordsFailed

/--
Structural retained-right Jacobi recursion with explicit smaller boundaries
constructs inverse coordinate polynomials.
-/
theorem
    commutators_frontier_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      JCBuilda.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_failed_builder
    hn e builder.expandedWordsFailed

end TCTex
end Submission

/-!
# Certified descendants for retained-right polynomial recursion

The retained-right Jacobi step produces two recursive factor residuals.  This
file packages each one with the proper-subtree inequality proved by the
structural decomposition:

* the first descendant retains the second child of the old right root;
* the second descendant retains the first child of the old right root.

Both children are strictly smaller than the old retained right tree.  A
single callback over certified descendants therefore replaces the two
unstructured recursive callbacks.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open CEWord
open
  RCDecomp

universe u

/-- One factor residual generated with a strictly smaller retained right tree. -/
structure
    TDCase
    {d : ℕ}
    {ι : Type}
    (parent :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (frontier :
      NWCase
        parent) where
  factor :
    SPFactor
      (concreteBasicCommutators.{u} d) ι
  left :
    HallTree (FreeGenerator.{u} d)
  retainedRight :
    HallTree (FreeGenerator.{u} d)
  tree_eq :
    tree factor.word = .commutator left retainedRight
  retainedRight_lt : retainedRight < frontier.right

namespace
  TDCase

/-- The first reversed Jacobi descendant retains the second proper subtree. -/
noncomputable def first
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (frontier :
      NWCase
        factor)
    (hrightNonbasic : ¬frontier.right.IsBasic) :
    TDCase
      factor frontier :=
  let retained := ofNonbasic factor frontier hrightNonbasic
  {
    factor :=
      expandedJacobiFactor
        (retainedSwapFactor factor frontier) retained.decomposition
    left :=
      .commutator retained.left (.commutator frontier.left frontier.middle)
    retainedRight := retained.middle
    tree_eq := retained.tree_first_factor
    retainedRight_lt := retained.middle_lt_right
  }

/-- The second reversed Jacobi descendant retains the first proper subtree. -/
noncomputable def second
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (frontier :
      NWCase
        factor)
    (hrightNonbasic : ¬frontier.right.IsBasic) :
    TDCase
      factor frontier :=
  let retained := ofNonbasic factor frontier hrightNonbasic
  {
    factor :=
      expandedJacobiSecond
        (retainedSwapFactor factor frontier) retained.decomposition
    left :=
      .commutator retained.middle (.commutator frontier.left frontier.middle)
    retainedRight := retained.left
    tree_eq := retained.tree_second_factor
    retainedRight_lt := retained.left_lt_right
  }

end
  TDCase

/--
Reachable ranked routing and the recursive boundaries left after retained
right Jacobi recursion has been reduced to certified proper-subtree
descendants.
-/
structure
    DJBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    ∀ ι : Type,
      PCRoute.{u}
        (d := d) (n := n) ι
  rootSwapResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              PSRecoll
                (n := n) factor left right hword
  retainedDescendantResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ (frontier :
                NWCase
                  factor)
                (_hrightNonbasic : ¬frontier.right.IsBasic)
                (descendant :
                  TDCase
                    factor frontier),
                  TRRecoll
                    (n := n) descendant.factor
  repeatedRightResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right = frontier.middle →
                    TRRecoll
                      (n := n) factor
  leftNonbasicResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    ¬frontier.left.IsBasic →
                      TRRecoll
                        (n := n) factor
  middleNonbasicResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    frontier.left.IsBasic →
                      ¬frontier.middle.IsBasic →
                        TRRecoll
                          (n := n) factor
  failedInnerChildren :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    frontier.left.IsBasic →
                      frontier.middle.IsBasic →
                        ¬frontier.middle < frontier.left →
                          TRRecoll
                            (n := n) factor

namespace
  DJBuild

open
  TDCase

/-- Compile the two retained-right descendant slots from one certified callback. -/
noncomputable def frontierCollectionBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      DJBuild.{u}
        (d := d) (n := n) hn) :
    JCBuilda.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  retainedFirstResidual :=
    fun lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
        frontier hrightNonbasic =>
      builder.retainedDescendantResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated frontier hrightNonbasic
          (first factor frontier hrightNonbasic)
  retainedSecondResidual :=
    fun lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
        frontier hrightNonbasic =>
      builder.retainedDescendantResidual lowerWeight hnonterminal factor
        hfactorWeight hfactorTruncated frontier hrightNonbasic
          (second factor frontier hrightNonbasic)
  repeatedRightResidual := builder.repeatedRightResidual
  leftNonbasicResidual := builder.leftNonbasicResidual
  middleNonbasicResidual := builder.middleNonbasicResidual
  failedInnerChildren := builder.failedInnerChildren

end
  DJBuild

/--
Certified retained-right descendants with explicit smaller boundaries
construct product coordinate polynomials.
-/
theorem
    descendants_jacobi_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      DJBuild.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_collect_builder
    hn e builder.frontierCollectionBuilder

/--
Certified retained-right descendants with explicit smaller boundaries
construct inverse coordinate polynomials.
-/
theorem
    commutators_descendants_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      DJBuild.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_frontier_builder
    hn e builder.frontierCollectionBuilder

end TCTex
end Submission

/-!
# Structural cases for repeated-right polynomial recursion

The repeated-right frontier `[[left, middle], middle]` is the one place where
root Jacobi recursion does not move: its first ordinary descendant is the
parent again and its second descendant is a self-commutator.

When `left` and `middle` are basic and `middle < left`, the exposed nonbasic
inner bracket forces a more useful obstruction.  The basic tree `left` must
itself be a commutator `[leftLeft, leftRight]`, and Hall admissibility fails
exactly far enough to give

`middle < leftRight`.

This file packages that structural case and narrows the repeated-right
boundary to contextual recursion on the exposed nested left tree.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
The genuinely recursive repeated-right case: a basic left root has exposed
basic children, and the repeated middle tree lies strictly below its right
child.
-/
structure
    TNCase
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (frontier :
      NWCase
        factor) where
  leftLeft :
    HallTree (FreeGenerator.{u} d)
  leftRight :
    HallTree (FreeGenerator.{u} d)
  left_eq :
    frontier.left = .commutator leftLeft leftRight
  left_isBasic :
    frontier.left.IsBasic
  middle_isBasic :
    frontier.middle.IsBasic
  middle_lt_left :
    frontier.middle < frontier.left
  left_basic :
    leftLeft.IsBasic
  left_right_basic :
    leftRight.IsBasic
  left_right :
    leftRight < leftLeft
  middle_left_right :
    frontier.middle < leftRight

namespace
  TNCase

/--
Expose the failed Hall-admissibility witness inside an ordered basic-left
repeated-right frontier.
-/
noncomputable def ofBasicOrdered
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (frontier :
      NWCase
        factor)
    (hrightBasic : frontier.right.IsBasic)
    (hrightEqMiddle : frontier.right = frontier.middle)
    (hleftBasic : frontier.left.IsBasic)
    (hmiddleLtLeft : frontier.middle < frontier.left) :
    TNCase
      factor frontier := by
  have hmiddleBasic : frontier.middle.IsBasic := by
    rw [← hrightEqMiddle]
    exact hrightBasic
  cases hleft : frontier.left with
  | atom generator =>
      have hmiddleLtAtom :
          frontier.middle < HallTree.atom generator := by
        rw [← hleft]
        exact hmiddleLtLeft
      have hinnerBasic :
          (HallTree.commutator (.atom generator) frontier.middle).IsBasic :=
        HallTree.basic_commutator_admissible
          (HallTree.isBasic_atom generator) hmiddleBasic hmiddleLtAtom trivial
      exfalso
      apply frontier.inner_nonbasic
      simpa only [hleft] using hinnerBasic
  | commutator leftLeft leftRight =>
      have hleftBasic' :
          (HallTree.commutator leftLeft leftRight).IsBasic := by
        rw [← hleft]
        exact hleftBasic
      have hmiddleLtLeft' :
          frontier.middle < HallTree.commutator leftLeft leftRight := by
        rw [← hleft]
        exact hmiddleLtLeft
      have hleftData :=
        (HallTree.isBasic_commutator leftLeft leftRight).mp hleftBasic'
      have hnotLeftRightLeMiddle : ¬leftRight ≤ frontier.middle := by
        intro hleftRightLeMiddle
        have hinnerBasic :
            (HallTree.commutator
              (.commutator leftLeft leftRight) frontier.middle).IsBasic :=
          HallTree.basic_commutator_admissible hleftBasic' hmiddleBasic
            hmiddleLtLeft' hleftRightLeMiddle
        apply frontier.inner_nonbasic
        simpa only [hleft] using hinnerBasic
      exact
        {
          leftLeft := leftLeft
          leftRight := leftRight
          left_eq := hleft
          left_isBasic := hleftBasic
          middle_isBasic := hmiddleBasic
          middle_lt_left := hmiddleLtLeft
          left_basic := hleftData.1
          left_right_basic := hleftData.2.1
          left_right := hleftData.2.2.1
          middle_left_right := lt_of_not_ge hnotLeftRightLeMiddle
        }

end
  TNCase

/--
Reachable ranked routing and the recursive boundaries left after exposing the
structural obstruction inside repeated-right frontiers.
-/
structure
    TCBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    ∀ ι : Type,
      PCRoute.{u}
        (d := d) (n := n) ι
  rootSwapResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι)
          (left right :
            CWord
              (HEAddres (concreteBasicCommutators.{u} d)))
          (hword : factor.word = .commutator left right),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              PSRecoll
                (n := n) factor left right hword
  retainedDescendantResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ (frontier :
                NWCase
                  factor)
                (_hrightNonbasic : ¬frontier.right.IsBasic)
                (descendant :
                  TDCase
                    factor frontier),
                  TRRecoll
                    (n := n) descendant.factor
  repeatedNonbasicResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right = frontier.middle →
                    ¬frontier.left.IsBasic →
                      TRRecoll
                        (n := n) factor
  repeatedFailedInner :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right = frontier.middle →
                    frontier.left.IsBasic →
                      ¬frontier.middle < frontier.left →
                        TRRecoll
                          (n := n) factor
  repeatedRightNested :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ (frontier :
                NWCase
                  factor)
                (_hrightBasic : frontier.right.IsBasic)
                (_hrightEqMiddle : frontier.right = frontier.middle)
                (_nested :
                  TNCase
                    factor frontier),
                  TRRecoll
                    (n := n) factor
  leftNonbasicResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    ¬frontier.left.IsBasic →
                      TRRecoll
                        (n := n) factor
  middleNonbasicResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    frontier.left.IsBasic →
                      ¬frontier.middle.IsBasic →
                        TRRecoll
                          (n := n) factor
  failedInnerChildren :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ∀ frontier :
                NWCase
                  factor,
                frontier.right.IsBasic →
                  frontier.right < frontier.middle →
                    frontier.left.IsBasic →
                      frontier.middle.IsBasic →
                        ¬frontier.middle < frontier.left →
                          TRRecoll
                            (n := n) factor

namespace
  TCBuild

open
  TNCase

/-- Compile repeated-right structural classification into the previous builder. -/
noncomputable def descendantsJacobiBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      TCBuild.{u}
        (d := d) (n := n) hn) :
    DJBuild.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  retainedDescendantResidual := builder.retainedDescendantResidual
  repeatedRightResidual := by
    intro ι lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
      frontier hrightBasic hrightEqMiddle
    by_cases hleftBasic : frontier.left.IsBasic
    · by_cases hmiddleLtLeft : frontier.middle < frontier.left
      · exact
          builder.repeatedRightNested lowerWeight hnonterminal
            factor hfactorWeight hfactorTruncated frontier hrightBasic
              hrightEqMiddle
                (ofBasicOrdered factor frontier hrightBasic hrightEqMiddle
                  hleftBasic hmiddleLtLeft)
      · exact
          builder.repeatedFailedInner lowerWeight
            hnonterminal factor hfactorWeight hfactorTruncated frontier
              hrightBasic hrightEqMiddle hleftBasic hmiddleLtLeft
    · exact
        builder.repeatedNonbasicResidual lowerWeight hnonterminal
          factor hfactorWeight hfactorTruncated frontier hrightBasic
            hrightEqMiddle hleftBasic
  leftNonbasicResidual := builder.leftNonbasicResidual
  middleNonbasicResidual := builder.middleNonbasicResidual
  failedInnerChildren := builder.failedInnerChildren

end
  TCBuild

/--
Repeated-right structural cases with explicit contextual recursion boundaries
construct product coordinate polynomials.
-/
theorem
    cases_jacobi_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      TCBuild.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  descendants_jacobi_builder
    hn e builder.descendantsJacobiBuilder

/--
Repeated-right structural cases with explicit contextual recursion boundaries
construct inverse coordinate polynomials.
-/
theorem
    commutators_cases_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      TCBuild.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_descendants_builder
    hn e builder.descendantsJacobiBuilder

end TCTex
end Submission

/-!
# Signed collection from retained recipe traces and ranked outer factories

The retained recipe-coefficient law supplies the correction packet at every
support stratum. Support-local Hall-ranked residual recursion supplies the
remaining exact-weight factor tail from full-weight outer residual factories
and branch classifications.

This file compiles those two inputs directly to the global signed semantic
normalizer. It is intentionally not imported by the existing collection proof.
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
The remaining concrete inputs after retained recipe packets and support-local
ranked recursion have been compiled into the signed collector.
-/
structure
    PCBuild
    {d n : ℕ} where
  outerFactory :
    ∀ ι : Type,
      TRFtrya
        (d := d) (n := n) ι
  cases :
    ∀ {ι : Type}
      (lowerWeight : ℕ)
      (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι)
      (rankDefect : ℕ),
      factor.word.weight HEAddres.weight = lowerWeight →
        factor.word.weight HEAddres.weight < n →
          RankedBranchCase
            (n := n) factor rankDefect

namespace
  PCBuild

/-- Compile retained recipe coefficients to a correction packet at every stratum. -/
noncomputable def supportedFactorySchedule
    {d n : ℕ}
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n) :
    SFSched
      (n := n) (concreteBasicCommutators.{u} d) where
  factory lowerWeight :=
    CDBuild.retainedRecipeFactory
      (lowerWeight := lowerWeight) hrecipes

/--
Construct the global signed semantic normalizer by support recursion. Recursive
uses occur only at strictly larger support weights, including the normalizers
used inside support-local Hall-ranked residual collection.
-/
noncomputable def supportedCoordinateNormalizer
    {d n : ℕ}
    (hn : 2 ≤ n)
    (builder :
      PCBuild.{u}
        (d := d) (n := n))
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowerWeight : ℕ) :
    TSNormal
      (n := n) (lowerWeight := lowerWeight)
        (concreteBasicCommutators.{u} d) :=
  if hterminal : n ≤ 2 * lowerWeight then
    TSNormal.of_highWeight
      hn (concreteBasicCommutators.{u} d)
        (fun r hr hrn =>
          concrete_forms_associated d n r hr
            hrn)
        hterminal
  else
    TSNormal.ofInsertionKernel
      { insert := by
          intro ι coordinates factor hcoordinates hfactorSupported
            hfactorTruncated
          let hH :=
            fun r hr hrn =>
              concrete_forms_associated d n r hr
                hrn
          let nextNormalizer :=
            builder.supportedCoordinateNormalizer
              hn hrecipes (lowerWeight + 1)
          by_cases hfactorStrict :
              lowerWeight <
                factor.word.weight HEAddres.weight
          · exact
              nextNormalizer.insertion_word_weight coordinates
                factor hcoordinates hfactorStrict hfactorTruncated
          · have hfactorWeight :
                factor.word.weight HEAddres.weight = lowerWeight := by
              omega
            let schedule :=
              supportedFactorySchedule
                hrecipes
            let normalizerAbove :=
              fun strongerWeight
                  (_hstronger : lowerWeight < strongerWeight) =>
                builder.supportedCoordinateNormalizer
                  hn hrecipes strongerWeight
            let routing :=
              PFRoute.factory_above_outer
                schedule normalizerAbove (builder.outerFactory ι)
            let packetFactory := schedule.factory lowerWeight
            let sharp :
                TSNormala
                  (n := n) (lowerWeight := lowerWeight)
                    (concreteBasicCommutators.{u} d) :=
              TSNormala.ofNormalizerAbove
                normalizerAbove
            let factorTail :=
              routing.expansion_exact_cases hn hH
                (builder.cases lowerWeight) factor 0 hfactorWeight
                  hfactorTruncated
            let merge :=
              (packetFactory
                |>.coord_sharp_normalizer
                  hn (concreteBasicCommutators.{u} d) hH sharp coordinates
                    factor)
                |>.mergeResidualExpansion hfactorWeight hfactorTruncated
            let block :=
              merge.activeBlockResolution factorTail hcoordinates
                hfactorWeight
            let tail :=
              (packetFactory
                |>.supported_route_normalizer
                  sharp coordinates factor hfactorWeight)
                |>.higherTailResolution hfactorWeight hfactorTruncated
            exact
              (TPResolu.active_block_tail
                hcoordinates hfactorWeight hfactorTruncated block tail)
                |>.exists_insertion nextNormalizer hfactorWeight
                  hfactorTruncated }
termination_by n - lowerWeight
decreasing_by
  all_goals
    have hlowerWeightCutoff : lowerWeight < n := by
      omega
    omega

end
  PCBuild

/--
Retained recipe traces and support-local ranked outer residual data construct
the canonical product recollection polynomials.
-/
theorem
    coeff_collect_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      PCBuild.{u}
        (d := d) (n := n))
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  signed_semantic_normalizer
    (concreteBasicCommutators.{u} d) e
      (builder.supportedCoordinateNormalizer hn hrecipes 1)

/--
Retained recipe traces and support-local ranked outer residual data construct
the canonical inverse recollection polynomials.
-/
theorem
    poly_collect_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      PCBuild.{u}
        (d := d) (n := n))
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  collected_data_normalizer
    (concreteBasicCommutators.{u} d) e
      (builder.supportedCoordinateNormalizer hn hrecipes 1)

end TCTex
end Submission

/-!
# Signed retained-trace collection with structural ranked descendants

Retained recipe coefficients supply the active correction packet. An
arbitrary active-block factor is classified once at rank zero. Its recursive
children are certified as two-basic-child tasks and then recollected by the
support-local structural Hall-ranked scheduler.

This narrows the signed retained-trace boundary from classifiers for every
ranked descendant to one root classifier, one retained-right certificate, and
the two semantic residuals exposed by Jacobi orientation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open CEWord
open
  CCThree
open
  CPSplita

/--
The signed structural inputs remaining after retained recipe packets and
support-local two-basic-child scheduling have been compiled.
-/
structure
    TBBuild
    {d n : ℕ} where
  outerFactory :
    ∀ ι : Type,
      TRFtrya
        (d := d) (n := n) ι
  rootCase :
    ∀ {ι : Type}
      (lowerWeight : ℕ)
      (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι),
      factor.word.weight HEAddres.weight = lowerWeight →
        factor.word.weight HEAddres.weight < n →
          RankedBranchCase
            (n := n) factor 0
  root_case_tree :
    ∀ {ι : Type}
      (lowerWeight : ℕ)
      (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι)
      (hfactorWeight :
        factor.word.weight HEAddres.weight = lowerWeight)
      (hfactorTruncated :
        factor.word.weight HEAddres.weight < n)
      (innerCase :
        TruncatedRankedCase
          (n := n) factor 0),
      rootCase lowerWeight factor hfactorWeight hfactorTruncated =
          .innerReductionOuter innerCase →
        tree innerCase.rightWord = innerCase.unchanged
  valueResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ)
      (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι)
      (ranked :
        ERDecomp
          factor),
      factor.word.weight HEAddres.weight = lowerWeight →
        factor.word.weight HEAddres.weight < n →
          TRRecolla
            (n := n) factor ranked.decomposition
  swapValueInverse :
    ∀ {ι : Type}
      (lowerWeight : ℕ)
      (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι)
      (left right : HallTree (FreeGenerator.{u} d))
      (hleftBasic : left.IsBasic)
      (hrightBasic : right.IsBasic)
      (htree : tree factor.word = .commutator left right),
      factor.word.weight HEAddres.weight = lowerWeight →
        factor.word.weight HEAddres.weight < n →
          TVRecoll
            (n := n) factor left right hleftBasic hrightBasic htree

namespace
  TBBuild

/-- Compile retained recipe coefficients to correction packets at every stratum. -/
noncomputable def supportedFactorySchedule
    {d n : ℕ}
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n) :
    SFSched
      (n := n) (concreteBasicCommutators.{u} d) where
  factory lowerWeight :=
    CDBuild.retainedRecipeFactory
      (lowerWeight := lowerWeight) hrecipes

/--
Construct the global signed normalizer by support recursion. At one active
stratum, recursive Hall-ranked children are handled structurally.
-/
noncomputable def supportedCoordinateNormalizer
    {d n : ℕ}
    (hn : 2 ≤ n)
    (builder :
      TBBuild.{u}
        (d := d) (n := n))
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (lowerWeight : ℕ) :
    TSNormal
      (n := n) (lowerWeight := lowerWeight)
        (concreteBasicCommutators.{u} d) :=
  if hterminal : n ≤ 2 * lowerWeight then
    TSNormal.of_highWeight
      hn (concreteBasicCommutators.{u} d)
        (fun r hr hrn =>
          concrete_forms_associated d n r hr
            hrn)
        hterminal
  else
    TSNormal.ofInsertionKernel
      { insert := by
          intro ι coordinates factor hcoordinates hfactorSupported
            hfactorTruncated
          let hH :=
            fun r hr hrn =>
              concrete_forms_associated d n r hr
                hrn
          let nextNormalizer :=
            builder.supportedCoordinateNormalizer
              hn hrecipes (lowerWeight + 1)
          by_cases hfactorStrict :
              lowerWeight <
                factor.word.weight HEAddres.weight
          · exact
              nextNormalizer.insertion_word_weight coordinates
                factor hcoordinates hfactorStrict hfactorTruncated
          · have hfactorWeight :
                factor.word.weight HEAddres.weight = lowerWeight := by
              omega
            let schedule :=
              supportedFactorySchedule
                hrecipes
            let normalizerAbove :=
              fun strongerWeight
                  (_hstronger : lowerWeight < strongerWeight) =>
                builder.supportedCoordinateNormalizer
                  hn hrecipes strongerWeight
            let outerRouting :=
              PFRoute.factory_above_outer
                schedule normalizerAbove (builder.outerFactory ι)
            let routing :
                TCRoute
                  (d := d) (n := n) (lowerWeight := lowerWeight) ι :=
              {
                outerRouting := outerRouting
                valueResidual :=
                  fun child ranked hchildWeight hchildTruncated =>
                    builder.valueResidual lowerWeight child ranked hchildWeight
                      hchildTruncated
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
                TSNormala
                  (n := n) (lowerWeight := lowerWeight)
                    (concreteBasicCommutators.{u} d) :=
              TSNormala.ofNormalizerAbove
                normalizerAbove
            let factorTail :=
              routing.factor_expansion_case hn hH factor
                hfactorWeight hfactorTruncated rootCase
                  (fun task htask =>
                    PCReach.children_factory_case
                      hn hH outerRouting factor 0 (by omega) rootCase
                        hrootCaseRightTree
                        htask)
            let merge :=
              (packetFactory
                |>.coord_sharp_normalizer
                  hn (concreteBasicCommutators.{u} d) hH sharp coordinates
                    factor)
                |>.mergeResidualExpansion hfactorWeight hfactorTruncated
            let block :=
              merge.activeBlockResolution factorTail hcoordinates
                hfactorWeight
            let tail :=
              (packetFactory
                |>.supported_route_normalizer
                  sharp coordinates factor hfactorWeight)
                |>.higherTailResolution hfactorWeight hfactorTruncated
            exact
              (TPResolu.active_block_tail
                hcoordinates hfactorWeight hfactorTruncated block tail)
                |>.exists_insertion nextNormalizer hfactorWeight
                  hfactorTruncated }
termination_by n - lowerWeight
decreasing_by
  all_goals
    have hlowerWeightCutoff : lowerWeight < n := by
      omega
    omega

end
  TBBuild

/--
Retained recipe traces and structural signed residual data construct product
coordinate polynomials.
-/
theorem
    commutators_coeff_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      TBBuild.{u}
        (d := d) (n := n))
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  signed_semantic_normalizer
    (concreteBasicCommutators.{u} d) e
      (builder.supportedCoordinateNormalizer hn hrecipes 1)

/--
Retained recipe traces and structural signed residual data construct inverse
coordinate polynomials.
-/
theorem
    commutators_supported_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      TBBuild.{u}
        (d := d) (n := n))
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  collected_data_normalizer
    (concreteBasicCommutators.{u} d) e
      (builder.supportedCoordinateNormalizer hn hrecipes 1)

end TCTex
end Submission

/-!
# Signed retained-trace collection with Jacobi-only value routing

Exact signed-swap cancellation removes the inverse skew-packet callback from
support-local polynomial Hall collection.  The remaining semantic packet
boundary is the forward Jacobi value residual.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open CEWord
open
  CCThree

/--
Signed retained-trace inputs after exact swap cancellation.
-/
structure
    PJBuild
    {d n : ℕ} where
  outerFactory :
    ∀ ι : Type,
      TRFtrya
        (d := d) (n := n) ι
  rootCase :
    ∀ {ι : Type}
      (lowerWeight : ℕ)
      (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι),
      factor.word.weight HEAddres.weight = lowerWeight →
        factor.word.weight HEAddres.weight < n →
          RankedBranchCase
            (n := n) factor 0
  root_case_tree :
    ∀ {ι : Type}
      (lowerWeight : ℕ)
      (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι)
      (hfactorWeight :
        factor.word.weight HEAddres.weight = lowerWeight)
      (hfactorTruncated :
        factor.word.weight HEAddres.weight < n)
      (innerCase :
        TruncatedRankedCase
          (n := n) factor 0),
      rootCase lowerWeight factor hfactorWeight hfactorTruncated =
          .innerReductionOuter innerCase →
        tree innerCase.rightWord = innerCase.unchanged
  valueResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ)
      (factor :
        SPFactor
          (concreteBasicCommutators.{u} d) ι)
      (ranked :
        ERDecomp
          factor),
      factor.word.weight HEAddres.weight = lowerWeight →
        factor.word.weight HEAddres.weight < n →
          TRRecolla
            (n := n) factor ranked.decomposition

namespace
  PJBuild

/-- Compile exact empty swap packets into the structural signed collector. -/
noncomputable def
    supportedChildrenBuilder
    {d n : ℕ}
    (builder :
      PJBuild.{u}
        (d := d) (n := n)) :
    TBBuild.{u}
      (d := d) (n := n) where
  outerFactory :=
    builder.outerFactory
  rootCase :=
    builder.rootCase
  root_case_tree :=
    builder.root_case_tree
  valueResidual :=
    builder.valueResidual
  swapValueInverse :=
    fun _lowerWeight factor left right hleftBasic hrightBasic htree
        _hfactorWeight _hfactorTruncated =>
      TVRecoll.empty
        factor left right hleftBasic hrightBasic htree

/--
Jacobi-only signed retained-trace inputs construct product coordinate
polynomials.
-/
theorem
    jacobi_coeff_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      PJBuild.{u}
        (d := d) (n := n))
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_coeff_builder
    hn e
      builder.supportedChildrenBuilder
      hrecipes

/--
Jacobi-only signed retained-trace inputs construct inverse coordinate
polynomials.
-/
theorem
    basic_commutators_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      PJBuild.{u}
        (d := d) (n := n))
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_supported_builder
    hn e
      builder.supportedChildrenBuilder
      hrecipes

end
  PJBuild

end TCTex
end Submission

-- Merged from PolynomialConcreteOuterRightContextual.lean

/-!
# Contextual collection for signed-polynomial basic outer-right frontiers

For a signed-polynomial nested frontier `[[left, middle], right]`, a Hall-basic
outer-right tree permits direct contextual inner reduction.  Every emitted
full-weight child is a reachable two-basic-child task, so the canonical ranked
scheduler recollects the entire finite child packet.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open CEWord

namespace
  TRRecoll

/--
Fold independently recollected concrete residuals over an arbitrary finite
signed-polynomial source.
-/
noncomputable def source_recollection_residuals
    {d n lowerWeight : ℕ}
    {ι : Type}
    (source :
      List
        (SPFactor
          (concreteBasicCommutators.{u} d) ι))
    (hsourceTruncated :
      SPFactor.IsTruncated n source)
    (hsourceSupported :
      SPFactor.WordWeightLeast lowerWeight source)
    (residual :
      ∀ factor ∈ source,
        TRRecoll
          (n := n) factor) :
    SSRecol
      (n := n) (lowerWeight := lowerWeight)
        (concreteBasicCommutators.{u} d) source := by
  have hsource :
      source.flatMap
          (fun factor :
              SPFactor
                (concreteBasicCommutators.{u} d) ι =>
            [factor]) =
        source := by
    clear hsourceTruncated hsourceSupported residual
    induction source with
    | nil =>
        rfl
    | cons factor source ih =>
        simp only [List.flatMap_cons, List.singleton_append, ih]
  rw [← hsource]
  exact
    SSRecol.flatMap
      source
      (fun factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι =>
        [factor])
      (fun factor hfactor =>
        (residual factor hfactor).singletonSourceRecollection
          (hsourceTruncated factor hfactor)
          (hsourceSupported factor hfactor))

end
  TRRecoll

namespace
  PCReach

/--
Every full-weight child emitted by contextual inner reduction is a reachable
two-basic-child task when the retained right tree is Hall-basic.
-/
noncomputable def inner_reduction_outer
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (unchanged : HallTree (FreeGenerator.{u} d))
    (hrightTree : tree rightWord = unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    {child :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hchild :
      child ∈
        CEWord.innerOuterFactors
          factor innerWord rightWord hword) :
    Σ rankDefect : ℕ,
      PCReach
        (n := n) child rankDefect := by
  rw [CEWord.innerOuterFactors] at hchild
  let indexExists := List.mem_map.mp hchild
  let i := Classical.choose indexExists
  have hi := Classical.choose_spec indexExists
  have hchild_eq := hi.2
  rw [← hchild_eq]
  exact
    ⟨HallTree.bracketRankDefect
        ((HallTree.indexedBasicTree i).weight + unchanged.weight)
        (HallTree.indexedBasicTree i) unchanged,
      {
        left := HallTree.indexedBasicTree i
        right := unchanged
        left_isBasic := HallTree.indexed_tree i
        right_isBasic := hunchangedBasic
        tree_eq := by
          rw [inner_reduction_factor, tree_commutator, tree_atom,
            basicReductionAddress, concreteBasicTree, hrightTree]
        factor_truncated := by
          rw [inner_outer_factor]
          exact hfactorTruncated
        rankDefect_eq := rfl
      }⟩

end
  PCReach

namespace
  TRRecoll

/--
Recollect a parent by reducing its immediate inner bracket and routing every
emitted full-weight child independently.
-/
noncomputable def
    inner_reduction_residuals
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (family :
      SNFam
        (n := n) (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (residual :
      ∀ child ∈
          CEWord.innerOuterFactors
            factor innerWord rightWord hword,
        TRRecoll
          (n := n) child) :
    TRRecoll
      (n := n) factor := by
  let children :=
    source_recollection_residuals
      (CEWord.innerOuterFactors
        factor innerWord rightWord hword)
      (CEWord.truncated_inner_factors
        factor innerWord rightWord hword hfactorTruncated)
      (CEWord.least_inner_factors
        factor innerWord rightWord hword)
      residual
  let normalizer :=
    family.normalizer
      (factor.word.weight HEAddres.weight)
  let comparison :=
    normalizer.child_normalized_raw
      hn hH factor innerWord rightWord hword rfl factor.word_weight_pos
        hfactorTruncated children
  let outer :=
    normalizer.recollection_inner_raw
      hn hH factor innerWord rightWord hword rfl factor.word_weight_pos
        hfactorTruncated
  exact
    inner_child_normalization factor innerWord rightWord
      hword children
      (by
        simpa only [
          CEWord.innerChildNormalized]
          using comparison)
      outer

end
  TRRecoll

namespace
  NWCase

/--
Collect any signed-polynomial nested frontier whose retained outer-right tree
is Hall-basic.
-/
noncomputable def outerResidualRecollect
    {d n : ℕ}
    (hn : 2 ≤ n)
    {ι : Type}
    (routing :
      PCRoute
        (d := d) (n := n) ι)
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (frontier :
      NWCase
        factor)
    (hrightBasic : frontier.right.IsBasic)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRRecoll
      (n := n) factor := by
  let innerWord :=
    CWord.commutator frontier.decomposition.left
      frontier.decomposition.middle
  let rightWord := frontier.decomposition.right
  have hrightTree : tree rightWord = frontier.right := by
    exact (trees_frontier factor frontier).2.2
  apply
    TRRecoll.inner_reduction_residuals
      hn
        (fun s hs hsn =>
          concrete_forms_associated d n s hs
            hsn)
        routing.normalizerFamily factor innerWord rightWord
          frontier.decomposition.word_eq hfactorTruncated
  intro child hchild
  let reachable :=
    PCReach.inner_reduction_outer
      factor innerWord rightWord frontier.decomposition.word_eq frontier.right
        hrightTree hrightBasic hfactorTruncated hchild
  exact
    routing.residualRecollection hn
      (fun s hs hsn =>
        concrete_forms_associated d n s hs hsn)
      child reachable.1 ⟨reachable.2⟩

end
  NWCase

end TCTex
end Submission

-- Merged from PolynomialConcreteOuterRightSubtree.lean

/-!
# Retained-right subtree recursion for signed-polynomial frontiers

Every exposed signed-polynomial nested frontier with a nonbasic retained-right
tree produces two descendants whose retained-right trees are proper subtrees.
This file closes that recursion by the well-founded Hall-tree order.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open CEWord
open
  TRRecoll
  RCDecomp
  TDCase

/-- One signed-polynomial nested frontier scheduled at a fixed weight. -/
structure
    PSTask
    {d n : ℕ}
    (ι : Type)
    (lowerWeight : ℕ) where
  factor :
    SPFactor
      (concreteBasicCommutators.{u} d) ι
  factor_weight :
    factor.word.weight HEAddres.weight = lowerWeight
  factor_truncated :
    factor.word.weight HEAddres.weight < n
  frontier :
    NWCase
      factor

namespace
  PSTask

/-- Recursive tasks decrease by their retained outer-right Hall tree. -/
def RetainedRightLT
    {d n lowerWeight : ℕ}
    {ι : Type}
    (child parent :
      PSTask.{u}
        (d := d) (n := n) ι lowerWeight) :
    Prop :=
  child.frontier.right < parent.frontier.right

/-- Retained-right task recursion is well founded by the Hall-tree order. -/
theorem well_founded_right
    {d n lowerWeight : ℕ}
    {ι : Type} :
    WellFounded
      (RetainedRightLT.{u}
        (d := d) (n := n) (ι := ι) (lowerWeight := lowerWeight)) := by
  unfold RetainedRightLT
  exact InvImage.wf
    (fun task :
        PSTask.{u}
          (d := d) (n := n) ι lowerWeight =>
      task.frontier.right)
    (HallTree.lt_wellFounded (α := FreeGenerator.{u} d))

/--
Classify one retained-right descendant. Terminal roots recollect immediately;
every surviving nested root becomes a strictly smaller subtree task.
-/
noncomputable def residual_recollection_descendant
    {d n lowerWeight : ℕ}
    {ι : Type}
    {parent :
      PSTask.{u}
        (d := d) (n := n) ι lowerWeight}
    (descendant :
      TDCase
        parent.factor parent.frontier)
    (newLeft newMiddle : HallTree (FreeGenerator.{u} d))
    (hdescendantLeft :
      descendant.left = .commutator newLeft newMiddle)
    (hnewMiddleNonbasic : ¬newMiddle.IsBasic)
    (hfactorWeight :
      descendant.factor.word.weight HEAddres.weight =
        lowerWeight)
    (hfactorTruncated :
      descendant.factor.word.weight HEAddres.weight < n)
    (recursive :
      ∀ child :
          PSTask.{u}
            (d := d) (n := n) ι lowerWeight,
        RetainedRightLT child parent →
          TRRecoll
            (n := n) child.factor) :
    TRRecoll
      (n := n) descendant.factor := by
  by_cases htreeBasic : (tree descendant.factor.word).IsBasic
  · exact tree_basic descendant.factor htreeBasic
  · by_cases hchildrenEq : descendant.left = descendant.retainedRight
    · exact
        tree_commutator_self descendant.factor descendant.left
          (by simpa only [hchildrenEq] using descendant.tree_eq)
    · by_cases hreverseBasic :
          (HallTree.commutator descendant.retainedRight descendant.left).IsBasic
      · exact
          tree_swap_basic descendant.factor descendant.retainedRight
            descendant.left descendant.tree_eq hreverseBasic
      · have htree :
            tree descendant.factor.word =
              .commutator (.commutator newLeft newMiddle)
                descendant.retainedRight := by
          rw [descendant.tree_eq, hdescendantLeft]
        have houterNonbasic :
            ¬(HallTree.commutator (.commutator newLeft newMiddle)
                descendant.retainedRight).IsBasic := by
          intro hbasic
          apply htreeBasic
          rw [htree]
          exact hbasic
        have hinnerNonbasic :
            ¬(HallTree.commutator newLeft newMiddle).IsBasic := by
          intro hbasic
          exact
            hnewMiddleNonbasic
              ((HallTree.isBasic_commutator newLeft newMiddle).mp hbasic).2.1
        let decomposition :=
          syntacticTreeNonbasic
            descendant.factor.word newLeft newMiddle descendant.retainedRight
              htree houterNonbasic hinnerNonbasic
        let child :
            PSTask.{u}
              (d := d) (n := n) ι lowerWeight :=
          {
            factor := descendant.factor
            factor_weight := hfactorWeight
            factor_truncated := hfactorTruncated
            frontier :=
              {
                left := newLeft
                middle := newMiddle
                right := descendant.retainedRight
                tree_eq := htree
                outer_nonbasic := houterNonbasic
                inner_nonbasic := hinnerNonbasic
                children_ne := by
                  simpa only [← hdescendantLeft] using hchildrenEq
                reverse_nonbasic := by
                  simpa only [← hdescendantLeft] using hreverseBasic
                decomposition := decomposition
              }
          }
        exact
          recursive child (by
            simpa only [RetainedRightLT, child] using
              descendant.retainedRight_lt)

end
  PSTask

/--
Canonical signed-polynomial routing closes retained-right subtree recursion.
-/
structure
    SJBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  routing :
    ∀ ι : Type,
      PCRoute.{u}
        (d := d) (n := n) ι

namespace
  SJBuild

open
  PSTask

/-- Resolve one retained-right task, assuming smaller subtree tasks resolved. -/
noncomputable def resolveTaskStep
    {d n lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {ι : Type}
    (builder :
      SJBuild.{u}
        (d := d) (n := n) hn)
    (task :
      PSTask.{u}
        (d := d) (n := n) ι lowerWeight)
    (recursive :
      ∀ child :
          PSTask.{u}
            (d := d) (n := n) ι lowerWeight,
        RetainedRightLT child task →
          TRRecoll
            (n := n) child.factor) :
    TRRecoll
      (n := n) task.factor := by
  by_cases hrightBasic : task.frontier.right.IsBasic
  · exact
      NWCase.outerResidualRecollect
        hn (builder.routing ι) task.factor task.frontier hrightBasic
          task.factor_truncated
  · let retained := ofNonbasic task.factor task.frontier hrightBasic
    let firstDescendant := first task.factor task.frontier hrightBasic
    let secondDescendant := second task.factor task.frontier hrightBasic
    have hfirstWeight :
        firstDescendant.factor.word.weight HEAddres.weight =
          lowerWeight := by
      simpa only [firstDescendant, first,
        expanded_jacobi_factor,
        word_swap_factor] using task.factor_weight
    have hfirstTruncated :
        firstDescendant.factor.word.weight HEAddres.weight <
          n := by
      simpa only [firstDescendant, first,
        expanded_jacobi_factor,
        word_swap_factor] using task.factor_truncated
    have hsecondWeight :
        secondDescendant.factor.word.weight HEAddres.weight =
          lowerWeight := by
      simpa only [secondDescendant, second,
        expanded_second_factor,
        word_swap_factor] using task.factor_weight
    have hsecondTruncated :
        secondDescendant.factor.word.weight HEAddres.weight <
          n := by
      simpa only [secondDescendant, second,
        expanded_second_factor,
        word_swap_factor] using task.factor_truncated
    let firstResidual :=
      residual_recollection_descendant firstDescendant retained.left
        (.commutator task.frontier.left task.frontier.middle) (by rfl)
          task.frontier.inner_nonbasic hfirstWeight hfirstTruncated recursive
    let secondResidual :=
      residual_recollection_descendant secondDescendant retained.middle
        (.commutator task.frontier.left task.frontier.middle) (by rfl)
          task.frontier.inner_nonbasic hsecondWeight hsecondTruncated recursive
    let reversed := retainedSwapFactor task.factor task.frontier
    let reversedResidual :=
      expanded_normalizer_family hn builder.packet
        (builder.routing ι).normalizerFamily reversed retained.decomposition
        (by
          simpa only [reversed,
            word_swap_factor] using task.factor_weight)
        (by
          simpa only [reversed,
            word_swap_factor] using
              task.factor_truncated)
        firstResidual secondResidual
    exact
      expanded_swap task.factor
        (.commutator task.frontier.decomposition.left
          task.frontier.decomposition.middle)
        task.frontier.decomposition.right task.frontier.decomposition.word_eq
          reversedResidual
          (PSRecoll.ofNormalizerFamily
            hn
              (fun s hs hsn =>
                concrete_forms_associated d n s
                  hs hsn)
              (builder.routing ι).normalizerFamily task.factor
                (.commutator task.frontier.decomposition.left
                  task.frontier.decomposition.middle)
                task.frontier.decomposition.right
                  task.frontier.decomposition.word_eq task.factor_weight
                    task.factor_truncated)

/-- Run the retained-right resolver by well-founded Hall-tree recursion. -/
noncomputable def taskResidualRecollection
    {d n lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {ι : Type}
    (builder :
      SJBuild.{u}
        (d := d) (n := n) hn)
    (task :
      PSTask.{u}
        (d := d) (n := n) ι lowerWeight) :
    TRRecoll
      (n := n) task.factor :=
  (well_founded_right
      (d := d) (n := n) (ι := ι)
        (lowerWeight := lowerWeight)).fix
    (fun task recursive => builder.resolveTaskStep task recursive) task

/-- Compile closed retained-right recursion into the nested-word frontier. -/
noncomputable def expandedWordsBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      SJBuild.{u}
        (d := d) (n := n) hn) :
    CNBuild.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := by
    intro ι _lowerWeight _hnonterminal factor left right hword hfactorWeight
      hfactorTruncated
    exact
      PSRecoll.ofNormalizerFamily
        hn
          (fun s hs hsn =>
            concrete_forms_associated d n s hs
              hsn)
          (builder.routing ι).normalizerFamily factor left right hword
            hfactorWeight hfactorTruncated
  nestedWordsResidual :=
    fun lowerWeight _hnonterminal factor hfactorWeight hfactorTruncated
        frontier =>
      builder.taskResidualRecollection
        {
          factor := factor
          factor_weight := hfactorWeight
          factor_truncated := hfactorTruncated
          frontier := frontier
        }

end
  SJBuild

/-- Closed retained-right subtree recursion constructs product polynomials. -/
theorem
    frontier_collect_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      SJBuild.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_ranked_builder
    hn e builder.expandedWordsBuilder

/-- Closed retained-right subtree recursion constructs inverse polynomials. -/
theorem
    commutators_collected_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      SJBuild.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  ranked_expanded_builder
    hn e builder.expandedWordsBuilder

end TCTex
end Submission

-- Merged from PolynomialConcreteOuterRightSubtreeFromReachableBuilder.lean

/-!
# Closed retained-right signed collection from reachable builders

A reachable universal signed collector already supplies canonical routing for
every exponent-variable type.  This file routes that data through the closed
retained-right Hall-tree recursion.

For retained recipe coefficients, the product law and a packet-free reachable
insertion schedule construct the reachable builder automa.

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

namespace
  SJBuild

/--
Route an existing reachable universal signed collector through closed
retained-right subtree recursion.
-/
noncomputable def ofReachableBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    SJBuild.{u}
      (d := d) (n := n) hn :=
  let canonical :=
    CCBuild.ofReachableBuilder
      (hn := hn) packet builder
  {
    packet := canonical.packet
    routing := canonical.routing
  }

/--
Retained recipe coefficients and a packet-free reachable insertion schedule
route through closed retained-right subtree recursion.
-/
noncomputable def
    recipe_reachable_schedule
    {d n : ℕ}
    {hn : 2 ≤ n}
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (schedule :
      TIDeriva
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    SJBuild.{u}
      (d := d) (n := n) hn :=
  ofReachableBuilder
    (retainedAllPacket hrecipes)
    (CDBuild.recipe_coeff_trace
      hrecipes schedule)

end
  SJBuild

/--
A reachable universal signed collector routes product recollection through
closed retained-right subtree recursion.
-/
theorem
    right_subtree_recursion
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  frontier_collect_builder
    hn e
      (SJBuild.ofReachableBuilder
        packet builder)

/--
A reachable universal signed collector routes inverse recollection through
closed retained-right subtree recursion.
-/
theorem
    inverse_subtree_recursion
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (builder :
      CDBuild
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_collected_builder
    hn e
      (SJBuild.ofReachableBuilder
        packet builder)

/--
Retained recipe coefficients and reachable insertion derivations route product
recollection through closed retained-right subtree recursion.
-/
theorem
    collected_subtree_recursion
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (schedule :
      TIDeriva
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  frontier_collect_builder
    hn e
      (SJBuild.recipe_reachable_schedule
        hrecipes schedule)

/--
Retained recipe coefficients and reachable insertion derivations route inverse
recollection through closed retained-right subtree recursion.
-/
theorem
    commutators_subtree_recursion
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (schedule :
      TIDeriva
        (n := n) (concreteCommutatorsWeight.{u} d)) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_collected_builder
    hn e
      (SJBuild.recipe_reachable_schedule
        hrecipes schedule)

end TCTex
end Submission
