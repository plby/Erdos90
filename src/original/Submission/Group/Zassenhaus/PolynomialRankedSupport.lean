import Submission.Group.Zassenhaus.SignedReductionFactors
import Submission.Group.Zassenhaus.ErasedShapePrograms
import Submission.Group.Zassenhaus.FamilyCollectorSupport
import Submission.Group.Zassenhaus.RankedChildSources
import Submission.Group.Zassenhaus.PolynomialBracketSupport
import Submission.Group.Zassenhaus.Polynomial
import Submission.Group.Zassenhaus.SignedCorrectionSemantics
import Submission.Group.Zassenhaus.CompletePetrescoRecipe


-- Merged from PolynomialConcreteNonbasicReductionCollection.lean

/-!
# Signed-polynomial collection reduced to non-basic expanded trees

The concrete comparison residual is automatic, and all-weight PBW uniqueness
makes the true reduction residual trivial whenever the expanded Hall tree is
already basic.  This file exposes the remaining arbitrary-cutoff boundary:
finite upward recollection is required only for genuinely non-basic expanded
trees.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
A cutoff Hall-Petresco packet and upward recollection of true residuals only
for factors whose expanded Hall trees are non-basic.
-/
structure TNBuilda
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  nonbasicResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ¬(CEWord.tree factor.word).IsBasic →
                TRRecoll
                  (n := n) factor

namespace
  TNBuilda

open
  TRRecoll

/--
Fill every basic expanded-tree residual with the empty recollection and leave
only non-basic residuals to the caller.
-/
noncomputable def automaticCollectionBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      TNBuilda.{u}
        (d := d) (n := n) hn) :
    TPBuild.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  basicResidual lowerWeight hnonterminal factor hfactorWeight
      hfactorTruncated := by
    by_cases htreeBasic :
        (CEWord.tree factor.word).IsBasic
    · exact tree_basic factor htreeBasic
    · exact
        builder.nonbasicResidual lowerWeight hnonterminal factor hfactorWeight
          hfactorTruncated htreeBasic

end
  TNBuilda

/--
For canonical Hall families, a cutoff packet and true residual recollections
for non-basic expanded trees construct product coordinate polynomials.
-/
theorem
    nonbasic_collect_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      TNBuilda.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  collected_automatic_builder
    hn e builder.automaticCollectionBuilder

/--
For canonical Hall families, a cutoff packet and true residual recollections
for non-basic expanded trees construct inverse coordinate polynomials.
-/
theorem
    commutators_nonbasic_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      TNBuilda.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  automatic_collect_builder
    hn e builder.automaticCollectionBuilder

end TCTex
end Submission

-- Merged from PolynomialOrbitExpansion.lean

/-!
# Recurrence-sum occurrence accounting for guarded raw-source grids

This file packages the explicit scalar recurrence sum for the guarded raw-source
scheduler as a standalone replacement for exact finite-index trace occurrence
accounting.  It also identifies the same residual equality with evaluation of
the canonical scalar local collector.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  SOAccouna

open HACoeff
open
  LMBounda
open
  ILModela
open
  CLFree
open
  ALFree
open FIProf
open RITrace
open
  ISLift
open
  IMRec
open
  FISchedu

/--
The standalone residual recurrence-sum statement: for every concrete source
pair and retained root index, the recursively computed scheduler multiplicity
is the multiplicity in the canonical concrete root-index trace.
-/
structure
    IOAccoun
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  recurrence_sum_count :
    ∀ M N index,
      guardedSchedulerRecurrence
          (multiplicityProfileShape raw)
          M N index =
        (generatedGridBranch
          (n := n) hleftWeight hrightWeight M N).count index

namespace
  IOAccoun

/--
Pointwise equality of the explicit recurrence sum and the canonical trace
counts reconstructs exact finite-index trace occurrence accounting.
-/
noncomputable def
    schedulerOccAccounting
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      IOAccoun
        (n := n) hleftWeight hrightWeight) :
    SOAccoun
      (n := n) hleftWeight hrightWeight where
  raw := kernel.raw
  scheduler_perm_root M N := by
    rw [List.perm_iff_count]
    intro index
    rw [
      count_recurrence_sum]
    exact kernel.recurrence_sum_count M N index

end
  IOAccoun

namespace
  SOAccoun

/--
Exact finite-index trace occurrence accounting implies the standalone
recurrence-sum criterion.
-/
noncomputable def
    sumOccAccounting
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      SOAccoun
        (n := n) hleftWeight hrightWeight) :
    IOAccoun
      (n := n) hleftWeight hrightWeight where
  raw := kernel.raw
  recurrence_sum_count M N index := by
    rw [←
      count_recurrence_sum]
    exact
      (kernel.scheduler_perm_root M N).count_eq
        index

end
  SOAccoun

/--
The recurrence-sum criterion is equivalent to exact finite-index trace
occurrence accounting.
-/
noncomputable def
    occAccountingKernel
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    SOAccoun
        (n := n) hleftWeight hrightWeight ≃
      IOAccoun
        (n := n) hleftWeight hrightWeight where
  toFun :=
    SOAccoun.sumOccAccounting
  invFun :=
    IOAccoun.schedulerOccAccounting
  left_inv kernel := by
    cases kernel
    congr
  right_inv kernel := by
    cases kernel
    congr

/--
Equivalent scalar formulation: the recursively computed scheduler
multiplicity agrees with the canonical local collector evaluated on the raw
generated source.
-/
structure
    GICollec
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  recurrence_sum_collection :
    ∀ M N index,
      guardedSchedulerRecurrence
          (multiplicityProfileShape raw)
          M N index =
        (generatedGridModel
          M N n leftWeight rightWeight hleftWeight hrightWeight index).collection
            (inverseDecoratedTerms M N)
            (inverse_generated_source M N)

namespace
  GICollec

/--
The local-collector recurrence statement implies the canonical trace-count
recurrence statement.
-/
noncomputable def
    sumOccAccounting
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GICollec
        (n := n) hleftWeight hrightWeight) :
    IOAccoun
      (n := n) hleftWeight hrightWeight where
  raw := kernel.raw
  recurrence_sum_count M N index := by
    rw [←
      decorated_branch_idx
        index]
    exact kernel.recurrence_sum_collection M N index

/--
The local-collector recurrence statement directly reconstructs exact
finite-index trace occurrence accounting.
-/
noncomputable def
    schedulerOccAccounting
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GICollec
        (n := n) hleftWeight hrightWeight) :
    SOAccoun
      (n := n) hleftWeight hrightWeight :=
  kernel
    |>.sumOccAccounting
    |>.schedulerOccAccounting

end
  GICollec

namespace
  IOAccoun

/--
The canonical trace-count recurrence statement implies the scalar
local-collector recurrence statement.
-/
noncomputable def
    guardedCollectKernel
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      IOAccoun
        (n := n) hleftWeight hrightWeight) :
    GICollec
      (n := n) hleftWeight hrightWeight where
  raw := kernel.raw
  recurrence_sum_collection M N index := by
    rw [
      decorated_branch_idx
        index]
    exact kernel.recurrence_sum_count M N index

end
  IOAccoun

/--
The canonical scalar local-collector criterion and the canonical trace-count
criterion are interchangeable.
-/
noncomputable def
    guardedIdxCollect
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    IOAccoun
        (n := n) hleftWeight hrightWeight ≃
      GICollec
        (n := n) hleftWeight hrightWeight where
  toFun :=
    IOAccoun.guardedCollectKernel
  invFun :=
    GICollec.sumOccAccounting
  left_inv kernel := by
    cases kernel
    congr
  right_inv kernel := by
    cases kernel
    congr

end
  SOAccouna
end TCTex
end Submission

/-!
# Decomposed recurrence-sum occurrence accounting

The residual raw-source collector identity can be stated with its algebraic
shape exposed: a left nested sum, a matching correction-root product sum, and
a right nested sum.  This file packages that statement and proves it
equivalent to the scalar recurrence-sum local-collector kernel.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex


namespace
  DOAccoun

open HACoeff
open
  ILModela
open
  LMBounda
open
  ALFree
open FIProf
open RITrace
open
  ISLift
open
  IMRec
open
  SOAccouna

/--
Standalone decomposed residual collector statement: the left nested,
root-product, and right nested sums evaluate to the canonical scalar local
collector on the generated inverse-raw source.
-/
structure
    GIDecompa
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  raw :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight
  add_product_collection :
    ∀ M N index,
      idxNestedRecurrence
          (multiplicityProfileShape raw)
          M N index +
        idxRecurrenceSum
            (multiplicityProfileShape raw)
            M N index +
          guardedRecurrenceSum
              (multiplicityProfileShape raw)
              M N index =
        (generatedGridModel
          M N n leftWeight rightWeight hleftWeight hrightWeight index).collection
            (inverseDecoratedTerms M N)
            (inverse_generated_source M N)

namespace
  GIDecompa

/-- Collapse the decomposed residual collector statement to the recurrence sum. -/
noncomputable def
    guardedCollectKernel
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GIDecompa
        (n := n) hleftWeight hrightWeight) :
    GICollec
      (n := n) hleftWeight hrightWeight where
  raw := kernel.raw
  recurrence_sum_collection M N index := by
    rw [
      guarded_idx_nested]
    exact
      kernel.add_product_collection
        M N index

/-- The decomposed residual statement reconstructs exact occurrence accounting. -/
noncomputable def
    schedulerOccAccounting
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GIDecompa
        (n := n) hleftWeight hrightWeight) :
    SOAccoun
      (n := n) hleftWeight hrightWeight :=
  kernel
    |>.guardedCollectKernel
    |>.schedulerOccAccounting

/--
In the empty-grid range, a decomposed residual kernel forces the canonical
local collector value to vanish.
-/
lemma canonical_collection_sum
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GIDecompa
        (n := n) hleftWeight hrightWeight)
    (M N : ℕ)
    (index : RetainedOrbitIndex n leftWeight rightWeight)
    (hhigh : n ≤ 2 * (leftWeight + rightWeight)) :
    (generatedGridModel
      M N n leftWeight rightWeight hleftWeight hrightWeight index).collection
        (inverseDecoratedTerms M N)
        (inverse_generated_source M N) =
      0 := by
  rw [←
    kernel.add_product_collection
      M N index]
  rw [
    guarded_idx_left
      _ M N index hhigh,
    guarded_idx_sum
      _ M N index hhigh,
    guarded_source_idx
      _ M N index hhigh]

end
  GIDecompa

namespace
  GICollec

/-- Expand the scalar recurrence-sum residual statement into three algebraic sums. -/
noncomputable def
    guardedDecomposedCollect
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      GICollec
        (n := n) hleftWeight hrightWeight) :
    GIDecompa
      (n := n) hleftWeight hrightWeight where
  raw := kernel.raw
  add_product_collection M N index := by
    rw [←
      guarded_idx_nested]
    exact kernel.recurrence_sum_collection M N index

end
  GICollec

/--
The scalar recurrence-sum residual statement and its three-way algebraic
decomposition are equivalent data.
-/
noncomputable def
    guardedIdxDecomposed
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    GICollec
        (n := n) hleftWeight hrightWeight ≃
      GIDecompa
        (n := n) hleftWeight hrightWeight where
  toFun :=
    GICollec.guardedDecomposedCollect
  invFun :=
    GIDecompa.guardedCollectKernel
  left_inv kernel := by
    cases kernel
    congr
  right_inv kernel := by
    cases kernel
    congr

end
  DOAccoun
end TCTex
end Submission

-- Merged from PolynomialRankedStructuralRestart.lean

/-!
# Ranked structural restarts for signed symbolic Hall collection

A structural restart consists of a finite Hall-ranked child source and a
strictly higher normalized quotient from those children to an exact symbolic
target.  Appending the quotient coordinates to the child factors reconstructs
the target while the quotient block can be scheduled by cutoff-defect descent.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


namespace SPFactor

/--
A finite Hall-ranked child source with a normalized quotient to an exact
symbolic target.
-/
structure RSRestar
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (parent : SPFactor H ι)
    (parentRankDefect : ℕ)
    (targetSource : List (SPFactor H ι)) where
  source :
    RCSrc (n := n) parent parentRankDefect
  normalization :
    SSNorm
      (n := n) (lowerWeight := lowerWeight) H
      (SPFactor.inverseList source.factorSource ++
        targetSource)

namespace RSRestar

/-- Append the normalized restart quotient after the ranked child source. -/
def rewriteSource
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    {targetSource : List (SPFactor H ι)}
    (restart :
      RSRestar
        (n := n) (lowerWeight := lowerWeight)
          parent parentRankDefect targetSource) :
    List (SPFactor H ι) :=
  restart.source.factorSource ++ restart.normalization.coordinates.factors
    (n := n)

/-- Ranked children followed by the restart quotient evaluate to the target. -/
theorem list_rewrite_target
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    {targetSource : List (SPFactor H ι)}
    (restart :
      RSRestar
        (n := n) (lowerWeight := lowerWeight)
          parent parentRankDefect targetSource)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e restart.rewriteSource =
      SPFactor.listEval e targetSource := by
  rw [rewriteSource, SPFactor.listEval_append,
    restart.normalization.coordinates_raw_source,
    SPFactor.listEval_append,
    SPFactor.list_eval_inverse]
  group

/--
Expose a structural restart as a recollection of its exact target at any
weaker support bound carried by the ranked child source.
-/
def targetSourceRecollection
    {d n restartWeight targetWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    {targetSource : List (SPFactor H ι)}
    (restart :
      RSRestar
        (n := n) (lowerWeight := restartWeight)
          parent parentRankDefect targetSource)
    (hsourceTruncated :
      SPFactor.IsTruncated n restart.source.factorSource)
    (hsourceSupported :
      SPFactor.WordWeightLeast targetWeight
        restart.source.factorSource)
    (htargetWeight : targetWeight ≤ restartWeight) :
    SSRecol
      (n := n) (lowerWeight := targetWeight) H targetSource where
  higherSource := restart.rewriteSource
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hsourceTruncated x hx
    · exact restart.normalization.factors_isTruncated x hx
  higher_weight_least := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hsourceSupported x hx
    · exact htargetWeight.trans
        (restart.normalization.factors_weight_least x hx)
  list_higher_raw :=
    restart.list_rewrite_target

/-- Every retained restart factor improves the parent cutoff defect. -/
lemma restart_defect_parent
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    {targetSource : List (SPFactor H ι)}
    (restart :
      RSRestar
        (n := n) (lowerWeight := lowerWeight)
          parent parentRankDefect targetSource)
    (hparent : parent.word.weight HEAddres.weight < lowerWeight)
    {x : SPFactor H ι}
    (hx : x ∈ restart.normalization.coordinates.factors (n := n)) :
    cutoffDefect n x < cutoffDefect n parent := by
  have hxSupported :=
    restart.normalization.factors_weight_least x hx
  have hxTruncated := restart.normalization.factors_isTruncated x hx
  simp only [cutoffDefect]
  omega

/-- Replacing the parent by the normalized restart quotient strictly descends. -/
lemma multiset_restart_singleton
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    {targetSource : List (SPFactor H ι)}
    (restart :
      RSRestar
        (n := n) (lowerWeight := lowerWeight)
          parent parentRankDefect targetSource)
    (hparent : parent.word.weight HEAddres.weight < lowerWeight)
    (P : List (SPFactor H ι)) :
    CutoffDefectMultiset n
      (P ++ restart.normalization.coordinates.factors (n := n))
      (P ++ [parent]) := by
  unfold CutoffDefectMultiset
  rw [defect_multiset_append, defect_multiset_append,
    cutoff_multiset_singleton]
  apply Multiset.dershowitz_manna_forall
  intro y hy
  rw [cutoffDefectMultiset] at hy
  rcases List.mem_map.mp (Multiset.mem_coe.mp hy) with ⟨x, hx, rfl⟩
  exact restart.restart_defect_parent hparent hx

end RSRestar
end SPFactor

end TCTex
end Submission

-- Merged from PolynomialRankedTaskSourceInduction.lean

/-!
# Induction over ranked signed-polynomial child sources

A Hall-ranked child source packages both a finite emitted source and strict
lexicographic descent for every task.  This file turns that package into the
well-founded recursion principle consumed by a signed-polynomial Hall
collector.

It also records the erased-source view: every emitted symbolic factor has some
rank at which the recursive motive is available.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace SPFactor
namespace RCSrc

/-- A parent induction hypothesis supplies the motive for every ranked task. -/
theorem motive_tasks
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    (source : RCSrc (n := n) parent parentRankDefect)
    {motive : SPFactor H ι → ℕ → Prop}
    (ih :
      ∀ child childRankDefect,
        HallRankedDescends n child childRankDefect parent parentRankDefect →
          motive child childRankDefect)
    {task : SPFactor H ι × ℕ}
    (htask : task ∈ source.tasks) :
    motive task.1 task.2 :=
  ih task.1 task.2 (source.tasks_descend task htask)

/--
After erasing recursion ranks, every emitted symbolic factor still has a rank
at which the parent induction hypothesis supplies its motive.
-/
theorem rank_defect_motive
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {parent child : SPFactor H ι}
    {parentRankDefect : ℕ}
    (source : RCSrc (n := n) parent parentRankDefect)
    {motive : SPFactor H ι → ℕ → Prop}
    (ih :
      ∀ descendant descendantRankDefect,
        HallRankedDescends n descendant descendantRankDefect parent
            parentRankDefect →
          motive descendant descendantRankDefect)
    (hchild : child ∈ source.factorSource) :
    ∃ childRankDefect : ℕ,
      motive child childRankDefect := by
  rcases source.rank_ranked_descends
      hchild with
    ⟨childRankDefect, _htask, hdescends⟩
  exact ⟨childRankDefect, ih child childRankDefect hdescends⟩

end RCSrc

/--
A finite Hall-ranked child-source scheduler supplies a recursion principle for
the cutoff-defect/Hall-rank relation.
-/
theorem induction_child_sources
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {motive : SPFactor H ι → ℕ → Prop}
    (children :
      ∀ parent parentRankDefect,
        RCSrc (n := n) parent parentRankDefect)
    (step :
      ∀ parent parentRankDefect,
        (∀ task ∈ (children parent parentRankDefect).tasks,
          motive task.1 task.2) →
            motive parent parentRankDefect)
    (factor : SPFactor H ι)
    (rankDefect : ℕ) :
    motive factor rankDefect :=
  descends_induction_children
    (fun parent parentRankDefect =>
      (children parent parentRankDefect).tasks)
    (fun parent parentRankDefect task htask =>
      (children parent parentRankDefect).tasks_descend task htask)
    step factor rankDefect

end SPFactor
end TCTex
end Submission

-- Merged from PolynomialTransient.lean

/-!
# Transient polynomial substitution against a unit right exponent

The permanent signed polynomial factor type ties the arithmetic weight of its
coefficient formula to the physical weight of its Hall word.  Inner reduction
temporarily needs a weaker object: an existing parent coefficient is reattached
to a smaller inner word before expanding `[inner ^ e, right]`.

The powered collector represents the right exponent by a transient
constant-one carrier.  A homogeneous Claim 8 formula cannot represent that
constant.  This file instead specializes the first Hall-Petresco substitution
directly against right exponent one.  Its output coefficients are homogeneous
formulas again, with explicit arithmetic bounds kept separate from their
physical output words.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement
open HACoeff

namespace WBForm

/-- Multiply every signed recipe term by one fixed integer scalar. -/
def scaleRight
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (formula : WBForm H ι targetWeight)
    (scalar : ℤ) :
    WBForm H ι targetWeight where
  terms := formula.terms.map fun term => (term.1 * scalar, term.2)

@[simp]
lemma eval_scaleRight
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (formula : WBForm H ι targetWeight)
    (scalar : ℤ)
    (e : ι → HEFam H) :
    (formula.scaleRight scalar).eval e = formula.eval e * scalar := by
  cases formula with
  | mk terms =>
      induction terms with
      | nil =>
          simp [scaleRight, eval]
      | cons term terms ih =>
          simp only [scaleRight, eval, List.map_cons, List.sum_cons,
            WBTerm.eval] at ih ⊢
          rw [ih]
          ring

/-- Transport a formula across an equality of arithmetic target weights. -/
def reweight
    {d leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hweight : leftWeight = rightWeight)
    (formula : WBForm H ι leftWeight) :
    WBForm H ι rightWeight :=
  hweight ▸ formula

@[simp]
lemma eval_reweight
    {d leftWeight rightWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hweight : leftWeight = rightWeight)
    (formula : WBForm H ι leftWeight)
    (e : ι → HEFam H) :
    (formula.reweight hweight).eval e = formula.eval e := by
  subst rightWeight
  rfl

end WBForm

/--
A Hall word carrying a homogeneous polynomial coefficient whose arithmetic
weight need not yet fit the physical Hall word.
-/
structure STExp
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  word :
    CWord (HEAddres H)
  coefficientWeight :
    ℕ
  coefficient :
    WBForm H ι coefficientWeight

namespace STExp

/-- Evaluate one transiently weighted polynomial Hall word. -/
def value
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (wordExpansion : STExp H ι) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  wordExpansion.word.eval
      HEAddres.freeLowerTruncation ^
    wordExpansion.coefficient.eval e

/-- Evaluate a finite ordered list of transient polynomial Hall words. -/
def listValue
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (wordExpansions :
      List (STExp H ι)) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  (wordExpansions.map fun wordExpansion => wordExpansion.value e).prod

/--
Reattach an ordinary polynomial coefficient to an arbitrary Hall word while
retaining its original arithmetic bound.
-/
def rewordFactor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι)
    (word : CWord (HEAddres H)) :
    STExp H ι where
  word := word
  coefficientWeight := factor.word.weight HEAddres.weight
  coefficient := factor.coefficient

@[simp]
lemma coefficient_reword_factor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι)
    (word : CWord (HEAddres H))
    (e : ι → HEFam H) :
    (rewordFactor factor word).coefficient.eval e =
      factor.coefficient.eval e :=
  rfl

/--
Return to an ordinary polynomial factor once the arithmetic coefficient bound
fits the physical Hall word.
-/
def toFactor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (wordExpansion : STExp H ι)
    (hweight :
      wordExpansion.coefficientWeight ≤
        wordExpansion.word.weight HEAddres.weight) :
    SPFactor H ι where
  word := wordExpansion.word
  coefficient := wordExpansion.coefficient.weaken hweight

@[simp]
lemma eval_toFactor
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (wordExpansion : STExp H ι)
    (hweight :
      wordExpansion.coefficientWeight ≤
        wordExpansion.word.weight HEAddres.weight)
    (e : ι → HEFam H) :
    (wordExpansion.toFactor hweight).eval (n := n) e =
      wordExpansion.value e := by
  simp [toFactor, SPFactor.eval,
    SPFactor.wordValue, value]

end STExp

namespace PIRed

/-- The Hall word produced by one recipe after a one-sided unit substitution. -/
def boundWord
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : BRecipe)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    CWord (HEAddres H) :=
  CWord.hallPairBind B.word rightWord R.erasedShape

@[simp]
lemma weight_boundWord
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : BRecipe)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    (boundWord R B rightWord).weight HEAddres.weight =
      R.leftDegree * B.word.weight HEAddres.weight +
        R.rightDegree * rightWord.weight HEAddres.weight := by
  rw [boundWord, CWord.weight_pair_bind,
    CWord.pair_atom_degree,
    R.erased_left_degree, R.erased_shape_degree]

/-- The scalar contribution obtained by substituting right exponent one. -/
def rightUnitCoefficient
    (R : BRecipe) :
    ℤ :=
  (R.rightBlocks.map fun degree => Ring.choose (1 : ℤ) degree).prod

/--
Normalize the left parent formula while evaluating the missing right parent
directly at exponent one.
-/
def coefficientFormula
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B : STExp H ι) :
    WBForm H ι
      (R.leftDegree * B.coefficientWeight) :=
  let left :=
    normalizer.ringChooseProduct B.coefficient
      (BRSpec.positiveDegrees R.leftBlocks)
      (by
        apply List.ne_nil_of_length_pos
        exact
          BRSpec.length_degrees_pos
            (by
              simpa [BRecipe.leftDegree] using
                BRSpec.leftDegree_pos R))
      (fun degree hdegree =>
        BRSpec.positive_degrees_pos hdegree)
  WBForm.reweight
    (by
      simp [BRecipe.leftDegree])
    (left.scaleRight (rightUnitCoefficient R))

@[simp]
lemma eval_coefficientFormula
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (R : BRecipe)
    (B : STExp H ι) :
    (coefficientFormula normalizer R B).eval e =
      BRSpec.coefficientValue R
        (B.coefficient.eval e) 1 := by
  simp only [coefficientFormula, WBForm.eval_reweight,
    WBForm.eval_scaleRight,
    WBForm.RCNormal.ring_choose_product,
    BRSpec.coefficientValue,
    BRSpec.choose_positive_degrees,
    rightUnitCoefficient]

/-- One recipe output with its honest transient arithmetic coefficient bound. -/
def wordExpansion
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    STExp H ι where
  word := boundWord R B rightWord
  coefficientWeight := R.leftDegree * B.coefficientWeight
  coefficient := coefficientFormula normalizer R B

@[simp]
lemma value_wordExpansion
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (R : BRecipe)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    (wordExpansion normalizer R B rightWord).value (n := n) e =
      R.erasedShape.eval
          (HPAtom.eval
            (B.word.eval
              (HEAddres.freeLowerTruncation
                (n := n)))
            (rightWord.eval
              (HEAddres.freeLowerTruncation
                (n := n)))) ^
        BRSpec.coefficientValue R
          (B.coefficient.eval e) 1 := by
  rw [STExp.value, wordExpansion,
    eval_coefficientFormula]
  exact congrArg
    (fun g =>
      g ^
        BRSpec.coefficientValue R
          (B.coefficient.eval e) 1)
    (CWord.eval_pair_bind
      HEAddres.freeLowerTruncation B.word rightWord
        R.erasedShape)

/-- Attach a finite ordered recipe packet after one-sided unit substitution. -/
def wordExpansions
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (recipes : List BRecipe)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    List (STExp H ι) :=
  recipes.map fun R => wordExpansion normalizer R B rightWord

/-- Evaluate an ordered one-sided unit recipe packet. -/
lemma list_value_expansions
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (recipes : List BRecipe)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    STExp.listValue (n := n) e
        (wordExpansions normalizer recipes B rightWord) =
      (recipes.map fun R =>
        R.erasedShape.eval
            (HPAtom.eval
              (B.word.eval
                (HEAddres.freeLowerTruncation
                  (n := n)))
              (rightWord.eval
                (HEAddres.freeLowerTruncation
                  (n := n)))) ^
          BRSpec.coefficientValue R
            (B.coefficient.eval e) 1).prod := by
  induction recipes with
  | nil =>
      rfl
  | cons R recipes ih =>
      change
        (wordExpansion normalizer R B rightWord).value e *
            STExp.listValue e
              (wordExpansions normalizer recipes B rightWord) =
          _ * _
      rw [value_wordExpansion, ih]
      rfl

/-- Every output recipe word is physically strictly above its left parent. -/
lemma left_weight_expansion
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    B.word.weight HEAddres.weight <
      (wordExpansion normalizer R B rightWord).word.weight
        HEAddres.weight := by
  rw [wordExpansion, weight_boundWord]
  refine lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _
      (BRSpec.leftDegree_pos R)) ?_
  exact Nat.lt_add_of_pos_right
    (Nat.mul_pos
      (BRSpec.rightDegree_pos R)
      (CWord.weight_pos
        HEAddres.weight HEAddres.weight_pos rightWord))

/-- Every output recipe word is physically strictly above the unit right word. -/
lemma right_weight_expansion
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    rightWord.weight HEAddres.weight <
      (wordExpansion normalizer R B rightWord).word.weight
        HEAddres.weight := by
  rw [wordExpansion, weight_boundWord]
  refine lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _
      (BRSpec.rightDegree_pos R)) ?_
  rw [Nat.add_comm]
  exact Nat.lt_add_of_pos_right
    (Nat.mul_pos
      (BRSpec.leftDegree_pos R)
      (CWord.weight_pos
        HEAddres.weight HEAddres.weight_pos B.word))

end PIRed

namespace PFSubsti.TAPkt

/--
Unconditionally expand `[B ^ f, right]` without constructing a homogeneous
constant-one formula for the right parent.
-/
def rightTransientExpansions
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    List (STExp H ι) :=
  PIRed.wordExpansions
    normalizer packet.recipes B rightWord

/-- The one-sided transient packet evaluates exactly to its parent bracket. -/
lemma list_transient_expansions
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H))
    (e : ι → HEFam H) :
    STExp.listValue (n := n) e
        (packet.rightTransientExpansions normalizer B rightWord) =
      ⁅B.value (n := n) e,
        rightWord.eval
          (HEAddres.freeLowerTruncation
            (n := n))⁆ := by
  rw [rightTransientExpansions,
    PIRed.list_value_expansions]
  let Bvalue :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
    B.word.eval
      (HEAddres.freeLowerTruncation
        (H := H) (n := n))
  let rightValue :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
    rightWord.eval
      (HEAddres.freeLowerTruncation
        (H := H) (n := n))
  simpa [STExp.value] using
    packet.listEval_eq Bvalue rightValue (B.coefficient.eval e) 1

/--
Reword an ordinary parent factor onto an inner Hall word and expand its
commutator with an unpowered right Hall word.
-/
def innerTransientExpansions
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    List (STExp H ι) :=
  packet.rightTransientExpansions normalizer
    (STExp.rewordFactor factor innerWord)
    rightWord

/--
The unconditional inner-reduction packet evaluates to
`[inner ^ factor.coefficient, right]`.
-/
lemma inner_transient_expansions
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (e : ι → HEFam H) :
    STExp.listValue (n := n) e
        (packet.innerTransientExpansions normalizer factor
          innerWord rightWord) =
      ⁅innerWord.eval
            (HEAddres.freeLowerTruncation
              (n := n)) ^
          factor.coefficient.eval e,
        rightWord.eval
          (HEAddres.freeLowerTruncation
            (n := n))⁆ := by
  simpa [innerTransientExpansions,
    STExp.value,
    STExp.rewordFactor] using
      packet.list_transient_expansions normalizer
        (STExp.rewordFactor factor
          innerWord)
        rightWord e

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Two-sided transient polynomial Hall-Petresco substitution

After the first one-sided inner-reduction expansion, every output coefficient
is again a homogeneous Claim 8 formula.  Its arithmetic target weight may
still exceed the physical weight of the Hall word carrying it.  This file
closes those transient polynomial words under ordinary two-sided
Hall-Petresco substitution and proves exact packet semantics.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement
open HACoeff

namespace FTSubsti

/-- Substitute two transient polynomial Hall words into one block recipe. -/
def boundWord
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : BRecipe)
    (B A : STExp H ι) :
    CWord (HEAddres H) :=
  CWord.hallPairBind B.word A.word R.erasedShape

@[simp]
lemma weight_boundWord
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : BRecipe)
    (B A : STExp H ι) :
    (boundWord R B A).weight HEAddres.weight =
      R.leftDegree * B.word.weight HEAddres.weight +
        R.rightDegree * A.word.weight HEAddres.weight := by
  rw [boundWord, CWord.weight_pair_bind,
    CWord.pair_atom_degree,
    R.erased_left_degree, R.erased_shape_degree]

/--
Normalize the coefficient of one recipe while preserving separate arithmetic
and physical Hall-word weights.
-/
def coefficientFormula
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B A : STExp H ι) :
    WBForm H ι
      (R.leftDegree * B.coefficientWeight +
        R.rightDegree * A.coefficientWeight) :=
  let left :=
    normalizer.ringChooseProduct B.coefficient
      (BRSpec.positiveDegrees R.leftBlocks)
      (by
        apply List.ne_nil_of_length_pos
        exact
          BRSpec.length_degrees_pos
            (by
              simpa [BRecipe.leftDegree] using
                BRSpec.leftDegree_pos R))
      (fun degree hdegree =>
        BRSpec.positive_degrees_pos hdegree)
  let right :=
    normalizer.ringChooseProduct A.coefficient
      (BRSpec.positiveDegrees R.rightBlocks)
      (by
        apply List.ne_nil_of_length_pos
        exact
          BRSpec.length_degrees_pos
            (by
              simpa [BRecipe.rightDegree] using
                BRSpec.rightDegree_pos R))
      (fun degree hdegree =>
        BRSpec.positive_degrees_pos hdegree)
  left.mul right (by
    simp only [BRSpec.sum_positiveDegrees]
    rfl)

@[simp]
lemma eval_coefficientFormula
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (R : BRecipe)
    (B A : STExp H ι) :
    (coefficientFormula normalizer R B A).eval e =
      BRSpec.coefficientValue R
        (B.coefficient.eval e) (A.coefficient.eval e) := by
  simp only [coefficientFormula, WBForm.eval_mul,
    WBForm.RCNormal.ring_choose_product,
    BRSpec.coefficientValue,
    BRSpec.choose_positive_degrees]

/-- One transient recipe output with its honest arithmetic coefficient bound. -/
def wordExpansion
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B A : STExp H ι) :
    STExp H ι where
  word := boundWord R B A
  coefficientWeight :=
    R.leftDegree * B.coefficientWeight +
      R.rightDegree * A.coefficientWeight
  coefficient := coefficientFormula normalizer R B A

@[simp]
lemma coefficient_word_expansion
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B A : STExp H ι) :
    (wordExpansion normalizer R B A).coefficientWeight =
      R.leftDegree * B.coefficientWeight +
        R.rightDegree * A.coefficientWeight :=
  rfl

@[simp]
lemma word_weight_expansion
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B A : STExp H ι) :
    (wordExpansion normalizer R B A).word.weight HEAddres.weight =
      R.leftDegree * B.word.weight HEAddres.weight +
        R.rightDegree * A.word.weight HEAddres.weight :=
  weight_boundWord R B A

@[simp]
lemma value_wordExpansion
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (R : BRecipe)
    (B A : STExp H ι) :
    (wordExpansion normalizer R B A).value (n := n) e =
      R.erasedShape.eval
          (HPAtom.eval
            (B.word.eval
              (HEAddres.freeLowerTruncation
                (n := n)))
            (A.word.eval
              (HEAddres.freeLowerTruncation
                (n := n)))) ^
        BRSpec.coefficientValue R
          (B.coefficient.eval e) (A.coefficient.eval e) := by
  rw [STExp.value, wordExpansion,
    eval_coefficientFormula]
  exact congrArg
    (fun g =>
      g ^
        BRSpec.coefficientValue R
          (B.coefficient.eval e) (A.coefficient.eval e))
    (CWord.eval_pair_bind
      HEAddres.freeLowerTruncation B.word A.word
        R.erasedShape)

/-- Attach a finite ordered recipe list to two transient polynomial parents. -/
def wordExpansions
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (recipes : List BRecipe)
    (B A : STExp H ι) :
    List (STExp H ι) :=
  recipes.map fun R => wordExpansion normalizer R B A

/-- Evaluate an ordered list of transiently substituted recipes. -/
lemma list_value_expansions
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (recipes : List BRecipe)
    (B A : STExp H ι) :
    STExp.listValue (n := n) e
        (wordExpansions normalizer recipes B A) =
      (recipes.map fun R =>
        R.erasedShape.eval
            (HPAtom.eval
              (B.word.eval
                (HEAddres.freeLowerTruncation
                  (n := n)))
              (A.word.eval
                (HEAddres.freeLowerTruncation
                  (n := n)))) ^
          BRSpec.coefficientValue R
            (B.coefficient.eval e) (A.coefficient.eval e)).prod := by
  induction recipes with
  | nil =>
      rfl
  | cons R recipes ih =>
      change
        (wordExpansion normalizer R B A).value e *
            STExp.listValue e
              (wordExpansions normalizer recipes B A) =
          _ * _
      rw [value_wordExpansion, ih]
      rfl

/-- Every transient output is physically strictly above its left parent. -/
lemma left_weight_expansion
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B A : STExp H ι) :
    B.word.weight HEAddres.weight <
      (wordExpansion normalizer R B A).word.weight
        HEAddres.weight := by
  rw [word_weight_expansion]
  refine lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _
      (BRSpec.leftDegree_pos R)) ?_
  exact Nat.lt_add_of_pos_right
    (Nat.mul_pos
      (BRSpec.rightDegree_pos R)
      (CWord.weight_pos
        HEAddres.weight HEAddres.weight_pos A.word))

/-- Every transient output is physically strictly above its right parent. -/
lemma right_weight_expansion
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B A : STExp H ι) :
    A.word.weight HEAddres.weight <
      (wordExpansion normalizer R B A).word.weight
        HEAddres.weight := by
  rw [word_weight_expansion]
  refine lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _
      (BRSpec.rightDegree_pos R)) ?_
  rw [Nat.add_comm]
  exact Nat.lt_add_of_pos_right
    (Nat.mul_pos
      (BRSpec.leftDegree_pos R)
      (CWord.weight_pos
        HEAddres.weight HEAddres.weight_pos B.word))

/--
If both transient arithmetic bounds fit their parent words, the output bound
fits its substituted Hall word as well.
-/
lemma coefficient_weight_expansion
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B A : STExp H ι)
    (hB :
      B.coefficientWeight ≤ B.word.weight HEAddres.weight)
    (hA :
      A.coefficientWeight ≤ A.word.weight HEAddres.weight) :
    (wordExpansion normalizer R B A).coefficientWeight ≤
      (wordExpansion normalizer R B A).word.weight
        HEAddres.weight := by
  rw [coefficient_word_expansion, word_weight_expansion]
  exact Nat.add_le_add
    (Nat.mul_le_mul_left R.leftDegree hB)
    (Nat.mul_le_mul_left R.rightDegree hA)

end FTSubsti

namespace PFSubsti.TAPkt

/-- Unconditionally substitute two transient polynomial parents into a packet. -/
def polynomialTransientExpansions
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι) :
    List (STExp H ι) :=
  FTSubsti.wordExpansions
    normalizer packet.recipes B A

/-- The transient polynomial packet evaluates exactly to the parent bracket. -/
lemma value_transient_expansions
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (e : ι → HEFam H) :
    STExp.listValue (n := n) e
        (packet.polynomialTransientExpansions normalizer B A) =
      ⁅B.value (n := n) e, A.value (n := n) e⁆ := by
  rw [polynomialTransientExpansions,
    FTSubsti.list_value_expansions]
  let Bvalue :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
    B.word.eval
      (HEAddres.freeLowerTruncation
        (H := H) (n := n))
  let Avalue :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
    A.word.eval
      (HEAddres.freeLowerTruncation
        (H := H) (n := n))
  simpa [STExp.value] using
    packet.listEval_eq Bvalue Avalue
      (B.coefficient.eval e) (A.coefficient.eval e)

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Classifying transient polynomial inner-reduction packets

The first one-sided expansion of `[inner ^ f, right]` has two kinds of
outputs.  Recipes with `leftDegree ≤ rightDegree` have enough physical
right-word weight to absorb the inherited arithmetic coefficient bound and
return to ordinary polynomial factors.  Excess-left recipes remain transient.

This file classifies those outputs without changing packet order and proves
that the mixed packet still evaluates to the original outer bracket.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement
open HACoeff

namespace PIRed

/--
Specialize one recipe to an arbitrary rewording of an ordinary parent factor
and an unpowered right Hall word.
-/
def innerOuterExpansion
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    STExp H ι :=
  wordExpansion normalizer R
    (STExp.rewordFactor factor innerWord)
    rightWord

@[simp]
lemma coefficient_inner_expansion
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    (innerOuterExpansion normalizer R factor innerWord
      rightWord).coefficientWeight =
        R.leftDegree *
          factor.word.weight HEAddres.weight :=
  rfl

@[simp]
lemma inner_reduction_expansion
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    (innerOuterExpansion normalizer R factor innerWord
      rightWord).word.weight HEAddres.weight =
        R.leftDegree * innerWord.weight HEAddres.weight +
          R.rightDegree * rightWord.weight HEAddres.weight :=
  weight_boundWord R
    (STExp.rewordFactor factor innerWord)
    rightWord

@[simp]
lemma value_inner_expansion
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (R : BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    (innerOuterExpansion normalizer R factor innerWord
      rightWord).value (n := n) e =
        R.erasedShape.eval
            (HPAtom.eval
              (innerWord.eval
                (HEAddres.freeLowerTruncation
                  (n := n)))
              (rightWord.eval
                (HEAddres.freeLowerTruncation
                  (n := n)))) ^
          BRSpec.coefficientValue R
            (factor.coefficient.eval e) 1 := by
  exact value_wordExpansion normalizer e R
    (STExp.rewordFactor factor innerWord)
    rightWord

/--
The transient arithmetic bound fits its physical output word exactly on the
balanced side `leftDegree ≤ rightDegree`.
-/
lemma coeff_outer_expansion
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    (innerOuterExpansion normalizer R factor innerWord
        rightWord).coefficientWeight ≤
          (innerOuterExpansion normalizer R factor innerWord
            rightWord).word.weight HEAddres.weight ↔
      R.leftDegree ≤ R.rightDegree := by
  rw [coefficient_inner_expansion,
    inner_reduction_expansion, hword,
    CWord.weight_commutator]
  rw [Nat.mul_add, Nat.add_le_add_iff_left]
  exact Nat.mul_le_mul_right_iff
    (CWord.weight_pos
      HEAddres.weight HEAddres.weight_pos rightWord)

/-- Attach one balanced one-sided recipe output to the permanent factor API. -/
def attachedInnerFactor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hbalanced : R.leftDegree ≤ R.rightDegree) :
    SPFactor H ι :=
  (innerOuterExpansion normalizer R factor innerWord rightWord)
    |>.toFactor
      ((coeff_outer_expansion
        normalizer R factor innerWord rightWord hword).2 hbalanced)

@[simp]
lemma attached_inner_factor
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hbalanced : R.leftDegree ≤ R.rightDegree)
    (e : ι → HEFam H) :
    (attachedInnerFactor normalizer R factor innerWord rightWord
      hword hbalanced).eval (n := n) e =
        (innerOuterExpansion normalizer R factor innerWord
          rightWord).value e :=
  STExp.eval_toFactor _ _ e

end PIRed

/--
One ordered polynomial inner-reduction output is either permanently attached
or still a transient frontier obligation.
-/
inductive SITerm
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  | attached (factor : SPFactor H ι)
  | frontier
      (wordExpansion : STExp H ι)

namespace SITerm

/-- Evaluate one mixed attached-or-frontier polynomial output. -/
def value
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H) :
    SITerm H ι →
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  | .attached factor => factor.eval e
  | .frontier wordExpansion => wordExpansion.value e

/-- Evaluate a finite mixed packet without changing its order. -/
def listValue
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (terms : List (SITerm H ι)) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  (terms.map fun term => term.value e).prod

end SITerm

namespace PIRed

/--
Classify one initial inner-reduction recipe, attaching balanced outputs and
retaining excess-left outputs as transient frontier entries.
-/
def classifiedOuterTerm
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    SITerm H ι :=
  if hbalanced : R.leftDegree ≤ R.rightDegree then
    .attached
      (attachedInnerFactor normalizer R factor innerWord
        rightWord hword hbalanced)
  else
    .frontier
      (innerOuterExpansion normalizer R factor innerWord
        rightWord)

/-- A balanced recipe is classified as an attached permanent factor. -/
lemma classified_left_degree
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hbalanced : R.leftDegree ≤ R.rightDegree) :
    classifiedOuterTerm normalizer R factor innerWord rightWord
        hword =
      .attached
        (attachedInnerFactor normalizer R factor innerWord
          rightWord hword hbalanced) := by
  simp [classifiedOuterTerm, hbalanced]

/-- An excess-left recipe remains a transient frontier entry. -/
lemma classified_inner_outer
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfrontier : R.rightDegree < R.leftDegree) :
    classifiedOuterTerm normalizer R factor innerWord rightWord
        hword =
      .frontier
        (innerOuterExpansion normalizer R factor innerWord
          rightWord) := by
  simp [classifiedOuterTerm, Nat.not_le_of_lt hfrontier]

/-- Classifying one recipe preserves the transient value it represents. -/
lemma value_classified_term
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (e : ι → HEFam H) :
    (classifiedOuterTerm normalizer R factor innerWord rightWord
      hword).value (n := n) e =
        (innerOuterExpansion normalizer R factor innerWord
          rightWord).value e := by
  by_cases hbalanced : R.leftDegree ≤ R.rightDegree
  · simp [classifiedOuterTerm, hbalanced,
      SITerm.value]
  · simp [classifiedOuterTerm, hbalanced,
      SITerm.value]

/-- Classifying an ordered recipe list preserves its transient product. -/
lemma classifiedInnerOuter
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (recipes : List BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (e : ι → HEFam H) :
    SITerm.listValue (n := n) e
        (recipes.map fun R =>
          classifiedOuterTerm normalizer R factor innerWord
            rightWord hword) =
      STExp.listValue (n := n) e
        (recipes.map fun R =>
          innerOuterExpansion normalizer R factor innerWord
            rightWord) := by
  induction recipes with
  | nil =>
      rfl
  | cons R recipes ih =>
      change
        (classifiedOuterTerm normalizer R factor innerWord
              rightWord hword).value e *
            SITerm.listValue e
              (recipes.map fun nextR =>
                classifiedOuterTerm normalizer nextR factor
                  innerWord rightWord hword) =
          (innerOuterExpansion normalizer R factor innerWord
                rightWord).value e *
            STExp.listValue e
              (recipes.map fun nextR =>
                innerOuterExpansion normalizer nextR factor
                  innerWord rightWord)
      rw [value_classified_term, ih]

end PIRed

namespace PFSubsti.TAPkt

/-- Classify every initial polynomial inner-reduction term in packet order. -/
def outerClassifiedTerms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    List (SITerm H ι) :=
  packet.recipes.map fun R =>
    PIRed.classifiedOuterTerm
      normalizer R factor innerWord rightWord hword

/-- The classified mixed packet evaluates exactly to the parent bracket. -/
lemma reduction_classified_terms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (e : ι → HEFam H) :
    SITerm.listValue (n := n) e
        (packet.outerClassifiedTerms normalizer factor
          innerWord rightWord hword) =
      ⁅innerWord.eval
            (HEAddres.freeLowerTruncation
              (n := n)) ^
          factor.coefficient.eval e,
        rightWord.eval
          (HEAddres.freeLowerTruncation
            (n := n))⁆ := by
  rw [outerClassifiedTerms,
    PIRed.classifiedInnerOuter]
  simpa [innerTransientExpansions,
    rightTransientExpansions,
    PIRed.wordExpansions,
    PIRed.innerOuterExpansion] using
      packet.inner_transient_expansions normalizer
        factor innerWord rightWord e

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Weight descent on the transient polynomial inner-reduction frontier

Excess-left outputs of transient polynomial inner reduction are not yet
ordinary bounded factors, but their physical Hall words already lie strictly
above the parent bracket.  Their cutoff defects therefore decrease, and they
vanish once their physical words reach the truncation cutoff.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HACoeff

namespace STExp

/--
A transient polynomial word lies in the lower-central layer predicted by its
physical Hall-word weight, independently of its arithmetic coefficient bound.
-/
lemma value_central_series
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (wordExpansion : STExp H ι) :
    wordExpansion.value (n := n) e ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (wordExpansion.word.weight HEAddres.weight - 1) := by
  exact
    (Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (wordExpansion.word.weight HEAddres.weight - 1)).zpow_mem
        (CWord.eval_lower_series
          HEAddres.freeLowerTruncation
          HEAddres.weight
          HEAddres.weight_pos
          HEAddres.free_truncation_series
          wordExpansion.word)
        (wordExpansion.coefficient.eval e)

/-- A transient polynomial word at the cutoff evaluates trivially. -/
lemma value_n_weight
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (wordExpansion : STExp H ι)
    (hweight :
      n ≤ wordExpansion.word.weight HEAddres.weight) :
    wordExpansion.value (n := n) e = 1 := by
  apply eq_bot_iff.mp
    SCFactor.trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (Nat.sub_le_sub_right hweight 1)
    (wordExpansion.value_central_series e)

/-- A transient packet supported at the cutoff evaluates trivially. -/
lemma list_value_n
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (wordExpansions :
      List (STExp H ι))
    (hweight :
      ∀ wordExpansion ∈ wordExpansions,
        n ≤ wordExpansion.word.weight HEAddres.weight) :
    STExp.listValue (n := n) e
        wordExpansions =
      1 := by
  induction wordExpansions with
  | nil =>
      rfl
  | cons wordExpansion wordExpansions ih =>
      change wordExpansion.value e *
          STExp.listValue e
            wordExpansions =
        1
      rw [wordExpansion.value_n_weight e
        (hweight wordExpansion (by simp)),
        ih (fun next hnext => hweight next (by simp [hnext]))]
      exact one_mul 1

end STExp

namespace PIRed

/-- An excess-left recipe uses its left parent at least twice. -/
lemma left_degree_right
    (R : BRecipe)
    (hfrontier : R.rightDegree < R.leftDegree) :
    1 < R.leftDegree := by
  have hrightPos := BRSpec.rightDegree_pos R
  omega

/--
Every excess-left transient output is physically strictly heavier than its
original outer bracket.
-/
lemma factor_inner_degree
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfrontier : R.rightDegree < R.leftDegree) :
    factor.word.weight HEAddres.weight <
      (innerOuterExpansion normalizer R factor innerWord
        rightWord).word.weight HEAddres.weight := by
  rw [inner_reduction_expansion, hword,
    CWord.weight_commutator]
  have hinnerPos :=
    CWord.weight_pos
      HEAddres.weight HEAddres.weight_pos innerWord
  have hrightPos :=
    CWord.weight_pos
      HEAddres.weight HEAddres.weight_pos rightWord
  have hleftDegree := left_degree_right R hfrontier
  have hrightDegree :=
    BRSpec.rightDegree_pos R
  have hinnerLt :
      innerWord.weight HEAddres.weight <
        R.leftDegree * innerWord.weight HEAddres.weight := by
    simpa using Nat.mul_lt_mul_of_pos_right hleftDegree hinnerPos
  have hrightLe :
      rightWord.weight HEAddres.weight ≤
        R.rightDegree * rightWord.weight HEAddres.weight :=
    Nat.le_mul_of_pos_left _ hrightDegree
  exact add_lt_add_of_lt_of_le hinnerLt hrightLe

/-- Every excess-left output has smaller cutoff defect than its parent. -/
lemma defect_inner_degree
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfrontier : R.rightDegree < R.leftDegree)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    n -
          (innerOuterExpansion normalizer R factor innerWord
            rightWord).word.weight HEAddres.weight <
      SPFactor.cutoffDefect n factor := by
  rw [SPFactor.cutoffDefect]
  have hweight :=
    factor_inner_degree
      normalizer R factor innerWord rightWord hword hfrontier
  omega

end PIRed

namespace PFSubsti.TAPkt

open PIRed

/-- Packet recipes that remain on the transient polynomial excess-left frontier. -/
def innerFrontierRecipes
    {d n : ℕ}
    (packet :
      PFSubsti.TAPkt d n) :
    List BRecipe :=
  packet.recipes.filter fun R => decide (R.rightDegree < R.leftDegree)

@[simp]
lemma inner_frontier_recipes
    {d n : ℕ}
    (packet :
      PFSubsti.TAPkt d n)
    (R : BRecipe) :
    R ∈ packet.innerFrontierRecipes ↔
      R ∈ packet.recipes ∧ R.rightDegree < R.leftDegree := by
  simp [innerFrontierRecipes]

/-- The ordered transient polynomial expansions left after balanced attachment. -/
def innerFrontierExpansions
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    List (STExp H ι) :=
  packet.innerFrontierRecipes.map fun R =>
    innerOuterExpansion normalizer R factor innerWord rightWord

/-- Every retained frontier expansion comes from an excess-left packet recipe. -/
lemma recipe_frontier_expansions
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    {wordExpansion : STExp H ι}
    (hwordExpansion :
      wordExpansion ∈
        packet.innerFrontierExpansions normalizer
          factor innerWord rightWord) :
    ∃ R ∈ packet.innerFrontierRecipes,
      wordExpansion =
        innerOuterExpansion normalizer R factor innerWord
          rightWord := by
  rcases List.mem_map.mp hwordExpansion with ⟨R, hR, hwordExpansion⟩
  exact ⟨R, hR, hwordExpansion.symm⟩

/-- Every retained frontier expansion is physically heavier than its parent. -/
lemma inner_frontier_expansions
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    {wordExpansion : STExp H ι}
    (hwordExpansion :
      wordExpansion ∈
        packet.innerFrontierExpansions normalizer
          factor innerWord rightWord) :
    factor.word.weight HEAddres.weight <
      wordExpansion.word.weight HEAddres.weight := by
  rcases
      packet.recipe_frontier_expansions
        normalizer factor innerWord rightWord hwordExpansion with
    ⟨R, hR, rfl⟩
  exact
    factor_inner_degree
      normalizer R factor innerWord rightWord hword
        ((packet.inner_frontier_recipes R).mp hR).2

/-- Each retained frontier expansion has smaller cutoff defect than its parent. -/
lemma defect_frontier_expansions
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    {wordExpansion : STExp H ι}
    (hwordExpansion :
      wordExpansion ∈
        packet.innerFrontierExpansions normalizer
          factor innerWord rightWord) :
    n - wordExpansion.word.weight HEAddres.weight <
      SPFactor.cutoffDefect n factor := by
  have hweight :=
    packet.inner_frontier_expansions
      normalizer factor innerWord rightWord hword hwordExpansion
  rw [SPFactor.cutoffDefect]
  omega

/-- At the next cutoff stratum the entire transient frontier vanishes. -/
lemma poly_inner_succ
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ factor.word.weight HEAddres.weight + 1)
    (e : ι → HEFam H) :
    STExp.listValue (n := n) e
        (packet.innerFrontierExpansions normalizer
          factor innerWord rightWord) =
      1 := by
  apply
    STExp.list_value_n
  intro wordExpansion hwordExpansion
  exact hcutoff.trans
    (Nat.succ_le_of_lt
      (packet.inner_frontier_expansions
        normalizer factor innerWord rightWord hword hwordExpansion))

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Classifying arbitrary transient polynomial Hall-Petresco packets

Recursive transient recollection expands frontier obligations, not only the
first inner reduction of an ordinary polynomial factor.  This file classifies
an arbitrary two-sided transient substitution.  Attachable outputs return to
the permanent polynomial factor API; the remaining frontier entries preserve
packet order and have strictly deeper physical Hall words than either parent.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

namespace FTSubsti

/-- Classify one arbitrary transient recipe output by its exact attachability. -/
def classifiedTransientTerm
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : HACoeff.BRecipe)
    (B A : STExp H ι) :
    SITerm H ι :=
  let expansion := wordExpansion normalizer R B A
  if hweight :
      expansion.coefficientWeight ≤
        expansion.word.weight HEAddres.weight then
    .attached (expansion.toFactor hweight)
  else
    .frontier expansion

/-- An attachable transient output returns to the permanent factor API. -/
lemma classified_attached_coefficient
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : HACoeff.BRecipe)
    (B A : STExp H ι)
    (hweight :
      (wordExpansion normalizer R B A).coefficientWeight ≤
        (wordExpansion normalizer R B A).word.weight
          HEAddres.weight) :
    classifiedTransientTerm normalizer R B A =
      .attached ((wordExpansion normalizer R B A).toFactor hweight) := by
  unfold classifiedTransientTerm
  dsimp only
  rw [dif_pos hweight]

/-- A nonattachable transient output remains a frontier obligation. -/
lemma classified_transient_not
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : HACoeff.BRecipe)
    (B A : STExp H ι)
    (hweight :
      ¬ (wordExpansion normalizer R B A).coefficientWeight ≤
        (wordExpansion normalizer R B A).word.weight
          HEAddres.weight) :
    classifiedTransientTerm normalizer R B A =
      .frontier (wordExpansion normalizer R B A) := by
  unfold classifiedTransientTerm
  dsimp only
  rw [dif_neg hweight]

/-- Classification preserves the represented transient value. -/
lemma classified_transient
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : HACoeff.BRecipe)
    (B A : STExp H ι)
    (e : ι → HEFam H) :
    (classifiedTransientTerm normalizer R B A).value (n := n) e =
      (wordExpansion normalizer R B A).value e := by
  by_cases hweight :
      (wordExpansion normalizer R B A).coefficientWeight ≤
        (wordExpansion normalizer R B A).word.weight HEAddres.weight
  · rw [classified_attached_coefficient
      normalizer R B A hweight]
    exact STExp.eval_toFactor _ _ e
  · rw [classified_transient_not
      normalizer R B A hweight]
    rfl

/-- Classifying an ordered recipe list preserves its transient product. -/
lemma list_classified_transient
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (recipes : List HACoeff.BRecipe)
    (B A : STExp H ι)
    (e : ι → HEFam H) :
    SITerm.listValue (n := n) e
        (recipes.map fun R => classifiedTransientTerm normalizer R B A) =
      STExp.listValue (n := n) e
        (recipes.map fun R => wordExpansion normalizer R B A) := by
  induction recipes with
  | nil =>
      rfl
  | cons R recipes ih =>
      change
        (classifiedTransientTerm normalizer R B A).value e *
            SITerm.listValue e
              (recipes.map fun nextR =>
                classifiedTransientTerm normalizer nextR B A) =
          (wordExpansion normalizer R B A).value e *
            STExp.listValue e
              (recipes.map fun nextR => wordExpansion normalizer nextR B A)
      rw [classified_transient, ih]

/-- Any arbitrary transient output has smaller cutoff defect than its left parent. -/
lemma cutoff_defect_left
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : HACoeff.BRecipe)
    (B A : STExp H ι)
    (hB : B.word.weight HEAddres.weight < n) :
    n - (wordExpansion normalizer R B A).word.weight HEAddres.weight <
      n - B.word.weight HEAddres.weight := by
  have hweight :=
    left_weight_expansion normalizer R B A
  omega

/-- Any arbitrary transient output has smaller cutoff defect than its right parent. -/
lemma cutoff_defect_right
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : HACoeff.BRecipe)
    (B A : STExp H ι)
    (hA : A.word.weight HEAddres.weight < n) :
    n - (wordExpansion normalizer R B A).word.weight HEAddres.weight <
      n - A.word.weight HEAddres.weight := by
  have hweight :=
    right_weight_expansion normalizer R B A
  omega

end FTSubsti

namespace PFSubsti.TAPkt

open FTSubsti

/-- Classify an arbitrary two-sided transient packet without changing order. -/
def polynomialTransientTerms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι) :
    List (SITerm H ι) :=
  packet.recipes.map fun R => classifiedTransientTerm normalizer R B A

/-- The classified arbitrary transient packet evaluates to its parent bracket. -/
lemma list_transient_terms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (e : ι → HEFam H) :
    SITerm.listValue (n := n) e
        (packet.polynomialTransientTerms normalizer B A) =
      ⁅B.value (n := n) e, A.value (n := n) e⁆ := by
  rw [polynomialTransientTerms,
    FTSubsti.list_classified_transient]
  simpa [polynomialTransientExpansions,
    FTSubsti.wordExpansions] using
      packet.value_transient_expansions normalizer B A e

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Multiset descent for classified transient polynomial packets

Attached polynomial outputs are terminal for transient recursion.  Frontier
outputs remain obligations, measured only by cutoff minus physical Hall-word
weight.  This file packages that measure and proves strict descent for both
the initial one-sided inner-reduction packet and arbitrary recursive
two-sided substitutions.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace SITerm

/-- Cutoff defects carried only by transient frontier entries. -/
def frontierDefectMultiset
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ) :
    List (SITerm H ι) →
      Multiset ℕ
  | [] => ∅
  | .attached _ :: terms => frontierDefectMultiset n terms
  | .frontier wordExpansion :: terms =>
      {n - wordExpansion.word.weight HEAddres.weight} +
        frontierDefectMultiset n terms

@[simp]
lemma frontier_multiset_nil
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type} :
    frontierDefectMultiset (H := H) (ι := ι) n
        ([] : List (SITerm H ι)) =
      ∅ :=
  rfl

@[simp]
lemma multiset_cons_attached
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι)
    (terms : List (SITerm H ι)) :
    frontierDefectMultiset n (.attached factor :: terms) =
      frontierDefectMultiset n terms :=
  rfl

@[simp]
lemma frontier_multiset_cons
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (wordExpansion : STExp H ι)
    (terms : List (SITerm H ι)) :
    frontierDefectMultiset n (.frontier wordExpansion :: terms) =
      {n - wordExpansion.word.weight HEAddres.weight} +
        frontierDefectMultiset n terms :=
  rfl

/-- Ordered mixed packets inherit Dershowitz-Manna frontier-defect descent. -/
def FrontierDefectMultiset
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ)
    (left right : List (SITerm H ι)) :
    Prop :=
  Multiset.IsDershowitzMannaLT
    (frontierDefectMultiset n left)
    (frontierDefectMultiset n right)

/-- Frontier-defect descent on mixed polynomial packets is well founded. -/
lemma well_founded_multiset
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type} :
    WellFounded (FrontierDefectMultiset (H := H) (ι := ι) n) :=
  InvImage.wf
    (frontierDefectMultiset (H := H) (ι := ι) n)
    Multiset.wellFounded_isDershowitzMannaLT

end SITerm

namespace PIRed

/-- Every initial excess-left frontier defect is smaller than its parent defect. -/
lemma cutoff_multiset_classified
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (recipes : List HACoeff.BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    ∀ defect ∈
        SITerm.frontierDefectMultiset n
          (recipes.map fun R =>
            classifiedOuterTerm normalizer R factor innerWord
              rightWord hword),
      defect < SPFactor.cutoffDefect n factor := by
  induction recipes with
  | nil =>
      simp
  | cons R recipes ih =>
      simp only [List.map_cons]
      by_cases hbalanced : R.leftDegree ≤ R.rightDegree
      · rw [classified_left_degree
          normalizer R factor innerWord rightWord hword hbalanced]
        simpa using ih
      · have hfrontier : R.rightDegree < R.leftDegree :=
          Nat.lt_of_not_ge hbalanced
        rw [classified_inner_outer
          normalizer R factor innerWord rightWord hword hfrontier]
        intro defect hdefect
        simp only [
          SITerm.frontier_multiset_cons,
          Multiset.mem_add, Multiset.mem_singleton] at hdefect
        rcases hdefect with rfl | hdefect
        · exact defect_inner_degree
            normalizer R factor innerWord rightWord hword hfrontier
              hfactorTruncated
        · exact ih defect hdefect

end PIRed

namespace FTSubsti

/-- Recursive frontier defects strictly decrease from the left transient parent. -/
lemma forall_frontier_left
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (recipes : List HACoeff.BRecipe)
    (B A : STExp H ι)
    (hB : B.word.weight HEAddres.weight < n) :
    ∀ defect ∈
        SITerm.frontierDefectMultiset n
          (recipes.map fun R => classifiedTransientTerm normalizer R B A),
      defect < n - B.word.weight HEAddres.weight := by
  induction recipes with
  | nil =>
      simp
  | cons R recipes ih =>
      simp only [List.map_cons]
      by_cases hweight :
          (wordExpansion normalizer R B A).coefficientWeight ≤
            (wordExpansion normalizer R B A).word.weight
              HEAddres.weight
      · rw [classified_attached_coefficient
          normalizer R B A hweight]
        simpa using ih
      · rw [classified_transient_not
          normalizer R B A hweight]
        intro defect hdefect
        simp only [
          SITerm.frontier_multiset_cons,
          Multiset.mem_add, Multiset.mem_singleton] at hdefect
        rcases hdefect with rfl | hdefect
        · exact cutoff_defect_left normalizer R B A hB
        · exact ih defect hdefect

/-- Recursive frontier defects strictly decrease from the right transient parent. -/
lemma forall_frontier_transient
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (recipes : List HACoeff.BRecipe)
    (B A : STExp H ι)
    (hA : A.word.weight HEAddres.weight < n) :
    ∀ defect ∈
        SITerm.frontierDefectMultiset n
          (recipes.map fun R => classifiedTransientTerm normalizer R B A),
      defect < n - A.word.weight HEAddres.weight := by
  induction recipes with
  | nil =>
      simp
  | cons R recipes ih =>
      simp only [List.map_cons]
      by_cases hweight :
          (wordExpansion normalizer R B A).coefficientWeight ≤
            (wordExpansion normalizer R B A).word.weight
              HEAddres.weight
      · rw [classified_attached_coefficient
          normalizer R B A hweight]
        simpa using ih
      · rw [classified_transient_not
          normalizer R B A hweight]
        intro defect hdefect
        simp only [
          SITerm.frontier_multiset_cons,
          Multiset.mem_add, Multiset.mem_singleton] at hdefect
        rcases hdefect with rfl | hdefect
        · exact cutoff_defect_right normalizer R B A hA
        · exact ih defect hdefect

end FTSubsti

namespace PFSubsti.TAPkt

/-- The complete initial mixed packet has only smaller recursive defects. -/
lemma forall_classified_terms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    ∀ defect ∈
        SITerm.frontierDefectMultiset n
          (packet.outerClassifiedTerms normalizer
            factor innerWord rightWord hword),
      defect < SPFactor.cutoffDefect n factor := by
  rw [outerClassifiedTerms]
  exact
    PIRed.cutoff_multiset_classified
      normalizer packet.recipes factor innerWord rightWord hword
        hfactorTruncated

/-- Replacing one initial parent by its classified packet strictly descends. -/
lemma frontierMultisetSingleton
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    Multiset.IsDershowitzMannaLT
      (SITerm.frontierDefectMultiset n
        (packet.outerClassifiedTerms normalizer factor
          innerWord rightWord hword))
      {SPFactor.cutoffDefect n factor} :=
  by
    simpa using
      (Multiset.dershowitz_manna_forall
        (X := ∅)
        (packet.forall_classified_terms
          normalizer factor innerWord rightWord hword hfactorTruncated))

/-- The initial classified packet descends from the singleton reworded parent. -/
lemma polyMultisetReword
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    SITerm.FrontierDefectMultiset n
      (packet.outerClassifiedTerms normalizer factor
        innerWord rightWord hword)
      [.frontier
        (STExp.rewordFactor factor
          factor.word)] := by
  simpa [
    SITerm.FrontierDefectMultiset,
    SPFactor.cutoffDefect,
    STExp.rewordFactor] using
      packet.frontierMultisetSingleton
        normalizer factor innerWord rightWord hword hfactorTruncated

/-- Recursive two-sided packets have only smaller defects than their left parent. -/
lemma forall_defect_multiset
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hB : B.word.weight HEAddres.weight < n) :
    ∀ defect ∈
        SITerm.frontierDefectMultiset n
          (packet.polynomialTransientTerms normalizer B A),
      defect < n - B.word.weight HEAddres.weight := by
  rw [polynomialTransientTerms]
  exact
    FTSubsti.forall_frontier_left
      normalizer packet.recipes B A hB

/-- Recursive two-sided packets have only smaller defects than their right parent. -/
lemma forall_multiset_classified
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hA : A.word.weight HEAddres.weight < n) :
    ∀ defect ∈
        SITerm.frontierDefectMultiset n
          (packet.polynomialTransientTerms normalizer B A),
      defect < n - A.word.weight HEAddres.weight := by
  rw [polynomialTransientTerms]
  exact
    FTSubsti.forall_frontier_transient
      normalizer packet.recipes B A hA

/-- A recursive classified packet descends from its left frontier parent. -/
lemma frontier_defect_multiset
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hB : B.word.weight HEAddres.weight < n) :
    Multiset.IsDershowitzMannaLT
      (SITerm.frontierDefectMultiset n
        (packet.polynomialTransientTerms normalizer B A))
      {n - B.word.weight HEAddres.weight} := by
  simpa using
    (Multiset.dershowitz_manna_forall
      (X := ∅)
      (packet.forall_defect_multiset
        normalizer B A hB))

/-- A recursive classified packet descends from its right frontier parent. -/
lemma frontier_multiset_classified
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hA : A.word.weight HEAddres.weight < n) :
    Multiset.IsDershowitzMannaLT
      (SITerm.frontierDefectMultiset n
        (packet.polynomialTransientTerms normalizer B A))
      {n - A.word.weight HEAddres.weight} := by
  simpa using
    (Multiset.dershowitz_manna_forall
      (X := ∅)
      (packet.forall_multiset_classified
        normalizer B A hA))

/-- Callback-shaped recursive descent from the left singleton frontier task. -/
lemma polyClassifiedSingleton
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hB : B.word.weight HEAddres.weight < n) :
    SITerm.FrontierDefectMultiset n
      (packet.polynomialTransientTerms normalizer B A)
      [.frontier B] := by
  simpa [
    SITerm.FrontierDefectMultiset] using
      packet.frontier_defect_multiset
        normalizer B A hB

/-- Callback-shaped recursive descent from the right singleton frontier task. -/
lemma polyTransientClassified
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hA : A.word.weight HEAddres.weight < n) :
    SITerm.FrontierDefectMultiset n
      (packet.polynomialTransientTerms normalizer B A)
      [.frontier A] := by
  simpa [
    SITerm.FrontierDefectMultiset] using
      packet.frontier_multiset_classified
        normalizer B A hA

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Provenance of generic transient polynomial frontiers

The arbitrary transient polynomial classifier retains only nonattachable
outputs on its frontier.  Contextual resolvers need to recover the source
Hall-Petresco recipe of each retained entry without changing packet order.

This file records that provenance and strict physical-weight growth from both
transient parents.  It is intentionally not imported by the existing
collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace FTSubsti

/-- A retained generic frontier entry comes from one nonattachable recipe. -/
lemma frontier_classified_transient
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {normalizer :
      WBForm.RCNormal H ι}
    {recipes : List HACoeff.BRecipe}
    {B A expansion : STExp H ι}
    (hexpansion :
      .frontier expansion ∈
        recipes.map fun R => classifiedTransientTerm normalizer R B A) :
    ∃ R ∈ recipes,
      ¬ (wordExpansion normalizer R B A).coefficientWeight ≤
          (wordExpansion normalizer R B A).word.weight
            HEAddres.weight ∧
        expansion = wordExpansion normalizer R B A := by
  rcases List.mem_map.mp hexpansion with ⟨R, hR, hterm⟩
  refine ⟨R, hR, ?_, ?_⟩
  · intro hweight
    rw [classified_attached_coefficient
      normalizer R B A hweight] at hterm
    cases hterm
  · by_cases hweight :
        (wordExpansion normalizer R B A).coefficientWeight ≤
          (wordExpansion normalizer R B A).word.weight
            HEAddres.weight
    · rw [classified_attached_coefficient
        normalizer R B A hweight] at hterm
      cases hterm
    · rw [classified_transient_not
        normalizer R B A hweight] at hterm
      cases hterm
      rfl

end FTSubsti

namespace PFSubsti.TAPkt

open FTSubsti

/-- A retained packet frontier entry remembers its source recipe. -/
lemma recipe_classified_frontier
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A expansion : STExp H ι)
    (hexpansion :
      .frontier expansion ∈
        packet.polynomialTransientTerms normalizer B A) :
    ∃ R ∈ packet.recipes,
      ¬ (wordExpansion normalizer R B A).coefficientWeight ≤
          (wordExpansion normalizer R B A).word.weight
            HEAddres.weight ∧
        expansion = wordExpansion normalizer R B A := by
  rw [polynomialTransientTerms] at hexpansion
  exact frontier_classified_transient hexpansion

/-- Every retained generic frontier entry is physically above its left parent. -/
lemma left_classified_frontier
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A expansion : STExp H ι)
    (hexpansion :
      .frontier expansion ∈
        packet.polynomialTransientTerms normalizer B A) :
    B.word.weight HEAddres.weight <
      expansion.word.weight HEAddres.weight := by
  rcases
      packet.recipe_classified_frontier
        normalizer B A expansion hexpansion with
    ⟨R, _, _, rfl⟩
  exact left_weight_expansion normalizer R B A

/-- Every retained generic frontier entry is physically above its right parent. -/
lemma transient_terms_frontier
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A expansion : STExp H ι)
    (hexpansion :
      .frontier expansion ∈
        packet.polynomialTransientTerms normalizer B A) :
    A.word.weight HEAddres.weight <
      expansion.word.weight HEAddres.weight := by
  rcases
      packet.recipe_classified_frontier
        normalizer B A expansion hexpansion with
    ⟨R, _, _, rfl⟩
  exact right_weight_expansion normalizer R B A

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Recollection interface for transient polynomial frontiers

An excess-left transient polynomial word cannot yet be attached to the
permanent signed-factor language, but its physical Hall-word weight is
strictly larger than the parent bracket.  This file isolates the recursive
singleton input needed to recollect such words and lifts it over an ordered
initial frontier packet.  Words at the nilpotent cutoff erase immediately.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/-- Recollect an ordered transient polynomial source into permanent factors. -/
structure TTRecolla
    {d : ℕ}
    (n lowerWeight : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    {ι : Type}
    (rawSource :
      List (STExp H ι)) where
  higherSource :
    List (SPFactor H ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_weight_least :
    SPFactor.WordWeightLeast lowerWeight higherSource
  list_higher_raw :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e higherSource =
        STExp.listValue (n := n) e
          rawSource

namespace TTRecolla

/-- The empty transient polynomial source recollects to itself. -/
def empty
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type} :
    TTRecolla
      n lowerWeight H
        ([] : List (STExp H ι)) where
  higherSource := []
  higher_source_truncated := by
    intro factor hfactor
    simp at hfactor
  higher_weight_least := by
    intro factor hfactor
    simp at hfactor
  list_higher_raw := by
    intro e
    rfl

/-- Concatenate independently recollected transient polynomial sources. -/
def append
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {leftSource rightSource :
      List (STExp H ι)}
    (left :
      TTRecolla
        n lowerWeight H leftSource)
    (right :
      TTRecolla
        n lowerWeight H rightSource) :
    TTRecolla
      n lowerWeight H (leftSource ++ rightSource) where
  higherSource := left.higherSource ++ right.higherSource
  higher_source_truncated := by
    intro factor hfactor
    rcases List.mem_append.mp hfactor with hfactor | hfactor
    · exact left.higher_source_truncated factor hfactor
    · exact right.higher_source_truncated factor hfactor
  higher_weight_least := by
    intro factor hfactor
    rcases List.mem_append.mp hfactor with hfactor | hfactor
    · exact left.higher_weight_least factor hfactor
    · exact right.higher_weight_least factor hfactor
  list_higher_raw := by
    intro e
    rw [SPFactor.listEval_append,
      left.list_higher_raw,
      right.list_higher_raw]
    simp [STExp.listValue]

/-- Lower the requested physical support bound. -/
def weaken
    {d n lowerWeight weakerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {rawSource :
      List (STExp H ι)}
    (recollection :
      TTRecolla
        n lowerWeight H rawSource)
    (hweight : weakerWeight ≤ lowerWeight) :
    TTRecolla
      n weakerWeight H rawSource where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least := fun factor hfactor =>
    hweight.trans
      (recollection.higher_weight_least factor hfactor)
  list_higher_raw :=
    recollection.list_higher_raw

/-- A transient singleton at the truncation cutoff recollects to the empty source. -/
def singleton_n_weight
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (wordExpansion : STExp H ι)
    (hweight :
      n ≤ wordExpansion.word.weight HEAddres.weight) :
    TTRecolla
      n lowerWeight H [wordExpansion] where
  higherSource := []
  higher_source_truncated := by
    intro factor hfactor
    simp at hfactor
  higher_weight_least := by
    intro factor hfactor
    simp at hfactor
  list_higher_raw := by
    intro e
    simp [STExp.listValue,
      wordExpansion.value_n_weight e hweight]

/-- Compose singleton transient recollections without changing order. -/
def of_singletons
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (rawSource :
      List (STExp H ι))
    (recollection :
      ∀ wordExpansion ∈ rawSource,
        TTRecolla
          n lowerWeight H [wordExpansion]) :
    TTRecolla
      n lowerWeight H rawSource := by
  induction rawSource with
  | nil =>
      exact empty
  | cons head tail ih =>
      simpa using
        (append
          (recollection head (by simp))
          (ih fun wordExpansion hwordExpansion =>
            recollection wordExpansion (by simp [hwordExpansion])))

end TTRecolla

/-- Recursive collector for one active transient polynomial word. -/
structure TRFtry
    (d n : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  sourceRecollection :
    ∀ wordExpansion : STExp H ι,
      wordExpansion.word.weight HEAddres.weight < n →
        TTRecolla
          n (wordExpansion.word.weight HEAddres.weight)
            H [wordExpansion]

namespace
  TRFtry

/-- Delegate active singleton words and erase words already at the cutoff. -/
noncomputable def recollectionOrEmpty
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TRFtry
        d n H ι)
    (wordExpansion : STExp H ι) :
    TTRecolla
      n (wordExpansion.word.weight HEAddres.weight)
        H [wordExpansion] := by
  by_cases hweight :
      wordExpansion.word.weight HEAddres.weight < n
  · exact factory.sourceRecollection wordExpansion hweight
  · exact
      TTRecolla.singleton_n_weight
        wordExpansion (Nat.le_of_not_gt hweight)

end
  TRFtry

namespace PFSubsti.TAPkt

open
  TRFtry

/-- Recollect the ordered initial excess-left frontier through singleton callbacks. -/
noncomputable def
    recollection_frontier_expansions
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TRFtry
        d n H ι)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecolla
      n (factor.word.weight HEAddres.weight + 1) H
        (packet.innerFrontierExpansions normalizer
          factor innerWord rightWord) :=
  TTRecolla.of_singletons _
    fun wordExpansion hwordExpansion =>
      (factory.recollectionOrEmpty wordExpansion).weaken
        (Nat.succ_le_of_lt
          (packet.inner_frontier_expansions
            normalizer factor innerWord rightWord hword hwordExpansion))

/-- At the next stratum endpoint, the whole initial frontier erases directly. -/
def
    frontier_expansions_terminal
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ factor.word.weight HEAddres.weight + 1) :
    TTRecolla
      n lowerWeight H
        (packet.innerFrontierExpansions normalizer
          factor innerWord rightWord) where
  higherSource := []
  higher_source_truncated := by
    intro replacement hreplacement
    simp at hreplacement
  higher_weight_least := by
    intro replacement hreplacement
    simp at hreplacement
  list_higher_raw := by
    intro e
    simpa using
      (packet.poly_inner_succ
        normalizer factor innerWord rightWord hword hcutoff e).symm

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Well-founded recursion on contextual transient polynomial packets

Transient polynomial inner reduction recurses on complete ordered classified
packets.  Attached factors and frontier words stay interleaved until contextual
recollection resolves them.  The frontier-defect multiset relation already
proves this recursion well founded.

This file packages the generic executable fixpoint and its unfolding equation.
It is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u v

/-- One resolver step for well-founded recursion on classified polynomial packets. -/
structure CRStep
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (Result :
      List (SITerm H ι) → Sort v) where
  resolve :
    ∀ parent,
      (∀ child,
        SITerm.FrontierDefectMultiset
            n child parent →
          Result child) →
        Result parent

namespace CRStep

/-- Run the resolver by well-founded frontier-defect multiset recursion. -/
noncomputable def recursiveResult
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {Result :
      List (SITerm H ι) → Sort v}
    (step :
      CRStep
        (n := n) H ι Result)
    (terms : List (SITerm H ι)) :
    Result terms :=
  (SITerm.well_founded_multiset
      (n := n) (H := H) (ι := ι)).fix step.resolve terms

/-- Unfold one resolver call of contextual polynomial packet recursion. -/
theorem recursiveResult_eq
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {Result :
      List (SITerm H ι) → Sort v}
    (step :
      CRStep
        (n := n) H ι Result)
    (terms : List (SITerm H ι)) :
    step.recursiveResult terms =
      step.resolve terms fun child _ => step.recursiveResult child := by
  rw [recursiveResult, WellFounded.fix_eq]
  rfl

end CRStep

namespace PFSubsti.TAPkt

/--
The recursive hypotheses of a singleton reworded parent include its complete
initial classified inner-reduction packet.
-/
def classified_result_reword
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {Result :
      List (SITerm H ι) → Sort v}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (recursiveResults :
      ∀ child,
        SITerm.FrontierDefectMultiset
            n child
              [.frontier
                (STExp.rewordFactor
                  factor factor.word)] →
          Result child) :
    Result
      (packet.outerClassifiedTerms normalizer factor
        innerWord rightWord hword) :=
  recursiveResults _
    (packet.polyMultisetReword
      normalizer factor innerWord rightWord hword hfactorTruncated)

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Order-preserving recollection of classified transient polynomial packets

Initial transient inner reduction keeps attached and excess-left outputs in
their original Hall-Petresco order.  Balanced terms truncate directly as
permanent polynomial factors.  Frontier terms delegate to the transient
singleton factory.  Their ordered composition remains supported at the parent
bracket weight and evaluates exactly to `[inner ^ f, right]`.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement
open HACoeff

/-- Recollect an ordered mixed polynomial packet into permanent factors. -/
structure TTRecoll
    {d : ℕ}
    (n lowerWeight : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    {ι : Type}
    (rawSource : List (SITerm H ι)) where
  higherSource :
    List (SPFactor H ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_weight_least :
    SPFactor.WordWeightLeast lowerWeight higherSource
  list_higher_raw :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e higherSource =
        SITerm.listValue (n := n) e
          rawSource

namespace TTRecoll

/-- The empty mixed source recollects to itself. -/
def empty
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type} :
    TTRecoll
      n lowerWeight H
        ([] : List (SITerm H ι)) where
  higherSource := []
  higher_source_truncated := by
    intro factor hfactor
    simp at hfactor
  higher_weight_least := by
    intro factor hfactor
    simp at hfactor
  list_higher_raw := by
    intro e
    rfl

/-- Concatenate recollected mixed sources without changing order. -/
def append
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {leftSource rightSource :
      List (SITerm H ι)}
    (left :
      TTRecoll
        n lowerWeight H leftSource)
    (right :
      TTRecoll
        n lowerWeight H rightSource) :
    TTRecoll
      n lowerWeight H (leftSource ++ rightSource) where
  higherSource := left.higherSource ++ right.higherSource
  higher_source_truncated := by
    intro factor hfactor
    rcases List.mem_append.mp hfactor with hfactor | hfactor
    · exact left.higher_source_truncated factor hfactor
    · exact right.higher_source_truncated factor hfactor
  higher_weight_least := by
    intro factor hfactor
    rcases List.mem_append.mp hfactor with hfactor | hfactor
    · exact left.higher_weight_least factor hfactor
    · exact right.higher_weight_least factor hfactor
  list_higher_raw := by
    intro e
    rw [SPFactor.listEval_append,
      left.list_higher_raw,
      right.list_higher_raw]
    simp [SITerm.listValue]

/-- Compose singleton mixed recollections in their original order. -/
def of_singletons
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (rawSource : List (SITerm H ι))
    (recollection :
      ∀ term ∈ rawSource,
        TTRecoll
          n lowerWeight H [term]) :
    TTRecoll
      n lowerWeight H rawSource := by
  induction rawSource with
  | nil =>
      exact empty
  | cons head tail ih =>
      simpa using
        (append
          (recollection head (by simp))
          (ih fun term hterm => recollection term (by simp [hterm])))

/-- Attach and truncate one permanent polynomial factor. -/
noncomputable def singleton_attached
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι)
    (hweight :
      lowerWeight ≤ factor.word.weight HEAddres.weight) :
    TTRecoll
      n lowerWeight H [.attached factor] where
  higherSource := SPFactor.truncate n [factor]
  higher_source_truncated := by
    intro next hnext
    exact SPFactor.word_weight_truncate hnext
  higher_weight_least := by
    intro next hnext
    have hnext' := (List.mem_filter.mp hnext).1
    simp only [List.mem_singleton] at hnext'
    subst next
    exact hweight
  list_higher_raw := by
    intro e
    rw [SPFactor.listEval_truncate]
    simp [SITerm.listValue,
      SITerm.value]

/-- Reuse one transient singleton recollection for a frontier term. -/
noncomputable def singleton_frontier
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (wordExpansion : STExp H ι)
    (recollection :
      TTRecolla
        n lowerWeight H [wordExpansion]) :
    TTRecoll
      n lowerWeight H [.frontier wordExpansion] where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least :=
    recollection.higher_weight_least
  list_higher_raw := by
    intro e
    rw [recollection.list_higher_raw]
    simp [STExp.listValue,
      SITerm.listValue,
      SITerm.value]

end TTRecoll

namespace PIRed

/-- Every initial transient recipe word is physically at least as heavy as its parent. -/
lemma inner_outer_expansion
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    factor.word.weight HEAddres.weight ≤
      (innerOuterExpansion normalizer R factor innerWord
        rightWord).word.weight HEAddres.weight := by
  rw [inner_reduction_expansion, hword,
    CWord.weight_commutator]
  exact Nat.add_le_add
    (Nat.le_mul_of_pos_left _
      (BRSpec.leftDegree_pos R))
    (Nat.le_mul_of_pos_left _
      (BRSpec.rightDegree_pos R))

/-- Recollect one classified initial recipe term in place. -/
noncomputable def recollection_classified_term
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TRFtry
        d n H ι)
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecoll
      n (factor.word.weight HEAddres.weight) H
        [classifiedOuterTerm normalizer R factor innerWord
          rightWord hword] := by
  by_cases hbalanced : R.leftDegree ≤ R.rightDegree
  · rw [classified_left_degree
      normalizer R factor innerWord rightWord hword hbalanced]
    exact
      TTRecoll.singleton_attached
        (attachedInnerFactor normalizer R factor innerWord
          rightWord hword hbalanced)
        (by
          exact
            inner_outer_expansion
              normalizer R factor innerWord rightWord hword)
  · have hfrontier : R.rightDegree < R.leftDegree :=
      Nat.lt_of_not_ge hbalanced
    rw [classified_inner_outer
      normalizer R factor innerWord rightWord hword hfrontier]
    exact
      TTRecoll.singleton_frontier
        (innerOuterExpansion normalizer R factor innerWord
          rightWord)
        ((factory.recollectionOrEmpty
          (innerOuterExpansion normalizer R factor innerWord
            rightWord)).weaken
              (inner_outer_expansion
                normalizer R factor innerWord rightWord hword))

end PIRed

namespace PFSubsti.TAPkt

open PIRed

/-- Recollect the complete classified initial packet without changing order. -/
noncomputable def
    inner_classified_terms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TRFtry
        d n H ι)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecoll
      n (factor.word.weight HEAddres.weight) H
        (packet.outerClassifiedTerms normalizer factor
          innerWord rightWord hword) :=
  TTRecoll.of_singletons _
    fun term hterm => by
      let R := Classical.choose (List.mem_map.mp hterm)
      have hR :
          classifiedOuterTerm normalizer R factor innerWord
              rightWord hword =
            term :=
        (Classical.choose_spec (List.mem_map.mp hterm)).2
      exact hR ▸
        recollection_classified_term factory
          normalizer R factor innerWord rightWord hword

/-- Classified-packet recollection still evaluates to `[inner ^ f, right]`. -/
lemma
    higher_classified_terms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TRFtry
        d n H ι)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e
        (packet
          |>.inner_classified_terms
            factory normalizer factor innerWord rightWord hword).higherSource =
      ⁅innerWord.eval
            (HEAddres.freeLowerTruncation
              (n := n)) ^
          factor.coefficient.eval e,
        rightWord.eval
          (HEAddres.freeLowerTruncation
            (n := n))⁆ := by
  rw [(packet
    |>.inner_classified_terms
      factory normalizer factor innerWord rightWord hword)
        |>.list_higher_raw]
  exact packet.reduction_classified_terms
    normalizer factor innerWord rightWord hword e

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Contextual recursion helpers for generic transient polynomial packets

The mixed-packet fixpoint exposes recursive results for strictly smaller
frontier-defect multisets.  Arbitrary transient polynomial Hall-Petresco
packets meet that interface directly: their complete classified packet
descends from the singleton obligation carried by either transient parent.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u v

namespace PFSubsti.TAPkt

/-- Obtain the complete classified child packet while resolving its left parent. -/
def classified_terms_result
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {Result :
      List (SITerm H ι) → Sort v}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hB : B.word.weight HEAddres.weight < n)
    (recursiveResults :
      ∀ child,
        SITerm.FrontierDefectMultiset
            n child [.frontier B] →
          Result child) :
    Result (packet.polynomialTransientTerms normalizer B A) :=
  recursiveResults _
    (packet.polyClassifiedSingleton
      normalizer B A hB)

/-- Obtain the complete classified child packet while resolving its right parent. -/
def transient_classified_result
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {Result :
      List (SITerm H ι) → Sort v}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hA : A.word.weight HEAddres.weight < n)
    (recursiveResults :
      ∀ child,
        SITerm.FrontierDefectMultiset
            n child [.frontier A] →
          Result child) :
    Result (packet.polynomialTransientTerms normalizer B A) :=
  recursiveResults _
    (packet.polyTransientClassified
      normalizer B A hA)

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Contextual recollection surface for transient polynomial inner reduction

The recursive obligation is the complete ordered classified packet.  While
another physical stratum remains below the cutoff, an active factory supplies
its recollection.  At the next-stratum endpoint, balanced factors truncate
locally and every frontier entry erases because its physical word is already
at the nilpotent cutoff.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

namespace PIRed

/-- Recollect one classified initial term directly at the terminal stratum. -/
noncomputable def
    classified_inner_terminal
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : HACoeff.BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ factor.word.weight HEAddres.weight + 1) :
    TTRecoll
      n (factor.word.weight HEAddres.weight) H
        [classifiedOuterTerm normalizer R factor innerWord
          rightWord hword] := by
  by_cases hbalanced : R.leftDegree ≤ R.rightDegree
  · rw [classified_left_degree
      normalizer R factor innerWord rightWord hword hbalanced]
    exact
      TTRecoll.singleton_attached
        (attachedInnerFactor normalizer R factor innerWord
          rightWord hword hbalanced)
        (inner_outer_expansion
          normalizer R factor innerWord rightWord hword)
  · have hfrontier : R.rightDegree < R.leftDegree :=
      Nat.lt_of_not_ge hbalanced
    rw [classified_inner_outer
      normalizer R factor innerWord rightWord hword hfrontier]
    exact
      TTRecoll.singleton_frontier
        (innerOuterExpansion normalizer R factor innerWord
          rightWord)
        (TTRecolla.singleton_n_weight
          (innerOuterExpansion normalizer R factor innerWord
            rightWord)
          (hcutoff.trans
            (Nat.succ_le_of_lt
              (factor_inner_degree
                normalizer R factor innerWord rightWord hword hfrontier))))

end PIRed

namespace PFSubsti.TAPkt

open PIRed

/-- Recollect the whole initial classified packet directly at the endpoint. -/
noncomputable def
    inner_classified_terminal
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ factor.word.weight HEAddres.weight + 1) :
    TTRecoll
      n (factor.word.weight HEAddres.weight) H
        (packet.outerClassifiedTerms normalizer factor
          innerWord rightWord hword) :=
  TTRecoll.of_singletons _
    fun term hterm => by
      let R := Classical.choose (List.mem_map.mp hterm)
      have hR :
          classifiedOuterTerm normalizer R factor innerWord
              rightWord hword =
            term :=
        (Classical.choose_spec (List.mem_map.mp hterm)).2
      exact hR ▸
        classified_inner_terminal
          normalizer R factor innerWord rightWord hword hcutoff

/-- Terminal classified-packet recollection preserves the parent bracket. -/
lemma
    higher_terms_terminal
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ factor.word.weight HEAddres.weight + 1)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e
        (packet
          |>.inner_classified_terminal
            normalizer factor innerWord rightWord hword hcutoff).higherSource =
      ⁅innerWord.eval
            (HEAddres.freeLowerTruncation
              (n := n)) ^
          factor.coefficient.eval e,
        rightWord.eval
          (HEAddres.freeLowerTruncation
            (n := n))⁆ := by
  rw [(packet
    |>.inner_classified_terminal
      normalizer factor innerWord rightWord hword hcutoff)
        |>.list_higher_raw]
  exact packet.reduction_classified_terms
    normalizer factor innerWord rightWord hword e

end PFSubsti.TAPkt

/--
Active contextual recollection input for complete ordered classified packets.
The recursive field is requested only while another stratum remains.
-/
structure
    TCFtry
    (d n : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  sourceRecollection :
    ∀
      (packet :
        PFSubsti.TAPkt.{u}
          d n)
      (normalizer :
        WBForm.RCNormal H ι)
      (factor : SPFactor H ι)
      (innerWord rightWord : CWord (HEAddres H))
      (hword : factor.word = .commutator innerWord rightWord),
      factor.word.weight HEAddres.weight + 1 < n →
        TTRecoll
          n (factor.word.weight HEAddres.weight) H
            (packet.outerClassifiedTerms normalizer
              factor innerWord rightWord hword)

namespace
  TCFtry

/-- Dispatch an initial classified packet to recursion or the terminal endpoint. -/
noncomputable def recollectionOrTerminal
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TCFtry
        d n H ι)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecoll
      n (factor.word.weight HEAddres.weight) H
        (packet.outerClassifiedTerms normalizer factor
          innerWord rightWord hword) := by
  by_cases hactive :
      factor.word.weight HEAddres.weight + 1 < n
  · exact
      factory.sourceRecollection packet normalizer factor innerWord rightWord
        hword hactive
  · exact
      packet.inner_classified_terminal
        normalizer factor innerWord rightWord hword (Nat.le_of_not_gt hactive)

/-- A singleton transient factory is sufficient for the contextual active field. -/
noncomputable def ofTransientFactory
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TRFtry
        d n H ι) :
    TCFtry
      d n H ι where
  sourceRecollection packet normalizer factor innerWord rightWord hword _ :=
    packet.inner_classified_terms
      factory normalizer factor innerWord rightWord hword

end
  TCFtry

end TCTex
end Submission

/-!
# Operations on contextual transient polynomial recollections

Contextual polynomial recollection keeps attached and frontier terms in their
original order.  Packet-specific cancellation arguments need only three
semantic operations: lower the requested support bound, transport across
equality of ordered packet values, and close a packet whose ordered value is
already trivial.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace TTRecoll

/-- Lower the requested physical support bound. -/
def weaken
    {d n lowerWeight weakerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {rawSource :
      List (SITerm H ι)}
    (recollection :
      TTRecoll
        n lowerWeight H rawSource)
    (hweight : weakerWeight ≤ lowerWeight) :
    TTRecoll
      n weakerWeight H rawSource where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least := fun factor hfactor =>
    hweight.trans
      (recollection.higher_weight_least factor hfactor)
  list_higher_raw :=
    recollection.list_higher_raw

/-- Transport contextual recollection across equality of complete packet values. -/
def list_value
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {rawSource targetSource :
      List (SITerm H ι)}
    (recollection :
      TTRecoll
        n lowerWeight H rawSource)
    (hvalue :
      ∀ e : ι → HEFam H,
        SITerm.listValue (n := n) e
            rawSource =
          SITerm.listValue e
            targetSource) :
    TTRecoll
      n lowerWeight H targetSource where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least :=
    recollection.higher_weight_least
  list_higher_raw := fun e =>
    (recollection.list_higher_raw e).trans (hvalue e)

/-- A complete mixed packet whose ordered value is trivial recollects to empty. -/
def empty_list_value
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (rawSource :
      List (SITerm H ι))
    (hvalue :
      ∀ e : ι → HEFam H,
        SITerm.listValue (n := n) e
          rawSource = 1) :
    TTRecoll
      n lowerWeight H rawSource where
  higherSource := []
  higher_source_truncated := by
    intro factor hfactor
    simp at hfactor
  higher_weight_least := by
    intro factor hfactor
    simp at hfactor
  list_higher_raw := by
    intro e
    simpa only [SPFactor.listEval_nil] using (hvalue e).symm

end TTRecoll

end TCTex
end Submission

/-!
# Contextual recollection of generic transient polynomial packets

Arbitrary two-sided transient Hall-Petresco substitutions retain attached and
frontier terms in their original order.  This file records their common
physical support bounds and closes a complete mixed packet once either parent
is one stratum below the nilpotent cutoff.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

namespace SITerm

/-- The physical Hall-word weight of one attached-or-frontier term. -/
def wordWeight
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type} :
    SITerm H ι → ℕ
  | .attached factor =>
      factor.word.weight HEAddres.weight
  | .frontier wordExpansion =>
      wordExpansion.word.weight HEAddres.weight

@[simp]
lemma wordWeight_attached
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι) :
    wordWeight (.attached factor) =
      factor.word.weight HEAddres.weight :=
  rfl

@[simp]
lemma wordWeight_frontier
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (wordExpansion : STExp H ι) :
    wordWeight (.frontier wordExpansion) =
      wordExpansion.word.weight HEAddres.weight :=
  rfl

end SITerm

namespace TTRecoll

/-- Recollect one supported mixed term whose frontier case has reached cutoff. -/
noncomputable def singleton_least_frontier
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (term : SITerm H ι)
    (hweight :
      lowerWeight ≤ SITerm.wordWeight
        term)
    (hfrontier :
      ∀ wordExpansion,
        term = .frontier wordExpansion →
          n ≤ wordExpansion.word.weight HEAddres.weight) :
    TTRecoll
      n lowerWeight H [term] := by
  cases term with
  | attached factor =>
      exact singleton_attached factor hweight
  | frontier wordExpansion =>
      exact
        singleton_frontier wordExpansion
          (TTRecolla.singleton_n_weight
            wordExpansion (hfrontier wordExpansion rfl))

/-- Recollect a supported mixed packet when every frontier word reaches cutoff. -/
noncomputable def word_frontier_cutoff
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (rawSource : List (SITerm H ι))
    (hweight :
      ∀ term ∈ rawSource,
        lowerWeight ≤
          SITerm.wordWeight term)
    (hfrontier :
      ∀ wordExpansion,
        .frontier wordExpansion ∈ rawSource →
          n ≤ wordExpansion.word.weight HEAddres.weight) :
    TTRecoll
      n lowerWeight H rawSource :=
  of_singletons rawSource fun term hterm =>
    singleton_least_frontier term
      (hweight term hterm) fun wordExpansion hterm_eq =>
        hfrontier wordExpansion (hterm_eq ▸ hterm)

end TTRecoll

namespace FTSubsti

/-- Every generic classified output is physically above its left parent. -/
lemma left_classified_transient
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : HACoeff.BRecipe)
    (B A : STExp H ι) :
    B.word.weight HEAddres.weight <
      (classifiedTransientTerm normalizer R B A).wordWeight := by
  by_cases hweight :
      (wordExpansion normalizer R B A).coefficientWeight ≤
        (wordExpansion normalizer R B A).word.weight HEAddres.weight
  · rw [classified_attached_coefficient
      normalizer R B A hweight]
    exact left_weight_expansion normalizer R B A
  · rw [classified_transient_not
      normalizer R B A hweight]
    exact left_weight_expansion normalizer R B A

/-- Every generic classified output is physically above its right parent. -/
lemma classified_transient_term
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : HACoeff.BRecipe)
    (B A : STExp H ι) :
    A.word.weight HEAddres.weight <
      (classifiedTransientTerm normalizer R B A).wordWeight := by
  by_cases hweight :
      (wordExpansion normalizer R B A).coefficientWeight ≤
        (wordExpansion normalizer R B A).word.weight HEAddres.weight
  · rw [classified_attached_coefficient
      normalizer R B A hweight]
    exact right_weight_expansion normalizer R B A
  · rw [classified_transient_not
      normalizer R B A hweight]
    exact right_weight_expansion normalizer R B A

end FTSubsti

namespace PFSubsti.TAPkt

open FTSubsti
open TTRecoll

/-- Every generic classified term is physically above its left parent. -/
lemma left_classified_terms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (term : SITerm H ι)
    (hterm : term ∈ packet.polynomialTransientTerms normalizer B A) :
    B.word.weight HEAddres.weight < term.wordWeight := by
  rw [polynomialTransientTerms] at hterm
  rcases List.mem_map.mp hterm with ⟨R, _, rfl⟩
  exact left_classified_transient normalizer R B A

/-- Every generic classified term is physically above its right parent. -/
lemma transient_classified_terms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (term : SITerm H ι)
    (hterm : term ∈ packet.polynomialTransientTerms normalizer B A) :
    A.word.weight HEAddres.weight < term.wordWeight := by
  rw [polynomialTransientTerms] at hterm
  rcases List.mem_map.mp hterm with ⟨R, _, rfl⟩
  exact classified_transient_term normalizer R B A

/-- Normalize a generic packet when its left parent is one stratum below cutoff. -/
noncomputable def
    source_classified_terminal
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hcutoff : n ≤ B.word.weight HEAddres.weight + 1) :
    TTRecoll
      n (B.word.weight HEAddres.weight) H
        (packet.polynomialTransientTerms normalizer B A) :=
  word_frontier_cutoff _
      (fun term hterm =>
        Nat.le_of_lt
          (packet.left_classified_terms
            normalizer B A term hterm))
      (fun wordExpansion hwordExpansion =>
        hcutoff.trans
          (Nat.succ_le_of_lt
            (packet.left_classified_frontier
              normalizer B A wordExpansion hwordExpansion)))

/-- Normalize a generic packet when its right parent is one stratum below cutoff. -/
noncomputable def
    transient_terms_terminal
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hcutoff : n ≤ A.word.weight HEAddres.weight + 1) :
    TTRecoll
      n (A.word.weight HEAddres.weight) H
        (packet.polynomialTransientTerms normalizer B A) :=
  word_frontier_cutoff _
      (fun term hterm =>
        Nat.le_of_lt
          (packet.transient_classified_terms
            normalizer B A term hterm))
      (fun wordExpansion hwordExpansion =>
        hcutoff.trans
          (Nat.succ_le_of_lt
            (packet.transient_terms_frontier
              normalizer B A wordExpansion hwordExpansion)))

/-- Left-terminal generic recollection evaluates to the parent commutator. -/
lemma
    higher_classified_terminal
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hcutoff : n ≤ B.word.weight HEAddres.weight + 1)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e
        (packet
          |>.source_classified_terminal
            normalizer B A hcutoff).higherSource =
      ⁅B.value (n := n) e, A.value (n := n) e⁆ := by
  rw [(packet
    |>.source_classified_terminal
      normalizer B A hcutoff).list_higher_raw]
  exact packet.list_transient_terms normalizer B A e

/-- Right-terminal generic recollection evaluates to the parent commutator. -/
lemma
    transient_classified_terminal
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hcutoff : n ≤ A.word.weight HEAddres.weight + 1)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e
        (packet
          |>.transient_terms_terminal
            normalizer B A hcutoff).higherSource =
      ⁅B.value (n := n) e, A.value (n := n) e⁆ := by
  rw [(packet
    |>.transient_terms_terminal
      normalizer B A hcutoff).list_higher_raw]
  exact packet.list_transient_terms normalizer B A e

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Descending contextual recursion steps for transient polynomial packets

An active classified packet callback should see the complete ordered packet
together with the strict frontier-defect descent certificate justifying its
recursive call.  This file packages that stronger callback surface and
compiles it to the active contextual factory.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/-- A certificate-carrying active classified-packet recollection callback. -/
structure
    TDClassi
    (d n : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  sourceRecollection :
    ∀
      (packet :
        PFSubsti.TAPkt.{u}
          d n)
      (normalizer :
        WBForm.RCNormal H ι)
      (factor : SPFactor H ι)
      (innerWord rightWord : CWord (HEAddres H))
      (hword : factor.word = .commutator innerWord rightWord),
      factor.word.weight HEAddres.weight + 1 < n →
        Multiset.IsDershowitzMannaLT
            (SITerm.frontierDefectMultiset
              n
              (packet.outerClassifiedTerms normalizer
                factor innerWord rightWord hword))
            {SPFactor.cutoffDefect n factor} →
          TTRecoll
            n (factor.word.weight HEAddres.weight) H
              (packet.outerClassifiedTerms normalizer
                factor innerWord rightWord hword)

namespace
  TDClassi

/-- Compile the certificate-carrying callback to the active contextual factory. -/
noncomputable def toActiveFactory
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      TDClassi
        d n H ι) :
    TCFtry
      d n H ι where
  sourceRecollection packet normalizer factor innerWord rightWord hword
      hactive :=
    step.sourceRecollection packet normalizer factor innerWord rightWord hword
      hactive
        (packet.frontierMultisetSingleton
          normalizer factor innerWord rightWord hword
            (Nat.lt_trans (Nat.lt_succ_self _) hactive))

/-- Any active factory supplies the stronger callback surface by ignoring its proof. -/
noncomputable def ofActiveFactory
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TCFtry
        d n H ι) :
    TDClassi
      d n H ι where
  sourceRecollection packet normalizer factor innerWord rightWord hword
      hactive _ :=
    factory.sourceRecollection packet normalizer factor innerWord rightWord
      hword hactive

end
  TDClassi

end TCTex
end Submission

/-!
# Recursive recollection of contextual transient polynomial packets

The generic contextual packet fixpoint is specialized here to ordinary
recollections of complete ordered mixed packets.  A local resolver may use
recursive recollections for strictly smaller frontier-defect multisets.  The
compiled fixpoint supplies the descending classified-packet factory used by
future polynomial outer-residual routing.

The local resolver is the remaining packet-specific cancellation obligation.
This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
One contextual recollection resolver for complete ordered polynomial packets.
Every recursive recollection is available only at a strictly smaller
frontier-defect multiset.
-/
structure CRRecol
    (d n : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  resolve :
    ∀
      (lowerWeight : ℕ)
      (parent : List (SITerm H ι)),
      (∀ child,
        SITerm.FrontierDefectMultiset
            n child parent →
          TTRecoll
            n lowerWeight H child) →
        TTRecoll
          n lowerWeight H parent

namespace
  CRRecol

/-- Forget recollection specialization into the generic packet resolver. -/
noncomputable def toRecursiveStep
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      CRRecol
        d n H ι)
    (lowerWeight : ℕ) :
    CRStep
      (n := n) H ι fun
        terms : List (SITerm H ι) =>
        TTRecoll
          n lowerWeight H terms where
  resolve := step.resolve lowerWeight

/-- Run mixed-packet recollection by frontier-defect recursion. -/
noncomputable def sourceRecollection
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      CRRecol
        d n H ι)
    (lowerWeight : ℕ)
    (terms : List (SITerm H ι)) :
    TTRecoll
      n lowerWeight H terms :=
  (step.toRecursiveStep lowerWeight).recursiveResult terms

/-- Unfold one contextual recollection resolver call. -/
theorem sourceRecollection_eq
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      CRRecol
        d n H ι)
    (lowerWeight : ℕ)
    (terms : List (SITerm H ι)) :
    step.sourceRecollection lowerWeight terms =
      step.resolve lowerWeight terms fun child _ =>
        step.sourceRecollection lowerWeight child := by
  rw [sourceRecollection,
    CRStep.recursiveResult_eq]
  rfl

/-- Compile a contextual resolver into the certificate-carrying active step. -/
noncomputable def toDescendingStep
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      CRRecol
        d n H ι) :
    TDClassi
      d n H ι where
  sourceRecollection packet normalizer factor innerWord rightWord hword
      _ _ :=
    step.sourceRecollection
      (factor.word.weight HEAddres.weight)
      (packet.outerClassifiedTerms normalizer factor
        innerWord rightWord hword)

/-- Compile a contextual resolver directly into the active packet factory. -/
noncomputable def toActiveFactory
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      CRRecol
        d n H ι) :
    TCFtry
      d n H ι :=
  step.toDescendingStep.toActiveFactory

end
  CRRecol

end TCTex
end Submission

/-!
# Recursive factory bridge for transient polynomial words

The contextual packet fixpoint recollects mixed attached-or-frontier packets.
Older polynomial normalization interfaces ask instead for one transient-word
singleton at its own physical Hall-word weight.  A singleton frontier packet
is exactly that input, so the compiled fixpoint supplies the singleton
factory directly.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace TTRecolla

/--
Forget that a recollected singleton transient polynomial frontier was
presented through the mixed contextual packet API.
-/
def singleton_frontier_recollection
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (wordExpansion : STExp H ι)
    (recollection :
      TTRecoll
        n lowerWeight H [.frontier wordExpansion]) :
    TTRecolla
      n lowerWeight H [wordExpansion] where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least :=
    recollection.higher_weight_least
  list_higher_raw := by
    intro e
    rw [recollection.list_higher_raw]
    simp [STExp.listValue,
      SITerm.listValue,
      SITerm.value]

end TTRecolla

namespace
  CRRecol

/--
A support-polymorphic contextual packet resolver supplies the historical
transient-singleton factory by recollecting each singleton frontier at its
own physical Hall-word weight.
-/
noncomputable def toTransientFactory
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      CRRecol
        d n H ι) :
    TRFtry
      d n H ι where
  sourceRecollection wordExpansion _ :=
    TTRecolla.singleton_frontier_recollection
      wordExpansion
        (step.sourceRecollection
          (wordExpansion.word.weight HEAddres.weight)
            [.frontier wordExpansion])

end
  CRRecol

end TCTex
end Submission

/-!
# Callback-facing recollection of strict transient polynomial tails

A transient polynomial word with strictly larger physical Hall-word weight
has a strictly smaller frontier defect.  Consequently every ordered list of
such words can be recollected from the contextual callback rooted at its
parent singleton.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace SITerm

/--
A physically heavier transient polynomial singleton strictly descends from
an active transient polynomial singleton in the frontier-defect order.
-/
lemma
    defect_multiset_weight
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (child parent : STExp H ι)
    (hparentTruncated :
      parent.word.weight HEAddres.weight < n)
    (hweight :
      parent.word.weight HEAddres.weight <
        child.word.weight HEAddres.weight) :
    FrontierDefectMultiset n [.frontier child] [.frontier parent] := by
  refine ⟨∅,
    {n - child.word.weight HEAddres.weight},
    {n - parent.word.weight HEAddres.weight},
    by simp, by simp, by simp, ?_⟩
  intro defect hdefect
  simp only [Multiset.mem_singleton] at hdefect
  subst defect
  exact
    ⟨n - parent.word.weight HEAddres.weight, by simp, by omega⟩

end SITerm

namespace TTRecolla

/--
Recollect an ordered strict transient tail from contextual recursive results
rooted at its active parent singleton.
-/
noncomputable def strictly_heavier_results
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (parent : STExp H ι)
    (hparentTruncated :
      parent.word.weight HEAddres.weight < n)
    (rawSource : List (STExp H ι))
    (hweight :
      ∀ child ∈ rawSource,
        parent.word.weight HEAddres.weight <
          child.word.weight HEAddres.weight)
    (recursiveResults :
      ∀ child,
        SITerm.FrontierDefectMultiset
            n child [.frontier parent] →
          TTRecoll
            n lowerWeight H child) :
    TTRecolla
      n lowerWeight H rawSource :=
  of_singletons _ fun child hchild =>
    singleton_frontier_recollection child <|
      recursiveResults [.frontier child] <|
        SITerm.defect_multiset_weight
          child parent hparentTruncated (hweight child hchild)

/--
Recollect an ordered strict transient tail by rerunning the compiled
contextual fixpoint on its singleton children.
-/
noncomputable def strictly_heavier_recursive
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      CRRecol
        d n H ι)
    (parent : STExp H ι)
    (hparentTruncated :
      parent.word.weight HEAddres.weight < n)
    (rawSource : List (STExp H ι))
    (hweight :
      ∀ child ∈ rawSource,
        parent.word.weight HEAddres.weight <
          child.word.weight HEAddres.weight) :
    TTRecolla
      n lowerWeight H rawSource :=
  strictly_heavier_results parent hparentTruncated
    rawSource hweight fun child _ =>
      step.sourceRecollection lowerWeight child

end TTRecolla

end TCTex
end Submission

/-!
# Active-or-terminal dispatch for transient polynomial packets

Generic two-sided transient Hall-Petresco substitution is recursive while a
chosen parent has room for one further Hall stratum.  At the endpoint every
frontier output is already at the truncation cutoff and the packet closes
directly.  This file packages both left- and right-parent dispatch.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace PFSubsti.TAPkt

/--
Use contextual recursive results for a generic packet while its left parent
is active, or close the packet directly at the left-parent endpoint.
-/
noncomputable def
    or_terminal_results
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (recursiveResults :
      ∀ child,
        SITerm.FrontierDefectMultiset
            n child [.frontier B] →
          TTRecoll
            n (B.word.weight HEAddres.weight) H child) :
    TTRecoll
      n (B.word.weight HEAddres.weight) H
        (packet.polynomialTransientTerms normalizer B A) := by
  by_cases hactive : B.word.weight HEAddres.weight + 1 < n
  · exact
      packet.classified_terms_result normalizer B A
        (by omega) recursiveResults
  · exact
      packet.source_classified_terminal
        normalizer B A (by omega)

/--
Use contextual recursive results for a generic packet while its right parent
is active, or close the packet directly at the right-parent endpoint.
-/
noncomputable def
    terminal_recursive_results
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (recursiveResults :
      ∀ child,
        SITerm.FrontierDefectMultiset
            n child [.frontier A] →
          TTRecoll
            n (A.word.weight HEAddres.weight) H child) :
    TTRecoll
      n (A.word.weight HEAddres.weight) H
        (packet.polynomialTransientTerms normalizer B A) := by
  by_cases hactive : A.word.weight HEAddres.weight + 1 < n
  · exact
      packet.transient_classified_result normalizer B A
        (by omega) recursiveResults
  · exact
      packet.transient_terms_terminal
        normalizer B A (by omega)

/--
Run left-parent active-or-terminal dispatch directly from the compiled
contextual recollection fixpoint.
-/
noncomputable def
    terminal_classified_recursive
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (step :
      CRRecol
        d n H ι)
    (B A : STExp H ι) :
    TTRecoll
      n (B.word.weight HEAddres.weight) H
        (packet.polynomialTransientTerms normalizer B A) :=
  packet
    |>.or_terminal_results
      normalizer B A fun child _ =>
        step.sourceRecollection
          (B.word.weight HEAddres.weight) child

/--
Run right-parent active-or-terminal dispatch directly from the compiled
contextual recollection fixpoint.
-/
noncomputable def
    or_terminal_classified
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (step :
      CRRecol
        d n H ι)
    (B A : STExp H ι) :
    TTRecoll
      n (A.word.weight HEAddres.weight) H
        (packet.polynomialTransientTerms normalizer B A) :=
  packet
    |>.terminal_recursive_results
      normalizer B A fun child _ =>
        step.sourceRecollection
          (A.word.weight HEAddres.weight) child

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Support-indexed recursion for transient polynomial packets

The unrestricted contextual recollection step is useful as a recursion
skeleton, but a concrete resolver also needs the physical support invariant
carried by generated packets.  This file records that invariant, proves it
for initial and recursive Hall-Petresco packets, and specializes the generic
frontier-defect fixpoint to support-indexed recollection.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace SITerm

/-- Every mixed packet term has physical Hall-word weight at least `lowerWeight`. -/
def WordWeightLeast
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (lowerWeight : ℕ)
    (terms : List (SITerm H ι)) :
    Prop :=
  ∀ term ∈ terms, lowerWeight ≤ term.wordWeight

end SITerm

namespace PIRed

/-- Every initial classified recipe output remains above its parent factor. -/
lemma inner_outer_term
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : HACoeff.BRecipe)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    factor.word.weight HEAddres.weight ≤
      (classifiedOuterTerm normalizer R factor innerWord
        rightWord hword).wordWeight := by
  by_cases hbalanced : R.leftDegree ≤ R.rightDegree
  · rw [classified_left_degree
      normalizer R factor innerWord rightWord hword hbalanced]
    exact
      inner_outer_expansion
        normalizer R factor innerWord rightWord hword
  · have hfrontier : R.rightDegree < R.leftDegree :=
      Nat.lt_of_not_ge hbalanced
    rw [classified_inner_outer
      normalizer R factor innerWord rightWord hword hfrontier]
    exact
      inner_outer_expansion
        normalizer R factor innerWord rightWord hword

end PIRed

namespace PFSubsti.TAPkt

/-- The initial classified inner-reduction packet is supported at its parent weight. -/
lemma least_classified_terms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    SITerm.WordWeightLeast
      (factor.word.weight HEAddres.weight)
        (packet.outerClassifiedTerms normalizer factor
          innerWord rightWord hword) := by
  intro term hterm
  rw [outerClassifiedTerms] at hterm
  rcases List.mem_map.mp hterm with ⟨R, _, rfl⟩
  exact
    PIRed.inner_outer_term
      normalizer R factor innerWord rightWord hword

/-- A recursive two-sided packet is supported strictly above its left parent. -/
lemma least_classified_left
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι) :
    SITerm.WordWeightLeast
      (B.word.weight HEAddres.weight + 1)
        (packet.polynomialTransientTerms normalizer B A) := by
  intro term hterm
  exact
    Nat.succ_le_of_lt
      (packet.left_classified_terms
        normalizer B A term hterm)

/-- A recursive two-sided packet is supported strictly above its right parent. -/
lemma least_transient_classified
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι) :
    SITerm.WordWeightLeast
      (A.word.weight HEAddres.weight + 1)
        (packet.polynomialTransientTerms normalizer B A) := by
  intro term hterm
  exact
    Nat.succ_le_of_lt
      (packet.transient_classified_terms
        normalizer B A term hterm)

end PFSubsti.TAPkt

/--
A concrete contextual resolver for supported packets.  Recursive children
must provide the same physical support certificate before they may be used.
-/
structure
    SCRec
    (d n : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  resolve :
    ∀
      (lowerWeight : ℕ)
      (parent : List (SITerm H ι)),
      SITerm.WordWeightLeast
          lowerWeight parent →
        (∀ child,
          SITerm.FrontierDefectMultiset
              n child parent →
            SITerm.WordWeightLeast
                lowerWeight child →
              TTRecoll
                n lowerWeight H child) →
          TTRecoll
            n lowerWeight H parent

namespace
  SCRec

/-- Forget support indexing into the generic frontier-defect resolver. -/
noncomputable def toRecursiveStep
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      SCRec
        d n H ι) :
    CRStep
      (n := n) H ι fun
        terms : List (SITerm H ι) =>
          ∀ lowerWeight,
            SITerm.WordWeightLeast
                lowerWeight terms →
              TTRecoll
                n lowerWeight H terms where
  resolve parent recursiveResults lowerWeight hparent :=
    step.resolve lowerWeight parent hparent fun child hchild hsupport =>
      recursiveResults child hchild lowerWeight hsupport

/-- Run support-indexed recollection by frontier-defect recursion. -/
noncomputable def sourceRecollection
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      SCRec
        d n H ι)
    (terms : List (SITerm H ι))
    (hsupport :
      SITerm.WordWeightLeast
        lowerWeight terms) :
    TTRecoll
      n lowerWeight H terms :=
  step.toRecursiveStep.recursiveResult terms lowerWeight hsupport

/-- Compile a supported resolver to the active initial-packet callback. -/
noncomputable def toActiveFactory
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      SCRec
        d n H ι) :
    TCFtry
      d n H ι where
  sourceRecollection packet normalizer factor innerWord rightWord hword _ :=
    step.sourceRecollection _
      (packet.least_classified_terms
        normalizer factor innerWord rightWord hword)

/-- Compile a supported resolver to the transient singleton factory. -/
noncomputable def toTransientFactory
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      SCRec
        d n H ι) :
    TRFtry
      d n H ι where
  sourceRecollection wordExpansion _ :=
    TTRecolla.singleton_frontier_recollection
      wordExpansion <|
        step.sourceRecollection [.frontier wordExpansion] <| by
          intro term hterm
          simp only [List.mem_singleton] at hterm
          subst term
          exact Nat.le_refl _

end
  SCRec

end TCTex
end Submission

/-!
# Frontier-only resolver interface for transient polynomial recursion

Supported mixed packets contain attached permanent factors and transient
frontier words.  Attached terms recollect immediately.  Therefore a complete
support-indexed packet resolver reduces to one callback for each frontier
singleton, with recursive results available for strictly smaller packets.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
One local resolver for supported transient polynomial frontier singletons.
The surrounding packet is retained so the callback may use its recursive
children under the packet's frontier-defect certificate.
-/
structure
    SFRec
    (d n : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  resolve :
    ∀
      (lowerWeight : ℕ)
      (parent : List (SITerm H ι))
      (wordExpansion : STExp H ι),
      SITerm.WordWeightLeast
          lowerWeight parent →
        .frontier wordExpansion ∈ parent →
          (∀ child,
            SITerm.FrontierDefectMultiset
                n child parent →
              SITerm.WordWeightLeast
                  lowerWeight child →
                TTRecoll
                  n lowerWeight H child) →
            TTRecoll
              n lowerWeight H [.frontier wordExpansion]

namespace
  SFRec

/--
Resolve attached terms immediately and delegate only transient singleton
frontiers to the local callback.
-/
noncomputable def supportedPacketStep
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      SFRec
        d n H ι) :
    SCRec
      d n H ι where
  resolve lowerWeight parent hparent recursiveResults :=
    TTRecoll.of_singletons
      parent fun term hterm => by
        cases term with
        | attached factor =>
            exact
              TTRecoll.singleton_attached
                factor (hparent (.attached factor) hterm)
        | frontier wordExpansion =>
            exact
              step.resolve lowerWeight parent wordExpansion hparent hterm
                recursiveResults

/-- Compile a frontier-only resolver to the active initial-packet callback. -/
noncomputable def toActiveFactory
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      SFRec
        d n H ι) :
    TCFtry
      d n H ι :=
  step.supportedPacketStep.toActiveFactory

/-- Compile a frontier-only resolver to the transient singleton factory. -/
noncomputable def toTransientFactory
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      SFRec
        d n H ι) :
    TRFtry
      d n H ι :=
  step.supportedPacketStep.toTransientFactory

end
  SFRec

end TCTex
end Submission

/-!
# Active frontier resolver interface for transient polynomial recursion

A transient frontier singleton at or above the nilpotent cutoff evaluates to
one and recollects to the empty permanent source.  Thus a complete frontier
resolver only needs a local rule below the cutoff.  This file packages that
terminal dispatch and compiles the active rule through the support-indexed
packet fixpoint.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/-- One local resolver for supported active transient polynomial frontiers. -/
structure
    FRRecol
    (d n : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  resolve :
    ∀
      (lowerWeight : ℕ)
      (parent : List (SITerm H ι))
      (wordExpansion : STExp H ι),
      SITerm.WordWeightLeast
          lowerWeight parent →
        .frontier wordExpansion ∈ parent →
          wordExpansion.word.weight HEAddres.weight < n →
            (∀ child,
              SITerm.FrontierDefectMultiset
                  n child parent →
                SITerm.WordWeightLeast
                    lowerWeight child →
                  TTRecoll
                    n lowerWeight H child) →
              TTRecoll
                n lowerWeight H [.frontier wordExpansion]

namespace
  FRRecol

/-- Erase terminal frontier words and delegate only active words. -/
noncomputable def supportedFrontierStep
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      FRRecol
        d n H ι) :
    SFRec
      d n H ι where
  resolve lowerWeight parent wordExpansion hparent hwordExpansion
      recursiveResults := by
    by_cases hactive :
        wordExpansion.word.weight HEAddres.weight < n
    · exact
        step.resolve lowerWeight parent wordExpansion hparent hwordExpansion
          hactive recursiveResults
    · exact
        TTRecoll.singleton_frontier
          wordExpansion <|
            TTRecolla.singleton_n_weight
              wordExpansion (Nat.le_of_not_gt hactive)

/-- Compile an active frontier resolver to the active initial-packet callback. -/
noncomputable def toActiveFactory
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      FRRecol
        d n H ι) :
    TCFtry
      d n H ι :=
  step.supportedFrontierStep.toActiveFactory

/-- Compile an active frontier resolver to the transient singleton factory. -/
noncomputable def toTransientFactory
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      FRRecol
        d n H ι) :
    TRFtry
      d n H ι :=
  step.supportedFrontierStep.toTransientFactory

end
  FRRecol

end TCTex
end Submission

/-!
# Nonattachable frontier resolver interface for transient polynomial recursion

An active transient polynomial word may return to the permanent factor
language as soon as its arithmetic coefficient bound fits its physical Hall
word.  This file performs that reattachment automa.  The remaining
local callback is restricted to active words whose coefficient bound still
does not fit.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
One local resolver for supported active transient polynomial frontiers whose
coefficient bound still exceeds their physical Hall-word weight.
-/
structure
    NFRec
    (d n : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  resolve :
    ∀
      (lowerWeight : ℕ)
      (parent : List (SITerm H ι))
      (wordExpansion : STExp H ι),
      SITerm.WordWeightLeast
          lowerWeight parent →
        .frontier wordExpansion ∈ parent →
          wordExpansion.word.weight HEAddres.weight < n →
            ¬ wordExpansion.coefficientWeight ≤
                wordExpansion.word.weight HEAddres.weight →
              (∀ child,
                SITerm.FrontierDefectMultiset
                    n child parent →
                  SITerm.WordWeightLeast
                      lowerWeight child →
                    TTRecoll
                      n lowerWeight H child) →
                TTRecoll
                  n lowerWeight H [.frontier wordExpansion]

namespace
  NFRec

/-- Reattach coefficient-compatible words and delegate only nonattachable words. -/
noncomputable def activeFrontierStep
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      NFRec
        d n H ι) :
    FRRecol
      d n H ι where
  resolve lowerWeight parent wordExpansion hparent hwordExpansion hactive
      recursiveResults := by
    by_cases hattach :
        wordExpansion.coefficientWeight ≤
          wordExpansion.word.weight HEAddres.weight
    · exact
        (TTRecoll.singleton_attached
          (wordExpansion.toFactor hattach)
          (hparent (.frontier wordExpansion) hwordExpansion)).list_value
            fun e => by
              simp [SITerm.listValue,
                SITerm.value]
    · exact
        step.resolve lowerWeight parent wordExpansion hparent hwordExpansion
          hactive hattach recursiveResults

/-- Compile a nonattachable frontier resolver to the active initial-packet callback. -/
noncomputable def toActiveFactory
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      NFRec
        d n H ι) :
    TCFtry
      d n H ι :=
  step.activeFrontierStep.toActiveFactory

/-- Compile a nonattachable frontier resolver to the transient singleton factory. -/
noncomputable def toTransientFactory
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (step :
      NFRec
        d n H ι) :
    TRFtry
      d n H ι :=
  step.activeFrontierStep.toTransientFactory

end
  NFRec

end TCTex
end Submission

/-!
# Commutator structure of generated transient polynomial frontiers

Every Hall-Petresco block recipe has positive left and right bidegrees.
Consequently its substituted Hall word is syntactically a commutator.  This
file recovers that decomposition for retained polynomial frontiers in both
the initial one-sided packet and arbitrary recursive two-sided packets.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HACoeff

namespace PIRed

/-- Every one-sided substituted polynomial recipe output is a commutator word. -/
lemma word_expansion_commutator
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    ∃ innerWord nextRightWord : CWord (HEAddres H),
      (wordExpansion normalizer R B rightWord).word =
        .commutator innerWord nextRightWord := by
  rcases pair_bidegree_positive R.positive with
    ⟨innerShape, rightShape, hshape⟩
  change R.erasedShape = .commutator innerShape rightShape at hshape
  refine
    ⟨CWord.hallPairBind B.word rightWord innerShape,
      CWord.hallPairBind B.word rightWord rightShape, ?_⟩
  simp only [wordExpansion, boundWord, hshape, CWord.hallPairBind,
    CWord.bind_commutator]

end PIRed

namespace FTSubsti

/-- Every two-sided substituted polynomial recipe output is a commutator word. -/
lemma word_expansion_commutator
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B A : STExp H ι) :
    ∃ innerWord rightWord : CWord (HEAddres H),
      (wordExpansion normalizer R B A).word =
        .commutator innerWord rightWord := by
  rcases pair_bidegree_positive R.positive with
    ⟨innerShape, rightShape, hshape⟩
  change R.erasedShape = .commutator innerShape rightShape at hshape
  refine
    ⟨CWord.hallPairBind B.word A.word innerShape,
      CWord.hallPairBind B.word A.word rightShape, ?_⟩
  simp only [wordExpansion, boundWord, hshape, CWord.hallPairBind,
    CWord.bind_commutator]

end FTSubsti

namespace PFSubsti.TAPkt

/--
Every retained frontier of an arbitrary recursive polynomial packet is
syntactically a commutator word.
-/
lemma words_classified_frontier
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A expansion : STExp H ι)
    (hexpansion :
      .frontier expansion ∈
        packet.polynomialTransientTerms normalizer B A) :
    ∃ innerWord rightWord : CWord (HEAddres H),
      expansion.word = .commutator innerWord rightWord := by
  rcases
      packet.recipe_classified_frontier
        normalizer B A expansion hexpansion with
    ⟨R, _, _, rfl⟩
  exact
    FTSubsti.word_expansion_commutator
      normalizer R B A

/--
Every retained frontier of an initial one-sided polynomial packet is
syntactically a commutator word.
-/
lemma words_terms_frontier
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (expansion : STExp H ι)
    (hexpansion :
      .frontier expansion ∈
        packet.outerClassifiedTerms normalizer factor
          innerWord rightWord hword) :
    ∃ nextInnerWord nextRightWord : CWord (HEAddres H),
      expansion.word = .commutator nextInnerWord nextRightWord := by
  rw [outerClassifiedTerms] at hexpansion
  rcases List.mem_map.mp hexpansion with ⟨R, _, hterm⟩
  by_cases hbalanced : R.leftDegree ≤ R.rightDegree
  · rw [
      PIRed.classified_left_degree
        normalizer R factor innerWord rightWord hword hbalanced] at hterm
    cases hterm
  · have hfrontier : R.rightDegree < R.leftDegree :=
      Nat.lt_of_not_ge hbalanced
    rw [
      PIRed.classified_inner_outer
        normalizer R factor innerWord rightWord hword hfrontier] at hterm
    cases hterm
    exact
      PIRed.word_expansion_commutator
        normalizer R
          (STExp.rewordFactor factor
            innerWord)
          rightWord

end PFSubsti.TAPkt

/-- A generated transient polynomial frontier with its commutator decomposition. -/
structure SGFront
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (expansion : STExp H ι) where
  innerWord : CWord (HEAddres H)
  rightWord : CWord (HEAddres H)
  word_eq : expansion.word = .commutator innerWord rightWord

namespace SGFront

/-- Recover structural routing data for a retained recursive packet frontier. -/
noncomputable def classified_frontier
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A expansion : STExp H ι)
    (hexpansion :
      .frontier expansion ∈
        packet.polynomialTransientTerms normalizer B A) :
    SGFront H ι expansion := by
  let hwords :=
    packet
      |>.words_classified_frontier
        normalizer B A expansion hexpansion
  exact
    { innerWord := Classical.choose hwords
      rightWord := Classical.choose (Classical.choose_spec hwords)
      word_eq := Classical.choose_spec (Classical.choose_spec hwords) }

/-- Recover structural routing data for a retained initial packet frontier. -/
noncomputable def
    classified_inner_frontier
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (expansion : STExp H ι)
    (hexpansion :
      .frontier expansion ∈
        packet.outerClassifiedTerms normalizer factor
          innerWord rightWord hword) :
    SGFront H ι expansion := by
  let hwords :=
    packet
      |>.words_terms_frontier
        normalizer factor innerWord rightWord hword expansion hexpansion
  exact
    { innerWord := Classical.choose hwords
      rightWord := Classical.choose (Classical.choose_spec hwords)
      word_eq := Classical.choose_spec (Classical.choose_spec hwords) }

end SGFront

end TCTex
end Submission

/-!
# Generated packet routing for transient polynomial frontiers

Attached outputs of a classified transient polynomial packet recollect
immediately.  Once each retained frontier singleton has been recollected, the
whole packet therefore recollects in its original order.  This file packages
that fold for initial one-sided packets and for recursive two-sided packets
rooted at either chosen parent.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace PFSubsti.TAPkt

/--
Recollect an initial classified packet from recollections of its retained
generated frontier singletons.
-/
noncomputable def
    classified_frontier_recollections
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hlowerWeight :
      lowerWeight ≤ factor.word.weight HEAddres.weight)
    (frontierRecollection :
      ∀ expansion,
        .frontier expansion ∈
            packet.outerClassifiedTerms normalizer
              factor innerWord rightWord hword →
          TTRecoll
            n lowerWeight H [.frontier expansion]) :
    TTRecoll
      n lowerWeight H
        (packet.outerClassifiedTerms normalizer factor
          innerWord rightWord hword) :=
  TTRecoll.of_singletons
    _ fun term hterm => by
      cases term with
      | attached nextFactor =>
          exact
            TTRecoll.singleton_attached
              nextFactor <|
                hlowerWeight.trans <|
                  packet.least_classified_terms
                    normalizer factor innerWord rightWord hword
                      (.attached nextFactor) hterm
      | frontier expansion =>
          exact frontierRecollection expansion hterm

/--
Recollect a recursive two-sided packet from retained frontier recollections,
using its left parent for the physical support bound.
-/
noncomputable def
    recollection_frontier_recollections
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hlowerWeight :
      lowerWeight ≤ B.word.weight HEAddres.weight)
    (frontierRecollection :
      ∀ expansion,
        .frontier expansion ∈
            packet.polynomialTransientTerms normalizer B A →
          TTRecoll
            n lowerWeight H [.frontier expansion]) :
    TTRecoll
      n lowerWeight H
        (packet.polynomialTransientTerms normalizer B A) :=
  TTRecoll.of_singletons
    _ fun term hterm => by
      cases term with
      | attached factor =>
          exact
            TTRecoll.singleton_attached
              factor <|
                hlowerWeight.trans <| Nat.le_of_lt <|
                  packet.left_classified_terms
                    normalizer B A (.attached factor) hterm
      | frontier expansion =>
          exact frontierRecollection expansion hterm

/--
Recollect a recursive two-sided packet from retained frontier recollections,
using its right parent for the physical support bound.
-/
noncomputable def
    classified_terms_recollections
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hlowerWeight :
      lowerWeight ≤ A.word.weight HEAddres.weight)
    (frontierRecollection :
      ∀ expansion,
        .frontier expansion ∈
            packet.polynomialTransientTerms normalizer B A →
          TTRecoll
            n lowerWeight H [.frontier expansion]) :
    TTRecoll
      n lowerWeight H
        (packet.polynomialTransientTerms normalizer B A) :=
  TTRecoll.of_singletons
    _ fun term hterm => by
      cases term with
      | attached factor =>
          exact
            TTRecoll.singleton_attached
              factor <|
                hlowerWeight.trans <| Nat.le_of_lt <|
                  packet.transient_classified_terms
                    normalizer B A (.attached factor) hterm
      | frontier expansion =>
          exact frontierRecollection expansion hterm

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Structural routing for generated transient polynomial packets

Generated packet frontiers are syntactically commutator words.  The packet
folds can therefore pass a recovered decomposition to each singleton
frontier callback automa.  This is the structural restart boundary
needed before polynomial residual normalization is attached.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace PFSubsti.TAPkt

/--
Recollect an initial packet from structural restart callbacks for each
retained generated frontier.
-/
noncomputable def
    recollect_poly_recollections
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hlowerWeight :
      lowerWeight ≤ factor.word.weight HEAddres.weight)
    (frontierRecollection :
      ∀ expansion,
        .frontier expansion ∈
            packet.outerClassifiedTerms normalizer
              factor innerWord rightWord hword →
          SGFront H ι expansion →
            TTRecoll
              n lowerWeight H [.frontier expansion]) :
    TTRecoll
      n lowerWeight H
        (packet.outerClassifiedTerms normalizer factor
          innerWord rightWord hword) :=
  packet
    |>.classified_frontier_recollections
      normalizer factor innerWord rightWord hword hlowerWeight
        fun expansion hexpansion =>
          frontierRecollection expansion hexpansion <|
            SGFront.classified_inner_frontier
              packet normalizer factor innerWord rightWord hword expansion
                hexpansion

/--
Recollect a recursive packet from generated structural restart callbacks,
using its left parent for physical support.
-/
noncomputable def
    generated_frontier_recollections
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hlowerWeight :
      lowerWeight ≤ B.word.weight HEAddres.weight)
    (frontierRecollection :
      ∀ expansion,
        .frontier expansion ∈
            packet.polynomialTransientTerms normalizer B A →
          SGFront H ι expansion →
            TTRecoll
              n lowerWeight H [.frontier expansion]) :
    TTRecoll
      n lowerWeight H
        (packet.polynomialTransientTerms normalizer B A) :=
  packet
    |>.recollection_frontier_recollections
      normalizer B A hlowerWeight fun expansion hexpansion =>
        frontierRecollection expansion hexpansion <|
          SGFront.classified_frontier
            packet normalizer B A expansion hexpansion

/--
Recollect a recursive packet from generated structural restart callbacks,
using its right parent for physical support.
-/
noncomputable def
    transient_classified_recollections
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hlowerWeight :
      lowerWeight ≤ A.word.weight HEAddres.weight)
    (frontierRecollection :
      ∀ expansion,
        .frontier expansion ∈
            packet.polynomialTransientTerms normalizer B A →
          SGFront H ι expansion →
            TTRecoll
              n lowerWeight H [.frontier expansion]) :
    TTRecoll
      n lowerWeight H
        (packet.polynomialTransientTerms normalizer B A) :=
  packet
    |>.classified_terms_recollections
      normalizer B A hlowerWeight fun expansion hexpansion =>
        frontierRecollection expansion hexpansion <|
          SGFront.classified_frontier
            packet normalizer B A expansion hexpansion

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Generated commutator frontier boundary for transient polynomial recursion

All automatic transient routing has now been discharged except normalization
of an active generated frontier whose coefficient bound still exceeds its
physical Hall-word weight.  This file states that remaining callback exactly
and threads it through initial and recursive classified packets.  Terminal
frontiers erase without invoking the callback.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
The remaining semantic callback for generated transient polynomial words:
an active nonattachable commutator carrier may use strictly smaller supported
packet recollections.
-/
structure
    RRFtry
    (d n : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  sourceRecollection :
    ∀
      (lowerWeight : ℕ)
      (expansion : STExp H ι),
      SGFront H ι expansion →
        lowerWeight ≤ expansion.word.weight HEAddres.weight →
          expansion.word.weight HEAddres.weight < n →
            ¬ expansion.coefficientWeight ≤
                expansion.word.weight HEAddres.weight →
              (∀ child,
                SITerm.FrontierDefectMultiset
                    n child [.frontier expansion] →
                  SITerm.WordWeightLeast
                      lowerWeight child →
                    TTRecoll
                      n lowerWeight H child) →
                TTRecoll
                  n lowerWeight H [.frontier expansion]

namespace PFSubsti.TAPkt

/-- Every retained recursive frontier is still genuinely nonattachable. -/
lemma transient_classified_frontier
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A expansion : STExp H ι)
    (hexpansion :
      .frontier expansion ∈
        packet.polynomialTransientTerms normalizer B A) :
    ¬ expansion.coefficientWeight ≤
        expansion.word.weight HEAddres.weight := by
  rcases
      packet.recipe_classified_frontier
        normalizer B A expansion hexpansion with
    ⟨R, _, hnot, rfl⟩
  exact hnot

/-- Every retained initial frontier is still genuinely nonattachable. -/
lemma
    not_classified_frontier
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (expansion : STExp H ι)
    (hexpansion :
      .frontier expansion ∈
        packet.outerClassifiedTerms normalizer factor
          innerWord rightWord hword) :
    ¬ expansion.coefficientWeight ≤
        expansion.word.weight HEAddres.weight := by
  rw [outerClassifiedTerms] at hexpansion
  rcases List.mem_map.mp hexpansion with ⟨R, _, hterm⟩
  by_cases hbalanced : R.leftDegree ≤ R.rightDegree
  · rw [
      PIRed.classified_left_degree
        normalizer R factor innerWord rightWord hword hbalanced] at hterm
    cases hterm
  · have hfrontier : R.rightDegree < R.leftDegree :=
      Nat.lt_of_not_ge hbalanced
    rw [
      PIRed.classified_inner_outer
        normalizer R factor innerWord rightWord hword hfrontier] at hterm
    cases hterm
    exact fun hweight =>
      hbalanced <|
        (PIRed.coeff_outer_expansion
          normalizer R factor innerWord rightWord hword).mp hweight

/--
Route an initial classified packet through generated active nonattachable
frontier normalization, erasing terminal frontier words automa.
-/
noncomputable def
    recollect_nonattachable_frontier
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factory :
      RRFtry
        d n H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hlowerWeight :
      lowerWeight ≤ factor.word.weight HEAddres.weight)
    (recursiveResults :
      ∀ expansion,
        .frontier expansion ∈
            packet.outerClassifiedTerms normalizer
              factor innerWord rightWord hword →
          ∀ child,
            SITerm.FrontierDefectMultiset
                n child [.frontier expansion] →
              SITerm.WordWeightLeast
                  lowerWeight child →
                TTRecoll
                  n lowerWeight H child) :
    TTRecoll
      n lowerWeight H
        (packet.outerClassifiedTerms normalizer factor
          innerWord rightWord hword) :=
  packet
    |>.recollect_poly_recollections
      normalizer factor innerWord rightWord hword hlowerWeight
        fun expansion hexpansion generated => by
          by_cases hactive :
              expansion.word.weight HEAddres.weight < n
          · exact
              factory.sourceRecollection lowerWeight expansion generated
                (hlowerWeight.trans <|
                  packet.least_classified_terms
                    normalizer factor innerWord rightWord hword
                      (.frontier expansion) hexpansion)
                hactive
                (packet
                  |>.not_classified_frontier
                    normalizer factor innerWord rightWord hword expansion
                      hexpansion)
                (recursiveResults expansion hexpansion)
          · exact
              TTRecoll.singleton_frontier
                expansion <|
                  TTRecolla.singleton_n_weight
                    expansion (Nat.le_of_not_gt hactive)

/--
Route a recursive packet through generated frontier normalization, using its
left parent for physical support.
-/
noncomputable def
    nonattachable_frontier_factory
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factory :
      RRFtry
        d n H ι)
    (B A : STExp H ι)
    (hlowerWeight :
      lowerWeight ≤ B.word.weight HEAddres.weight)
    (recursiveResults :
      ∀ expansion,
        .frontier expansion ∈
            packet.polynomialTransientTerms normalizer B A →
          ∀ child,
            SITerm.FrontierDefectMultiset
                n child [.frontier expansion] →
              SITerm.WordWeightLeast
                  lowerWeight child →
                TTRecoll
                  n lowerWeight H child) :
    TTRecoll
      n lowerWeight H
        (packet.polynomialTransientTerms normalizer B A) :=
  packet
    |>.generated_frontier_recollections
      normalizer B A hlowerWeight fun expansion hexpansion generated => by
        by_cases hactive :
            expansion.word.weight HEAddres.weight < n
        · exact
            factory.sourceRecollection lowerWeight expansion generated
              (hlowerWeight.trans <| Nat.le_of_lt <|
                packet.left_classified_frontier
                  normalizer B A expansion hexpansion)
              hactive
              (packet
                |>.transient_classified_frontier
                  normalizer B A expansion hexpansion)
              (recursiveResults expansion hexpansion)
        · exact
            TTRecoll.singleton_frontier
              expansion <|
                TTRecolla.singleton_n_weight
                  expansion (Nat.le_of_not_gt hactive)

/--
Route a recursive packet through generated frontier normalization, using its
right parent for physical support.
-/
noncomputable def
    recollect_nonattachable_factory
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factory :
      RRFtry
        d n H ι)
    (B A : STExp H ι)
    (hlowerWeight :
      lowerWeight ≤ A.word.weight HEAddres.weight)
    (recursiveResults :
      ∀ expansion,
        .frontier expansion ∈
            packet.polynomialTransientTerms normalizer B A →
          ∀ child,
            SITerm.FrontierDefectMultiset
                n child [.frontier expansion] →
              SITerm.WordWeightLeast
                  lowerWeight child →
                TTRecoll
                  n lowerWeight H child) :
    TTRecoll
      n lowerWeight H
        (packet.polynomialTransientTerms normalizer B A) :=
  packet
    |>.transient_classified_recollections
      normalizer B A hlowerWeight fun expansion hexpansion generated => by
        by_cases hactive :
            expansion.word.weight HEAddres.weight < n
        · exact
            factory.sourceRecollection lowerWeight expansion generated
              (hlowerWeight.trans <| Nat.le_of_lt <|
                packet.transient_terms_frontier
                  normalizer B A expansion hexpansion)
              hactive
              (packet
                |>.transient_classified_frontier
                  normalizer B A expansion hexpansion)
              (recursiveResults expansion hexpansion)
        · exact
            TTRecoll.singleton_frontier
              expansion <|
                TTRecolla.singleton_n_weight
                  expansion (Nat.le_of_not_gt hactive)

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Inverting transient symbolic Hall polynomials

Transient polynomial carriers retain an explicit integral coefficient
formula, so they remain closed under negation even when that formula's
arithmetic bound does not fit the physical Hall word yet.  This file adds
negation and the corresponding reversed-negated inverse operation on finite
transient source lists.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace STExp

/--
Move a transient polynomial coefficient onto another Hall word while
retaining its arithmetic bound.
-/
def reword
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (wordExpansion : STExp H ι)
    (word : CWord (HEAddres H)) :
    STExp H ι where
  word := word
  coefficientWeight := wordExpansion.coefficientWeight
  coefficient := wordExpansion.coefficient

@[simp]
lemma word_reword
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (wordExpansion : STExp H ι)
    (word : CWord (HEAddres H)) :
    (wordExpansion.reword word).word = word :=
  rfl

@[simp]
lemma coefficientWeight_reword
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (wordExpansion : STExp H ι)
    (word : CWord (HEAddres H)) :
    (wordExpansion.reword word).coefficientWeight =
      wordExpansion.coefficientWeight :=
  rfl

@[simp]
lemma coefficient_eval_reword
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (wordExpansion : STExp H ι)
    (word : CWord (HEAddres H))
    (e : ι → HEFam H) :
    (wordExpansion.reword word).coefficient.eval e =
      wordExpansion.coefficient.eval e :=
  rfl

/-- Negate a transient polynomial coefficient without changing its Hall word. -/
def neg
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (wordExpansion : STExp H ι) :
    STExp H ι where
  word := wordExpansion.word
  coefficientWeight := wordExpansion.coefficientWeight
  coefficient := wordExpansion.coefficient.scaleRight (-1)

@[simp]
lemma word_neg
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (wordExpansion : STExp H ι) :
    wordExpansion.neg.word = wordExpansion.word :=
  rfl

@[simp]
lemma coefficientWeight_neg
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (wordExpansion : STExp H ι) :
    wordExpansion.neg.coefficientWeight = wordExpansion.coefficientWeight :=
  rfl

@[simp]
lemma coefficient_eval_neg
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (wordExpansion : STExp H ι)
    (e : ι → HEFam H) :
    wordExpansion.neg.coefficient.eval e =
      -wordExpansion.coefficient.eval e := by
  simp [neg, WBForm.eval_scaleRight]

@[simp]
lemma value_neg
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (wordExpansion : STExp H ι)
    (e : ι → HEFam H) :
    wordExpansion.neg.value (n := n) e =
      (wordExpansion.value e)⁻¹ := by
  rw [value, value, coefficient_eval_neg, zpow_neg, word_neg]

/-- Reverse a transient polynomial source while negating every coefficient. -/
def inverseList
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (source : List (STExp H ι)) :
    List (STExp H ι) :=
  source.reverse.map neg

/-- The transient polynomial inverse list evaluates to the inverse group element. -/
lemma list_value_inverse
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (source : List (STExp H ι))
    (e : ι → HEFam H) :
    listValue (n := n) e (inverseList source) = (listValue e source)⁻¹ := by
  induction source with
  | nil =>
      rfl
  | cons wordExpansion source ih =>
      rw [show inverseList (wordExpansion :: source) =
          inverseList source ++ [wordExpansion.neg] by
        simp [inverseList]]
      simp only [listValue, List.map_append, List.prod_append, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      change
        listValue (n := n) e (inverseList source) *
              wordExpansion.neg.value (n := n) e =
          (wordExpansion.value (n := n) e * listValue (n := n) e source)⁻¹
      rw [ih, value_neg]
      group

@[simp]
lemma neg_reword
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (wordExpansion : STExp H ι)
    (word : CWord (HEAddres H)) :
    (wordExpansion.reword word).neg = wordExpansion.neg.reword word :=
  rfl

end STExp

end TCTex
end Submission

/-!
# Residual sources for reworded transient polynomial commutators

Rewording a transient outer coefficient onto its inner Hall word produces a
temporary one-sided Hall-Petresco packet for `[inner ^ f, right]`.  The
original outer carrier differs from that temporary packet by a commutator
residual.  This file represents the residual without prematurely attaching
any transient term: reverse-negate the complete temporary packet, then append
the original outer carrier.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement
open HACoeff

namespace PIRed

/-- Every transient substituted word remembers its source block recipe. -/
lemma recipe_word_expansions
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {normalizer :
      WBForm.RCNormal H ι}
    {recipes : List BRecipe}
    {B : STExp H ι}
    {rightWord : CWord (HEAddres H)}
    {expansion : STExp H ι}
    (hexpansion :
      expansion ∈ wordExpansions normalizer recipes B rightWord) :
    ∃ R ∈ recipes, expansion = wordExpansion normalizer R B rightWord := by
  rcases List.mem_map.mp hexpansion with ⟨R, hR, rfl⟩
  exact ⟨R, hR, rfl⟩

/--
Every temporary recipe output is at least as heavy as the original outer
bracket whose coefficient was reworded onto the inner input.
-/
lemma outer_expansion_reword
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord) :
    outerExpansion.word.weight HEAddres.weight ≤
      (wordExpansion normalizer R (outerExpansion.reword innerWord)
        rightWord).word.weight HEAddres.weight := by
  rw [wordExpansion, weight_boundWord,
    STExp.word_reword]
  rw [hword, CWord.weight_commutator]
  exact Nat.add_le_add
    (Nat.le_mul_of_pos_left _
      (BRSpec.leftDegree_pos R))
    (Nat.le_mul_of_pos_left _
      (BRSpec.rightDegree_pos R))

/--
Same-stratum temporary outputs can occur only for a recipe of bidegree
`(1, 1)`.  Every other recipe is physically heavier than the parent bracket.
-/
lemma left_expansion_reword
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (heq :
      (wordExpansion normalizer R (outerExpansion.reword innerWord)
        rightWord).word.weight HEAddres.weight =
        outerExpansion.word.weight HEAddres.weight) :
    R.leftDegree = 1 ∧ R.rightDegree = 1 := by
  have hinner :
      0 < innerWord.weight HEAddres.weight :=
    CWord.weight_pos
      HEAddres.weight HEAddres.weight_pos innerWord
  have hright :
      0 < rightWord.weight HEAddres.weight :=
    CWord.weight_pos
      HEAddres.weight HEAddres.weight_pos rightWord
  have hleftDegree :=
    BRSpec.leftDegree_pos R
  have hrightDegree :=
    BRSpec.rightDegree_pos R
  rw [wordExpansion, weight_boundWord,
    STExp.word_reword] at heq
  change
    R.leftDegree * innerWord.weight HEAddres.weight +
          R.rightDegree * rightWord.weight HEAddres.weight =
      outerExpansion.word.weight HEAddres.weight at heq
  rw [hword, CWord.weight_commutator] at heq
  constructor
  · by_contra hne
    have htwo : 2 ≤ R.leftDegree := by
      omega
    have hleftMul :
        2 * innerWord.weight HEAddres.weight ≤
          R.leftDegree * innerWord.weight HEAddres.weight :=
      Nat.mul_le_mul_right _ htwo
    have hrightMul :
        rightWord.weight HEAddres.weight ≤
          R.rightDegree * rightWord.weight HEAddres.weight :=
      Nat.le_mul_of_pos_left _ hrightDegree
    omega
  · by_contra hne
    have htwo : 2 ≤ R.rightDegree := by
      omega
    have hleftMul :
        innerWord.weight HEAddres.weight ≤
          R.leftDegree * innerWord.weight HEAddres.weight :=
      Nat.le_mul_of_pos_left _ hleftDegree
    have hrightMul :
        2 * rightWord.weight HEAddres.weight ≤
          R.rightDegree * rightWord.weight HEAddres.weight :=
      Nat.mul_le_mul_right _ htwo
    omega

/--
Every temporary output whose recipe is not of bidegree `(1, 1)` is strictly
heavier than the original outer bracket.
-/
lemma outer_reword_bidegree
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hdegree : R.leftDegree ≠ 1 ∨ R.rightDegree ≠ 1) :
    outerExpansion.word.weight HEAddres.weight <
      (wordExpansion normalizer R (outerExpansion.reword innerWord)
        rightWord).word.weight HEAddres.weight := by
  apply lt_of_le_of_ne
    (outer_expansion_reword
      normalizer R outerExpansion innerWord rightWord hword)
  intro heq
  have hone :=
    left_expansion_reword
      normalizer R outerExpansion innerWord rightWord hword heq.symm
  exact hdegree.elim (fun hleft => hleft hone.1) (fun hright => hright hone.2)

end PIRed

namespace PFSubsti.TAPkt

open PIRed

/--
The transient polynomial quotient: inverse temporary correction followed by
the original outer carrier.
-/
def transientInnerSource
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    List (STExp H ι) :=
  STExp.inverseList
      (packet.rightTransientExpansions normalizer
        (outerExpansion.reword innerWord) rightWord) ++
    [outerExpansion]

/--
Every carrier in the transient quotient source is physically supported at
the original outer-bracket weight.
-/
theorem
    transient_inner_source
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (nextExpansion : STExp H ι)
    (hnext :
      nextExpansion ∈
        packet.transientInnerSource normalizer
          outerExpansion innerWord rightWord) :
    outerExpansion.word.weight HEAddres.weight ≤
      nextExpansion.word.weight HEAddres.weight := by
  rw [transientInnerSource] at hnext
  rcases List.mem_append.mp hnext with hnext | hnext
  · rw [STExp.inverseList] at hnext
    rcases List.mem_map.mp hnext with ⟨sourceExpansion, hsource, rfl⟩
    rw [STExp.word_neg]
    have hsource' :
        sourceExpansion ∈
          packet.rightTransientExpansions normalizer
            (outerExpansion.reword innerWord) rightWord := by
      simpa using hsource
    rw [rightTransientExpansions] at hsource'
    rcases recipe_word_expansions hsource' with ⟨R, _hR, rfl⟩
    exact
      outer_expansion_reword
        normalizer R outerExpansion innerWord rightWord hword
  · simp only [List.mem_singleton] at hnext
    subst nextExpansion
    exact le_rfl

/--
The transient residual is exactly the quotient of `[inner ^ f, right]` from
the original outer carrier.
-/
lemma transient_inner_outer
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (e : ι → HEFam H) :
    STExp.listValue (n := n) e
        (packet.transientInnerSource normalizer
          outerExpansion innerWord rightWord) =
      ⁅innerWord.eval
            (HEAddres.freeLowerTruncation
              (n := n)) ^
          outerExpansion.coefficient.eval e,
        rightWord.eval
          (HEAddres.freeLowerTruncation
            (n := n))⁆⁻¹ *
        outerExpansion.value e := by
  rw [transientInnerSource]
  simp only [STExp.listValue,
    List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
  change
    STExp.listValue (n := n) e
          (STExp.inverseList
            (packet.rightTransientExpansions normalizer
              (outerExpansion.reword innerWord) rightWord)) *
        outerExpansion.value (n := n) e =
      _
  rw [STExp.list_value_inverse,
    packet.list_transient_expansions]
  simp [STExp.value]
  rfl

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Semantics of the basic transient polynomial rewording term

The principal `(1, 1)` Hall-Petresco recipe produced while recollecting
`[inner ^ f, right]` carries the same word and coefficient value as the
original outer carrier `[inner, right] ^ f`.  This file records that semantic
cancellation point independently of any ordering or tail-recollection
strategy.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace PIRed

open BRSpec

/-- The principal temporary output after rewording an outer coefficient inward. -/
def rewordedBasicExpansion
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    STExp H ι :=
  wordExpansion normalizer hallPair (outerExpansion.reword innerWord) rightWord

/-- The principal temporary output has the expected outer bracket word. -/
@[simp]
lemma word_reworded_expansion
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    (rewordedBasicExpansion normalizer outerExpansion innerWord
      rightWord).word = .commutator innerWord rightWord := by
  simp [rewordedBasicExpansion, wordExpansion, boundWord]

/-- The principal temporary output retains the outer arithmetic bound. -/
@[simp]
lemma coefficient_reworded_expansion
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    (rewordedBasicExpansion normalizer outerExpansion innerWord
      rightWord).coefficientWeight = outerExpansion.coefficientWeight := by
  simp [rewordedBasicExpansion, wordExpansion]

/-- The principal temporary output retains the outer coefficient value. -/
@[simp]
lemma reworded_basic_expansion
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (e : ι → HEFam H) :
    (rewordedBasicExpansion normalizer outerExpansion innerWord
      rightWord).coefficient.eval e =
        outerExpansion.coefficient.eval e := by
  rw [rewordedBasicExpansion, wordExpansion, eval_coefficientFormula]
  simp
  rfl

/-- When the parent carries the expected bracket, the principal words agree. -/
lemma reworded_expansion_outer
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord) :
    (rewordedBasicExpansion normalizer outerExpansion innerWord
      rightWord).word = outerExpansion.word := by
  rw [word_reworded_expansion, hword]

/-- The principal temporary output evaluates exactly to its outer parent. -/
lemma reworded_pair_outer
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (e : ι → HEFam H) :
    (rewordedBasicExpansion normalizer outerExpansion innerWord
      rightWord).value (n := n) e = outerExpansion.value e := by
  simp only [STExp.value,
    reworded_expansion_outer normalizer outerExpansion
      innerWord rightWord hword,
    reworded_basic_expansion]

/-- The inverse principal output evaluates to the inverse outer parent. -/
lemma value_reworded_inv
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (e : ι → HEFam H) :
    (rewordedBasicExpansion normalizer outerExpansion innerWord
      rightWord).neg.value (n := n) e =
        (outerExpansion.value e)⁻¹ := by
  rw [STExp.value_neg,
    reworded_pair_outer normalizer outerExpansion
      innerWord rightWord hword e]

end PIRed

end TCTex
end Submission

/-!
# Strict tails around the basic transient polynomial Hall-Petresco term

The transient polynomial residual contains one same-stratum basic term and
higher-weight correction terms.  The basic term need not sit at either end of
the ordered packet.  This file records an ordered
`prefix ++ basic :: suffix` interface and proves that both nonbasic sides
become strictly heavier after rewording.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HACoeff
open BRSpec

namespace PIRed

/-- Every recipe in a tail has bidegree different from `(1, 1)`. -/
def SOTail
    (recipes : List BRecipe) :
    Prop :=
  ∀ R ∈ recipes, R.leftDegree ≠ 1 ∨ R.rightDegree ≠ 1

namespace SOTail

/-- The empty recipe list is a strict outer tail. -/
lemma nil :
    SOTail [] := by
  intro R hR
  simp at hR

/-- Concatenating strict tails preserves strictness. -/
lemma append
    {left right : List BRecipe}
    (hleft : SOTail left)
    (hright : SOTail right) :
    SOTail (left ++ right) := by
  intro R hR
  rcases List.mem_append.mp hR with hR | hR
  · exact hleft R hR
  · exact hright R hR

end SOTail

/--
Every member of a strict temporary reworded tail is physically heavier than
the original outer bracket.
-/
theorem outer_expansions_reword
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    {recipes : List BRecipe}
    (htail : SOTail recipes)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (nextExpansion : STExp H ι)
    (hnext :
      nextExpansion ∈
        wordExpansions normalizer recipes (outerExpansion.reword innerWord)
          rightWord) :
    outerExpansion.word.weight HEAddres.weight <
      nextExpansion.word.weight HEAddres.weight := by
  rcases recipe_word_expansions hnext with ⟨R, hR, rfl⟩
  exact
    outer_reword_bidegree
      normalizer R outerExpansion innerWord rightWord hword (htail R hR)

/--
Reverse-negating a strict temporary tail preserves its strict physical
support bound.
-/
theorem
    expansions_reword_tail
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    {recipes : List BRecipe}
    (htail : SOTail recipes)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (nextExpansion : STExp H ι)
    (hnext :
      nextExpansion ∈
        STExp.inverseList
          (wordExpansions normalizer recipes
            (outerExpansion.reword innerWord) rightWord)) :
    outerExpansion.word.weight HEAddres.weight <
      nextExpansion.word.weight HEAddres.weight := by
  rw [STExp.inverseList] at hnext
  rcases List.mem_map.mp hnext with ⟨sourceExpansion, hsource, rfl⟩
  rw [STExp.word_neg]
  apply
    outer_expansions_reword
      normalizer htail outerExpansion innerWord rightWord hword
  simpa using hsource

end PIRed

namespace PFSubsti.TAPkt

open PIRed

/--
An ordered packet decomposition around its same-stratum basic recipe.

Both sides are retained separately because inversion reverses the complete
temporary packet, so their relative position matters to later recollection.
-/
structure PBSplit
    {d n : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n) where
  beforeBasic :
    List BRecipe
  afterBasic :
    List BRecipe
  recipes_eq :
    packet.recipes = beforeBasic ++ hallPair :: afterBasic
  before_strict_tail :
    SOTail beforeBasic
  after_strict_tail :
    SOTail afterBasic

namespace PBSplit

/-- The nonbasic recipes on both sides form a strict outer tail. -/
def strictRecipes
    {d n : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet) :
    List BRecipe :=
  split.beforeBasic ++ split.afterBasic

/-- Every recipe retained away from the basic term has nonbasic bidegree. -/
lemma strict_recipes_tail
    {d n : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet) :
    SOTail split.strictRecipes :=
  split.before_strict_tail.append split.after_strict_tail

/-- Transient substitution preserves the ordered split around the basic term. -/
lemma expans_prefi_suffi
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    wordExpansions normalizer packet.recipes B rightWord =
      wordExpansions normalizer split.beforeBasic B rightWord ++
        [wordExpansion normalizer hallPair B rightWord] ++
          wordExpansions normalizer split.afterBasic B rightWord := by
  rw [split.recipes_eq]
  simp [wordExpansions]

/--
After inversion, the suffix moves before the basic inverse and the prefix
moves after it.  This is the ordered shape needed for contextual cancellation.
-/
lemma expans_suffi_prefi
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    STExp.inverseList
        (wordExpansions normalizer packet.recipes B rightWord) =
      STExp.inverseList
          (wordExpansions normalizer split.afterBasic B rightWord) ++
        [(wordExpansion normalizer hallPair B rightWord).neg] ++
          STExp.inverseList
            (wordExpansions normalizer split.beforeBasic B rightWord) := by
  rw [split.expans_prefi_suffi]
  simp [STExp.inverseList]

/--
The full residual source exposes both strict inverse tails around the basic
inverse, followed by the original outer carrier.
-/
lemma inner_after_before
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    packet.transientInnerSource normalizer
        outerExpansion innerWord rightWord =
      STExp.inverseList
          (wordExpansions normalizer split.afterBasic
            (outerExpansion.reword innerWord) rightWord) ++
        [(wordExpansion normalizer hallPair (outerExpansion.reword innerWord)
          rightWord).neg] ++
        STExp.inverseList
            (wordExpansions normalizer split.beforeBasic
              (outerExpansion.reword innerWord) rightWord) ++
          [outerExpansion] := by
  rw [transientInnerSource,
    rightTransientExpansions,
    split.expans_suffi_prefi]

end PBSplit

/-- The cutoff-three singleton packet has an empty strict prefix and suffix. -/
def poly_split_n
    {d n : ℕ}
    (hn : n ≤ 3) :
    PBSplit
      (n_three hn :
        PFSubsti.TAPkt.{u}
          d n) where
  beforeBasic := []
  afterBasic := []
  recipes_eq := by rfl
  before_strict_tail := SOTail.nil
  after_strict_tail := SOTail.nil

/--
The cutoff-four packet keeps the left triple before the basic term and the
right triple after it.
-/
def poly_split_four
    {d n : ℕ}
    (hn : n ≤ 4) :
    PBSplit
      (n_four hn :
        PFSubsti.TAPkt.{u}
          d n) where
  beforeBasic := [leftTriple]
  afterBasic := [rightTriple]
  recipes_eq := by rfl
  before_strict_tail := by
    intro R hR
    simp only [List.mem_singleton] at hR
    subst R
    left
    simp [leftTriple, BRecipe.leftDegree]
  after_strict_tail := by
    intro R hR
    simp only [List.mem_singleton] at hR
    subst R
    right
    simp [rightTriple, BRecipe.rightDegree]

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Classifying arbitrary one-sided transient polynomial packets

The specialized unit-right Hall-Petresco substitution expands `[B ^ f, right]`
without pretending that the right exponent one is a homogeneous polynomial.
This file classifies those outputs by exact attachability.  It is the
arbitrary-transient counterpart of the initial ordinary-factor classifier.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

namespace PIRed

/-- Classify one unit-right transient recipe output by exact attachability. -/
def classifiedUnitTransient
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : HACoeff.BRecipe)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    SITerm H ι :=
  let expansion := wordExpansion normalizer R B rightWord
  if hweight :
      expansion.coefficientWeight ≤
        expansion.word.weight HEAddres.weight then
    .attached (expansion.toFactor hweight)
  else
    .frontier expansion

/-- An attachable unit-right output returns to the permanent factor API. -/
lemma classified_transient_attached
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : HACoeff.BRecipe)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H))
    (hweight :
      (wordExpansion normalizer R B rightWord).coefficientWeight ≤
        (wordExpansion normalizer R B rightWord).word.weight
          HEAddres.weight) :
    classifiedUnitTransient normalizer R B rightWord =
      .attached ((wordExpansion normalizer R B rightWord).toFactor hweight) := by
  unfold classifiedUnitTransient
  dsimp only
  rw [dif_pos hweight]

/-- A nonattachable unit-right output remains a transient frontier. -/
lemma classified_transient_frontier
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : HACoeff.BRecipe)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H))
    (hweight :
      ¬ (wordExpansion normalizer R B rightWord).coefficientWeight ≤
        (wordExpansion normalizer R B rightWord).word.weight
          HEAddres.weight) :
    classifiedUnitTransient normalizer R B rightWord =
      .frontier (wordExpansion normalizer R B rightWord) := by
  unfold classifiedUnitTransient
  dsimp only
  rw [dif_neg hweight]

/-- Classification preserves the represented unit-right transient value. -/
lemma value_transient_term
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : HACoeff.BRecipe)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H))
    (e : ι → HEFam H) :
    (classifiedUnitTransient normalizer R B rightWord).value
        (n := n) e =
      (wordExpansion normalizer R B rightWord).value e := by
  by_cases hweight :
      (wordExpansion normalizer R B rightWord).coefficientWeight ≤
        (wordExpansion normalizer R B rightWord).word.weight
          HEAddres.weight
  · rw [classified_transient_attached
      normalizer R B rightWord hweight]
    exact STExp.eval_toFactor _ _ e
  · rw [
      classified_transient_frontier
        normalizer R B rightWord hweight]
    rfl

/-- Classifying an ordered unit-right recipe list preserves its product. -/
lemma value_classified_transient
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (recipes : List HACoeff.BRecipe)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H))
    (e : ι → HEFam H) :
    SITerm.listValue (n := n) e
        (recipes.map fun R =>
          classifiedUnitTransient normalizer R B rightWord) =
      STExp.listValue (n := n) e
        (recipes.map fun R => wordExpansion normalizer R B rightWord) := by
  induction recipes with
  | nil =>
      rfl
  | cons R recipes ih =>
      change
        (classifiedUnitTransient normalizer R B rightWord).value e *
              SITerm.listValue e
                (recipes.map fun nextR =>
                  classifiedUnitTransient normalizer nextR B
                    rightWord) =
          (wordExpansion normalizer R B rightWord).value e *
              STExp.listValue e
                (recipes.map fun nextR =>
                  wordExpansion normalizer nextR B rightWord)
      rw [value_transient_term, ih]

end PIRed

namespace PFSubsti.TAPkt

open PIRed

/-- Classify a complete specialized unit-right transient packet in place. -/
def polynomialClassifiedTerms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    List (SITerm H ι) :=
  packet.recipes.map fun R =>
    classifiedUnitTransient normalizer R B rightWord

/-- The classified unit-right packet still evaluates to `[B ^ f, right]`. -/
lemma list_classified_terms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H))
    (e : ι → HEFam H) :
    SITerm.listValue (n := n) e
        (packet.polynomialClassifiedTerms normalizer B
          rightWord) =
      ⁅B.value (n := n) e,
        rightWord.eval
          (HEAddres.freeLowerTruncation
            (n := n))⁆ := by
  rw [polynomialClassifiedTerms,
    value_classified_transient]
  exact packet.list_transient_expansions normalizer B
    rightWord e

/--
Classify the temporary packet emitted after moving an arbitrary transient
outer coefficient onto the selected inner Hall word.
-/
def innerClassifiedTerms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    List (SITerm H ι) :=
  packet.polynomialClassifiedTerms normalizer
    (outerExpansion.reword innerWord) rightWord

/-- The classified temporary packet evaluates to `[inner ^ f, right]`. -/
lemma transient_inner_terms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (e : ι → HEFam H) :
    SITerm.listValue (n := n) e
        (packet.innerClassifiedTerms
          normalizer outerExpansion innerWord rightWord) =
      ⁅innerWord.eval
            (HEAddres.freeLowerTruncation
              (n := n)) ^
          outerExpansion.coefficient.eval e,
        rightWord.eval
          (HEAddres.freeLowerTruncation
            (n := n))⁆ := by
  rw [innerClassifiedTerms,
    packet.list_classified_terms]
  change
    ⁅innerWord.eval
          (HEAddres.freeLowerTruncation
            (n := n)) ^
        (outerExpansion.reword innerWord).coefficient.eval e,
      rightWord.eval
        (HEAddres.freeLowerTruncation
          (n := n))⁆ =
      _
  rw [STExp.coefficient_eval_reword]

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Polynomial ordered basic splits from principal packet inventory

The polynomial transient residual uses the same packet inventory as the
powered residual, but its strict-tail witness lives in the polynomial
transient-word layer.  This file transports principal packet inventory into
that ordered polynomial split.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace PFSubsti.TAPkt

open BRSpec

/--
A polynomial packet has a principal basic recipe when it emits `basic` and
no other recipe has bidegree `(1, 1)`.
-/
structure PPRecipe
    {d n : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n) : Prop where
  basic_mem :
    hallPair ∈ packet.recipes
  basic_bidegree_one :
    ∀ R ∈ packet.recipes,
      R.leftDegree = 1 →
        R.rightDegree = 1 →
          R = hallPair

end PFSubsti.TAPkt

namespace
  PFSubsti.TAPkt.PBSplit

open BRSpec
open PIRed

/-- Forget the ordered polynomial tails while retaining principal inventory. -/
def principalBasicRecipe
    {d n : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : packet.PBSplit) :
    packet.PPRecipe where
  basic_mem := by
    rw [split.recipes_eq]
    simp
  basic_bidegree_one := by
    intro R hR hleft hright
    rw [split.recipes_eq] at hR
    rcases List.mem_append.mp hR with hR | hR
    · exact False.elim <|
        (split.before_strict_tail R hR).elim
          (fun hne => hne hleft) (fun hne => hne hright)
    · rcases List.mem_cons.mp hR with rfl | hR
      · rfl
      · exact False.elim <|
          (split.after_strict_tail R hR).elim
            (fun hne => hne hleft) (fun hne => hne hright)

end
  PFSubsti.TAPkt.PBSplit

namespace
  PFSubsti.TAPkt.PPRecipe

open HACoeff
open BRSpec
open PIRed

/--
A duplicate-free packet with a principal basic recipe admits an ordered
polynomial decomposition around that recipe.  Every recipe in either tail is
strict.
-/
noncomputable def basic_split_nodup
    {d n : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (principal : packet.PPRecipe)
    (hnodup : packet.recipes.Nodup) :
    packet.PBSplit := by
  let hsplit := List.mem_iff_append.mp principal.basic_mem
  let beforeBasic := Classical.choose hsplit
  let afterBasic := Classical.choose (Classical.choose_spec hsplit)
  have hrecipes :
      packet.recipes = beforeBasic ++ hallPair :: afterBasic :=
    Classical.choose_spec (Classical.choose_spec hsplit)
  have hnodup' : (beforeBasic ++ hallPair :: afterBasic).Nodup := by
    simpa only [hrecipes] using hnodup
  have hbasicNotBefore : hallPair ∉ beforeBasic := by
    intro hbasic
    exact
      (List.nodup_append.mp hnodup').2.2 hallPair hbasic hallPair (by simp) rfl
  have hbasicNotAfter : hallPair ∉ afterBasic :=
    (List.nodup_cons.mp (List.nodup_append.mp hnodup').2.1).1
  refine
    { beforeBasic := beforeBasic
      afterBasic := afterBasic
      recipes_eq := hrecipes
      before_strict_tail := ?_
      after_strict_tail := ?_ }
  · intro R hR
    by_cases hleft : R.leftDegree = 1
    · by_cases hright : R.rightDegree = 1
      · have hRbasic :
            R = hallPair :=
          principal.basic_bidegree_one R (by
            rw [hrecipes]
            simp [hR]) hleft hright
        exact False.elim (hbasicNotBefore (hRbasic ▸ hR))
      · exact Or.inr hright
    · exact Or.inl hleft
  · intro R hR
    by_cases hleft : R.leftDegree = 1
    · by_cases hright : R.rightDegree = 1
      · have hRbasic :
            R = hallPair :=
          principal.basic_bidegree_one R (by
            rw [hrecipes]
            simp [hR]) hleft hright
        exact False.elim (hbasicNotAfter (hRbasic ▸ hR))
      · exact Or.inr hright
    · exact Or.inl hleft

end
  PFSubsti.TAPkt.PPRecipe

end TCTex
end Submission

/-!
# Ordered semantics of transient polynomial rewording residuals

An ordered split around the principal basic recipe leaves two strict inverse
tails.  The basic inverse evaluates to the inverse parent, but the strict
prefix still sits between it and the appended parent.  This file records that
noncommutative shape without commuting any factors.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace STExp

/-- Transient source evaluation preserves ordered concatenation. -/
@[simp]
lemma listValue_append
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (left right :
      List (STExp H ι)) :
    listValue (n := n) e (left ++ right) =
      listValue e left * listValue e right := by
  simp [listValue]

/-- Transient evaluation of a singleton is evaluation of its carrier. -/
@[simp]
lemma listValue_singleton
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (wordExpansion : STExp H ι) :
    listValue (n := n) e [wordExpansion] =
      wordExpansion.value e := by
  simp [listValue]

end STExp

namespace PFSubsti.TAPkt
namespace PBSplit

open PIRed

/-- Reverse-negated strict suffix emitted before the principal inverse. -/
def strictAfterSource
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    List (STExp H ι) :=
  STExp.inverseList
    (wordExpansions normalizer split.afterBasic
      (outerExpansion.reword innerWord) rightWord)

/-- Reverse-negated strict prefix emitted after the principal inverse. -/
def strictBeforeSource
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    List (STExp H ι) :=
  STExp.inverseList
    (wordExpansions normalizer split.beforeBasic
      (outerExpansion.reword innerWord) rightWord)

/-- Both strict inverse tails, forgetting the principal carrier between them. -/
def strictInverseSource
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    List (STExp H ι) :=
  split.strictAfterSource normalizer outerExpansion innerWord
      rightWord ++
    split.strictBeforeSource normalizer outerExpansion innerWord
      rightWord

/--
The residual source is the strict suffix, principal inverse, strict prefix,
and parent in that exact order.
-/
lemma transient_after_before
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    packet.transientInnerSource normalizer
        outerExpansion innerWord rightWord =
      split.strictAfterSource normalizer outerExpansion innerWord
          rightWord ++
        [(rewordedBasicExpansion normalizer outerExpansion innerWord
          rightWord).neg] ++
        split.strictBeforeSource normalizer outerExpansion innerWord
            rightWord ++
          [outerExpansion] := by
  rw [split.inner_after_before]
  rfl

/-- Every carrier in the reverse-negated suffix is strictly heavier. -/
theorem outer_after_source
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (nextExpansion : STExp H ι)
    (hnext :
      nextExpansion ∈
        split.strictAfterSource normalizer outerExpansion innerWord
          rightWord) :
    outerExpansion.word.weight HEAddres.weight <
      nextExpansion.word.weight HEAddres.weight := by
  apply
    expansions_reword_tail
      normalizer split.after_strict_tail outerExpansion innerWord
        rightWord hword nextExpansion
  exact hnext

/-- Every carrier in the reverse-negated prefix is strictly heavier. -/
theorem outer_before_source
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (nextExpansion : STExp H ι)
    (hnext :
      nextExpansion ∈
        split.strictBeforeSource normalizer outerExpansion innerWord
          rightWord) :
    outerExpansion.word.weight HEAddres.weight <
      nextExpansion.word.weight HEAddres.weight := by
  apply
    expansions_reword_tail
      normalizer split.before_strict_tail outerExpansion innerWord
        rightWord hword nextExpansion
  exact hnext

/-- Every carrier in either strict inverse tail is strictly heavier. -/
theorem outer_strict_source
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (nextExpansion : STExp H ι)
    (hnext :
      nextExpansion ∈
        split.strictInverseSource normalizer outerExpansion innerWord
          rightWord) :
    outerExpansion.word.weight HEAddres.weight <
      nextExpansion.word.weight HEAddres.weight := by
  rcases List.mem_append.mp hnext with hnext | hnext
  · exact split.outer_after_source
      normalizer outerExpansion innerWord rightWord hword nextExpansion hnext
  · exact split.outer_before_source
      normalizer outerExpansion innerWord rightWord hword nextExpansion hnext

/--
The ordered residual evaluates to a strict suffix, the parent inverse, the
strict prefix, and the parent.  The middle conjugation must be preserved.
-/
lemma raw_strict_tails
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (e : ι → HEFam H) :
    STExp.listValue (n := n) e
        (packet.transientInnerSource normalizer
          outerExpansion innerWord rightWord) =
      STExp.listValue e
          (split.strictAfterSource normalizer outerExpansion innerWord
            rightWord) *
        (outerExpansion.value e)⁻¹ *
        STExp.listValue e
            (split.strictBeforeSource normalizer outerExpansion
              innerWord rightWord) *
          outerExpansion.value e := by
  rw [
    split.transient_after_before,
    STExp.listValue_append,
    STExp.listValue_append,
    STExp.listValue_append,
    STExp.listValue_singleton,
    STExp.listValue_singleton,
    value_reworded_inv normalizer outerExpansion
      innerWord rightWord hword e]

end PBSplit
end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Generated routing for arbitrary one-sided transient polynomial packets

The exact unit-right classifier returns attachable outputs immediately and
retains only genuinely nonattachable transient frontiers.  Every retained
frontier remembers its recipe, is physically supported above the original
outer commutator, and is itself a generated commutator word.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace PFSubsti.TAPkt

open PIRed

/-- Recover the recipe of one retained specialized unit-right frontier. -/
lemma classified_terms_frontier
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B expansion : STExp H ι)
    (rightWord : CWord (HEAddres H))
    (hexpansion :
      .frontier expansion ∈
        packet.polynomialClassifiedTerms normalizer B
          rightWord) :
    ∃ R ∈ packet.recipes,
      ¬ (wordExpansion normalizer R B rightWord).coefficientWeight ≤
          (wordExpansion normalizer R B rightWord).word.weight
            HEAddres.weight ∧
        expansion = wordExpansion normalizer R B rightWord := by
  rw [polynomialClassifiedTerms] at hexpansion
  rcases List.mem_map.mp hexpansion with ⟨R, hR, hterm⟩
  refine ⟨R, hR, ?_⟩
  by_cases hweight :
      (wordExpansion normalizer R B rightWord).coefficientWeight ≤
        (wordExpansion normalizer R B rightWord).word.weight
          HEAddres.weight
  · rw [
      classified_transient_attached
        normalizer R B rightWord hweight] at hterm
    cases hterm
  · rw [
      classified_transient_frontier
        normalizer R B rightWord hweight] at hterm
    cases hterm
    exact ⟨hweight, rfl⟩

/-- Every classified unit-right output is physically above its left parent. -/
lemma left_transient_classified
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H))
    (term : SITerm H ι)
    (hterm :
      term ∈
        packet.polynomialClassifiedTerms normalizer B
          rightWord) :
    B.word.weight HEAddres.weight < term.wordWeight := by
  rw [polynomialClassifiedTerms] at hterm
  rcases List.mem_map.mp hterm with ⟨R, _, rfl⟩
  by_cases hweight :
      (wordExpansion normalizer R B rightWord).coefficientWeight ≤
        (wordExpansion normalizer R B rightWord).word.weight
          HEAddres.weight
  · rw [
      classified_transient_attached
        normalizer R B rightWord hweight]
    exact left_weight_expansion normalizer R B rightWord
  · rw [
      classified_transient_frontier
        normalizer R B rightWord hweight]
    exact left_weight_expansion normalizer R B rightWord

/--
Every classified temporary output is physically supported at its original
outer commutator weight.
-/
lemma
    poly_classified_terms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (term : SITerm H ι)
    (hterm :
      term ∈
        packet.innerClassifiedTerms
          normalizer outerExpansion innerWord rightWord) :
    outerExpansion.word.weight HEAddres.weight ≤ term.wordWeight := by
  rw [innerClassifiedTerms,
    polynomialClassifiedTerms] at hterm
  rcases List.mem_map.mp hterm with ⟨R, _, rfl⟩
  by_cases hweight :
      (wordExpansion normalizer R (outerExpansion.reword innerWord)
          rightWord).coefficientWeight ≤
        (wordExpansion normalizer R (outerExpansion.reword innerWord)
          rightWord).word.weight HEAddres.weight
  · rw [
      classified_transient_attached
        normalizer R (outerExpansion.reword innerWord) rightWord hweight]
    exact
      outer_expansion_reword normalizer R
        outerExpansion innerWord rightWord hword
  · rw [
      classified_transient_frontier
        normalizer R (outerExpansion.reword innerWord) rightWord hweight]
    exact
      outer_expansion_reword normalizer R
        outerExpansion innerWord rightWord hword

/--
Every retained temporary frontier is a generated commutator word with its
decomposition recorded for structural restart routing.
-/
noncomputable def
    frontier_classified_terms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion expansion :
      STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hexpansion :
      .frontier expansion ∈
        packet.innerClassifiedTerms
          normalizer outerExpansion innerWord rightWord) :
    SGFront H ι expansion := by
  let hrecipe :=
    packet.classified_terms_frontier
      normalizer (outerExpansion.reword innerWord) expansion rightWord
        hexpansion
  let R := Classical.choose hrecipe
  have hexpansion_eq :
      expansion =
        wordExpansion normalizer R (outerExpansion.reword innerWord)
          rightWord :=
    (Classical.choose_spec hrecipe).2.2
  let hwords :=
    PIRed.word_expansion_commutator
      normalizer R (outerExpansion.reword innerWord) rightWord
  exact
    { innerWord := Classical.choose hwords
      rightWord := Classical.choose (Classical.choose_spec hwords)
      word_eq := by
        rw [hexpansion_eq]
        exact Classical.choose_spec (Classical.choose_spec hwords) }

/--
Recollect one complete temporary packet from generated-frontier callbacks,
closing every attached output in place.
-/
noncomputable def
    recollect_frontier_recollections
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hlowerWeight :
      lowerWeight ≤ outerExpansion.word.weight HEAddres.weight)
    (frontierRecollection :
      ∀ expansion,
        .frontier expansion ∈
            packet.innerClassifiedTerms
              normalizer outerExpansion innerWord rightWord →
          SGFront H ι expansion →
            TTRecoll
              n lowerWeight H [.frontier expansion]) :
    TTRecoll
      n lowerWeight H
        (packet.innerClassifiedTerms
          normalizer outerExpansion innerWord rightWord) :=
  TTRecoll.of_singletons
    _ fun term hterm => by
      cases term with
      | attached factor =>
          exact
            TTRecoll.singleton_attached
              factor <|
                hlowerWeight.trans <|
                  packet
                    |>.poly_classified_terms
                      normalizer outerExpansion innerWord rightWord hword
                        (.attached factor) hterm
      | frontier expansion =>
          exact
            frontierRecollection expansion hterm <|
              packet
                |>.frontier_classified_terms
                  normalizer outerExpansion expansion innerWord rightWord hterm

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Polynomial ordered basic splits from a unique principal occurrence

Polynomial transient restart routing only needs the distinguished `basic`
recipe to occur once.  Duplicate nonbasic recipes remain valid strict-tail
terms and need not be ruled out.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace PFSubsti.TAPkt

open HACoeff
open BRSpec

/--
The polynomial packet contains exactly one occurrence of its principal
`basic` recipe.  Repeated nonbasic recipes remain permitted.
-/
def UniqueBasicOccurrence
    {d n : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n) :
    Prop :=
  ∃ beforeBasic afterBasic : List BRecipe,
    packet.recipes = beforeBasic ++ hallPair :: afterBasic ∧
      hallPair ∉ beforeBasic ∧
        hallPair ∉ afterBasic

end PFSubsti.TAPkt

namespace
  PFSubsti.TAPkt.PBSplit

open HACoeff
open BRSpec
open PIRed

/--
An ordered polynomial basic split records exactly one occurrence of the
principal `basic` recipe.
-/
def uniqueBasicOccurrence
    {d n : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : packet.PBSplit) :
    packet.UniqueBasicOccurrence := by
  refine
    ⟨split.beforeBasic, split.afterBasic, split.recipes_eq, ?_, ?_⟩
  · intro hbasic
    exact
      (split.before_strict_tail hallPair hbasic).elim
        (fun h => h left_hall_pair)
        (fun h => h right_degree_pair)
  · intro hbasic
    exact
      (split.after_strict_tail hallPair hbasic).elim
        (fun h => h left_hall_pair)
        (fun h => h right_degree_pair)

end
  PFSubsti.TAPkt.PBSplit

namespace
  PFSubsti.TAPkt.PPRecipe

open HACoeff
open BRSpec
open PIRed

/--
A packet with a principal basic recipe and exactly one occurrence of `basic`
admits an ordered polynomial decomposition around that recipe.  Repeated
nonbasic tail recipes are allowed.
-/
noncomputable def split_unique_pair
    {d n : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (principal : packet.PPRecipe)
    (hunique : packet.UniqueBasicOccurrence) :
    packet.PBSplit := by
  let beforeBasic := Classical.choose hunique
  let afterBasic := Classical.choose (Classical.choose_spec hunique)
  have hspec :=
    Classical.choose_spec (Classical.choose_spec hunique)
  have hrecipes :
      packet.recipes = beforeBasic ++ hallPair :: afterBasic :=
    hspec.1
  have hbasicNotBefore : hallPair ∉ beforeBasic :=
    hspec.2.1
  have hbasicNotAfter : hallPair ∉ afterBasic :=
    hspec.2.2
  refine
    { beforeBasic := beforeBasic
      afterBasic := afterBasic
      recipes_eq := hrecipes
      before_strict_tail := ?_
      after_strict_tail := ?_ }
  · intro R hR
    by_cases hleft : R.leftDegree = 1
    · by_cases hright : R.rightDegree = 1
      · have hRbasic :
            R = hallPair :=
          principal.basic_bidegree_one R (by
            rw [hrecipes]
            simp [hR]) hleft hright
        exact False.elim (hbasicNotBefore (hRbasic ▸ hR))
      · exact Or.inr hright
    · exact Or.inl hleft
  · intro R hR
    by_cases hleft : R.leftDegree = 1
    · by_cases hright : R.rightDegree = 1
      · have hRbasic :
            R = hallPair :=
          principal.basic_bidegree_one R (by
            rw [hrecipes]
            simp [hR]) hleft hright
        exact False.elim (hbasicNotAfter (hRbasic ▸ hR))
      · exact Or.inr hright
    · exact Or.inl hleft

end
  PFSubsti.TAPkt.PPRecipe

namespace
  PFSubsti.TAPkt.PPRecipe

open HACoeff
open BRSpec

/--
Duplicate-free polynomial principal inventory implies the sharper
unique-basic-occurrence condition.  Repeated nonbasic recipes are not needed
for this sufficient condition.
-/
noncomputable def unique_occurrence_nodup
    {d n : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (principal : packet.PPRecipe)
    (hnodup : packet.recipes.Nodup) :
    packet.UniqueBasicOccurrence := by
  let hsplit := List.mem_iff_append.mp principal.basic_mem
  let beforeBasic := Classical.choose hsplit
  let afterBasic := Classical.choose (Classical.choose_spec hsplit)
  have hrecipes :
      packet.recipes = beforeBasic ++ hallPair :: afterBasic :=
    Classical.choose_spec (Classical.choose_spec hsplit)
  have hnodup' : (beforeBasic ++ hallPair :: afterBasic).Nodup := by
    simpa only [hrecipes] using hnodup
  refine ⟨beforeBasic, afterBasic, hrecipes, ?_, ?_⟩
  · intro hbasic
    exact
      (List.nodup_append.mp hnodup').2.2 hallPair hbasic hallPair (by simp) rfl
  · exact (List.nodup_cons.mp (List.nodup_append.mp hnodup').2.1).1

end
  PFSubsti.TAPkt.PPRecipe

end TCTex
end Submission

/-!
# Terminal ordered transient polynomial rewording residuals

At the next outer-word stratum, every member of the two strict inverse tails
reaches the truncation cutoff.  Their values vanish separately, and the
remaining principal inverse cancels the appended parent semantically.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace PFSubsti.TAPkt
namespace PBSplit

/-- At the next parent stratum, the strict suffix evaluates trivially. -/
lemma strict_after_terminal
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ outerExpansion.word.weight HEAddres.weight + 1)
    (e : ι → HEFam H) :
    STExp.listValue (n := n) e
        (split.strictAfterSource normalizer outerExpansion innerWord
          rightWord) =
      1 := by
  apply
    STExp.list_value_n
  intro nextExpansion hnext
  have hweight :=
    split.outer_after_source normalizer
      outerExpansion innerWord rightWord hword nextExpansion hnext
  omega

/-- At the next parent stratum, the strict prefix evaluates trivially. -/
lemma strict_before_terminal
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ outerExpansion.word.weight HEAddres.weight + 1)
    (e : ι → HEFam H) :
    STExp.listValue (n := n) e
        (split.strictBeforeSource normalizer outerExpansion innerWord
          rightWord) =
      1 := by
  apply
    STExp.list_value_n
  intro nextExpansion hnext
  have hweight :=
    split.outer_before_source normalizer
      outerExpansion innerWord rightWord hword nextExpansion hnext
  omega

/-- At the next parent stratum, both strict inverse tails evaluate trivially. -/
lemma value_strict_terminal
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ outerExpansion.word.weight HEAddres.weight + 1)
    (e : ι → HEFam H) :
    STExp.listValue (n := n) e
        (split.strictInverseSource normalizer outerExpansion innerWord
          rightWord) =
      1 := by
  rw [strictInverseSource,
    STExp.listValue_append,
    split.strict_after_terminal normalizer
      outerExpansion innerWord rightWord hword hcutoff e,
    split.strict_before_terminal normalizer
      outerExpansion innerWord rightWord hword hcutoff e,
    one_mul]

/--
At the next parent stratum, the explicit ordered residual semantics collapses
to the identity.
-/
lemma transi_split_termi
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ outerExpansion.word.weight HEAddres.weight + 1)
    (e : ι → HEFam H) :
    STExp.listValue (n := n) e
        (packet.transientInnerSource normalizer
          outerExpansion innerWord rightWord) =
      1 := by
  rw [
    split.raw_strict_tails
      normalizer outerExpansion innerWord rightWord hword e,
    split.strict_after_terminal normalizer
      outerExpansion innerWord rightWord hword hcutoff e,
    split.strict_before_terminal normalizer
      outerExpansion innerWord rightWord hword hcutoff e]
  group

end PBSplit
end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Terminal recollection of ordered transient polynomial rewording residuals

The two strict inverse tails of an ordered rewording residual vanish
independently at the next outer-word stratum.  This file packages those
terminal facts as transient polynomial source recollections, preserving their
ordered composition for later contextual use.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace TTRecolla

/-- A semantically trivial transient polynomial source recollects to empty. -/
def empty_list_value
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (rawSource :
      List (STExp H ι))
    (hvalue :
      ∀ e : ι → HEFam H,
        STExp.listValue (n := n) e
          rawSource = 1) :
    TTRecolla
      n lowerWeight H rawSource where
  higherSource := []
  higher_source_truncated := by
    intro factor hfactor
    simp at hfactor
  higher_weight_least := by
    intro factor hfactor
    simp at hfactor
  list_higher_raw := by
    intro e
    simpa only [SPFactor.listEval_nil] using (hvalue e).symm

end TTRecolla

namespace PFSubsti.TAPkt
namespace PBSplit

/-- Recollect the terminal strict suffix to the empty ordinary source. -/
def recoll_after_termi
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ outerExpansion.word.weight HEAddres.weight + 1) :
    TTRecolla
      n lowerWeight H
        (split.strictAfterSource normalizer outerExpansion innerWord
          rightWord) :=
  TTRecolla.empty_list_value
    _ fun e =>
      split.strict_after_terminal normalizer
        outerExpansion innerWord rightWord hword hcutoff e

/-- Recollect the terminal strict prefix to the empty ordinary source. -/
def recoll_befor_termi
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ outerExpansion.word.weight HEAddres.weight + 1) :
    TTRecolla
      n lowerWeight H
        (split.strictBeforeSource normalizer outerExpansion innerWord
          rightWord) :=
  TTRecolla.empty_list_value
    _ fun e =>
      split.strict_before_terminal normalizer
        outerExpansion innerWord rightWord hword hcutoff e

/-- Recollect both terminal strict tails in their original concatenated order. -/
def source_recol_termi
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ outerExpansion.word.weight HEAddres.weight + 1) :
    TTRecolla
      n lowerWeight H
        (split.strictInverseSource normalizer outerExpansion innerWord
          rightWord) :=
  TTRecolla.append
    (split.recoll_after_termi normalizer
      outerExpansion innerWord rightWord hword hcutoff)
    (split.recoll_befor_termi normalizer
      outerExpansion innerWord rightWord hword hcutoff)

/--
Recollect the whole explicitly normalized terminal residual to the empty
ordinary source.
-/
def
    recollect_split_terminal
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff :
      n ≤ outerExpansion.word.weight HEAddres.weight + 1) :
    TTRecolla
      n lowerWeight H
        (packet.transientInnerSource normalizer
          outerExpansion innerWord rightWord) :=
  TTRecolla.empty_list_value
    _ fun e =>
      split
        |>.transi_split_termi
          normalizer outerExpansion innerWord rightWord hword hcutoff e

end PBSplit
end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Recollection of ordered transient polynomial rewording residuals

An ordered transient polynomial residual is a strict suffix followed by the
conjugate of a strict prefix.  Once both strict tails have been recollected
into ordinary symbolic factors, the existing sharp higher-tail router removes
the conjugating parent wrappers around the prefix.

This file packages that nonterminal composition boundary.  The transient
parent is matched with an ordinary conjugator only through pointwise
evaluation equality, so no invalid attachment of a loose transient carrier is
assumed.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace STExp

/-- The transient view of an ordinary factor on its original word preserves value. -/
@[simp]
lemma value_reword_self
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι)
    (e : ι → HEFam H) :
    (rewordFactor factor factor.word).value (n := n) e = factor.eval e := by
  rw [value, SPFactor.eval, coefficient_reword_factor]
  rfl

end STExp

namespace PFSubsti.TAPkt
namespace PBSplit

/--
Recollect an ordered transient polynomial residual from independent
recollections of its two strict tails and a sharp route for the conjugated
prefix.
-/
noncomputable def
    recollect_transient_split
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (conjugator : SPFactor H ι)
    (hconjugatorWeight :
      conjugator.word.weight HEAddres.weight = lowerWeight)
    (hconjugatorTruncated :
      conjugator.word.weight HEAddres.weight < n)
    (hconjugatorEval :
      ∀ e : ι → HEFam H,
        conjugator.eval (n := n) e = outerExpansion.value e)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (afterRecollection :
      TTRecolla
        n (lowerWeight + 1) H
          (split.strictAfterSource normalizer outerExpansion innerWord
            rightWord))
    (beforeRecollection :
      TTRecolla
        n (lowerWeight + 1) H
          (split.strictBeforeSource normalizer outerExpansion innerWord
            rightWord)) :
    TTRecolla
      n (lowerWeight + 1) H
        (packet.transientInnerSource normalizer
          outerExpansion innerWord rightWord) := by
  let conjugatedBefore :=
    factory.conjugated_recollection_normalizer sharp
      conjugator hconjugatorWeight hconjugatorTruncated
      beforeRecollection.higherSource beforeRecollection.higherSource
      beforeRecollection.higher_source_truncated
      beforeRecollection.higher_weight_least
      (fun _ => rfl)
  exact
    { higherSource :=
        afterRecollection.higherSource ++ conjugatedBefore.higherSource
      higher_source_truncated := by
        intro factor hfactor
        rcases List.mem_append.mp hfactor with hfactor | hfactor
        · exact afterRecollection.higher_source_truncated factor hfactor
        · exact conjugatedBefore.higher_source_truncated factor hfactor
      higher_weight_least := by
        intro factor hfactor
        rcases List.mem_append.mp hfactor with hfactor | hfactor
        · exact
            afterRecollection.higher_weight_least factor hfactor
        · exact
            conjugatedBefore.higher_least_succ factor
              hfactor
      list_higher_raw := by
        intro e
        rw [SPFactor.listEval_append,
          afterRecollection.list_higher_raw,
          conjugatedBefore.higher_conjugated_raw]
        simp only [SPFactor.conjugatedRawSource,
          SPFactor.listEval_append,
          SPFactor.listEval_cons,
          SPFactor.listEval_nil, mul_one,
          SPFactor.eval_neg,
          beforeRecollection.list_higher_raw,
          hconjugatorEval e]
        rw [
          split.raw_strict_tails
            normalizer outerExpansion innerWord rightWord hword e]
        group
    }

/-- Recollect the strict suffix by recursively recollecting each transient carrier. -/
noncomputable def recoll_after_inver
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (factory :
      TRFtry
        d n H ι)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord) :
    TTRecolla
      n (outerExpansion.word.weight HEAddres.weight + 1) H
        (split.strictAfterSource normalizer outerExpansion innerWord
          rightWord) :=
  TTRecolla.of_singletons _
    fun wordExpansion hwordExpansion =>
      (factory.recollectionOrEmpty wordExpansion).weaken
        (Nat.succ_le_of_lt
          (split.outer_after_source
            normalizer outerExpansion innerWord rightWord hword
              wordExpansion hwordExpansion))

/-- Recollect the strict prefix by recursively recollecting each transient carrier. -/
noncomputable def recoll_befor_inver
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (factory :
      TRFtry
        d n H ι)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord) :
    TTRecolla
      n (outerExpansion.word.weight HEAddres.weight + 1) H
        (split.strictBeforeSource normalizer outerExpansion innerWord
          rightWord) :=
  TTRecolla.of_singletons _
    fun wordExpansion hwordExpansion =>
      (factory.recollectionOrEmpty wordExpansion).weaken
        (Nat.succ_le_of_lt
          (split.outer_before_source
            normalizer outerExpansion innerWord rightWord hword
              wordExpansion hwordExpansion))

/--
Specialize ordered residual recollection to the transient view of one ordinary
parent factor.
-/
noncomputable def
    transient_reword_factor
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (afterRecollection :
      TTRecolla
        n (lowerWeight + 1) H
          (split.strictAfterSource normalizer
            (STExp.rewordFactor factor
              factor.word)
            innerWord rightWord))
    (beforeRecollection :
      TTRecolla
        n (lowerWeight + 1) H
          (split.strictBeforeSource normalizer
            (STExp.rewordFactor factor
              factor.word)
            innerWord rightWord)) :
    TTRecolla
      n (lowerWeight + 1) H
        (packet.transientInnerSource normalizer
          (STExp.rewordFactor factor
            factor.word)
          innerWord rightWord) := by
  apply
    split.recollect_transient_split
      factory sharp normalizer
        (STExp.rewordFactor factor
          factor.word)
        factor hfactorWeight hfactorTruncated
  · intro e
    exact
      (STExp.value_reword_self
        factor e).symm
  · exact hword
  · exact afterRecollection
  · exact beforeRecollection

/--
Recollect the residual of an ordinary parent directly from the recursive
transient singleton factory.
-/
noncomputable def
    recollect_transient_factory
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (transientFactory :
      TRFtry
        d n H ι)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecolla
      n (lowerWeight + 1) H
        (packet.transientInnerSource normalizer
          (STExp.rewordFactor factor
            factor.word)
          innerWord rightWord) := by
  apply
    split.transient_reword_factor
      factory sharp normalizer factor hfactorWeight hfactorTruncated innerWord
        rightWord hword
  · simpa only [STExp.rewordFactor,
      hfactorWeight] using
      split.recoll_after_inver transientFactory
        normalizer
          (STExp.rewordFactor factor
            factor.word)
          innerWord rightWord hword
  · simpa only [STExp.rewordFactor,
      hfactorWeight] using
      split.recoll_befor_inver transientFactory
        normalizer
          (STExp.rewordFactor factor
            factor.word)
          innerWord rightWord hword

end PBSplit
end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Conjugating polynomial higher tails by arbitrary transient carriers

An active transient polynomial carrier need not attach to one permanent
factor.  It can still conjugate an already recollected permanent higher tail:
move across that tail one factor at a time and recollect each emitted bracket
through the generic two-sided transient packet API.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

/--
An upward semantic recollection of an ordinary polynomial source conjugated
by one possibly nonattachable transient polynomial carrier.
-/
structure TransientConjugatedRecollection
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    {ι : Type}
    (conjugator : STExp H ι)
    (rawSource : List (SPFactor H ι)) where
  higherSource :
    List (SPFactor H ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_weight_least :
    SPFactor.WordWeightLeast lowerWeight higherSource
  transient_conjugated_raw :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e higherSource =
        (conjugator.value (n := n) e)⁻¹ *
          SPFactor.listEval e rawSource *
            conjugator.value e

namespace PFSubsti.TAPkt

/--
Conjugate a permanent polynomial source by a transient carrier one factor at
a time.  Every emitted correction bracket is supplied as one recollected
generic transient packet.
-/
noncomputable def transientConjugatedRecollection
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (conjugator : STExp H ι) :
    ∀
      (rawSource : List (SPFactor H ι)),
      SPFactor.IsTruncated n rawSource →
      SPFactor.WordWeightLeast lowerWeight rawSource →
      (∀ factor ∈ rawSource,
        TTRecoll
          n lowerWeight H
            (packet.polynomialTransientTerms normalizer
              conjugator.neg
              (STExp.rewordFactor
                factor factor.word))) →
      TransientConjugatedRecollection
        (n := n) (lowerWeight := lowerWeight) H conjugator rawSource
  | [], _, _, _ =>
      { higherSource := []
        higher_source_truncated := by
          intro factor hfactor
          simp at hfactor
        higher_weight_least := by
          intro factor hfactor
          simp at hfactor
        transient_conjugated_raw := by
          intro e
          simp }
  | head :: tail, hsourceTruncated, hsourceSupported,
      correctionRecollection =>
      let correction := correctionRecollection head (by simp)
      let tailRecollection :=
        packet.transientConjugatedRecollection normalizer
          conjugator tail
            (fun factor hfactor =>
              hsourceTruncated factor (by simp [hfactor]))
            (fun factor hfactor =>
              hsourceSupported factor (by simp [hfactor]))
            (fun factor hfactor =>
              correctionRecollection factor (by simp [hfactor]))
      { higherSource :=
          correction.higherSource ++
            (head :: tailRecollection.higherSource)
        higher_source_truncated := by
          intro factor hfactor
          simp only [List.mem_cons, List.mem_append] at hfactor
          rcases hfactor with hfactor | rfl | hfactor
          · exact correction.higher_source_truncated factor hfactor
          · exact hsourceTruncated factor (by simp)
          · exact tailRecollection.higher_source_truncated factor hfactor
        higher_weight_least := by
          intro factor hfactor
          simp only [List.mem_cons, List.mem_append] at hfactor
          rcases hfactor with hfactor | rfl | hfactor
          · exact correction.higher_weight_least factor hfactor
          · exact hsourceSupported factor (by simp)
          · exact
              tailRecollection.higher_weight_least factor
                hfactor
        transient_conjugated_raw := by
          intro e
          simp only [SPFactor.listEval_cons,
            SPFactor.listEval_append]
          rw [correction.list_higher_raw,
            packet.list_transient_terms,
            STExp.value_neg,
            STExp.value_reword_self,
            tailRecollection.transient_conjugated_raw]
          group }

/--
Inside the contextual resolver for an active transient singleton, all
correction packets needed to conjugate an ordinary higher tail descend from
that singleton.
-/
noncomputable def
    conjugated_recursive_results
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (conjugator : STExp H ι)
    (hconjugatorTruncated :
      conjugator.word.weight HEAddres.weight < n)
    (rawSource : List (SPFactor H ι))
    (hsourceTruncated :
      SPFactor.IsTruncated n rawSource)
    (hsourceSupported :
      SPFactor.WordWeightLeast lowerWeight rawSource)
    (recursiveResults :
      ∀ child,
        SITerm.FrontierDefectMultiset
            n child [.frontier conjugator] →
          TTRecoll
            n lowerWeight H child) :
    TransientConjugatedRecollection
      (n := n) (lowerWeight := lowerWeight) H conjugator rawSource :=
  packet.transientConjugatedRecollection normalizer conjugator
    rawSource hsourceTruncated hsourceSupported fun factor _ =>
      packet.classified_terms_result normalizer
        conjugator.neg
        (STExp.rewordFactor factor
          factor.word)
        (by simpa using hconjugatorTruncated) fun child hchild =>
          recursiveResults child (by
            simpa only [
              SITerm.FrontierDefectMultiset,
              SITerm.frontier_multiset_cons,
              SITerm.frontier_multiset_nil,
              STExp.word_neg] using
                hchild)

/--
A compiled support-polymorphic contextual step recollects the generated
correction packets directly, without attaching the transient conjugator.
-/
noncomputable def
    transient_conjugated_recursive
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (step :
      CRRecol
        d n H ι)
    (conjugator : STExp H ι)
    (rawSource : List (SPFactor H ι))
    (hsourceTruncated :
      SPFactor.IsTruncated n rawSource)
    (hsourceSupported :
      SPFactor.WordWeightLeast lowerWeight rawSource) :
    TransientConjugatedRecollection
      (n := n) (lowerWeight := lowerWeight) H conjugator rawSource :=
  packet.transientConjugatedRecollection normalizer conjugator
    rawSource hsourceTruncated hsourceSupported fun factor _ =>
      step.sourceRecollection lowerWeight
        (packet.polynomialTransientTerms normalizer conjugator.neg
          (STExp.rewordFactor factor
            factor.word))

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Factory routing for ordered transient polynomial rewording residuals

The nonterminal ordered residual consists of a strict suffix and a conjugated
strict prefix.  Both strict tails delegate to the heavier transient-singleton
collector.  The parent conjugation is available only when the transient outer
carrier can be matched semantically with an ordinary symbolic factor.

This file packages that matched-conjugator input explicitly and dispatches
the next-stratum terminal endpoint without requesting it.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
An ordinary symbolic factor whose evaluation agrees with a transient parent
carrier.  The factor is used only to route conjugation through an already
recollected strict higher tail.
-/
structure SMConjug
    {d n : ℕ}
    (lowerWeight : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    {ι : Type}
    (outerExpansion : STExp H ι) where
  conjugator :
    SPFactor H ι
  conjugator_word_weight :
    conjugator.word.weight HEAddres.weight = lowerWeight
  conjugator_isTruncated :
    conjugator.word.weight HEAddres.weight < n
  conjugator_eval :
    ∀ e : ι → HEFam H,
      conjugator.eval (n := n) e = outerExpansion.value e

namespace SMConjug

/-- The transient view of an ordinary factor is matched by that same factor. -/
def reword_factor_self
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    SMConjug
      (n := n) lowerWeight H
        (STExp.rewordFactor factor
          factor.word) where
  conjugator := factor
  conjugator_word_weight := hfactorWeight
  conjugator_isTruncated := hfactorTruncated
  conjugator_eval := fun e =>
    (STExp.value_reword_self
      factor e).symm

end SMConjug

namespace PFSubsti.TAPkt
namespace PBSplit

/--
Recollect the strict inverse suffix by recursively recollecting its heavier
transient singleton carriers in their original order.
-/
noncomputable def
    after_transient_factory
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (transientFactory :
      TRFtry
        d n H ι)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight HEAddres.weight = lowerWeight) :
    TTRecolla
      n (lowerWeight + 1) H
        (split.strictAfterSource normalizer outerExpansion innerWord
          rightWord) := by
  simpa only [houterWeight] using
    split.recoll_after_inver transientFactory
      normalizer outerExpansion innerWord rightWord hword

/--
Recollect the strict inverse prefix by recursively recollecting its heavier
transient singleton carriers in their original order.
-/
noncomputable def
    before_transient_factory
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (transientFactory :
      TRFtry
        d n H ι)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight HEAddres.weight = lowerWeight) :
    TTRecolla
      n (lowerWeight + 1) H
        (split.strictBeforeSource normalizer outerExpansion innerWord
          rightWord) := by
  simpa only [houterWeight] using
    split.recoll_befor_inver transientFactory
      normalizer outerExpansion innerWord rightWord hword

/--
Recollect a nonterminal ordered residual from heavier singleton recursion and
one ordinary factor matching the transient parent.
-/
noncomputable def
    recollection_transient_factory
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (correctionFactory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (transientFactory :
      TRFtry
        d n H ι)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (matched :
      SMConjug
        (n := n) lowerWeight H outerExpansion)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight HEAddres.weight = lowerWeight) :
    TTRecolla
      n (lowerWeight + 1) H
        (packet.transientInnerSource normalizer
          outerExpansion innerWord rightWord) :=
  split
    |>.recollect_transient_split
      correctionFactory sharp normalizer outerExpansion matched.conjugator
        matched.conjugator_word_weight matched.conjugator_isTruncated
          matched.conjugator_eval innerWord rightWord hword
            (split.after_transient_factory
              transientFactory normalizer outerExpansion innerWord rightWord
                hword houterWeight)
            (split.before_transient_factory
              transientFactory normalizer outerExpansion innerWord rightWord
                hword houterWeight)

/--
Dispatch an ordered residual to heavier singleton recursion while active, or
erase it at the next parent stratum without requesting a matched conjugator.
-/
noncomputable def
    or_terminal_raw
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (correctionFactory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (transientFactory :
      TRFtry
        d n H ι)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight HEAddres.weight = lowerWeight)
    (matched :
      lowerWeight + 1 < n →
        SMConjug
          (n := n) lowerWeight H outerExpansion) :
    TTRecolla
      n (lowerWeight + 1) H
        (packet.transientInnerSource normalizer
          outerExpansion innerWord rightWord) := by
  by_cases hactive : lowerWeight + 1 < n
  · exact
      split
        |>.recollection_transient_factory
          correctionFactory sharp transientFactory normalizer outerExpansion
            (matched hactive) innerWord rightWord hword houterWeight
  · exact
      split
        |>.recollect_split_terminal
          normalizer outerExpansion innerWord rightWord hword (by omega)

/--
Dispatch the residual of the transient view of an ordinary parent factor.
While active, the parent factor itself supplies the matched conjugator.
-/
noncomputable def
    or_terminal_reword
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : PBSplit packet)
    (correctionFactory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (transientFactory :
      TRFtry
        d n H ι)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecolla
      n (lowerWeight + 1) H
        (packet.transientInnerSource normalizer
          (STExp.rewordFactor factor
            factor.word)
          innerWord rightWord) :=
  split
    |>.or_terminal_raw
      correctionFactory sharp transientFactory normalizer
        (STExp.rewordFactor factor
          factor.word)
        innerWord rightWord hword hfactorWeight fun hactive =>
          SMConjug.reword_factor_self
            factor hfactorWeight (by omega)

end PBSplit
end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Polynomial ordered residual routing from principal packet inventory

The active-or-terminal residual collector consumes an ordered split around
the packet's principal `basic` recipe.  This file packages that split as
routing data and constructs it from the packet-level inventory conditions
available to callers.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/-- Packet-local routing data for ordered transient polynomial residuals. -/
structure TRData
    {d n : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n) where
  split :
    packet.PBSplit

namespace TRData

/--
Construct ordered polynomial residual routing from principal inventory and a
unique occurrence of the principal `basic` recipe.
-/
noncomputable def poly_principal_unique
    {d n : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (principal : packet.PPRecipe)
    (hunique : packet.UniqueBasicOccurrence) :
    TRData packet where
  split := principal.split_unique_pair hunique

/--
Duplicate-free principal inventory is a sufficient entry point for ordered
polynomial residual routing.
-/
noncomputable def poly_principal_nodup
    {d n : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (principal : packet.PPRecipe)
    (hnodup : packet.recipes.Nodup) :
    TRData packet where
  split := principal.basic_split_nodup hnodup

/-- The cutoff-three singleton packet has canonical ordered residual routing. -/
def n_three
    {d n : ℕ}
    (hn : n ≤ 3) :
    TRData
      (PFSubsti.TAPkt.n_three
        (d := d) hn) where
  split :=
    PFSubsti.TAPkt.poly_split_n
      hn

/-- The cutoff-four class-three packet has canonical ordered residual routing. -/
def n_four
    {d n : ℕ}
    (hn : n ≤ 4) :
    TRData
      (PFSubsti.TAPkt.n_four
        (d := d) hn) where
  split :=
    PFSubsti.TAPkt.poly_split_four
      hn

/--
Route a matched transient polynomial parent residual through heavier
singleton recursion while active, or erase its terminal quotient.
-/
noncomputable def
    or_terminal_raw
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (routing :
      TRData packet)
    (correctionFactory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (transientFactory :
      TRFtry
        d n H ι)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight HEAddres.weight = lowerWeight)
    (matched :
      lowerWeight + 1 < n →
        SMConjug
          (n := n) lowerWeight H outerExpansion) :
    TTRecolla
      n (lowerWeight + 1) H
        (packet.transientInnerSource normalizer
          outerExpansion innerWord rightWord) :=
  routing.split
    |>.or_terminal_raw
      correctionFactory sharp transientFactory normalizer outerExpansion
        innerWord rightWord hword houterWeight matched

/--
Route the residual of the transient view of an ordinary polynomial parent
factor.  The parent factor supplies its own matched conjugator while active.
-/
noncomputable def
    or_terminal_reword
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (routing :
      TRData packet)
    (correctionFactory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (transientFactory :
      TRFtry
        d n H ι)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecolla
      n (lowerWeight + 1) H
        (packet.transientInnerSource normalizer
          (STExp.rewordFactor factor
            factor.word)
          innerWord rightWord) :=
  routing.split
    |>.or_terminal_reword
      correctionFactory sharp transientFactory normalizer factor
        hfactorWeight innerWord rightWord hword

end TRData

end TCTex
end Submission

/-!
# Contextual recursive factory for ordered transient polynomial residuals

The contextual packet fixpoint is support-polymorphic.  Its singleton
projection therefore supplies every strictly heavier tail recollection
required by ordered residual routing.  This file feeds that projection into
the packet-local routing adapter.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace TRData

/--
Use one contextual recursive step to recollect every heavier singleton tail
of a matched transient polynomial parent residual.
-/
noncomputable def
    or_terminal_recursive
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (routing :
      TRData packet)
    (correctionFactory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (step :
      CRRecol
        d n H ι)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (houterWeight :
      outerExpansion.word.weight HEAddres.weight = lowerWeight)
    (matched :
      lowerWeight + 1 < n →
        SMConjug
          (n := n) lowerWeight H outerExpansion) :
    TTRecolla
      n (lowerWeight + 1) H
        (packet.transientInnerSource normalizer
          outerExpansion innerWord rightWord) :=
  routing
    |>.or_terminal_raw
      correctionFactory sharp step.toTransientFactory normalizer
        outerExpansion innerWord rightWord hword houterWeight matched

/--
Use one contextual recursive step to recollect the residual of the transient
view of an ordinary polynomial parent factor.
-/
noncomputable def
    recollect_or_rec
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (routing :
      TRData packet)
    (correctionFactory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (step :
      CRRecol
        d n H ι)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecolla
      n (lowerWeight + 1) H
        (packet.transientInnerSource normalizer
          (STExp.rewordFactor factor
            factor.word)
          innerWord rightWord) :=
  routing
    |>.or_terminal_reword
      correctionFactory sharp step.toTransientFactory normalizer factor
        hfactorWeight innerWord rightWord hword

end TRData

end TCTex
end Submission

/-!
# Singleton-frontier routing from ordered transient polynomial residuals

An ordinary polynomial parent reworded onto its inner Hall word expands to a
classified temporary packet.  Multiplying that packet by the ordered
rewording residual recovers the original transient parent carrier.  This file
packages that quotient composition and feeds it from the contextual fixpoint.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace SITerm

/-- Regard every transient polynomial carrier in a source as a frontier term. -/
def frontierTerms
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (source : List (STExp H ι)) :
    List (SITerm H ι) :=
  source.map .frontier

/-- Frontier-list transport preserves the ordered transient product. -/
@[simp]
lemma value_frontier_terms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (source : List (STExp H ι)) :
    listValue (n := n) e (frontierTerms source) =
      STExp.listValue e source := by
  induction source with
  | nil =>
      rfl
  | cons head tail ih =>
      change
        head.value e * listValue e (frontierTerms tail) =
          head.value e *
            STExp.listValue e tail
      rw [ih]

/-- Mixed-source evaluation preserves ordered concatenation. -/
@[simp]
lemma listValue_append
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (left right : List (SITerm H ι)) :
    listValue (n := n) e (left ++ right) =
      listValue e left * listValue e right := by
  simp [listValue]

/-- A singleton frontier evaluates to its transient carrier. -/
@[simp]
lemma value_singleton_frontier
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (wordExpansion : STExp H ι) :
    listValue (n := n) e [.frontier wordExpansion] =
      wordExpansion.value e := by
  simp [listValue, value]

end SITerm

namespace TTRecoll

/-- Regard a recollected transient source as a recollected mixed frontier list. -/
def transient_source_recollect
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source : List (STExp H ι)}
    (recollection :
      TTRecolla
        n lowerWeight H source) :
    TTRecoll
      n lowerWeight H
        (SITerm.frontierTerms
          source) where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least :=
    recollection.higher_weight_least
  list_higher_raw := by
    intro e
    rw [recollection.list_higher_raw]
    exact
      (SITerm.value_frontier_terms
        e source).symm

end TTRecoll

namespace PFSubsti.TAPkt

/--
The classified inner-reduction packet followed by its rewording residual is
the original transient view of the ordinary polynomial parent factor.
-/
def rewordContextualTerms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    List (SITerm H ι) :=
  packet.outerClassifiedTerms normalizer factor
      innerWord rightWord hword ++
    SITerm.frontierTerms
      (packet.transientInnerSource normalizer
        (STExp.rewordFactor factor
          factor.word)
        innerWord rightWord)

/-- The contextual temporary-packet expansion evaluates to its parent carrier. -/
lemma reword_contextual_terms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (e : ι → HEFam H) :
    SITerm.listValue (n := n) e
        (packet.rewordContextualTerms
          normalizer factor innerWord rightWord hword) =
      (STExp.rewordFactor factor
        factor.word).value e := by
  rw [rewordContextualTerms,
    SITerm.listValue_append,
    packet.reduction_classified_terms,
    SITerm.value_frontier_terms,
    packet.transient_inner_outer]
  rw [STExp.coefficient_reword_factor]
  group

/--
Compose recollections of the classified temporary packet and its residual,
then transport the result back to the original transient singleton frontier.
-/
noncomputable def
    recollection_frontier_reword
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (packetRecollection :
      TTRecoll
        n lowerWeight H
          (packet.outerClassifiedTerms normalizer
            factor innerWord rightWord hword))
    (residualRecollection :
      TTRecolla
        n lowerWeight H
          (packet.transientInnerSource normalizer
            (STExp.rewordFactor factor
              factor.word)
            innerWord rightWord)) :
    TTRecoll
      n lowerWeight H
        [.frontier
          (STExp.rewordFactor factor
            factor.word)] :=
  let residualTermsRecollection :=
    TTRecoll.transient_source_recollect
      residualRecollection
  TTRecoll.list_value
    (TTRecoll.append
      packetRecollection residualTermsRecollection) fun e => by
        simpa only [
          rewordContextualTerms,
          SITerm.value_singleton_frontier] using
            packet.reword_contextual_terms
              normalizer factor innerWord rightWord hword e

end PFSubsti.TAPkt

namespace TRData

/--
Use one contextual recursive step for the temporary packet and all ordered
residual tails, yielding a recollection of the original singleton frontier.
-/
noncomputable def frontier_reword_recursive
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (routing :
      TRData packet)
    (correctionFactory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (step :
      CRRecol
        d n H ι)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecoll
      n lowerWeight H
        [.frontier
          (STExp.rewordFactor factor
            factor.word)] :=
  packet
    |>.recollection_frontier_reword
      normalizer factor innerWord rightWord hword
        (step.sourceRecollection lowerWeight
          (packet.outerClassifiedTerms normalizer
            factor innerWord rightWord hword))
        ((routing
          |>.recollect_or_rec
            correctionFactory sharp step normalizer factor hfactorWeight
              innerWord rightWord hword).weaken
                (Nat.le_succ lowerWeight))

end TRData

end TCTex
end Submission

/-!
# Generated-child routing for transient polynomial outer residuals

The ordered residual of an arbitrary transient commutator has two strict
tails.  The strict suffix recollects directly.  The strict prefix must be
conjugated by the original transient carrier, which may still be
nonattachable; its correction brackets are routed through generated
two-sided transient packets.

This file packages that generated-child surface and reconstructs the original
singleton frontier after an external recollection of the temporary one-sided
packet.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace PFSubsti.TAPkt

/--
The generated recursive inputs used by one arbitrary transient polynomial
outer residual.
-/
structure TORoutea
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : packet.PBSplit)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H)) where
  strictAfterRecollection :
    TTRecolla
      n lowerWeight H
        (split.strictAfterSource normalizer outerExpansion innerWord
          rightWord)
  strictBeforeRecollection :
    TTRecolla
      n lowerWeight H
        (split.strictBeforeSource normalizer outerExpansion innerWord
          rightWord)
  correctionPacketRecollection :
    ∀ factor ∈ strictBeforeRecollection.higherSource,
      TTRecoll
        n lowerWeight H
          (packet.polynomialTransientTerms normalizer
            outerExpansion.neg
            (STExp.rewordFactor factor
              factor.word))

namespace TORoutea

/--
Restrict the contextual callback rooted at the outer singleton to the strict
tails and generated correction packets actually used by its ordered residual.
-/
noncomputable def of_recursiveResults
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : packet.PBSplit)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (houterTruncated :
      outerExpansion.word.weight HEAddres.weight < n)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (recursiveResults :
      ∀ child,
        SITerm.FrontierDefectMultiset
            n child [.frontier outerExpansion] →
          TTRecoll
            n lowerWeight H child) :
    TORoutea
      (lowerWeight := lowerWeight) split normalizer outerExpansion innerWord
        rightWord where
  strictAfterRecollection :=
    TTRecolla.strictly_heavier_results
      outerExpansion houterTruncated
        (split.strictAfterSource normalizer outerExpansion innerWord
          rightWord)
        (split.outer_after_source normalizer
          outerExpansion innerWord rightWord hword)
        recursiveResults
  strictBeforeRecollection :=
    TTRecolla.strictly_heavier_results
      outerExpansion houterTruncated
        (split.strictBeforeSource normalizer outerExpansion innerWord
          rightWord)
        (split.outer_before_source normalizer
          outerExpansion innerWord rightWord hword)
        recursiveResults
  correctionPacketRecollection := fun factor _ =>
    packet.classified_terms_result normalizer
      outerExpansion.neg
      (STExp.rewordFactor factor
        factor.word)
      (by simpa using houterTruncated) fun child hchild =>
        recursiveResults child (by
          simpa only [
            SITerm.FrontierDefectMultiset,
            SITerm.frontier_multiset_cons,
            SITerm.frontier_multiset_nil,
            STExp.word_neg] using
              hchild)

/-- Compose generated strict-tail and correction-packet inputs into the residual. -/
noncomputable def sourceRecollection
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {split : packet.PBSplit}
    {normalizer :
      WBForm.RCNormal H ι}
    {outerExpansion : STExp H ι}
    {innerWord rightWord : CWord (HEAddres H)}
    (routing :
      TORoutea
        (lowerWeight := lowerWeight) split normalizer outerExpansion innerWord
          rightWord)
    (hword : outerExpansion.word = .commutator innerWord rightWord) :
    TTRecolla
      n lowerWeight H
        (packet.transientInnerSource normalizer
          outerExpansion innerWord rightWord) := by
  let conjugatedBefore :=
    packet.transientConjugatedRecollection normalizer
      outerExpansion routing.strictBeforeRecollection.higherSource
        routing.strictBeforeRecollection.higher_source_truncated
          routing.strictBeforeRecollection.higher_weight_least
            routing.correctionPacketRecollection
  exact
    { higherSource :=
        routing.strictAfterRecollection.higherSource ++
          conjugatedBefore.higherSource
      higher_source_truncated := by
        intro factor hfactor
        rcases List.mem_append.mp hfactor with hfactor | hfactor
        · exact
            routing.strictAfterRecollection.higher_source_truncated factor
              hfactor
        · exact conjugatedBefore.higher_source_truncated factor hfactor
      higher_weight_least := by
        intro factor hfactor
        rcases List.mem_append.mp hfactor with hfactor | hfactor
        · exact
            routing.strictAfterRecollection.higher_weight_least
              factor hfactor
        · exact
            conjugatedBefore.higher_weight_least factor hfactor
      list_higher_raw := by
        intro e
        rw [SPFactor.listEval_append,
          routing.strictAfterRecollection.list_higher_raw,
          conjugatedBefore.transient_conjugated_raw,
          routing.strictBeforeRecollection.list_higher_raw,
          split.raw_strict_tails
            normalizer outerExpansion innerWord rightWord hword e]
        group }

end TORoutea

/--
The classified arbitrary one-sided temporary packet followed by its residual
evaluates to the original transient outer carrier.
-/
def transientContextualTerms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    List (SITerm H ι) :=
  packet.innerClassifiedTerms normalizer
      outerExpansion innerWord rightWord ++
    SITerm.frontierTerms
      (packet.transientInnerSource normalizer
        outerExpansion innerWord rightWord)

/-- The contextual arbitrary temporary packet evaluates to its parent carrier. -/
lemma transient_contextual_terms
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (e : ι → HEFam H) :
    SITerm.listValue (n := n) e
        (packet.transientContextualTerms
          normalizer outerExpansion innerWord rightWord) =
      outerExpansion.value e := by
  rw [transientContextualTerms,
    SITerm.listValue_append,
    packet.transient_inner_terms,
    SITerm.value_frontier_terms,
    packet.transient_inner_outer]
  group

/--
Compose recollections of an arbitrary classified temporary packet and its
generated residual, then transport back to the original singleton frontier.
-/
noncomputable def
    recollection_frontier_transient
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (packetRecollection :
      TTRecoll
        n lowerWeight H
          (packet.innerClassifiedTerms
            normalizer outerExpansion innerWord rightWord))
    (residualRecollection :
      TTRecolla
        n lowerWeight H
          (packet.transientInnerSource normalizer
            outerExpansion innerWord rightWord)) :
    TTRecoll
      n lowerWeight H [.frontier outerExpansion] :=
  let residualTermsRecollection :=
    TTRecoll.transient_source_recollect
      residualRecollection
  TTRecoll.list_value
    (TTRecoll.append
      packetRecollection residualTermsRecollection) fun e => by
        simpa only [
          transientContextualTerms,
          SITerm.value_singleton_frontier] using
            packet.transient_contextual_terms
              normalizer outerExpansion innerWord rightWord e

namespace TORoutea

/--
Compose an externally recollected arbitrary temporary packet with the
generated-child residual route, recovering the parent singleton frontier.
-/
noncomputable def sourcerec_frontier
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {split : packet.PBSplit}
    {normalizer :
      WBForm.RCNormal H ι}
    {outerExpansion : STExp H ι}
    {innerWord rightWord : CWord (HEAddres H)}
    (routing :
      TORoutea
        (lowerWeight := lowerWeight) split normalizer outerExpansion innerWord
          rightWord)
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (packetRecollection :
      TTRecoll
        n lowerWeight H
          (packet.innerClassifiedTerms
            normalizer outerExpansion innerWord rightWord)) :
    TTRecoll
      n lowerWeight H [.frontier outerExpansion] :=
  packet
    |>.recollection_frontier_transient
      normalizer outerExpansion innerWord rightWord packetRecollection
        (routing.sourceRecollection hword)

end TORoutea

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Recursive singleton factory for ordered transient polynomial residuals

Ordered residual routing reconstructs the transient view of an ordinary
polynomial parent as a mixed singleton frontier.  Historical normalization
interfaces consume a transient singleton recollection instead.  This file
projects the contextual result back to that interface.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace TRData

/--
Expose recursive ordinary-parent rewording through the transient singleton
source API.
-/
noncomputable def recollection_reword_recursive
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (routing :
      TRData packet)
    (correctionFactory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (step :
      CRRecol
        d n H ι)
    (normalizer : WBForm.RCNormal H ι)
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecolla
      n lowerWeight H
        [STExp.rewordFactor factor
          factor.word] :=
  TTRecolla.singleton_frontier_recollection
    _ <|
      routing.frontier_reword_recursive
        correctionFactory sharp step normalizer factor hfactorWeight
          innerWord rightWord hword

end TRData

end TCTex
end Submission

/-!
# Structural restarts for generated transient polynomial frontiers

The ordered residual children of a generated transient commutator descend in
outer cutoff defect.  Its temporary one-sided packet instead descends from the
reworded inner carrier.  That carrier is strictly lighter because it is a
proper commutator subtree.

This file keeps those recursion orders separate and preserves the physical
support certificate required by the polynomial contextual resolver.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace SGFront

/-- The selected inner subtree of a generated commutator is strictly lighter. -/
lemma inner_weight_outer
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {expansion : STExp H ι}
    (generated :
      SGFront H ι expansion) :
    generated.innerWord.weight HEAddres.weight <
      expansion.word.weight HEAddres.weight := by
  rw [generated.word_eq, CWord.weight_commutator]
  exact
    Nat.lt_add_of_pos_right
      (CWord.weight_pos HEAddres.weight
        HEAddres.weight_pos generated.rightWord)

/-- Rewording onto the selected inner subtree exposes a strictly lighter root. -/
lemma reword_inner_outer
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {expansion : STExp H ι}
    (generated :
      SGFront H ι expansion) :
    (expansion.reword generated.innerWord).word.weight
        HEAddres.weight <
      expansion.word.weight HEAddres.weight := by
  simpa only [STExp.word_reword] using
    generated.inner_weight_outer

end SGFront

/--
A restart handler for the second recursive root exposed by decomposing a
generated transient polynomial frontier.
-/
structure
    SmallerRestartFactory
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (outerExpansion : STExp H ι) where
  sourceRecollection :
    ∀
      (smallerExpansion : STExp H ι),
      smallerExpansion.word.weight HEAddres.weight <
          outerExpansion.word.weight HEAddres.weight →
        ∀ lowerWeight,
          lowerWeight ≤
              outerExpansion.word.weight HEAddres.weight →
            ∀ child,
              SITerm.FrontierDefectMultiset
                  n child [.frontier smallerExpansion] →
                SITerm.WordWeightLeast
                    lowerWeight child →
                  TTRecoll
                    n lowerWeight H child

namespace SGFront

/--
Close one active generated transient polynomial frontier from its outer
cutoff-defect callback and an explicit strictly-smaller-root restart handler.
-/
noncomputable def recollection_smaller_restart
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (split : packet.PBSplit)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (generated :
      SGFront H ι outerExpansion)
    (hlowerWeight :
      lowerWeight ≤ outerExpansion.word.weight HEAddres.weight)
    (houterTruncated :
      outerExpansion.word.weight HEAddres.weight < n)
    (outerRecursiveResults :
      ∀ child,
        SITerm.FrontierDefectMultiset
            n child [.frontier outerExpansion] →
          SITerm.WordWeightLeast
              lowerWeight child →
            TTRecoll
              n lowerWeight H child)
    (restart :
      SmallerRestartFactory
        (n := n) H ι outerExpansion) :
    TTRecoll
      n lowerWeight H [.frontier outerExpansion] := by
  let strictAfterRecollection :
      TTRecolla
        n lowerWeight H
          (split.strictAfterSource normalizer outerExpansion
            generated.innerWord generated.rightWord) :=
    TTRecolla.of_singletons
      _ fun expansion hexpansion =>
        TTRecolla.singleton_frontier_recollection
          expansion <|
            outerRecursiveResults [.frontier expansion]
              (SITerm.defect_multiset_weight
                expansion outerExpansion houterTruncated <|
                  split.outer_after_source
                    normalizer outerExpansion generated.innerWord
                      generated.rightWord generated.word_eq expansion
                        hexpansion)
              (by
                intro term hterm
                simp only [List.mem_singleton] at hterm
                subst term
                exact hlowerWeight.trans <| Nat.le_of_lt <|
                  split.outer_after_source
                    normalizer outerExpansion generated.innerWord
                      generated.rightWord generated.word_eq expansion
                        hexpansion)
  let strictBeforeRecollection :
      TTRecolla
        n lowerWeight H
          (split.strictBeforeSource normalizer outerExpansion
            generated.innerWord generated.rightWord) :=
    TTRecolla.of_singletons
      _ fun expansion hexpansion =>
        TTRecolla.singleton_frontier_recollection
          expansion <|
            outerRecursiveResults [.frontier expansion]
              (SITerm.defect_multiset_weight
                expansion outerExpansion houterTruncated <|
                  split.outer_before_source
                    normalizer outerExpansion generated.innerWord
                      generated.rightWord generated.word_eq expansion
                        hexpansion)
              (by
                intro term hterm
                simp only [List.mem_singleton] at hterm
                subst term
                exact hlowerWeight.trans <| Nat.le_of_lt <|
                  split.outer_before_source
                    normalizer outerExpansion generated.innerWord
                      generated.rightWord generated.word_eq expansion
                        hexpansion)
  let residualRouting :
      PFSubsti.TAPkt.TORoutea
        (lowerWeight := lowerWeight) split normalizer outerExpansion
          generated.innerWord generated.rightWord :=
    { strictAfterRecollection := strictAfterRecollection
      strictBeforeRecollection := strictBeforeRecollection
      correctionPacketRecollection := fun factor _ =>
        outerRecursiveResults
          (packet.polynomialTransientTerms normalizer
            outerExpansion.neg
            (STExp.rewordFactor factor
              factor.word))
          (by
            simpa only [
              SITerm.FrontierDefectMultiset,
              SITerm.frontier_multiset_cons,
              SITerm.frontier_multiset_nil,
              STExp.word_neg] using
                packet.polyClassifiedSingleton
                  normalizer outerExpansion.neg
                    (STExp.rewordFactor
                      factor factor.word)
                    (by simpa using houterTruncated))
          (by
            intro term hterm
            exact hlowerWeight.trans <| Nat.le_trans (Nat.le_succ _) <|
              packet.least_classified_left
                normalizer outerExpansion.neg
                  (STExp.rewordFactor
                    factor factor.word)
                  term hterm) }
  apply residualRouting.sourcerec_frontier generated.word_eq
  exact
    packet
      |>.recollect_frontier_recollections
        normalizer outerExpansion generated.innerWord generated.rightWord
          generated.word_eq hlowerWeight fun expansion hexpansion _ =>
            restart.sourceRecollection
              (outerExpansion.reword generated.innerWord)
              generated.reword_inner_outer
              lowerWeight hlowerWeight [.frontier expansion]
              (SITerm.defect_multiset_weight
                expansion (outerExpansion.reword generated.innerWord)
                (by
                  exact generated.reword_inner_outer.trans
                    houterTruncated)
                (packet
                  |>.left_transient_classified
                    normalizer (outerExpansion.reword generated.innerWord)
                      generated.rightWord (.frontier expansion) hexpansion))
              (by
                intro term hterm
                simp only [List.mem_singleton] at hterm
                subst term
                exact hlowerWeight.trans <|
                  packet
                    |>.poly_classified_terms
                      normalizer outerExpansion generated.innerWord
                        generated.rightWord generated.word_eq
                          (.frontier expansion) hexpansion)

end SGFront

end TCTex
end Submission

/-!
# Generated nonattachable-frontier factories from structural restarts

The generated-frontier boundary asks for one callback normalizing every
active nonattachable commutator carrier.  Structural restart routing supplies
that callback once a packet split and a scheduler for genuinely
strictly-lighter reworded roots are available.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
Packet-local data compiling strictly-lighter-root structural restarts into
the generated active nonattachable-frontier callback.
-/
structure
    PRRoutea
    (d n : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer :
      WBForm.RCNormal H ι) where
  split : packet.PBSplit
  restart :
    ∀
      (expansion : STExp H ι),
      SGFront H ι expansion →
        expansion.word.weight HEAddres.weight < n →
          ¬ expansion.coefficientWeight ≤
              expansion.word.weight HEAddres.weight →
            SmallerRestartFactory
              (n := n) H ι expansion

namespace PRRoutea

/--
Compile structural restart scheduling into the exact generated-frontier
factory consumed by initial and recursive classified polynomial packets.
-/
noncomputable def generatedNonattachableFactory
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {normalizer :
      WBForm.RCNormal H ι}
    (routing :
      PRRoutea
        d n H ι packet normalizer) :
    RRFtry
      d n H ι where
  sourceRecollection _lowerWeight expansion generated hlowerWeight hactive
      hnonattachable recursiveResults :=
    generated.recollection_smaller_restart routing.split
      normalizer expansion hlowerWeight hactive recursiveResults
        (routing.restart expansion generated hactive hnonattachable)

end PRRoutea

end TCTex
end Submission

/-!
# Low-cutoff generated structural restart factories

The explicit class-two and class-three Hall-Petresco packets already expose
their canonical ordered splits around the principal `basic` recipe.  This
file installs those splits into generated transient structural restart
routing and compiles the result into the nonattachable-frontier callback.

The genuinely recursive input remains visible: generated commutator
frontiers restart from a strictly lighter reworded root.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace PRRoutea

/--
At cutoff at most three, the singleton Hall-Petresco packet supplies the
canonical generated structural-restart split.
-/
noncomputable def n_three
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hn : n ≤ 3)
    (normalizer :
      WBForm.RCNormal H ι)
    (restart :
      ∀
        (expansion : STExp H ι),
        SGFront H ι expansion →
          expansion.word.weight HEAddres.weight < n →
            ¬ expansion.coefficientWeight ≤
                expansion.word.weight HEAddres.weight →
              SmallerRestartFactory
                (n := n) H ι expansion) :
    PRRoutea
      d n H ι
        (PFSubsti.TAPkt.n_three
          hn)
        normalizer where
  split :=
    PFSubsti.TAPkt.poly_split_n
      hn
  restart := restart

/--
At cutoff at most four, the class-three Hall-Petresco packet supplies the
canonical generated structural-restart split.
-/
noncomputable def n_four
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hn : n ≤ 4)
    (normalizer :
      WBForm.RCNormal H ι)
    (restart :
      ∀
        (expansion : STExp H ι),
        SGFront H ι expansion →
          expansion.word.weight HEAddres.weight < n →
            ¬ expansion.coefficientWeight ≤
                expansion.word.weight HEAddres.weight →
              SmallerRestartFactory
                (n := n) H ι expansion) :
    PRRoutea
      d n H ι
        (PFSubsti.TAPkt.n_four
          hn)
        normalizer where
  split :=
    PFSubsti.TAPkt.poly_split_four
      hn
  restart := restart

end PRRoutea

namespace
  RRFtry

/--
Compile the cutoff-three singleton packet and a lighter-root scheduler into
the generated active nonattachable-frontier callback.
-/
noncomputable def n_three
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hn : n ≤ 3)
    (normalizer :
      WBForm.RCNormal H ι)
    (restart :
      ∀
        (expansion : STExp H ι),
        SGFront H ι expansion →
          expansion.word.weight HEAddres.weight < n →
            ¬ expansion.coefficientWeight ≤
                expansion.word.weight HEAddres.weight →
              SmallerRestartFactory
                (n := n) H ι expansion) :
    RRFtry
      d n H ι :=
  (PRRoutea.n_three
    hn normalizer restart).generatedNonattachableFactory

/--
Compile the cutoff-four class-three packet and a lighter-root scheduler into
the generated active nonattachable-frontier callback.
-/
noncomputable def n_four
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hn : n ≤ 4)
    (normalizer :
      WBForm.RCNormal H ι)
    (restart :
      ∀
        (expansion : STExp H ι),
        SGFront H ι expansion →
          expansion.word.weight HEAddres.weight < n →
            ¬ expansion.coefficientWeight ≤
                expansion.word.weight HEAddres.weight →
              SmallerRestartFactory
                (n := n) H ι expansion) :
    RRFtry
      d n H ι :=
  (PRRoutea.n_four
    hn normalizer restart).generatedNonattachableFactory

end
  RRFtry

end TCTex
end Submission

/-!
# Generated structural restart routing from principal packet inventory

Generated transient structural restart only needs an ordered split around
the packet's principal `basic` recipe.  Principal inventory together with a
unique basic occurrence constructs that split; duplicate-free recipes remain
a convenient sufficient condition.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace PRRoutea

/--
Construct generated structural-restart routing from principal inventory and
a unique occurrence of the principal `basic` recipe.
-/
noncomputable def poly_principal_unique
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (normalizer :
      WBForm.RCNormal H ι)
    (restart :
      ∀
        (expansion : STExp H ι),
        SGFront H ι expansion →
          expansion.word.weight HEAddres.weight < n →
            ¬ expansion.coefficientWeight ≤
                expansion.word.weight HEAddres.weight →
              SmallerRestartFactory
                (n := n) H ι expansion)
    (principal : packet.PPRecipe)
    (hunique : packet.UniqueBasicOccurrence) :
    PRRoutea
      d n H ι packet normalizer where
  split := principal.split_unique_pair hunique
  restart := restart

/--
Construct generated structural-restart routing from duplicate-free principal
packet inventory.
-/
noncomputable def poly_principal_nodup
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (normalizer :
      WBForm.RCNormal H ι)
    (restart :
      ∀
        (expansion : STExp H ι),
        SGFront H ι expansion →
          expansion.word.weight HEAddres.weight < n →
            ¬ expansion.coefficientWeight ≤
                expansion.word.weight HEAddres.weight →
              SmallerRestartFactory
                (n := n) H ι expansion)
    (principal : packet.PPRecipe)
    (hnodup : packet.recipes.Nodup) :
    PRRoutea
      d n H ι packet normalizer where
  split := principal.basic_split_nodup hnodup
  restart := restart

end PRRoutea

namespace
  RRFtry

/--
Compile principal packet inventory and a lighter-root scheduler into the
generated active nonattachable-frontier callback.
-/
noncomputable def poly_principal_unique
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (normalizer :
      WBForm.RCNormal H ι)
    (restart :
      ∀
        (expansion : STExp H ι),
        SGFront H ι expansion →
          expansion.word.weight HEAddres.weight < n →
            ¬ expansion.coefficientWeight ≤
                expansion.word.weight HEAddres.weight →
              SmallerRestartFactory
                (n := n) H ι expansion)
    (principal : packet.PPRecipe)
    (hunique : packet.UniqueBasicOccurrence) :
    RRFtry
      d n H ι :=
  (PRRoutea.poly_principal_unique
    normalizer restart principal hunique)
      |>.generatedNonattachableFactory

/--
Compile duplicate-free principal packet inventory and a lighter-root
scheduler into the generated active nonattachable-frontier callback.
-/
noncomputable def poly_principal_nodup
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (normalizer :
      WBForm.RCNormal H ι)
    (restart :
      ∀
        (expansion : STExp H ι),
        SGFront H ι expansion →
          expansion.word.weight HEAddres.weight < n →
            ¬ expansion.coefficientWeight ≤
                expansion.word.weight HEAddres.weight →
              SmallerRestartFactory
                (n := n) H ι expansion)
    (principal : packet.PPRecipe)
    (hnodup : packet.recipes.Nodup) :
    RRFtry
      d n H ι :=
  (PRRoutea.poly_principal_nodup
    normalizer restart principal hnodup)
      |>.generatedNonattachableFactory

end
  RRFtry

end TCTex
end Submission

/-!
# The class-two principal structural-restart cycle

For the singleton class-two Hall-Petresco packet, moving a transient outer
coefficient onto the selected inner word emits only the principal `basic`
recipe.  If the parent carrier is nonattachable, that temporary output stays
nonattachable and retains the parent's physical word, coefficient bound, and
value.

Thus an automatic scheduler must cancel the principal output contextually.
Recursively normalizing that singleton in isolation does not expose a
strictly heavier carrier.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open BRSpec

namespace
  PFSubsti.TAPkt

/-- The cutoff-three packet emits only its principal unit-right term. -/
lemma transient_classified_three
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hn : n ≤ 3)
    (normalizer :
      WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    polynomialClassifiedTerms
        (n_three hn :
          PFSubsti.TAPkt.{u}
            d n)
        normalizer B rightWord =
      [PIRed.classifiedUnitTransient
        normalizer hallPair B rightWord] := by
  rfl

/-- The cutoff-three temporary inner-reduction packet is the basic singleton. -/
lemma classified_terms_n
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hn : n ≤ 3)
    (normalizer :
      WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    innerClassifiedTerms
        (n_three hn :
          PFSubsti.TAPkt.{u}
            d n)
        normalizer outerExpansion innerWord rightWord =
      [PIRed.classifiedUnitTransient
        normalizer hallPair (outerExpansion.reword innerWord) rightWord] := by
  rfl

end
  PFSubsti.TAPkt

namespace
  PIRed

/-- The basic unit-right output is the principal reworded outer expansion. -/
lemma expansion_reword_reworded
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer :
      WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    wordExpansion normalizer hallPair (outerExpansion.reword innerWord)
        rightWord =
      rewordedBasicExpansion normalizer outerExpansion innerWord
        rightWord := by
  rfl

/--
A nonattachable outer carrier produces a nonattachable principal temporary
output with the same physical word and coefficient bound.
-/
lemma classified_reword_frontier
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer :
      WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hnonattachable :
      ¬ outerExpansion.coefficientWeight ≤
          outerExpansion.word.weight HEAddres.weight) :
    classifiedUnitTransient normalizer hallPair
        (outerExpansion.reword innerWord) rightWord =
      .frontier
        (rewordedBasicExpansion normalizer outerExpansion innerWord
          rightWord) := by
  rw [
    classified_transient_frontier]
  · rfl
  · simpa only [
      expansion_reword_reworded,
      coefficient_reworded_expansion,
      reworded_expansion_outer normalizer outerExpansion
        innerWord rightWord hword] using hnonattachable

end
  PIRed

namespace
  PFSubsti.TAPkt

/--
At cutoff three, a nonattachable temporary packet consists of one principal
frontier with the same physical outer word and coefficient bound.
-/
lemma
    classified_singleton_frontier
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hn : n ≤ 3)
    (normalizer :
      WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hnonattachable :
      ¬ outerExpansion.coefficientWeight ≤
          outerExpansion.word.weight HEAddres.weight) :
    innerClassifiedTerms
        (n_three hn :
          PFSubsti.TAPkt.{u}
            d n)
        normalizer outerExpansion innerWord rightWord =
      [.frontier
        (PIRed.rewordedBasicExpansion
          normalizer outerExpansion innerWord rightWord)] := by
  rw [classified_terms_n]
  rw [
    PIRed.classified_reword_frontier
      normalizer outerExpansion innerWord rightWord hword hnonattachable]

/--
The retained cutoff-three principal singleton evaluates exactly to its outer
parent frontier.
-/
lemma
    transient_classified_n
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hn : n ≤ 3)
    (normalizer :
      WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hnonattachable :
      ¬ outerExpansion.coefficientWeight ≤
          outerExpansion.word.weight HEAddres.weight)
    (e : ι → HEFam H) :
    SITerm.listValue (n := n) e
        (innerClassifiedTerms
          (n_three hn :
            PFSubsti.TAPkt.{u}
              d n)
          normalizer outerExpansion innerWord rightWord) =
      outerExpansion.value e := by
  rw [
    classified_singleton_frontier
      hn normalizer outerExpansion innerWord rightWord hword hnonattachable]
  simp only [SITerm.listValue,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    SITerm.value]
  exact
    PIRed.reworded_pair_outer
      normalizer outerExpansion innerWord rightWord hword e

end
  PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Contextual cancellation of polynomial transient packets

A classified unit-right transient Hall-Petresco packet has the same ordered
value as its raw transient packet.  Appending the raw packet in
reverse-negated order therefore gives a mixed contextual packet with trivial
value, even when some classified terms remain nonattachable frontiers.

This cancellation kernel lets a scheduler erase a packet together with its
exact inverse without normalizing any loose transient carrier in isolation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace PFSubsti.TAPkt

/--
An arbitrary classified transient packet followed by the all-frontier view
of its exact reverse-negated raw transient packet.
-/
def classifiedTermsContextual
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι) :
    List (SITerm H ι) :=
  packet.polynomialTransientTerms normalizer B A ++
    SITerm.frontierTerms
      (STExp.inverseList
        (packet.polynomialTransientExpansions normalizer B A))

/-- The arbitrary classified-packet inverse contextual kernel has trivial value. -/
lemma transient_terms_contextual
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (e : ι → HEFam H) :
    SITerm.listValue (n := n) e
        (packet.classifiedTermsContextual
          normalizer B A) =
      1 := by
  rw [classifiedTermsContextual,
    SITerm.listValue_append,
    packet.list_transient_terms,
    SITerm.value_frontier_terms,
    STExp.list_value_inverse,
    packet.value_transient_expansions]
  group

/-- Recollect an arbitrary classified-packet inverse contextual kernel to empty. -/
def recoll_trans_conte
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι) :
    TTRecoll
      n lowerWeight H
        (packet.classifiedTermsContextual
          normalizer B A) :=
  TTRecoll.empty_list_value
    _ fun e =>
      packet.transient_terms_contextual
        normalizer B A e

/--
Erase an arbitrary classified-packet inverse cancellation kernel in the
middle of an already recollected mixed context.
-/
def splice_transient_contextual
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (leftContext rightContext :
      List (SITerm H ι))
    (contextRecollection :
      TTRecoll
        n lowerWeight H (leftContext ++ rightContext)) :
    TTRecoll
      n lowerWeight H
        (leftContext ++
          packet.classifiedTermsContextual
            normalizer B A ++
          rightContext) :=
  TTRecoll.list_value
    contextRecollection fun e => by
      simp only [
        SITerm.listValue_append]
      rw [
        packet.transient_terms_contextual]
      group

/--
A classified unit-right transient packet followed by the all-frontier view of
its exact reverse-negated raw transient packet.
-/
def transientClassifiedContextual
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    List (SITerm H ι) :=
  packet.polynomialClassifiedTerms normalizer B rightWord ++
    SITerm.frontierTerms
      (STExp.inverseList
        (packet.rightTransientExpansions normalizer B rightWord))

/-- The classified-packet inverse contextual kernel has trivial value. -/
lemma classified_terms_contextual
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H))
    (e : ι → HEFam H) :
    SITerm.listValue (n := n) e
        (packet.transientClassifiedContextual
          normalizer B rightWord) =
      1 := by
  rw [transientClassifiedContextual,
    SITerm.listValue_append,
    packet.list_classified_terms,
    SITerm.value_frontier_terms,
    STExp.list_value_inverse,
    packet.list_transient_expansions]
  group

/-- Recollect the classified-packet inverse contextual kernel to empty. -/
def recoll_class_conte
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    TTRecoll
      n lowerWeight H
        (packet.transientClassifiedContextual
          normalizer B rightWord) :=
  TTRecoll.empty_list_value
    _ fun e =>
      packet.classified_terms_contextual
        normalizer B rightWord e

/--
Erase a classified-packet inverse cancellation kernel in the middle of an
already recollected mixed context.
-/
def splice_classified_contextual
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H))
    (leftContext rightContext :
      List (SITerm H ι))
    (contextRecollection :
      TTRecoll
        n lowerWeight H (leftContext ++ rightContext)) :
    TTRecoll
      n lowerWeight H
        (leftContext ++
          packet.transientClassifiedContextual
            normalizer B rightWord ++
          rightContext) :=
  TTRecoll.list_value
    contextRecollection fun e => by
      simp only [
        SITerm.listValue_append]
      rw [
        packet.classified_terms_contextual]
      group

/--
The reworded inner-reduction contextual expansion is a unit-right
classified-packet inverse kernel followed by the original outer frontier.
-/
lemma transient_contextual_append
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    packet.transientContextualTerms normalizer
        outerExpansion innerWord rightWord =
      packet.transientClassifiedContextual
          normalizer (outerExpansion.reword innerWord) rightWord ++
        [.frontier outerExpansion] := by
  rw [transientContextualTerms,
    transientClassifiedContextual,
    innerClassifiedTerms,
    transientInnerSource]
  simp only [SITerm.frontierTerms,
    List.map_append, List.map_singleton, List.append_assoc]

/--
Expand one transient outer frontier inside an already recollected mixed
context.  The inserted block is semantically equal to the original frontier.
-/
def recollection_splice_contextual
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (leftContext rightContext :
      List (SITerm H ι))
    (contextRecollection :
      TTRecoll
        n lowerWeight H
          (leftContext ++ [.frontier outerExpansion] ++ rightContext)) :
    TTRecoll
      n lowerWeight H
        (leftContext ++
          packet.transientContextualTerms
            normalizer outerExpansion innerWord rightWord ++
          rightContext) :=
  TTRecoll.list_value
    contextRecollection fun e => by
      simp only [
        SITerm.listValue_append,
        SITerm.value_singleton_frontier]
      rw [packet.transient_contextual_terms]

/--
Contract one reworded contextual expansion inside an already recollected
mixed context back to its original transient outer frontier.
-/
def splice_contextual_terms
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (leftContext rightContext :
      List (SITerm H ι))
    (contextRecollection :
      TTRecoll
        n lowerWeight H
          (leftContext ++
            packet.transientContextualTerms
              normalizer outerExpansion innerWord rightWord ++
            rightContext)) :
    TTRecoll
      n lowerWeight H
        (leftContext ++ [.frontier outerExpansion] ++ rightContext) :=
  TTRecoll.list_value
    contextRecollection fun e => by
      simp only [
        SITerm.listValue_append,
        SITerm.value_singleton_frontier]
      rw [packet.transient_contextual_terms]

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Class-two polynomial transient principal cancellation

At cutoff three, the unit-right Hall-Petresco packet consists only of its
principal basic term.  For a nonattachable reworded outer carrier, the
contextual restart therefore exposes the principal frontier, its exact
inverse, and the original outer frontier.

The first two terms cancel contextually.  A scheduler need not recursively
normalize the principal singleton before returning to the parent frontier.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open BRSpec

namespace PFSubsti.TAPkt

/-- At cutoff three, the unit-right inverse kernel is the principal pair. -/
lemma
    transient_classified_contextual
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hn : n ≤ 3)
    (normalizer :
      WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    transientClassifiedContextual
        (n_three hn :
          PFSubsti.TAPkt.{u}
            d n)
        normalizer B rightWord =
      [PIRed.classifiedUnitTransient
          normalizer hallPair B rightWord,
        .frontier
          (PIRed.wordExpansion
            normalizer hallPair B rightWord).neg] := by
  rfl

/--
For a nonattachable reworded outer carrier, the cutoff-three inverse kernel
is the principal frontier followed by its exact inverse.
-/
lemma
    poly_transient_pair
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hn : n ≤ 3)
    (normalizer :
      WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hnonattachable :
      ¬ outerExpansion.coefficientWeight ≤
          outerExpansion.word.weight HEAddres.weight) :
    transientClassifiedContextual
        (n_three hn :
          PFSubsti.TAPkt.{u}
            d n)
        normalizer (outerExpansion.reword innerWord) rightWord =
      [.frontier
          (PIRed.rewordedBasicExpansion
            normalizer outerExpansion innerWord rightWord),
        .frontier
          (PIRed.rewordedBasicExpansion
            normalizer outerExpansion innerWord rightWord).neg] := by
  rw [
    transient_classified_contextual,
    PIRed.classified_reword_frontier
      normalizer outerExpansion innerWord rightWord hword hnonattachable]
  rfl

/--
At cutoff three, the complete nonattachable contextual restart is the
principal cancellation pair followed by the original outer frontier.
-/
lemma
    poly_transient_outer
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hn : n ≤ 3)
    (normalizer :
      WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hnonattachable :
      ¬ outerExpansion.coefficientWeight ≤
          outerExpansion.word.weight HEAddres.weight) :
    transientContextualTerms
        (n_three hn :
          PFSubsti.TAPkt.{u}
            d n)
        normalizer outerExpansion innerWord rightWord =
      [.frontier
          (PIRed.rewordedBasicExpansion
            normalizer outerExpansion innerWord rightWord),
        .frontier
          (PIRed.rewordedBasicExpansion
            normalizer outerExpansion innerWord rightWord).neg,
        .frontier outerExpansion] := by
  rw [
    transient_contextual_append,
    poly_transient_pair
      hn normalizer outerExpansion innerWord rightWord hword hnonattachable]
  rfl

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Reachable contextual polynomial transient packets

Loose polynomial transient carriers should be manipulated in the mixed
packet contexts where their cancellation is visible, rather than normalized
as isolated ordinary factors.  This file records two semantic context moves:

* insert a classified transient packet together with its exact inverse;
* expand one transient outer frontier into its reworded contextual block.

Their equivalence closure is a small reachable-context vocabulary.  Every
reachable context has the same ordered value, so any ordinary recollection
transports across the complete relation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/-- One contextual polynomial transient-packet expansion inside a list context. -/
inductive STContexa
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) :
    List (SITerm H ι) →
      List (SITerm H ι) →
        Prop
  | inverseKernel
      (packet :
        PFSubsti.TAPkt.{u}
          d n)
      (normalizer :
        WBForm.RCNormal H ι)
      (B A : STExp H ι)
      (leftContext rightContext :
        List (SITerm H ι)) :
      STContexa H ι
        (leftContext ++ rightContext)
        (leftContext ++
          packet.classifiedTermsContextual
            normalizer B A ++
          rightContext)
  | rightInverseKernel
      (packet :
        PFSubsti.TAPkt.{u}
          d n)
      (normalizer :
        WBForm.RCNormal H ι)
      (B : STExp H ι)
      (rightWord : CWord (HEAddres H))
      (leftContext rightContext :
        List (SITerm H ι)) :
      STContexa H ι
        (leftContext ++ rightContext)
        (leftContext ++
          packet.transientClassifiedContextual
            normalizer B rightWord ++
          rightContext)
  | rewordedOuter
      (packet :
        PFSubsti.TAPkt.{u}
          d n)
      (normalizer :
        WBForm.RCNormal H ι)
      (outerExpansion : STExp H ι)
      (innerWord rightWord : CWord (HEAddres H))
      (leftContext rightContext :
        List (SITerm H ι)) :
      STContexa H ι
        (leftContext ++ [.frontier outerExpansion] ++ rightContext)
        (leftContext ++
          packet.transientContextualTerms
            normalizer outerExpansion innerWord rightWord ++
          rightContext)

namespace STContexa

/-- Every one-step contextual expansion preserves the ordered packet value. -/
lemma listValue_eq
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source target :
      List (SITerm H ι)}
    (step :
      STContexa
        (n := n) H ι source target)
    (e : ι → HEFam H) :
    SITerm.listValue (n := n) e
        source =
      SITerm.listValue e target := by
  cases step with
  | inverseKernel packet normalizer B A leftContext rightContext =>
      simp only [
        SITerm.listValue_append]
      rw [
        packet.transient_terms_contextual]
      group
  | rightInverseKernel packet normalizer B rightWord leftContext
      rightContext =>
      simp only [
        SITerm.listValue_append]
      rw [
        packet.classified_terms_contextual]
      group
  | rewordedOuter packet normalizer outerExpansion innerWord rightWord
      leftContext rightContext =>
      simp only [
        SITerm.listValue_append,
        SITerm.value_singleton_frontier]
      rw [packet.transient_contextual_terms]

end STContexa

/-- Equivalence closure of elementary contextual polynomial transient expansions. -/
def TCReach
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (source target :
      List (SITerm H ι)) :
    Prop :=
  Relation.EqvGen
    (STContexa (n := n) H ι)
      source target

namespace TCReach

/-- Contextually reachable mixed packets have the same ordered value. -/
lemma listValue_eq
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source target :
      List (SITerm H ι)}
    (reachable :
      TCReach
        (n := n) H ι source target)
    (e : ι → HEFam H) :
    SITerm.listValue (n := n) e
        source =
      SITerm.listValue e target := by
  induction reachable with
  | rel source target step =>
      exact step.listValue_eq e
  | refl =>
      rfl
  | symm source target _ ih =>
      exact ih.symm
  | trans source middle target _ _ hsource htarget =>
      exact hsource.trans htarget

end TCReach

namespace TTRecoll

/-- Transport ordinary recollection across any reachable contextual rewrite. -/
def of_contextuallyReachable
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source target :
      List (SITerm H ι)}
    (recollection :
      TTRecoll
        n lowerWeight H source)
    (reachable :
      TCReach
        (n := n) H ι source target) :
    TTRecoll
      n lowerWeight H target :=
  list_value recollection fun e => reachable.listValue_eq e

end TTRecoll

end TCTex
end Submission

/-!
# Congruence rules for reachable contextual polynomial transient packets

Reachable polynomial transient-packet rewrites are generated inside
arbitrary list contexts, but later collectors need to lift complete rewrite
chains through a larger surrounding packet.  This file packages that
congruence rule and the two elementary reachable expansions in a
callback-friendly form.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace TCReach

/-- Every mixed packet is contextually reachable from itself. -/
lemma refl
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (source : List (SITerm H ι)) :
    TCReach
      (n := n) H ι source source :=
  Relation.EqvGen.refl source

/-- Reverse a reachable contextual rewrite chain. -/
lemma symm
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source target :
      List (SITerm H ι)}
    (reachable :
      TCReach
        (n := n) H ι source target) :
    TCReach
      (n := n) H ι target source :=
  Relation.EqvGen.symm source target reachable

/-- Compose two reachable contextual rewrite chains. -/
lemma trans
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source middle target :
      List (SITerm H ι)}
    (left :
      TCReach
        (n := n) H ι source middle)
    (right :
      TCReach
        (n := n) H ι middle target) :
    TCReach
      (n := n) H ι source target :=
  Relation.EqvGen.trans source middle target left right

/-- Regard one elementary contextual expansion as a reachable rewrite. -/
lemma of_expansionStep
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source target :
      List (SITerm H ι)}
    (step :
      STContexa
        (n := n) H ι source target) :
    TCReach
      (n := n) H ι source target :=
  Relation.EqvGen.rel source target step

/--
Lift a complete reachable rewrite chain through an arbitrary surrounding
mixed-packet context.
-/
lemma context
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source target :
      List (SITerm H ι)}
    (reachable :
      TCReach
        (n := n) H ι source target)
    (leftContext rightContext :
      List (SITerm H ι)) :
    TCReach
      (n := n) H ι
        (leftContext ++ source ++ rightContext)
        (leftContext ++ target ++ rightContext) := by
  induction reachable with
  | rel source target step =>
      apply of_expansionStep
      cases step with
      | inverseKernel packet normalizer B A left right =>
          simpa only [List.append_assoc] using
            STContexa.inverseKernel
              packet normalizer B A (leftContext ++ left)
                (right ++ rightContext)
      | rightInverseKernel packet normalizer B rightWord left right =>
          simpa only [List.append_assoc] using
            STContexa.rightInverseKernel
              packet normalizer B rightWord (leftContext ++ left)
                (right ++ rightContext)
      | rewordedOuter packet normalizer outerExpansion innerWord rightWord
          left right =>
          simpa only [List.append_assoc] using
            STContexa.rewordedOuter
              packet normalizer outerExpansion innerWord rightWord
                (leftContext ++ left) (right ++ rightContext)
  | refl =>
      exact refl _
  | symm source target _ ih =>
      exact ih.symm
  | trans source middle target _ _ hsource htarget =>
      exact hsource.trans htarget

/-- Insert one exact classified-packet inverse kernel into a mixed context. -/
lemma inverseKernel
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (leftContext rightContext :
      List (SITerm H ι)) :
    TCReach
      (n := n) H ι
        (leftContext ++ rightContext)
        (leftContext ++
          packet.classifiedTermsContextual
            normalizer B A ++
          rightContext) :=
  of_expansionStep <|
    STContexa.inverseKernel
      packet normalizer B A leftContext rightContext

/-- Insert one exact unit-right inverse kernel into a mixed context. -/
lemma rightInverseKernel
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H))
    (leftContext rightContext :
      List (SITerm H ι)) :
    TCReach
      (n := n) H ι
        (leftContext ++ rightContext)
        (leftContext ++
          packet.transientClassifiedContextual
            normalizer B rightWord ++
          rightContext) :=
  of_expansionStep <|
    STContexa.rightInverseKernel
      packet normalizer B rightWord leftContext rightContext

/-- Expand one transient outer frontier into its reworded contextual block. -/
lemma rewordedOuter
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (leftContext rightContext :
      List (SITerm H ι)) :
    TCReach
      (n := n) H ι
        (leftContext ++ [.frontier outerExpansion] ++ rightContext)
        (leftContext ++
          packet.transientContextualTerms
            normalizer outerExpansion innerWord rightWord ++
          rightContext) :=
  of_expansionStep <|
    STContexa.rewordedOuter
      packet normalizer outerExpansion innerWord rightWord leftContext
        rightContext

/-- The empty source reaches one exact classified-packet inverse kernel. -/
lemma nilTransientContext
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι) :
    TCReach
      (n := n) H ι []
        (packet.classifiedTermsContextual
          normalizer B A) := by
  simpa using inverseKernel packet normalizer B A [] []

/-- The empty source reaches one exact unit-right inverse kernel. -/
lemma nilInverseContext
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    TCReach
      (n := n) H ι []
        (packet.transientClassifiedContextual
          normalizer B rightWord) := by
  simpa using rightInverseKernel packet normalizer B rightWord [] []

/-- A singleton frontier reaches its reworded contextual expansion. -/
lemma singletonFrontierContext
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    TCReach
      (n := n) H ι [.frontier outerExpansion]
        (packet.transientContextualTerms
          normalizer outerExpansion innerWord rightWord) := by
  simpa using
    rewordedOuter packet normalizer outerExpansion innerWord rightWord [] []

end TCReach

namespace PFSubsti.TAPkt

/-- Packet-style alias for inserting one exact inverse cancellation kernel. -/
lemma transientContextReachable
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι) :
    TCReach
      (n := n) H ι []
        (packet.classifiedTermsContextual
          normalizer B A) :=
  TCReach.nilTransientContext
    packet normalizer B A

/-- Packet-style alias for inserting one exact unit-right inverse kernel. -/
lemma
    rightContextReachable
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    TCReach
      (n := n) H ι []
        (packet.transientClassifiedContextual
          normalizer B rightWord) :=
  TCReach.nilInverseContext
    packet normalizer B rightWord

/-- Packet-style alias for expanding one transient outer frontier. -/
lemma reductionContextReachable
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H)) :
    TCReach
      (n := n) H ι [.frontier outerExpansion]
        (packet.transientContextualTerms
          normalizer outerExpansion innerWord rightWord) :=
  TCReach.singletonFrontierContext
    packet normalizer outerExpansion innerWord rightWord

end PFSubsti.TAPkt

namespace TTRecoll

/--
Transport a recollection through a reachable rewrite chain nested inside a
larger mixed-packet context.
-/
def contextually_context
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source target :
      List (SITerm H ι)}
    (leftContext rightContext :
      List (SITerm H ι))
    (recollection :
      TTRecoll
        n lowerWeight H (leftContext ++ source ++ rightContext))
    (reachable :
      TCReach
        (n := n) H ι source target) :
    TTRecoll
      n lowerWeight H (leftContext ++ target ++ rightContext) :=
  recollection.of_contextuallyReachable
    (reachable.context leftContext rightContext)

end TTRecoll

end TCTex
end Submission

/-!
# Reachably terminal polynomial transient contexts

A loose polynomial transient carrier need not have an ordinary symbolic
representative in isolation.  Contextual expansion can nevertheless expose
a mixed source whose remaining frontier terms have all reached the
nilpotent cutoff.

This file packages that endpoint and its closure under reachable contextual
rewrites.  The resulting type is compositional under list concatenation and
supplies an ordinary recollection without normalizing loose frontiers by
fiat.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace TCReach

/-- A reachable rewrite remains reachable after adding a fixed prefix. -/
lemma append_left
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source target :
      List (SITerm H ι)}
    (reachable :
      TCReach
        (n := n) H ι source target)
    (leftContext :
      List (SITerm H ι)) :
    TCReach
      (n := n) H ι
        (leftContext ++ source)
        (leftContext ++ target) := by
  simpa using reachable.context leftContext []

/-- A reachable rewrite remains reachable after adding a fixed suffix. -/
lemma append_right
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source target :
      List (SITerm H ι)}
    (reachable :
      TCReach
        (n := n) H ι source target)
    (rightContext :
      List (SITerm H ι)) :
    TCReach
      (n := n) H ι
        (source ++ rightContext)
        (target ++ rightContext) := by
  simpa using reachable.context [] rightContext

end TCReach

/--
A mixed polynomial transient context that can be recollected directly:
every term has enough physical support, and every retained frontier term has
reached the nilpotent cutoff.
-/
structure TTContex
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (source : List (SITerm H ι)) :
    Prop where
  wordLeast :
    ∀ term ∈ source,
      lowerWeight ≤ SITerm.wordWeight
        term
  frontierAtCutoff :
    ∀ wordExpansion,
      .frontier wordExpansion ∈ source →
        n ≤ wordExpansion.word.weight HEAddres.weight

namespace TTContex

/-- The empty mixed source is terminal at every requested support bound. -/
def empty
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type} :
    TTContex
      (n := n) (lowerWeight := lowerWeight) H ι
        ([] : List (SITerm H ι)) where
  wordLeast := by
    intro term hterm
    simp at hterm
  frontierAtCutoff := by
    intro wordExpansion hwordExpansion
    simp at hwordExpansion

/-- Concatenating terminal mixed sources preserves terminality. -/
def append
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {leftSource rightSource :
      List (SITerm H ι)}
    (left :
      TTContex
        (n := n) (lowerWeight := lowerWeight) H ι leftSource)
    (right :
      TTContex
        (n := n) (lowerWeight := lowerWeight) H ι rightSource) :
    TTContex
      (n := n) (lowerWeight := lowerWeight) H ι
        (leftSource ++ rightSource) where
  wordLeast := by
    intro term hterm
    rcases List.mem_append.mp hterm with hterm | hterm
    · exact left.wordLeast term hterm
    · exact right.wordLeast term hterm
  frontierAtCutoff := by
    intro wordExpansion hwordExpansion
    rcases List.mem_append.mp hwordExpansion with hwordExpansion | hwordExpansion
    · exact left.frontierAtCutoff wordExpansion hwordExpansion
    · exact right.frontierAtCutoff wordExpansion hwordExpansion

/-- One attached term is terminal whenever it has the requested support. -/
def singleton_attached
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι)
    (hweight :
      lowerWeight ≤ factor.word.weight HEAddres.weight) :
    TTContex
      (n := n) (lowerWeight := lowerWeight) H ι [.attached factor] where
  wordLeast := by
    intro term hterm
    simp only [List.mem_singleton] at hterm
    subst term
    exact hweight
  frontierAtCutoff := by
    intro wordExpansion hwordExpansion
    simp at hwordExpansion

/--
One frontier term is terminal whenever it has the requested support and has
already reached the nilpotent cutoff.
-/
def singleton_frontier
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (wordExpansion : STExp H ι)
    (hweight :
      lowerWeight ≤ wordExpansion.word.weight HEAddres.weight)
    (hcutoff :
      n ≤ wordExpansion.word.weight HEAddres.weight) :
    TTContex
      (n := n) (lowerWeight := lowerWeight) H ι
        [.frontier wordExpansion] where
  wordLeast := by
    intro term hterm
    simp only [List.mem_singleton] at hterm
    subst term
    exact hweight
  frontierAtCutoff := by
    intro transientExpansion htransientExpansion
    simp only [List.mem_singleton] at htransientExpansion
    cases htransientExpansion
    exact hcutoff

/-- A terminal mixed source recollects directly to ordinary factors. -/
noncomputable def sourceRecollection
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source : List (SITerm H ι)}
    (terminal :
      TTContex
        (n := n) (lowerWeight := lowerWeight) H ι source) :
    TTRecoll
      n lowerWeight H source :=
  TTRecoll.word_frontier_cutoff
    source terminal.wordLeast terminal.frontierAtCutoff

end TTContex

/--
A mixed polynomial transient source is reachably terminal when contextual
rewrites take it to a directly recollectable terminal endpoint.
-/
structure TRTermin
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (source : List (SITerm H ι)) :
    Type (u + 1) where
  target :
    List (SITerm H ι)
  reachable :
    TCReach
      (n := n) H ι source target
  terminal :
    TTContex
      (n := n) (lowerWeight := lowerWeight) H ι target

namespace TRTermin

/-- A directly terminal source is reachably terminal by reflexivity. -/
def of_terminal
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source : List (SITerm H ι)}
    (terminal :
      TTContex
        (n := n) (lowerWeight := lowerWeight) H ι source) :
    TRTermin
      (n := n) (lowerWeight := lowerWeight) H ι source where
  target := source
  reachable := TCReach.refl source
  terminal := terminal

/-- Reachably terminality transports backward across contextual rewrites. -/
def of_contextuallyReachable
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source target :
      List (SITerm H ι)}
    (targetTerminal :
      TRTermin
        (n := n) (lowerWeight := lowerWeight) H ι target)
    (reachable :
      TCReach
        (n := n) H ι source target) :
    TRTermin
      (n := n) (lowerWeight := lowerWeight) H ι source where
  target := targetTerminal.target
  reachable := reachable.trans targetTerminal.reachable
  terminal := targetTerminal.terminal

/-- Reachably terminal mixed sources compose in their original order. -/
def append
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {leftSource rightSource :
      List (SITerm H ι)}
    (left :
      TRTermin
        (n := n) (lowerWeight := lowerWeight) H ι leftSource)
    (right :
      TRTermin
        (n := n) (lowerWeight := lowerWeight) H ι rightSource) :
    TRTermin
      (n := n) (lowerWeight := lowerWeight) H ι
        (leftSource ++ rightSource) where
  target := left.target ++ right.target
  reachable :=
    (left.reachable.append_right rightSource).trans
      (right.reachable.append_left left.target)
  terminal := left.terminal.append right.terminal

/--
Recollect a reachably terminal source by recollecting its endpoint and
transporting the result back across the contextual rewrite chain.
-/
noncomputable def sourceRecollection
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source : List (SITerm H ι)}
    (normalizable :
      TRTermin
        (n := n) (lowerWeight := lowerWeight) H ι source) :
    TTRecoll
      n lowerWeight H source :=
  normalizable.terminal.sourceRecollection.of_contextuallyReachable
    normalizable.reachable.symm

end TRTermin

namespace PFSubsti.TAPkt

open TRTermin
open TTContex

/--
An arbitrary classified packet followed by its exact raw inverse is
reachably terminal at every requested support bound.
-/
def reachably_transient_contextual
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι) :
    TRTermin
      (n := n) (lowerWeight := lowerWeight) H ι
        (packet.classifiedTermsContextual
          normalizer B A) :=
  of_contextuallyReachable (of_terminal empty) <| by
    exact
      (TCReach.nilTransientContext
        packet normalizer B A).symm

/--
A unit-right classified packet followed by its exact raw inverse is
reachably terminal at every requested support bound.
-/
def
    reachably_classified_contextual
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H)) :
    TRTermin
      (n := n) (lowerWeight := lowerWeight) H ι
        (packet.transientClassifiedContextual
          normalizer B rightWord) :=
  of_contextuallyReachable (of_terminal empty) <| by
    exact
      (TCReach.nilInverseContext
        packet normalizer B rightWord).symm

/--
The reworded contextual expansion is reachably terminal whenever the outer
frontier singleton is reachably terminal.
-/
def reachably_terminal_transient
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (outerTerminal :
      TRTermin
        (n := n) (lowerWeight := lowerWeight) H ι
          [.frontier outerExpansion]) :
    TRTermin
      (n := n) (lowerWeight := lowerWeight) H ι
        (packet.transientContextualTerms
          normalizer outerExpansion innerWord rightWord) :=
  of_contextuallyReachable outerTerminal <| by
    exact
      (TCReach.singletonFrontierContext
        packet normalizer outerExpansion innerWord rightWord).symm

/--
Conversely, a reachably terminal reworded contextual expansion closes its
original outer frontier singleton.
-/
def
    reachably_terminal_contextual
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (contextualTerminal :
      TRTermin
        (n := n) (lowerWeight := lowerWeight) H ι
          (packet.transientContextualTerms
            normalizer outerExpansion innerWord rightWord)) :
    TRTermin
      (n := n) (lowerWeight := lowerWeight) H ι [.frontier outerExpansion] :=
  of_contextuallyReachable contextualTerminal <| by
    exact
      TCReach.singletonFrontierContext
        packet normalizer outerExpansion innerWord rightWord

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Contextual splicing for reachably terminal polynomial transient packets

Reachably terminal polynomial packets transport backward through contextual
rewrites.  Recursive collectors also need the nested form of that rule:
replace one subpacket inside a fixed prefix and suffix, or insert a
cancellation block that contextually rewrites to the empty packet.

This file packages those closure operations without normalizing any loose
transient carrier in isolation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace TRTermin

/--
Transport a reachably terminal endpoint backward through a contextual rewrite
nested inside a fixed prefix and suffix.
-/
def contextually_context
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source target :
      List (SITerm H ι)}
    (leftContext rightContext :
      List (SITerm H ι))
    (targetTerminal :
      TRTermin
        (n := n) (lowerWeight := lowerWeight) H ι
          (leftContext ++ target ++ rightContext))
    (reachable :
      TCReach
        (n := n) H ι source target) :
    TRTermin
      (n := n) (lowerWeight := lowerWeight) H ι
        (leftContext ++ source ++ rightContext) :=
  of_contextuallyReachable targetTerminal
    (reachable.context leftContext rightContext)

/--
Insert a mixed block into a reachably terminal context whenever that block
contextually rewrites to the empty packet.
-/
def insert_contextually_reachable
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {middle :
      List (SITerm H ι)}
    (leftContext rightContext :
      List (SITerm H ι))
    (contextTerminal :
      TRTermin
        (n := n) (lowerWeight := lowerWeight) H ι
          (leftContext ++ rightContext))
    (reachable :
      TCReach
        (n := n) H ι middle []) :
    TRTermin
      (n := n) (lowerWeight := lowerWeight) H ι
        (leftContext ++ middle ++ rightContext) := by
  apply contextually_context leftContext rightContext ?_ reachable
  simpa only [List.append_nil] using contextTerminal

/--
Recollect a source nested inside a larger context by transporting backward
from a reachably terminal replacement.
-/
noncomputable def contextually_reachable_context
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source target :
      List (SITerm H ι)}
    (leftContext rightContext :
      List (SITerm H ι))
    (targetTerminal :
      TRTermin
        (n := n) (lowerWeight := lowerWeight) H ι
          (leftContext ++ target ++ rightContext))
    (reachable :
      TCReach
        (n := n) H ι source target) :
    TTRecoll
      n lowerWeight H (leftContext ++ source ++ rightContext) :=
  (contextually_context leftContext rightContext targetTerminal
      reachable).sourceRecollection

end TRTermin

namespace PFSubsti.TAPkt

/--
Insert one exact classified-packet inverse kernel into an arbitrary reachably
terminal context.
-/
def
    reachably_terminal_insert
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (leftContext rightContext :
      List (SITerm H ι))
    (contextTerminal :
      TRTermin
        (n := n) (lowerWeight := lowerWeight) H ι
          (leftContext ++ rightContext)) :
    TRTermin
      (n := n) (lowerWeight := lowerWeight) H ι
        (leftContext ++
          packet.classifiedTermsContextual
            normalizer B A ++
          rightContext) :=
  TRTermin.insert_contextually_reachable
    leftContext rightContext contextTerminal <| by
      exact
        (packet.transientContextReachable
          normalizer B A).symm

/--
Recollect a context after inserting one exact classified-packet inverse
kernel.
-/
noncomputable def
    insert_transient_contextual
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (leftContext rightContext :
      List (SITerm H ι))
    (contextTerminal :
      TRTermin
        (n := n) (lowerWeight := lowerWeight) H ι
          (leftContext ++ rightContext)) :
    TTRecoll
      n lowerWeight H
        (leftContext ++
          packet.classifiedTermsContextual
            normalizer B A ++
          rightContext) :=
  (packet
    |>.reachably_terminal_insert
      normalizer B A leftContext rightContext contextTerminal
    |>.sourceRecollection)

/--
Insert one exact unit-right inverse kernel into an arbitrary reachably
terminal context.
-/
def
    reachably_insert_contextual
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H))
    (leftContext rightContext :
      List (SITerm H ι))
    (contextTerminal :
      TRTermin
        (n := n) (lowerWeight := lowerWeight) H ι
          (leftContext ++ rightContext)) :
    TRTermin
      (n := n) (lowerWeight := lowerWeight) H ι
        (leftContext ++
          packet.transientClassifiedContextual
            normalizer B rightWord ++
          rightContext) :=
  TRTermin.insert_contextually_reachable
    leftContext rightContext contextTerminal <| by
      exact
        (packet.rightContextReachable
          normalizer B rightWord).symm

/--
Recollect a context after inserting one exact unit-right inverse kernel.
-/
noncomputable def
    insert_classified_contextual
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H))
    (leftContext rightContext :
      List (SITerm H ι))
    (contextTerminal :
      TRTermin
        (n := n) (lowerWeight := lowerWeight) H ι
          (leftContext ++ rightContext)) :
    TTRecoll
      n lowerWeight H
        (leftContext ++
          packet.transientClassifiedContextual
            normalizer B rightWord ++
          rightContext) :=
  (packet
    |>.reachably_insert_contextual
      normalizer B rightWord leftContext rightContext contextTerminal
    |>.sourceRecollection)

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Terminal packet routes for reachable polynomial transient contexts

Reachably terminal polynomial contexts provide direct endpoints for
classified packets whose parent carrier is one stratum below the nilpotent
cutoff.  Reworded temporary packets use the same endpoint when their inner
carrier is terminal.

This file packages those endpoint instances and support weakening.  It is
intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace TTContex

/-- Lower the requested physical support bound of a terminal endpoint. -/
def weaken
    {d n lowerWeight weakerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source : List (SITerm H ι)}
    (terminal :
      TTContex
        (n := n) (lowerWeight := lowerWeight) H ι source)
    (hweight : weakerWeight ≤ lowerWeight) :
    TTContex
      (n := n) (lowerWeight := weakerWeight) H ι source where
  wordLeast := fun term hterm =>
    hweight.trans (terminal.wordLeast term hterm)
  frontierAtCutoff := terminal.frontierAtCutoff

end TTContex

namespace TRTermin

/-- Lower the requested physical support bound of a reachable endpoint. -/
def weaken
    {d n lowerWeight weakerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source : List (SITerm H ι)}
    (normalizable :
      TRTermin
        (n := n) (lowerWeight := lowerWeight) H ι source)
    (hweight : weakerWeight ≤ lowerWeight) :
    TRTermin
      (n := n) (lowerWeight := weakerWeight) H ι source where
  target := normalizable.target
  reachable := normalizable.reachable
  terminal := normalizable.terminal.weaken hweight

end TRTermin

namespace PFSubsti.TAPkt

open TRTermin
open TTContex

/--
A generic classified transient packet is a direct terminal endpoint when its
left parent is one stratum below the nilpotent cutoff.
-/
def terminal_context_left
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hcutoff : n ≤ B.word.weight HEAddres.weight + 1) :
    TTContex
      (n := n)
      (lowerWeight := B.word.weight HEAddres.weight)
      H ι (packet.polynomialTransientTerms normalizer B A) where
  wordLeast := fun term hterm =>
    Nat.le_of_lt
      (packet.left_classified_terms
        normalizer B A term hterm)
  frontierAtCutoff := fun wordExpansion hwordExpansion =>
    hcutoff.trans
      (Nat.succ_le_of_lt
        (packet.left_classified_frontier
          normalizer B A wordExpansion hwordExpansion))

/--
A generic classified transient packet is a direct terminal endpoint when its
right parent is one stratum below the nilpotent cutoff.
-/
def terminal_context_transient
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hcutoff : n ≤ A.word.weight HEAddres.weight + 1) :
    TTContex
      (n := n)
      (lowerWeight := A.word.weight HEAddres.weight)
      H ι (packet.polynomialTransientTerms normalizer B A) where
  wordLeast := fun term hterm =>
    Nat.le_of_lt
      (packet.transient_classified_terms
        normalizer B A term hterm)
  frontierAtCutoff := fun wordExpansion hwordExpansion =>
    hcutoff.trans
      (Nat.succ_le_of_lt
        (packet.transient_terms_frontier
          normalizer B A wordExpansion hwordExpansion))

/-- Reachably terminal view of the left-terminal generic packet. -/
def reachably_terminal_left
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hcutoff : n ≤ B.word.weight HEAddres.weight + 1) :
    TRTermin
      (n := n)
      (lowerWeight := B.word.weight HEAddres.weight)
      H ι (packet.polynomialTransientTerms normalizer B A) :=
  of_terminal <|
    packet.terminal_context_left
      normalizer B A hcutoff

/-- Reachably terminal view of the right-terminal generic packet. -/
def reachably_transient_classified
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : STExp H ι)
    (hcutoff : n ≤ A.word.weight HEAddres.weight + 1) :
    TRTermin
      (n := n)
      (lowerWeight := A.word.weight HEAddres.weight)
      H ι (packet.polynomialTransientTerms normalizer B A) :=
  of_terminal <|
    packet.terminal_context_transient
      normalizer B A hcutoff

/--
A unit-right classified transient packet is a direct terminal endpoint when
its left parent is one stratum below the nilpotent cutoff.
-/
def terminal_context_classified
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H))
    (hcutoff : n ≤ B.word.weight HEAddres.weight + 1) :
    TTContex
      (n := n)
      (lowerWeight := B.word.weight HEAddres.weight)
      H ι
        (packet.polynomialClassifiedTerms normalizer B
          rightWord) where
  wordLeast := fun term hterm =>
    Nat.le_of_lt
      (packet.left_transient_classified
        normalizer B rightWord term hterm)
  frontierAtCutoff := fun wordExpansion hwordExpansion =>
    hcutoff.trans
      (Nat.succ_le_of_lt
        (packet.left_transient_classified
          normalizer B rightWord (.frontier wordExpansion) hwordExpansion))

/-- Reachably terminal view of the left-terminal unit-right packet. -/
def
    reachably_terminal_classified
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (B : STExp H ι)
    (rightWord : CWord (HEAddres H))
    (hcutoff : n ≤ B.word.weight HEAddres.weight + 1) :
    TRTermin
      (n := n)
      (lowerWeight := B.word.weight HEAddres.weight)
      H ι
        (packet.polynomialClassifiedTerms normalizer B
          rightWord) :=
  of_terminal <|
    packet
      |>.terminal_context_classified
        normalizer B rightWord hcutoff

/--
The temporary packet emitted by rewording an outer carrier is directly
terminal at the stronger original outer support bound whenever its selected
inner Hall word is one stratum below cutoff.
-/
def
    terminal_context_poly
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff : n ≤ innerWord.weight HEAddres.weight + 1) :
    TTContex
      (n := n)
      (lowerWeight :=
        outerExpansion.word.weight HEAddres.weight)
      H ι
        (packet.innerClassifiedTerms
          normalizer outerExpansion innerWord rightWord) where
  wordLeast := fun term hterm =>
    packet
      |>.poly_classified_terms
        normalizer outerExpansion innerWord rightWord hword term hterm
  frontierAtCutoff := fun wordExpansion hwordExpansion =>
    hcutoff.trans
      (Nat.succ_le_of_lt <| by
        apply
          packet
            |>.left_transient_classified
              normalizer (outerExpansion.reword innerWord) rightWord
                (.frontier wordExpansion)
        simpa only [
          innerClassifiedTerms] using
            hwordExpansion)

/-- Reachably terminal view of the stronger outer-support temporary endpoint. -/
def
    reachably_terminal_poly
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion : STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hcutoff : n ≤ innerWord.weight HEAddres.weight + 1) :
    TRTermin
      (n := n)
      (lowerWeight :=
        outerExpansion.word.weight HEAddres.weight)
      H ι
        (packet.innerClassifiedTerms
          normalizer outerExpansion innerWord rightWord) :=
  of_terminal <|
    packet
      |>.terminal_context_poly
        normalizer outerExpansion innerWord rightWord hword hcutoff

end PFSubsti.TAPkt

end TCTex
end Submission

/-!
# Reachable contextual routing for one polynomial transient frontier

The generated residual collector closes the strict residual around a
transient polynomial commutator carrier.  The remaining local obligation is
exactly the temporary unit-right classified packet produced by rewording its
inner word.

This file records that restricted local rule.  It also transports the closed
frontier singleton across reachable contextual rewrites, without asserting a
collector for arbitrary loose transient carriers.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open PFSubsti.TAPkt

/--
The exact remaining local input for recollecting one decomposable polynomial
transient frontier from a contextual recursive callback.
-/
structure
    PRRoute
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion :
      STExp H ι) where
  innerWord : CWord (HEAddres H)
  rightWord : CWord (HEAddres H)
  word_eq : outerExpansion.word = .commutator innerWord rightWord
  temporaryPacketRecollection :
    (∀ child,
      SITerm.FrontierDefectMultiset
          n child [.frontier outerExpansion] →
        TTRecoll
          n lowerWeight H child) →
      TTRecoll
        n lowerWeight H
          (packet.innerClassifiedTerms
            normalizer outerExpansion innerWord rightWord)

namespace
  PRRoute

/--
Close the parent polynomial transient singleton using the supplied temporary
packet rule and the generated strict-residual route.
-/
noncomputable def sourceRecollection
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {normalizer :
      WBForm.RCNormal H ι}
    {outerExpansion :
      STExp H ι}
    (routing :
      PRRoute
        (lowerWeight := lowerWeight) H ι packet normalizer outerExpansion)
    (split : packet.PBSplit)
    (houterTruncated :
      outerExpansion.word.weight HEAddres.weight < n)
    (recursiveResults :
      ∀ child,
        SITerm.FrontierDefectMultiset
            n child [.frontier outerExpansion] →
          TTRecoll
            n lowerWeight H child) :
    TTRecoll
      n lowerWeight H [.frontier outerExpansion] :=
  let residualRouting :=
    TORoutea.of_recursiveResults
      split normalizer outerExpansion houterTruncated routing.innerWord
        routing.rightWord routing.word_eq recursiveResults
  residualRouting.sourcerec_frontier routing.word_eq
    (routing.temporaryPacketRecollection recursiveResults)

/--
After closing the parent singleton, transport its recollection across any
reachable contextual rewrite chain.
-/
noncomputable def recollection_contextually_reachable
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {normalizer :
      WBForm.RCNormal H ι}
    {outerExpansion :
      STExp H ι}
    (routing :
      PRRoute
        (lowerWeight := lowerWeight) H ι packet normalizer outerExpansion)
    (split : packet.PBSplit)
    (houterTruncated :
      outerExpansion.word.weight HEAddres.weight < n)
    (recursiveResults :
      ∀ child,
        SITerm.FrontierDefectMultiset
            n child [.frontier outerExpansion] →
          TTRecoll
            n lowerWeight H child)
    {target :
      List (SITerm H ι)}
    (reachable :
      TCReach
        (n := n) H ι [.frontier outerExpansion] target) :
    TTRecoll
      n lowerWeight H target :=
  (routing.sourceRecollection split houterTruncated recursiveResults)
    |>.of_contextuallyReachable reachable

/--
Build frontier routing data without a recursive temporary-packet call when
the reworded inner carrier is already one stratum below cutoff.
-/
def inner_terminal_outer
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion :
      STExp H ι)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hlowerWeight :
      lowerWeight ≤ outerExpansion.word.weight HEAddres.weight)
    (hcutoff : n ≤ innerWord.weight HEAddres.weight + 1) :
    PRRoute
      (lowerWeight := lowerWeight) H ι packet normalizer outerExpansion where
  innerWord := innerWord
  rightWord := rightWord
  word_eq := hword
  temporaryPacketRecollection := fun _ =>
    (packet
      |>.reachably_terminal_poly
        normalizer outerExpansion innerWord rightWord hword hcutoff
      |>.weaken hlowerWeight
      |>.sourceRecollection)

end
  PRRoute

end TCTex
end Submission

/-!
# Bifurcated routing for active polynomial transient frontiers

Recollecting a decomposable polynomial transient frontier has two distinct
recursive roots.  Its strict residual tails descend in cutoff defect from the
original outer carrier.  Its temporary unit-right classified packet instead
descends from the reworded inner carrier.

This file packages that bifurcation.  When the selected inner Hall word has
reached its terminal endpoint, the temporary packet closes directly at the
stronger original outer support bound.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
Routing data for an arbitrary decomposable polynomial transient frontier.
The outer and inner recursive callbacks used below intentionally have
different roots.
-/
structure
    BRRoutea
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (normalizer : WBForm.RCNormal H ι)
    (outerExpansion :
      STExp H ι) where
  innerWord : CWord (HEAddres H)
  rightWord : CWord (HEAddres H)
  word_eq : outerExpansion.word = .commutator innerWord rightWord

namespace
  BRRoutea

/--
Recollect one decomposable polynomial transient outer frontier.  Strict
residual tails use recursive results rooted at the outer carrier.  While the
inner carrier is active, temporary terms use recursive results rooted at the
reworded inner carrier; at its endpoint they close directly.
-/
noncomputable def sourceRecollection
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    {normalizer :
      WBForm.RCNormal H ι}
    {outerExpansion :
      STExp H ι}
    (routing :
      BRRoutea
        H ι packet normalizer outerExpansion)
    (split : packet.PBSplit)
    (hlowerWeight :
      lowerWeight ≤ outerExpansion.word.weight HEAddres.weight)
    (houterTruncated :
      outerExpansion.word.weight HEAddres.weight < n)
    (outerRecursiveResults :
      ∀ child,
        SITerm.FrontierDefectMultiset
            n child [.frontier outerExpansion] →
          TTRecoll
            n lowerWeight H child)
    (innerRecursiveResults :
      ∀ child,
        SITerm.FrontierDefectMultiset
            n child [.frontier (outerExpansion.reword routing.innerWord)] →
          TTRecoll
            n lowerWeight H child) :
    TTRecoll
      n lowerWeight H [.frontier outerExpansion] := by
  by_cases hinner :
      routing.innerWord.weight HEAddres.weight < n
  · let temporaryPacketRecollection :
        TTRecoll
          n lowerWeight H
            (packet.innerClassifiedTerms
              normalizer outerExpansion routing.innerWord
                routing.rightWord) :=
      packet
        |>.recollect_frontier_recollections
          normalizer outerExpansion routing.innerWord routing.rightWord
            routing.word_eq hlowerWeight fun expansion hexpansion _ =>
              innerRecursiveResults [.frontier expansion] <|
                SITerm.defect_multiset_weight
                  expansion (outerExpansion.reword routing.innerWord)
                  (by simpa only [
                    STExp.word_reword]
                    using hinner)
                  (packet
                    |>.left_transient_classified
                      normalizer (outerExpansion.reword routing.innerWord)
                        routing.rightWord (.frontier expansion) hexpansion)
    exact
      ({ innerWord := routing.innerWord
         rightWord := routing.rightWord
         word_eq := routing.word_eq
         temporaryPacketRecollection := fun _ =>
           temporaryPacketRecollection } :
        PRRoute
          (lowerWeight := lowerWeight) H ι packet normalizer outerExpansion)
        |>.sourceRecollection split houterTruncated outerRecursiveResults
  · exact
      (PRRoute.inner_terminal_outer
        packet normalizer outerExpansion routing.innerWord routing.rightWord
          routing.word_eq hlowerWeight (by omega))
        |>.sourceRecollection split houterTruncated outerRecursiveResults

end
  BRRoutea

end TCTex
end Submission

-- Merged from PolynomialConcreteJacobiFrontierReductionCollection.lean

/-!
# Signed-polynomial collection reduced to the Jacobi frontier

Basic expanded Hall trees, expanded self-brackets, and reversed basic
brackets have automatic true residual recollections.  This file packages
those eliminations.  An arbitrary-cutoff collector now needs explicit
residual recollection only for nonbasic brackets with distinct children
whose reverse orientation is also nonbasic.

These are precisely the cases where the Hall reduction recursion proceeds
through a Jacobi rewrite.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
A cutoff Hall-Petresco packet and upward recollection of true residuals only
for expanded brackets on the Jacobi frontier.
-/
structure
    JFBuild
    {d n : ℕ}
    (hn : 2 ≤ n) where
  packet :
    PFSubsti.TAPkt.{u}
      d n
  jacobiFrontierResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor :
          SPFactor
            (concreteBasicCommutators.{u} d) ι),
          factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              ¬(CEWord.tree factor.word).IsBasic →
                ∀ left right : HallTree (FreeGenerator.{u} d),
                  CEWord.tree factor.word =
                      HallTree.commutator left right →
                    left ≠ right →
                      ¬(HallTree.commutator right left).IsBasic →
                        TRRecoll
                          (n := n) factor

namespace
  JFBuild

open
  TRRecoll

/--
Fill every terminal expanded-tree residual automa and leave only
Jacobi-frontier residuals to the caller.
-/
noncomputable def nonbasicReductionBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      JFBuild.{u}
        (d := d) (n := n) hn) :
    TNBuilda.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  nonbasicResidual lowerWeight hnonterminal factor hfactorWeight
      hfactorTruncated htreeNonbasic := by
    cases htree : CEWord.tree factor.word with
    | atom generator =>
        exfalso
        apply htreeNonbasic
        rw [htree]
        exact HallTree.isBasic_atom generator
    | commutator left right =>
        by_cases hsame : left = right
        · subst right
          exact tree_commutator_self factor left htree
        · by_cases hreverse : (HallTree.commutator right left).IsBasic
          · exact tree_swap_basic factor right left htree hreverse
          · exact
              builder.jacobiFrontierResidual lowerWeight hnonterminal factor
                hfactorWeight hfactorTruncated htreeNonbasic left right
                  htree hsame hreverse

end
  JFBuild

/--
For canonical Hall families, a cutoff packet and true residual recollections
on the Jacobi frontier construct product coordinate polynomials.
-/
theorem
    commutators_frontier_collect
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      JFBuild.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  nonbasic_collect_builder
    hn e builder.nonbasicReductionBuilder

/--
For canonical Hall families, a cutoff packet and true residual recollections
on the Jacobi frontier construct inverse coordinate polynomials.
-/
theorem
    commutators_reduction_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      JFBuild.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_nonbasic_builder
    hn e builder.nonbasicReductionBuilder

end TCTex
end Submission

-- Merged from PolynomialRankedStructuralRestartRecursiveRecollection.lean

/-!
# Recursive recollection through ranked structural restarts

A ranked structural restart separates one symbolic rewrite into two pieces:
strict Hall-ranked children and a normalized strictly higher quotient.  Once
the child source has itself been recollected recursively, appending the
quotient coordinates gives a recollection of the exact restart target.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace SPFactor
namespace RSRestar

/--
Compose a recursively recollected ranked child source with the normalized
restart quotient.
-/
def target_source_recollection
    {d n restartWeight targetWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    {targetSource : List (SPFactor H ι)}
    (restart :
      RSRestar
        (n := n) (lowerWeight := restartWeight)
          parent parentRankDefect targetSource)
    (sourceRecollection :
      SSRecol
        (n := n) (lowerWeight := targetWeight) H restart.source.factorSource)
    (htargetWeight : targetWeight ≤ restartWeight) :
    SSRecol
      (n := n) (lowerWeight := targetWeight) H targetSource where
  higherSource :=
    sourceRecollection.higherSource ++
      restart.normalization.coordinates.factors (n := n)
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact sourceRecollection.higher_source_truncated x hx
    · exact restart.normalization.factors_isTruncated x hx
  higher_weight_least := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact sourceRecollection.higher_weight_least x hx
    · exact htargetWeight.trans
        (restart.normalization.factors_weight_least x hx)
  list_higher_raw := by
    intro e
    rw [SPFactor.listEval_append,
      sourceRecollection.list_higher_raw]
    simpa only [rewriteSource,
      SPFactor.listEval_append] using
        restart.list_rewrite_target e

end RSRestar
end SPFactor

end TCTex
end Submission

-- Merged from PolynomialRankedChildSourceRecollection.lean

/-!
# Recollecting ranked signed-polynomial child sources

A ranked child source is consumed semantically after each of its finite tasks
has been recollected.  This file assembles those per-task recollections with
the source-level `flatMap` operation.

The singleton specialization is the direct interface for a scheduler whose
erased task list is itself the raw symbolic source.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace SPFactor
namespace RCSrc

/--
Assemble a recollection of an erased ranked source from recollections of
arbitrary finite pieces indexed by its ranked tasks.
-/
noncomputable def recollection_task_sources
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    (source : RCSrc (n := n) parent parentRankDefect)
    (rawSource :
      SPFactor H ι × ℕ →
        List (SPFactor H ι))
    (hfactorSource :
      source.factorSource = source.tasks.flatMap rawSource)
    (recollection :
      ∀ task ∈ source.tasks,
        SSRecol
          (n := n) (lowerWeight := lowerWeight) H (rawSource task)) :
    SSRecol
      (n := n) (lowerWeight := lowerWeight) H source.factorSource := by
  rw [hfactorSource]
  exact
    SSRecol.flatMap
      source.tasks rawSource recollection

/--
If each emitted factor recollects individually, their concatenation recollects
the complete erased ranked source.
-/
noncomputable def source_recollection_singletons
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {parent : SPFactor H ι}
    {parentRankDefect : ℕ}
    (source : RCSrc (n := n) parent parentRankDefect)
    (recollection :
      ∀ task ∈ source.tasks,
        SSRecol
          (n := n) (lowerWeight := lowerWeight) H [task.1]) :
    SSRecol
      (n := n) (lowerWeight := lowerWeight) H source.factorSource :=
  source.recollection_task_sources
    (fun task => [task.1])
    (by
      simp only [factorSource]
      induction source.tasks with
      | nil =>
          rfl
      | cons task tasks ih =>
          simp only [List.map_cons, List.flatMap_cons, List.singleton_append, ih])
    recollection

end RCSrc
end SPFactor
end TCTex
end Submission
