import Submission.Group.Zassenhaus.PolynomialConcrete
import Submission.Group.Zassenhaus.RankedStructuralRestarts
import Submission.Group.Zassenhaus.HallRankDescent

/-!
# Contextual collection for repeated-right polynomial frontiers

The repeated-right frontier `[[left, middle], middle]` cannot use the direct
ranked inner-reduction wrapper: that wrapper asks for the false comparison
`middle < middle`.

The underlying semantic reduction does not need that comparison.  Reducing
the immediate inner bracket while retaining the full parent factor emits a
finite packet `[basic_i, middle]`.  Each emitted child has its own canonical
two-basic-child rank and can be recollected by canonical routing.  This file
assembles those child recollections directly and reconstructs the parent
residual without assigning a parent-relative rank to the packet.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

namespace
  NWCase

/--
Collect any repeated-right frontier contextually.  The inner bracket may have
arbitrary Hall shape: preserving the full parent coefficient while reducing
that bracket emits children `[basic_i, middle]`, and `right = middle` makes
their retained right tree Hall-basic.
-/
noncomputable def repeatedResidualRecollect
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
    (hrightEqMiddle : frontier.right = frontier.middle)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRRecoll
      (n := n) factor := by
  let innerWord :=
    CWord.commutator frontier.decomposition.left
      frontier.decomposition.middle
  let rightWord := frontier.decomposition.right
  have hmiddleBasic : frontier.middle.IsBasic := by
    rw [← hrightEqMiddle]
    exact hrightBasic
  have hrightTree : tree rightWord = frontier.middle := by
    exact
      (trees_frontier factor frontier).2.2.trans
        hrightEqMiddle
  apply
    TRRecoll.inner_reduction_residuals
      hn
      (fun s hs hsn =>
        concrete_forms_associated d n s hs hsn)
      routing.normalizerFamily factor innerWord rightWord
        frontier.decomposition.word_eq hfactorTruncated
  intro child hchild
  let reachable :=
    PCReach.inner_reduction_outer
      factor innerWord rightWord frontier.decomposition.word_eq
        frontier.middle hrightTree hmiddleBasic hfactorTruncated hchild
  exact
    routing.residualRecollection hn
      (fun s hs hsn =>
        concrete_forms_associated d n s hs hsn)
      child reachable.1 ⟨reachable.2⟩

end
  NWCase

namespace
  TNCase

/--
The contextual recollection step for the genuinely recursive repeated-right
case.  The full parent coefficient is preserved while each emitted
`[basic_i, middle]` child is scheduled at its own canonical rank.
-/
noncomputable def residualRecollection
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
    (nested :
      TNCase
        factor frontier)
    (hrightEqMiddle : frontier.right = frontier.middle)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TRRecoll
      (n := n) factor := by
  let innerWord :=
    CWord.commutator frontier.decomposition.left
      frontier.decomposition.middle
  let rightWord := frontier.decomposition.right
  have hrightTree : tree rightWord = frontier.middle := by
    exact
      (trees_frontier factor frontier).2.2.trans
        hrightEqMiddle
  apply
    TRRecoll.inner_reduction_residuals
      hn
      (fun s hs hsn =>
        concrete_forms_associated d n s hs hsn)
      routing.normalizerFamily factor innerWord rightWord
        frontier.decomposition.word_eq hfactorTruncated
  intro child hchild
  let reachable :=
    PCReach.inner_reduction_outer
      factor innerWord rightWord frontier.decomposition.word_eq
        frontier.middle hrightTree nested.middle_isBasic hfactorTruncated
          hchild
  exact
    routing.residualRecollection hn
      (fun s hs hsn =>
        concrete_forms_associated d n s hs hsn)
      child reachable.1 ⟨reachable.2⟩

end
  TNCase

/--
Reachable ranked routing and the recursive boundaries left after contextual
collection automa discharges repeated-right nested-left frontiers.
-/
structure
    CJBuilda
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
  CJBuilda

/-- Compile automatic contextual repeated-right collection into the previous builder. -/
noncomputable def repeatedCasesBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      CJBuilda.{u}
        (d := d) (n := n) hn) :
    TCBuild.{u}
      (d := d) (n := n) hn where
  packet := builder.packet
  routing := builder.routing
  rootSwapResidual := builder.rootSwapResidual
  retainedDescendantResidual := builder.retainedDescendantResidual
  repeatedNonbasicResidual :=
    builder.repeatedNonbasicResidual
  repeatedFailedInner :=
    builder.repeatedFailedInner
  repeatedRightNested := by
    intro ι lowerWeight hnonterminal factor hfactorWeight hfactorTruncated
      frontier hrightBasic hrightEqMiddle nested
    exact
      TNCase.residualRecollection
        hn (builder.routing ι) factor frontier nested hrightEqMiddle
          hfactorTruncated
  leftNonbasicResidual := builder.leftNonbasicResidual
  middleNonbasicResidual := builder.middleNonbasicResidual
  failedInnerChildren := builder.failedInnerChildren

end
  CJBuilda

/--
Contextual repeated-right collection with explicit remaining recursive
boundaries constructs product coordinate polynomials.
-/
theorem
    contextual_collect_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      CJBuilda.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  cases_jacobi_builder
    hn e builder.repeatedCasesBuilder

/--
Contextual repeated-right collection with explicit remaining recursive
boundaries constructs inverse coordinate polynomials.
-/
theorem
    contextual_frontier_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      CJBuilda.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_cases_builder
    hn e builder.repeatedCasesBuilder

/--
Reachable ranked routing and the recursive boundaries left after all
repeated-right frontiers are collected contextually.
-/
structure
    TABuilda
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
  TABuilda

/-- Compile automatic repeated-right collection into the retained-right layer. -/
noncomputable def descendantsJacobiBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    (builder :
      TABuilda.{u}
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
    exact
      NWCase.repeatedResidualRecollect
        hn (builder.routing ι) factor frontier hrightBasic hrightEqMiddle
          hfactorTruncated
  leftNonbasicResidual := builder.leftNonbasicResidual
  middleNonbasicResidual := builder.middleNonbasicResidual
  failedInnerChildren := builder.failedInnerChildren

end
  TABuilda

/--
Automatic repeated-right collection with explicit remaining recursive
boundaries constructs product coordinate polynomials.
-/
theorem
    automatic_jacobi_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      List
        (HEFam
          (concreteCommutatorsWeight.{u} d)))
    (builder :
      TABuilda.{u}
        (d := d) (n := n) hn) :
    CollectedCoordinateData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  descendants_jacobi_builder
    hn e builder.descendantsJacobiBuilder

/--
Automatic repeated-right collection with explicit remaining recursive
boundaries constructs inverse coordinate polynomials.
-/
theorem
    commutators_automatic_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (e :
      HEFam
        (concreteCommutatorsWeight.{u} d))
    (builder :
      TABuilda.{u}
        (d := d) (n := n) hn) :
    CollectedInverseData
      (n := n) (concreteCommutatorsWeight.{u} d) e :=
  commutators_descendants_builder
    hn e builder.descendantsJacobiBuilder

end TCTex
end Submission
