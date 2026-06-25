import Submission.Group.Zassenhaus.PermutedPacketWorklist
import Submission.Group.Zassenhaus.LabelledWordMovements
import Submission.Group.Zassenhaus.PositiveDegreeRecipes


/-!
# Candidate closed packet schedules for recursive Hall-Petresco swaps

The direct recursive obstruction tree proposes one endpoint family list.  A
concrete operational proof would still have to exhibit a finite word-rewrite
run whose emitted correction slots close into exactly those packets.  This
file states that strong diagnostic contract and proves the semantic adapter.

No semantic identity is assumed by the contract: it follows from concrete
adjacent-word rewrites and closed packet compression.  The actual Hall trace
also uses inverse-oriented conjugation histories, so inhabiting this direct
tree contract is not asserted here.  This file is intentionally not imported
by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace BRSched

universe u

open HACoeff
open FRObstr
open RSInterf
open RSResolu
open BFTrunc
open HPWork

/--
A closed operational run for one recursive obstruction.  Its concrete swaps
start with the two parent packets and end with emitted words packeted by the
recursive endpoint family list, followed by the transposed parents.
-/
structure CPSched
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) where
  worklist :
    PWork M N
  correctionFamilies_eq :
    (worklist.map fun item =>
      item.leftFamily.correction item.rightFamily) =
        O.retainedCorrectionFamilies (n := n) hleftWeight hrightWeight
  closed :
    worklist.Closed
  rewrites :
    BBSched.LWRw
      (O.left.realizations ++ O.right.realizations)
      ((worklist.flatMap fun item => item.ledger.emitted) ++
        O.right.realizations ++ O.left.realizations)

namespace CPSched

/-- The emitted word prefix of a closed run compresses to its endpoint families. -/
lemma packetedBy
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    (schedule :
      CPSched n leftWeight rightWeight
        hleftWeight hrightWeight O) :
    PCCounti.CPBy
      (schedule.worklist.map fun item =>
        item.leftFamily.correction item.rightFamily)
      (schedule.worklist.flatMap fun item => item.ledger.emitted) :=
  PWork.packeted_closed schedule.worklist schedule.closed

/--
A closed operational packet schedule supplies the semantic certificate needed
by the recursive family consumer.
-/
def recursiveSemanticCertificate
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    (schedule :
      CPSched n leftWeight rightWeight
        hleftWeight hrightWeight O)
    (hroot : O.weight leftWeight rightWeight < n) :
    RSCert.{u}
      n leftWeight rightWeight hleftWeight hrightWeight O hroot where
  collapsed_list_eval := by
    intro G _ x y _hx _hy _hbot
    have hcompression :=
      schedule.packetedBy.collapsed_list_realization x y
    have hrewrites :=
      BFTrunc.collapsed_labelled_rewrites
        x y schedule.rewrites
    rw [← schedule.correctionFamilies_eq]
    calc
      collapsedList x y
          (BFam.realizationList
              (schedule.worklist.map fun item =>
                item.leftFamily.correction item.rightFamily) ++
            O.right.realizations ++ O.left.realizations) =
        collapsedList x y
          ((schedule.worklist.flatMap fun item => item.ledger.emitted) ++
            O.right.realizations ++ O.left.realizations) := by
              simp only [collapsed_list_append]
              rw [hcompression]
      _ = collapsedList x y
          (O.left.realizations ++ O.right.realizations) :=
        hrewrites

end CPSched

/--
Strong direct-tree scheduler conjecture.  Every inhabitant is sound, but the
actual Hall trace must first be packetized with inverse-oriented conjugation
histories before one can decide whether this endpoint list is sufficient.
-/
structure CSKern
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    Prop where
  schedule_nonterminal :
    ∀ (O : FObstru M N)
      (_hroot : O.weight leftWeight rightWeight < n),
      ¬ O.Terminal n leftWeight rightWeight →
        Nonempty
          (CPSched n leftWeight rightWeight
            hleftWeight hrightWeight O)

namespace CSKern

/--
Any operational kernel discharges the semantic kernel by closed-packet
compression.  Recursive branch certificates are not needed after the concrete
run has already reached the complete recursive endpoint list.
-/
noncomputable def recursiveSemanticKernel
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      CSKern (M := M) (N := N)
        n leftWeight rightWeight hleftWeight hrightWeight) :
    RSKern.{u} (M := M) (N := N) n leftWeight rightWeight
      hleftWeight hrightWeight where
  resolve_nonterminal := by
    intro O hroot hnonterminal _leftCertificate _rightCertificate
    exact
      (Classical.choice
        (kernel.schedule_nonterminal O hroot hnonterminal)).recursiveSemanticCertificate
          hroot

/-- Resolve every below-cutoff obstruction from one operational scheduler kernel. -/
noncomputable def resolve
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      CSKern (M := M) (N := N)
        n leftWeight rightWeight hleftWeight hrightWeight)
    (O : FObstru M N)
    (hroot : O.weight leftWeight rightWeight < n) :
    RSCert.{u}
      n leftWeight rightWeight hleftWeight hrightWeight O hroot :=
  kernel.recursiveSemanticKernel.resolve O hroot

end CSKern

end BRSched
end TCTex
end Submission

/-!
# Operational orientation of nested Hall-Petresco corrections

Weight arithmetic does not remember commutator orientation.  Concrete adjacent
rewrites do.  When an original parent word crosses a freshly emitted correction,
the new correction has the parent on the left and the earlier correction on the
right.  This file records the first exact traces and packages the corresponding
operational child obstructions.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace BFOrient

open HACoeff
open BRSpec
open BBSched
open FRObstr
open FRObstr.FObstru
open PLMoveme

/--
With two left words and one right word, the earlier left word crosses the first
correction on its left.  The nested correction is therefore `[B₀, [B₁, A]]`.
-/
lemma rewrites_left_right
    {M N : ℕ}
    (B₀ B₁ A : BatchLabelledWord M N) :
    BBSched.LWRw
      [B₀, B₁, A]
      [batchCorrection B₀ (batchCorrection B₁ A),
        batchCorrection B₁ A, B₀, A, B₁] := by
  have hfirst :
      BBSched.LWRw
        [B₀, B₁, A]
        [B₀, batchCorrection B₁ A, A, B₁] := by
    simpa using rewrites_single_step [B₀] [] B₁ A
  have hsecond :
      BBSched.LWRw
        [B₀, batchCorrection B₁ A, A, B₁]
        [batchCorrection B₀ (batchCorrection B₁ A),
          batchCorrection B₁ A, B₀, A, B₁] := by
    simpa using rewrites_single_step [] [A, B₁] B₀ (batchCorrection B₁ A)
  exact hfirst.trans hsecond

/--
With one left word and two right words, the earlier right word crosses the
second root correction on its left.  The nested correction is
`[A₀, [B, A₁]]`.
-/
lemma rewrites_two_right
    {M N : ℕ}
    (B A₀ A₁ : BatchLabelledWord M N) :
    BBSched.LWRw
      [B, A₀, A₁]
      [batchCorrection B A₀,
        batchCorrection A₀ (batchCorrection B A₁),
        batchCorrection B A₁, A₀, A₁, B] := by
  have hrow :
      BBSched.LWRw
        [B, A₀, A₁]
        [batchCorrection B A₀, A₀, batchCorrection B A₁, A₁, B] := by
    simpa using rewrites_moved_right B [A₀, A₁]
  have hnested :
      BBSched.LWRw
        [batchCorrection B A₀, A₀, batchCorrection B A₁, A₁, B]
        [batchCorrection B A₀,
          batchCorrection A₀ (batchCorrection B A₁),
          batchCorrection B A₁, A₀, A₁, B] := by
    simpa using rewrites_single_step
      [batchCorrection B A₀] [A₁, B] A₀ (batchCorrection B A₁)
  exact hrow.trans hnested

namespace FObstru

/--
Operational child created when an original left-parent word crosses a freshly
emitted correction word.
-/
def operationalNestedLeft
    {M N : ℕ}
    (O : FObstru M N) :
    FObstru M N where
  left := O.left
  right := O.correction

/--
Operational child created when an original right-parent word crosses a freshly
emitted correction word.
-/
def operationalNestedRight
    {M N : ℕ}
    (O : FObstru M N) :
    FObstru M N where
  left := O.right
  right := O.correction

@[simp]
lemma correction_operational_left
    {M N : ℕ}
    (O : FObstru M N) :
    (operationalNestedLeft O).correction =
      O.left.correction O.correction :=
  rfl

@[simp]
lemma correction_operational_nested
    {M N : ℕ}
    (O : FObstru M N) :
    (operationalNestedRight O).correction =
      O.right.correction O.correction :=
  rfl

@[simp]
lemma weight_nested_left
    {M N leftWeight rightWeight : ℕ}
    (O : FObstru M N) :
    (operationalNestedLeft O).weight leftWeight rightWeight =
      2 * weightedWordWeight leftWeight rightWeight O.left.recipe +
        weightedWordWeight leftWeight rightWeight O.right.recipe := by
  change
    weightedWordWeight leftWeight rightWeight O.left.recipe +
          weightedWordWeight leftWeight rightWeight
            (O.left.correction O.right).recipe =
      2 * weightedWordWeight leftWeight rightWeight O.left.recipe +
        weightedWordWeight leftWeight rightWeight O.right.recipe
  rw [BFam.recipe_correction, weighted_weight_correction]
  omega

@[simp]
lemma weight_operational_right
    {M N leftWeight rightWeight : ℕ}
    (O : FObstru M N) :
    (operationalNestedRight O).weight leftWeight rightWeight =
      weightedWordWeight leftWeight rightWeight O.left.recipe +
        2 * weightedWordWeight leftWeight rightWeight O.right.recipe := by
  change
    weightedWordWeight leftWeight rightWeight O.right.recipe +
          weightedWordWeight leftWeight rightWeight
            (O.left.correction O.right).recipe =
      weightedWordWeight leftWeight rightWeight O.left.recipe +
        2 * weightedWordWeight leftWeight rightWeight O.right.recipe
  rw [BFam.recipe_correction, weighted_weight_correction]
  omega

/-- Operational left children have the same weight as the unoriented draft children. -/
lemma operational_nested_left
    {M N leftWeight rightWeight : ℕ}
    (O : FObstru M N) :
    (operationalNestedLeft O).weight leftWeight rightWeight =
      O.nestedLeft.weight leftWeight rightWeight := by
  rw [weight_nested_left, weight_nestedLeft]

/-- Operational right children have the same weight as the unoriented draft children. -/
lemma operational_nested_right
    {M N leftWeight rightWeight : ℕ}
    (O : FObstru M N) :
    (operationalNestedRight O).weight leftWeight rightWeight =
      O.nestedRight.weight leftWeight rightWeight := by
  rw [weight_operational_right, weight_nestedRight]

/-- An operational left child strictly increases total Hall weight. -/
lemma weight_operational_left
    {M N leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) :
    O.weight leftWeight rightWeight <
      (operationalNestedLeft O).weight leftWeight rightWeight := by
  rw [operational_nested_left]
  exact O.nested_left hleftWeight hrightWeight

/-- An operational right child strictly increases total Hall weight. -/
lemma weight_operational_nested
    {M N leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) :
    O.weight leftWeight rightWeight <
      (operationalNestedRight O).weight leftWeight rightWeight := by
  rw [operational_nested_right]
  exact O.weight_nested_right hleftWeight hrightWeight

/-- Every surviving operational left child strictly descends in cutoff defect. -/
lemma nestedLeftDescends
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N)
    (hcutoff : (operationalNestedLeft O).weight leftWeight rightWeight < n) :
    Descends n leftWeight rightWeight (operationalNestedLeft O) O := by
  unfold Descends defect
  have hweight := weight_operational_left hleftWeight hrightWeight O
  omega

/-- Every surviving operational right child strictly descends in cutoff defect. -/
lemma nestedRightDescends
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N)
    (hcutoff : (operationalNestedRight O).weight leftWeight rightWeight < n) :
    Descends n leftWeight rightWeight (operationalNestedRight O) O := by
  unfold Descends defect
  have hweight := weight_operational_nested hleftWeight hrightWeight O
  omega

end FObstru

end BFOrient
end TCTex
end Submission

/-!
# Residual-aware closed packet schedules

A concrete cutoff-aware collector closes every retained correction packet but
may still leave explicit above-cutoff words in its exact free-group endpoint.
Those words cannot be erased by exact rewriting.  They disappear only after
collapsed evaluation in a matching nilpotent quotient.

This file combines the permutation-aware packet worklist with the residual-word
interface and proves the semantic adapter required by the recursive family
collector.  It is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace RRScheda

universe u

open HACoeff
open BBSched
open BFTrunc
open FRObstr
open RSInterf
open RSResolu
open BRScheda
open HPWork

/--
Closed retained packets plus an explicit high-weight residual word list for one
recursive obstruction.
-/
structure RCPkt
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) where
  worklist :
    PWork M N
  correctionFamilies_eq :
    (worklist.map fun item =>
      item.leftFamily.correction item.rightFamily) =
        O.retainedCorrectionFamilies (n := n) hleftWeight hrightWeight
  closed :
    worklist.Closed
  residualWords :
    List (BBSched.LabelledWord M N)
  wordsAboveCutoff :
    WordsAboveCutoff n leftWeight rightWeight residualWords
  rewrites :
    BBSched.LWRw
      (O.left.realizations ++ O.right.realizations)
      ((worklist.flatMap fun item => item.ledger.emitted) ++
        residualWords ++ O.right.realizations ++ O.left.realizations)

namespace RCPkt

/-- The emitted retained prefix compresses to the schedule's canonical families. -/
lemma packetedBy
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    (schedule :
      RCPkt n leftWeight rightWeight
        hleftWeight hrightWeight O) :
    PCCounti.CPBy
      (schedule.worklist.map fun item =>
        item.leftFamily.correction item.rightFamily)
      (schedule.worklist.flatMap fun item => item.ledger.emitted) :=
  PWork.packeted_closed schedule.worklist schedule.closed

/-- A residual-aware closed packet schedule supplies the recursive semantic endpoint. -/
def recursiveSemanticCertificate
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    (schedule :
      RCPkt n leftWeight rightWeight
        hleftWeight hrightWeight O)
    (hroot : O.weight leftWeight rightWeight < n) :
    RSCert.{u}
      n leftWeight rightWeight hleftWeight hrightWeight O hroot where
  collapsed_list_eval := by
    intro G _ x y hx hy hbot
    have hcompression :=
      schedule.packetedBy.collapsed_list_realization x y
    have hresidual :
        collapsedList x y schedule.residualWords = 1 :=
      collapsed_words_above
        hleftWeight hrightWeight hx hy hbot
          schedule.residualWords schedule.wordsAboveCutoff
    have hrewrites :=
      collapsed_labelled_rewrites x y schedule.rewrites
    rw [← schedule.correctionFamilies_eq]
    simp only [collapsed_list_append] at hcompression hrewrites ⊢
    rw [← hcompression]
    simpa [hresidual] using hrewrites

/-- The residual-free closed packet contract is a special case. -/
def closedPacketSchedule
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    (schedule :
      BRSched.CPSched
        n leftWeight rightWeight hleftWeight hrightWeight O) :
    RCPkt n leftWeight rightWeight
      hleftWeight hrightWeight O where
  worklist := schedule.worklist
  correctionFamilies_eq := schedule.correctionFamilies_eq
  closed := schedule.closed
  residualWords := []
  wordsAboveCutoff := by
    intro w hw
    simp at hw
  rewrites := by
    simpa [List.append_assoc] using schedule.rewrites

end RCPkt

/--
Operational recursive kernel with closed retained packets and explicit
above-cutoff residual words.
-/
structure RCSched
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    Prop where
  schedule_nonterminal :
    ∀ (O : FObstru M N)
      (_hroot : O.weight leftWeight rightWeight < n),
      ¬ O.Terminal n leftWeight rightWeight →
        Nonempty
          (RCPkt n leftWeight rightWeight
            hleftWeight hrightWeight O)

namespace RCSched

/-- Every residual-aware closed-packet kernel supplies the semantic recursion kernel. -/
noncomputable def recursiveSemanticKernel
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      RCSched (M := M) (N := N)
        n leftWeight rightWeight hleftWeight hrightWeight) :
    RSKern.{u} (M := M) (N := N)
      n leftWeight rightWeight hleftWeight hrightWeight where
  resolve_nonterminal := by
    intro O hroot hterminal _hleft _hright
    exact
      (Classical.choice
        (kernel.schedule_nonterminal O hroot hterminal)).recursiveSemanticCertificate
          hroot

/-- Resolve every below-cutoff obstruction from one residual closed-packet kernel. -/
noncomputable def resolve
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      RCSched (M := M) (N := N)
        n leftWeight rightWeight hleftWeight hrightWeight)
    (O : FObstru M N)
    (hroot : O.weight leftWeight rightWeight < n) :
    RSCert.{u}
      n leftWeight rightWeight hleftWeight hrightWeight O hroot :=
  kernel.recursiveSemanticKernel.resolve O hroot

end RCSched

end RRScheda
end TCTex
end Submission

/-!
# Operationally oriented recursive Hall-Petresco obstructions

Concrete More3 rewrites remember commutator orientation.  When an original
parent packet crosses a freshly emitted correction packet, the operational
children are `left ▷ correction` and `right ▷ correction`.  They have the same
weight arithmetic as the earlier unoriented diagnostic tree, but generally
different recipes.

This file constructs the finite oriented obstruction tree by cutoff-defect
recursion and proves the packet bounds needed by polynomial specialization.
The exact labelled-word scheduler for this oriented packet is built in a
subsequent standalone layer.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace BRObstr

open HACoeff
open BRSpec
open BFOrient
open FRObstr
open BFOrient.FObstru
open FRObstr.FObstru

namespace FObstru

mutual

  /-- Finite operational recursion tree rooted at one retained obstruction. -/
  inductive ORTree
      {M N : ℕ}
      (n leftWeight rightWeight : ℕ) :
      FObstru M N → Type
    | node
        (O : FObstru M N)
        (left :
          OOTree n leftWeight rightWeight
            (operationalNestedLeft O))
        (right :
          OOTree n leftWeight rightWeight
            (operationalNestedRight O)) :
        ORTree n leftWeight rightWeight O

  /-- A nested operational branch is either discarded or recursively retained. -/
  inductive OOTree
      {M N : ℕ}
      (n leftWeight rightWeight : ℕ) :
      FObstru M N → Type
    | cutoff
        (O : FObstru M N)
        (hcutoff : n ≤ O.weight leftWeight rightWeight) :
        OOTree n leftWeight rightWeight O
    | retained
        (O : FObstru M N)
        (hcutoff : O.weight leftWeight rightWeight < n)
        (tree :
          ORTree n leftWeight rightWeight O) :
        OOTree n leftWeight rightWeight O

end

/-- Build the finite operational tree by well-founded cutoff-defect recursion. -/
noncomputable def operationalRecursiveTree
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) :
    ORTree n leftWeight rightWeight O :=
  (descends_wellFounded M N n leftWeight rightWeight).fix
    (fun parent recurse =>
      ORTree.node parent
        (if hleft :
            (operationalNestedLeft parent).weight
              leftWeight rightWeight < n then
          OOTree.retained
            (operationalNestedLeft parent) hleft
              (recurse (operationalNestedLeft parent)
                (nestedLeftDescends
                  hleftWeight hrightWeight parent hleft))
        else
          OOTree.cutoff
            (operationalNestedLeft parent) (Nat.le_of_not_gt hleft))
        (if hright :
            (operationalNestedRight parent).weight
              leftWeight rightWeight < n then
          OOTree.retained
            (operationalNestedRight parent) hright
              (recurse (operationalNestedRight parent)
                (nestedRightDescends
                  hleftWeight hrightWeight parent hright))
        else
          OOTree.cutoff
            (operationalNestedRight parent) (Nat.le_of_not_gt hright)))
    O

mutual

  /-- Flatten the leading correction family at each operational tree node. -/
  def ORTree.correctionFamilies
      {M N n leftWeight rightWeight : ℕ}
      {O : FObstru M N} :
      ORTree n leftWeight rightWeight O →
        List (BFam M N)
    | .node O left right =>
        O.correction :: left.correctionFamilies ++ right.correctionFamilies

  /-- Cutoff branches emit nothing; retained branches emit their finite packet. -/
  def OOTree.correctionFamilies
      {M N n leftWeight rightWeight : ℕ}
      {O : FObstru M N} :
      OOTree n leftWeight rightWeight O →
        List (BFam M N)
    | .cutoff _ _ =>
        []
    | .retained _ _ tree =>
        tree.correctionFamilies

end

/-- Every flattened operational correction family remains below the cutoff. -/
lemma ORTree.corr_famsweight_ltcutoff
    {M N n leftWeight rightWeight : ℕ}
    {O : FObstru M N}
    (tree :
      ORTree n leftWeight rightWeight O)
    (hcutoff : O.weight leftWeight rightWeight < n) :
    ∀ C ∈ tree.correctionFamilies,
      weightedWordWeight leftWeight rightWeight C.recipe < n := by
  refine ORTree.recOn
    (motive_1 := fun O tree =>
      O.weight leftWeight rightWeight < n →
        ∀ C ∈ tree.correctionFamilies,
          weightedWordWeight leftWeight rightWeight C.recipe < n)
    (motive_2 := fun _ tree =>
      ∀ C ∈ tree.correctionFamilies,
        weightedWordWeight leftWeight rightWeight C.recipe < n)
    tree ?_ ?_ ?_ hcutoff
  · intro O left right hleft hright hcutoff C hC
    simp only [ORTree.correctionFamilies,
      List.mem_cons, List.mem_append] at hC
    rcases hC with (rfl | hC) | hC
    · rw [FObstru.weight_correction]
      exact hcutoff
    · exact hleft C hC
    · exact hright C hC
  · intro O hcutoff
    simp [OOTree.correctionFamilies]
  · intro O hcutoff tree htree
    exact htree hcutoff

/-- Every nested operational packet remains below the cutoff. -/
lemma OOTree.corr_famsweight_ltcutoff
    {M N n leftWeight rightWeight : ℕ}
    {O : FObstru M N}
    (tree :
      OOTree n leftWeight rightWeight O) :
    ∀ C ∈ tree.correctionFamilies,
      weightedWordWeight leftWeight rightWeight C.recipe < n := by
  refine OOTree.recOn
    (motive_1 := fun O tree =>
      O.weight leftWeight rightWeight < n →
        ∀ C ∈ tree.correctionFamilies,
          weightedWordWeight leftWeight rightWeight C.recipe < n)
    (motive_2 := fun _ tree =>
      ∀ C ∈ tree.correctionFamilies,
        weightedWordWeight leftWeight rightWeight C.recipe < n)
    tree ?_ ?_ ?_
  · intro O left right hleft hright hcutoff C hC
    simp only [ORTree.correctionFamilies,
      List.mem_cons, List.mem_append] at hC
    rcases hC with (rfl | hC) | hC
    · rw [FObstru.weight_correction]
      exact hcutoff
    · exact hleft C hC
    · exact hright C hC
  · intro O hcutoff
    simp [OOTree.correctionFamilies]
  · intro O hcutoff tree htree
    exact htree hcutoff

/-- Flattened operational families lie at or above the root obstruction weight. -/
lemma ORTree.weight_lecorr_fammem
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {O : FObstru M N}
    (tree :
      ORTree n leftWeight rightWeight O) :
    ∀ C ∈ tree.correctionFamilies,
      O.weight leftWeight rightWeight ≤
        weightedWordWeight leftWeight rightWeight C.recipe := by
  refine ORTree.recOn
    (motive_1 := fun O tree =>
      ∀ C ∈ tree.correctionFamilies,
        O.weight leftWeight rightWeight ≤
          weightedWordWeight leftWeight rightWeight C.recipe)
    (motive_2 := fun O tree =>
      ∀ C ∈ tree.correctionFamilies,
        O.weight leftWeight rightWeight ≤
          weightedWordWeight leftWeight rightWeight C.recipe)
    tree ?_ ?_ ?_
  · intro O left right hleft hright C hC
    simp only [ORTree.correctionFamilies,
      List.mem_cons, List.mem_append] at hC
    rcases hC with (rfl | hC) | hC
    · rw [FObstru.weight_correction]
    · exact le_trans
        (weight_operational_left hleftWeight hrightWeight O).le
        (hleft C hC)
    · exact le_trans
        (weight_operational_nested hleftWeight hrightWeight O).le
        (hright C hC)
  · intro O hcutoff
    simp [OOTree.correctionFamilies]
  · intro O hcutoff tree htree
    exact htree

/-- Nested operational packets lie at or above their branch obstruction weight. -/
lemma OOTree.weight_lecorr_fammem
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {O : FObstru M N}
    (tree :
      OOTree n leftWeight rightWeight O) :
    ∀ C ∈ tree.correctionFamilies,
      O.weight leftWeight rightWeight ≤
        weightedWordWeight leftWeight rightWeight C.recipe := by
  refine OOTree.recOn
    (motive_1 := fun O tree =>
      ∀ C ∈ tree.correctionFamilies,
        O.weight leftWeight rightWeight ≤
          weightedWordWeight leftWeight rightWeight C.recipe)
    (motive_2 := fun O tree =>
      ∀ C ∈ tree.correctionFamilies,
        O.weight leftWeight rightWeight ≤
          weightedWordWeight leftWeight rightWeight C.recipe)
    tree ?_ ?_ ?_
  · intro O left right hleft hright C hC
    simp only [ORTree.correctionFamilies,
      List.mem_cons, List.mem_append] at hC
    rcases hC with (rfl | hC) | hC
    · rw [FObstru.weight_correction]
    · exact le_trans
        (weight_operational_left hleftWeight hrightWeight O).le
        (hleft C hC)
    · exact le_trans
        (weight_operational_nested hleftWeight hrightWeight O).le
        (hright C hC)
  · intro O hcutoff
    simp [OOTree.correctionFamilies]
  · intro O hcutoff tree htree
    exact htree

/-- Every flattened operational family lies strictly above the root left parent. -/
lemma ORTree.leftweight_ltcorr_fammem
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {O : FObstru M N}
    (tree :
      ORTree n leftWeight rightWeight O)
    {C : BFam M N}
    (hC : C ∈ tree.correctionFamilies) :
    weightedWordWeight leftWeight rightWeight O.left.recipe <
      weightedWordWeight leftWeight rightWeight C.recipe :=
  lt_of_lt_of_le
    (O.left_weight hleftWeight hrightWeight)
    (tree.weight_lecorr_fammem hleftWeight hrightWeight C hC)

/-- Every flattened operational family lies strictly above the root right parent. -/
lemma ORTree.rightweight_ltcorr_fammem
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {O : FObstru M N}
    (tree :
      ORTree n leftWeight rightWeight O)
    {C : BFam M N}
    (hC : C ∈ tree.correctionFamilies) :
    weightedWordWeight leftWeight rightWeight O.right.recipe <
      weightedWordWeight leftWeight rightWeight C.recipe :=
  lt_of_lt_of_le
    (O.right_weight hleftWeight hrightWeight)
    (tree.weight_lecorr_fammem hleftWeight hrightWeight C hC)

/-- Concrete finite packet retained by the oriented obstruction tree. -/
noncomputable def operationalCorrectionFamilies
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) :
    List (BFam M N) :=
  (operationalRecursiveTree
    (n := n) hleftWeight hrightWeight O).correctionFamilies

end FObstru

end BRObstr
end TCTex
end Submission

/-!
# Polynomial endpoint for operationally oriented recursive packets

The oriented obstruction tree retains a finite list of higher-weight complete
block families.  This file forgets concrete realization slots only at the
endpoint, attaches the retained `BRecipe`s to Claim 8 symbolic polynomial
factors, and exposes the root-plus-operational-branches recurrence.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace ORPkt

universe u

open HACoeff
open BRSpec
open BFOrient.FObstru
open BRObstr
open BRObstr.FObstru
open FRObstr

/-- Operational raw-history recipes retained by one finite oriented tree. -/
noncomputable def retainedRecipes
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) :
    List BRecipe :=
  (operationalCorrectionFamilies
    (n := n) hleftWeight hrightWeight O).map BFam.recipe

/-- Every retained operational recipe comes from a concrete family packet. -/
lemma family_retained_recipes
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    {R : BRecipe}
    (hR : R ∈ retainedRecipes (n := n) hleftWeight hrightWeight O) :
    ∃ C ∈ operationalCorrectionFamilies
        (n := n) hleftWeight hrightWeight O,
      C.recipe = R := by
  rcases List.mem_map.mp hR with ⟨C, hC, rfl⟩
  exact ⟨C, hC, rfl⟩

/-- Every retained operational recipe remains below the quotient cutoff. -/
lemma retained_recipe_cutoff
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    (hroot : O.weight leftWeight rightWeight < n)
    {R : BRecipe}
    (hR : R ∈ retainedRecipes (n := n) hleftWeight hrightWeight O) :
    weightedWordWeight leftWeight rightWeight R < n := by
  rcases family_retained_recipes hR with ⟨C, hC, rfl⟩
  exact
    (operationalRecursiveTree
      (n := n) hleftWeight hrightWeight O).corr_famsweight_ltcutoff
        hroot C hC

/-- Every retained operational recipe lies strictly above the root left parent. -/
lemma left_retained_recipes
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    {R : BRecipe}
    (hR : R ∈ retainedRecipes (n := n) hleftWeight hrightWeight O) :
    weightedWordWeight leftWeight rightWeight O.left.recipe <
      weightedWordWeight leftWeight rightWeight R := by
  rcases family_retained_recipes hR with ⟨C, hC, rfl⟩
  exact
    (operationalRecursiveTree
      (n := n) hleftWeight hrightWeight O).leftweight_ltcorr_fammem
        hleftWeight hrightWeight hC

/-- Every retained operational recipe lies strictly above the root right parent. -/
lemma right_retained_recipes
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    {R : BRecipe}
    (hR : R ∈ retainedRecipes (n := n) hleftWeight hrightWeight O) :
    weightedWordWeight leftWeight rightWeight O.right.recipe <
      weightedWordWeight leftWeight rightWeight R := by
  rcases family_retained_recipes hR with ⟨C, hC, rfl⟩
  exact
    (operationalRecursiveTree
      (n := n) hleftWeight hrightWeight O).rightweight_ltcorr_fammem
        hleftWeight hrightWeight hC

/-- Attach operationally retained recipes to Claim 8 symbolic factors. -/
noncomputable def symbolicFactors
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (O : FObstru M N)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    List (SPFactor H ι) :=
  BRSpec.symbolicFactors
    (retainedRecipes (n := n)
      (HEAddres.weight_pos leftAddress)
      (HEAddres.weight_pos rightAddress) O)
    leftInput rightInput leftAddress rightAddress

/-- Every operational symbolic factor remembers one retained raw recipe. -/
lemma recipe_factors
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {O : FObstru M N}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈ symbolicFactors (n := n) O leftInput rightInput
        leftAddress rightAddress) :
    ∃ R ∈ retainedRecipes (n := n)
        (HEAddres.weight_pos leftAddress)
        (HEAddres.weight_pos rightAddress) O,
      factor =
        BRSpec.symbolicFactor
          R leftInput rightInput leftAddress rightAddress := by
  exact BRSpec.recipe_factors
    hfactor

/-- Every operational symbolic factor remains below the quotient cutoff. -/
lemma weight_symbolic_factors
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {O : FObstru M N}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    (hroot : O.weight leftAddress.weight rightAddress.weight < n)
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈ symbolicFactors (n := n) O leftInput rightInput
        leftAddress rightAddress) :
    factor.word.weight HEAddres.weight < n := by
  rcases recipe_factors hfactor with ⟨R, hR, rfl⟩
  rw [word_symbolic_factor, ← weighted_word_weight]
  exact retained_recipe_cutoff hroot hR

/-- Every operational symbolic factor lies above the original left parent. -/
lemma left_parent_factors
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {O : FObstru M N}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈ symbolicFactors (n := n) O leftInput rightInput
        leftAddress rightAddress) :
    weightedWordWeight leftAddress.weight rightAddress.weight O.left.recipe <
      factor.word.weight HEAddres.weight := by
  rcases recipe_factors hfactor with ⟨R, hR, rfl⟩
  rw [word_symbolic_factor, ← weighted_word_weight]
  exact left_retained_recipes hR

/-- Every operational symbolic factor lies above the original right parent. -/
lemma right_parent_factors
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {O : FObstru M N}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈ symbolicFactors (n := n) O leftInput rightInput
        leftAddress rightAddress) :
    weightedWordWeight leftAddress.weight rightAddress.weight O.right.recipe <
      factor.word.weight HEAddres.weight := by
  rcases recipe_factors hfactor with ⟨R, hR, rfl⟩
  rw [word_symbolic_factor, ← weighted_word_weight]
  exact right_retained_recipes hR

/--
The operational family packet consists of the root correction followed by the
two surviving oriented child packets.
-/
lemma families_cons_append
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) :
    operationalCorrectionFamilies
        (n := n) hleftWeight hrightWeight O =
      O.correction ::
        (if _hleft :
            (operationalNestedLeft O).weight leftWeight rightWeight < n then
          operationalCorrectionFamilies
            (n := n) hleftWeight hrightWeight (operationalNestedLeft O)
        else []) ++
        (if _hright :
            (operationalNestedRight O).weight leftWeight rightWeight < n then
          operationalCorrectionFamilies
            (n := n) hleftWeight hrightWeight (operationalNestedRight O)
        else []) := by
  rw [operationalCorrectionFamilies,
    operationalRecursiveTree, WellFounded.fix_eq]
  simp only [ORTree.correctionFamilies]
  split <;> split <;>
    simp [OOTree.correctionFamilies,
      operationalCorrectionFamilies,
      operationalRecursiveTree]

/-- Operational retained recipes satisfy the same root-and-branches recurrence. -/
lemma recipes_cons_append
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) :
    retainedRecipes (n := n) hleftWeight hrightWeight O =
      O.correction.recipe ::
        (if _hleft :
            (operationalNestedLeft O).weight leftWeight rightWeight < n then
          retainedRecipes
            (n := n) hleftWeight hrightWeight (operationalNestedLeft O)
        else []) ++
        (if _hright :
            (operationalNestedRight O).weight leftWeight rightWeight < n then
          retainedRecipes
            (n := n) hleftWeight hrightWeight (operationalNestedRight O)
        else []) := by
  rw [retainedRecipes,
    families_cons_append
      hleftWeight hrightWeight]
  simp only [List.map_cons, List.map_append]
  split <;> split <;> rfl

/-- Specialized symbolic factors expose the oriented recursive recurrence. -/
lemma symbolic_cons_append
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (O : FObstru M N)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    symbolicFactors (n := n) O leftInput rightInput leftAddress rightAddress =
      BRSpec.symbolicFactor
          O.correction.recipe leftInput rightInput leftAddress rightAddress ::
        (if _hleft :
            (operationalNestedLeft O).weight
                leftAddress.weight rightAddress.weight < n then
          symbolicFactors (n := n) (operationalNestedLeft O)
            leftInput rightInput leftAddress rightAddress
        else []) ++
        (if _hright :
            (operationalNestedRight O).weight
                leftAddress.weight rightAddress.weight < n then
          symbolicFactors (n := n) (operationalNestedRight O)
            leftInput rightInput leftAddress rightAddress
        else []) := by
  rw [symbolicFactors, recipes_cons_append]
  simp only [BRSpec.symbolicFactors,
    List.map_cons, List.map_append]
  split <;> split <;>
    simp_all [symbolicFactors,
      BRSpec.symbolicFactors]

end ORPkt
end TCTex
end Submission

/-!
# Recursive decomposition of operational Hall-Petresco packets

The operationally oriented obstruction tree is the packet source used by a
concrete nonterminal collector.  Its nested children remember the actual
adjacent-rewrite orientation: an original parent crosses the freshly emitted
correction packet.

This file exposes the corresponding symbolic evaluation recurrence.  It is
intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace BRDecomp

universe u

open HACoeff
open BFOrient.FObstru
open ORPkt
open FRObstr

/--
Evaluation of the operational symbolic packet is the root correction followed
by the two surviving oriented child packets.
-/
lemma list_factors_branches
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (O : FObstru M N)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    SPFactor.listEval (n := n) e
        (symbolicFactors (n := n) O leftInput rightInput
          leftAddress rightAddress) =
      (BRSpec.symbolicFactor
          O.correction.recipe leftInput rightInput
            leftAddress rightAddress).eval e *
        (SPFactor.listEval e
            (if _hleft :
                (operationalNestedLeft O).weight
                    leftAddress.weight rightAddress.weight < n then
              symbolicFactors (n := n) (operationalNestedLeft O)
                leftInput rightInput leftAddress rightAddress
            else []) *
          SPFactor.listEval e
            (if _hright :
                (operationalNestedRight O).weight
                    leftAddress.weight rightAddress.weight < n then
              symbolicFactors (n := n) (operationalNestedRight O)
                leftInput rightInput leftAddress rightAddress
            else [])) := by
  rw [symbolic_cons_append]
  simp only [SPFactor.listEval_cons,
    SPFactor.listEval_append]
  rw [mul_assoc]

end BRDecomp
end TCTex
end Submission
