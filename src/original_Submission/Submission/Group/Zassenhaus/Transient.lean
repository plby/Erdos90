import Submission.Group.Zassenhaus.Attachment
import Submission.Group.Zassenhaus.Polynomial
import Submission.Group.Zassenhaus.ContextualRecollection
import Submission.Group.Zassenhaus.Inverse
import Submission.Group.Zassenhaus.StrictTail
import Submission.Group.Zassenhaus.ContextualPacketRecursion
import Submission.Group.Zassenhaus.TransientPacketClassification
import Submission.Group.Zassenhaus.ResidualContextualRecollection
import
  Submission.Group.Zassenhaus.ClassifiedPacketRecollection

-- Merged from TransientBalancedPacketAttachment.lean

/-!
# Balanced transient packet attachment

A transient Hall-Petresco packet can be returned termwise to the ordinary
bounded symbolic language whenever all of its block recipes are balanced:
their left block degree does not exceed their right block degree.

This file packages that adapter, instantiates it for the cutoff-three packet,
and records the exact cutoff-four frontier.  The latter consists of the single
left-triple recipe of bidegree `(2, 1)`.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

open HACoeff
open BRSpec

namespace PTSubsti

/-- Attach every block in a balanced recipe list to the ordinary language. -/
def attachedInnerExpansions
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (recipes : List BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hbalanced : ∀ R ∈ recipes, R.leftDegree ≤ R.rightDegree) :
    List (SWExp H inputWeight) :=
  recipes.pmap
    (P := fun R => R.leftDegree ≤ R.rightDegree)
    (fun R hbalancedR =>
      attachedInnerExpansion hinputWeight R factor innerWord
        rightWord hword hbalancedR)
    hbalanced

/--
Evaluating the attached balanced recipe list gives the same ordered product
as the corresponding transient block substitutions.
-/
lemma attached_inner_expansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (recipes : List BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hbalanced : ∀ R ∈ recipes, R.leftDegree ≤ R.rightDegree)
    (q : ℕ) :
    SWExp.listValue (n := n) q
        (attachedInnerExpansions hinputWeight recipes factor
          innerWord rightWord hword hbalanced) =
      TWExp.listValue q
        (wordExpansions hinputWeight recipes
          (TWExp.rewordFactor factor
            innerWord)
          (TWExp.wordUnit rightWord)) := by
  induction recipes with
  | nil =>
      rfl
  | cons R recipes ih =>
      rw [attachedInnerExpansions, List.pmap_cons,
        wordExpansions]
      change
        (attachedInnerExpansion hinputWeight R factor
              innerWord rightWord hword
              (hbalanced R (by simp))).word.eval
              (PEAddres.freeLowerTruncation
                (H := H) (n := n)) ^
            (attachedInnerExpansion hinputWeight R factor
              innerWord rightWord hword
              (hbalanced R (by simp))).exponent q *
          SWExp.listValue (n := n) q
            (attachedInnerExpansions hinputWeight recipes
              factor innerWord rightWord hword
                (fun next hnext => hbalanced next (by simp [hnext]))) =
        (wordExpansion hinputWeight R
              (TWExp.rewordFactor factor
                innerWord)
              (TWExp.wordUnit
                rightWord)).word.eval
              (PEAddres.freeLowerTruncation
                (H := H) (n := n)) ^
            (wordExpansion hinputWeight R
              (TWExp.rewordFactor factor
                innerWord)
              (TWExp.wordUnit
                rightWord)).exponent q *
          TWExp.listValue (n := n) q
            (wordExpansions hinputWeight recipes
              (TWExp.rewordFactor factor
                innerWord)
              (TWExp.wordUnit rightWord))
      rw [attached_inner_expansion,
        exponent_attached_expansion,
        exponent_wordExpansion,
        TWExp.exponent_rewordFactor,
        TWExp.exponent_wordUnit,
        ih (fun next hnext => hbalanced next (by simp [hnext]))]
      simp [innerReductionExpansion]

end PTSubsti

namespace PFSubsti.TAPkt

open PTSubsti

/-- Every block of the packet is balanced for transient inner reduction. -/
def InnerOuterBalanced
    {d n : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n) :
    Prop :=
  ∀ R ∈ packet.recipes, R.leftDegree ≤ R.rightDegree

/-- Attach an entire balanced cutoff packet to ordinary symbolic words. -/
def innerAttachedExpansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hbalanced : packet.InnerOuterBalanced) :
    List (SWExp H inputWeight) :=
  PTSubsti.attachedInnerExpansions
    hinputWeight packet.recipes
      factor innerWord rightWord hword hbalanced

/--
A completely attached balanced packet still evaluates exactly to
`[inner ^ factor.exponent, right]`.
-/
lemma outer_attached_expansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hbalanced : packet.InnerOuterBalanced)
    (q : ℕ) :
    SWExp.listValue (n := n) q
        (packet.innerAttachedExpansions hinputWeight factor
          innerWord rightWord hword hbalanced) =
      ⁅innerWord.eval
            (PEAddres.freeLowerTruncation
              (n := n)) ^
          factor.exponent q,
        rightWord.eval
          (PEAddres.freeLowerTruncation
            (n := n))⁆ := by
  rw [innerAttachedExpansions,
    attached_inner_expansions]
  exact packet.outer_transient_expansions
    hinputWeight factor innerWord rightWord q

/-- The cutoff-three singleton packet is entirely balanced. -/
lemma inner_balanced_n
    {d n : ℕ}
    (hn : n ≤ 3) :
    (n_three (d := d) hn :
      TAPkt.{u} d n).InnerOuterBalanced := by
  intro R hR
  simp [n_three] at hR
  subst R
  simp

/--
At cutoff three, `[inner ^ factor.exponent, right]` therefore has an
unconditional finite ordinary symbolic word expansion.
-/
def inner_attached_expansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hn : n ≤ 3)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    List (SWExp H inputWeight) :=
  let packet : TAPkt.{u} d n :=
    n_three (d := d) hn
  packet.innerAttachedExpansions hinputWeight factor
    innerWord rightWord hword (inner_balanced_n hn)

end PFSubsti.TAPkt

namespace BRSpec

/-- The basic recipe is balanced. -/
lemma left_degree_pair :
    hallPair.leftDegree ≤ hallPair.rightDegree := by
  simp

/-- The cutoff-four left-triple recipe is the first excess-left frontier. -/
lemma not_degree_triple :
    ¬ leftTriple.leftDegree ≤ leftTriple.rightDegree := by
  simp [leftTriple, BRecipe.leftDegree, BRecipe.rightDegree]

/-- The cutoff-four right-triple recipe remains balanced. -/
lemma left_degree_triple :
    rightTriple.leftDegree ≤ rightTriple.rightDegree := by
  simp [rightTriple, BRecipe.leftDegree, BRecipe.rightDegree]

end BRSpec

end TCTex
end Submission

-- Merged from TransientFixedPacketContextualRecollection.lean

/-!
# Fixed-packet contextual recollection of transient inner reductions

The powered bridge uses one selected Hall-Petresco packet throughout a
collection run.  Its recursive input should therefore be indexed by that
packet rather than quantified over every possible packet at the same cutoff.

This file exposes the narrower interface and retains the automatic terminal
dispatch from the earlier contextual collector.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

/--
Recursive recollection input for complete classified packets emitted from one
fixed Hall-Petresco packet.
-/
structure
    CRFtry
    (d n inputWeight : ℕ)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (packet :
      PFSubsti.TAPkt.{u}
        d n) where
  sourceRecollection :
    ∀
      (hinputWeight : 0 < inputWeight)
      (factor : SPFactora H inputWeight)
      (innerWord rightWord : CWord (HEAddres H))
      (hword : factor.word = .commutator innerWord rightWord),
      factor.word.weight PEAddres.weight + 1 < n →
        TTRecol
          n (factor.word.weight PEAddres.weight) H
            (packet.innerOuterTerms hinputWeight factor
              innerWord rightWord hword)

namespace
  CRFtry

/--
Dispatch the fixed packet either to its active recursive field or to the
factory-free terminal classified-packet endpoint.
-/
noncomputable def recollectionOrTerminal
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {packet :
      PFSubsti.TAPkt.{u}
        d n}
    (factory :
      CRFtry
        d n inputWeight H packet)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    TTRecol
      n (factor.word.weight PEAddres.weight) H
        (packet.innerOuterTerms hinputWeight factor
          innerWord rightWord hword) := by
  by_cases hactive :
      factor.word.weight PEAddres.weight + 1 < n
  · exact
      factory.sourceRecollection hinputWeight factor innerWord rightWord hword
        hactive
  · exact
      packet.outer_classified_terminal
        hinputWeight factor innerWord rightWord hword (Nat.le_of_not_gt hactive)

end
  CRFtry

end TCTex
end Submission

-- Merged from TransientOperationalCorrectionStrictTail.lean

/-!
# Universal operational corrections as a transient strict tail

The inverse raw-source vocabulary is followed by recursively generated
operational corrections.  Principal separation shows that every generated
correction has bidegree different from `(1, 1)`, exactly the strict-tail
condition used by transient Hall-power restart routing.

This file extends an ordered basic split of the raw-source vocabulary through
the complete universal correction suffix.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HACoeff
open BRSpec
open PTSubsti

namespace URVocabu

/--
The complete recursively generated operational-correction vocabulary is a
strict transient outer tail.
-/
lemma operational_recipes_tail
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight} :
    SOTail
      (operationalCorrectionRecipes n leftWeight rightWeight
        hleftWeight hrightWeight) := by
  intro R hR
  exact bidegree_operational_recipes hR

/--
An ordered principal split of the retained raw-source vocabulary.  This is
the remaining inventory obligation after operational corrections have been
separated as a strict tail.
-/
structure SBSplit
    (n leftWeight rightWeight : ℕ) where
  beforeBasic :
    List BRecipe
  afterBasic :
    List BRecipe
  recipes_eq :
    sourceRecipes n leftWeight rightWeight =
      beforeBasic ++ hallPair :: afterBasic
  before_strict_tail :
    SOTail beforeBasic
  after_strict_tail :
    SOTail afterBasic

/--
An ordered principal split of the raw-source vocabulary extends through the
universal operational-correction suffix.
-/
def ordered_split_recipes
    {d truncation n leftWeight rightWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d truncation}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (hpacket :
      packet.recipes =
        recipes n leftWeight rightWeight hleftWeight hrightWeight)
    (beforeBasic afterBasic : List BRecipe)
    (hsource :
      sourceRecipes n leftWeight rightWeight =
        beforeBasic ++ hallPair :: afterBasic)
    (hbeforeBasic :
      SOTail beforeBasic)
    (hafterBasic :
      SOTail afterBasic) :
    packet.OBSplit where
  beforeBasic := beforeBasic
  afterBasic :=
    afterBasic ++
      operationalCorrectionRecipes n leftWeight rightWeight
        hleftWeight hrightWeight
  recipes_eq := by
    rw [hpacket, recipes, hsource, List.append_assoc]
    rfl
  before_strict_tail := hbeforeBasic
  after_strict_tail :=
    hafterBasic.append operational_recipes_tail

namespace SBSplit

/--
Extend a raw-source split through every recursively generated operational
correction.
-/
def orderedSplit
    {d truncation n leftWeight rightWeight : ℕ}
    {packet :
      PFSubsti.TAPkt.{u}
        d truncation}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (split : SBSplit n leftWeight rightWeight)
    (hpacket :
      packet.recipes =
        recipes n leftWeight rightWeight hleftWeight hrightWeight) :
    packet.OBSplit :=
  ordered_split_recipes hpacket split.beforeBasic split.afterBasic
    split.recipes_eq split.before_strict_tail
      split.after_strict_tail

end SBSplit

end URVocabu

end TCTex
end Submission

-- Merged from TransientPacketContextualRecursion.lean

/-!
# Contextual recursion helpers for arbitrary transient packets

The mixed-packet fixpoint exposes recursive results for every strictly
smaller frontier-defect multiset.  Arbitrary transient Hall-Petresco packets
meet that interface directly: their complete classified packet descends from
the singleton obligation carried by either transient parent.

This file packages those two recursive-hypothesis calls.  It is intentionally
not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u v

namespace PFSubsti.TAPkt

/--
While resolving one left transient singleton, recursively obtain the complete
classified packet emitted by a transient commutator substitution.
-/
def transient_result_left
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {Result :
      List (SOTerm H inputWeight) → Sort v}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (hB :
      B.word.weight PEAddres.weight < n)
    (recursiveResults :
      ∀ child,
        SOTerm.FrontierDefectMultiset
            n child [.frontier B] →
          Result child) :
    Result (packet.transientClassifiedTerms hinputWeight B A) :=
  recursiveResults _
    (packet.transient_multiset_singleton
      hinputWeight B A hB)

/--
While resolving one right transient singleton, recursively obtain the
complete classified packet emitted by a transient commutator substitution.
-/
def transient_terms_result
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {Result :
      List (SOTerm H inputWeight) → Sort v}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (hA :
      A.word.weight PEAddres.weight < n)
    (recursiveResults :
      ∀ child,
        SOTerm.FrontierDefectMultiset
            n child [.frontier A] →
          Result child) :
    Result (packet.transientClassifiedTerms hinputWeight B A) :=
  recursiveResults _
    (packet.transient_classified_multiset
      hinputWeight B A hA)

end PFSubsti.TAPkt

end TCTex
end Submission

-- Merged from TransientPacketFrontierProvenance.lean

/-!
# Provenance of generic transient frontiers

The arbitrary transient classifier retains only non-attachable outputs on its
frontier.  Later contextual resolvers need to recover where such an output
came from without changing packet order.

This file recovers the source Hall-Petresco recipe of every retained frontier
entry and records its strict physical-weight growth from both transient
parents.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HACoeff

namespace PTSubsti

/--
A retained frontier entry in a classified recipe list comes from one source
recipe whose transient output is not attachable.
-/
lemma frontier_classified_transient
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hinputWeight : 0 < inputWeight}
    {recipes : List BRecipe}
    {B A expansion :
      TWExp H inputWeight}
    (hexpansion :
      .frontier expansion ∈
        recipes.map fun R => classifiedTransientTerm hinputWeight R B A) :
    ∃ R ∈ recipes,
      ¬ (wordExpansion hinputWeight R B A).exponentWeight ≤
          (wordExpansion hinputWeight R B A).word.weight
            PEAddres.weight ∧
        expansion = wordExpansion hinputWeight R B A := by
  rcases List.mem_map.mp hexpansion with ⟨R, hR, hterm⟩
  refine ⟨R, hR, ?_, ?_⟩
  · intro hweight
    rw [classified_attached_exponent
      hinputWeight R B A hweight] at hterm
    cases hterm
  · by_cases hweight :
        (wordExpansion hinputWeight R B A).exponentWeight ≤
          (wordExpansion hinputWeight R B A).word.weight
            PEAddres.weight
    · rw [classified_attached_exponent
        hinputWeight R B A hweight] at hterm
      cases hterm
    · rw [classified_transient_exponent
        hinputWeight R B A hweight] at hterm
      cases hterm
      rfl

end PTSubsti

namespace PFSubsti.TAPkt

open PTSubsti

/--
A retained frontier entry in an arbitrary classified packet remembers one
source recipe and its failed attachment test.
-/
lemma recipe_transient_frontier
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A expansion :
      TWExp H inputWeight)
    (hexpansion :
      .frontier expansion ∈
        packet.transientClassifiedTerms hinputWeight B A) :
    ∃ R ∈ packet.recipes,
      ¬ (wordExpansion hinputWeight R B A).exponentWeight ≤
          (wordExpansion hinputWeight R B A).word.weight
            PEAddres.weight ∧
        expansion = wordExpansion hinputWeight R B A := by
  rw [transientClassifiedTerms] at hexpansion
  exact
    frontier_classified_transient hexpansion

/--
Every retained generic frontier entry is physically strictly above its left
transient parent.
-/
lemma left_transient_frontier
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A expansion :
      TWExp H inputWeight)
    (hexpansion :
      .frontier expansion ∈
        packet.transientClassifiedTerms hinputWeight B A) :
    B.word.weight PEAddres.weight <
      expansion.word.weight PEAddres.weight := by
  rcases
      packet.recipe_transient_frontier
        hinputWeight B A expansion hexpansion with
    ⟨R, _, _, rfl⟩
  exact left_weight_expansion hinputWeight R B A

/--
Every retained generic frontier entry is physically strictly above its right
transient parent.
-/
lemma right_classified_frontier
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A expansion :
      TWExp H inputWeight)
    (hexpansion :
      .frontier expansion ∈
        packet.transientClassifiedTerms hinputWeight B A) :
    A.word.weight PEAddres.weight <
      expansion.word.weight PEAddres.weight := by
  rcases
      packet.recipe_transient_frontier
        hinputWeight B A expansion hexpansion with
    ⟨R, _, _, rfl⟩
  exact right_weight_expansion hinputWeight R B A

end PFSubsti.TAPkt

end TCTex
end Submission

-- Merged from TransientPacketInverseCancellation.lean

/-!
# Contextual cancellation of classified transient packets

A classified transient Hall-Petresco packet has the same ordered value as its
raw transient packet.  Appending the raw packet in reverse-negated order
therefore gives a mixed contextual packet with trivial value, even when some
classified terms remain nonattachable frontiers.

This is the cancellation kernel needed by reachable-context recollection: it
erases a packet together with its exact inverse without attempting to
normalize any loose transient carrier in isolation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace PFSubsti.TAPkt

/--
A classified transient packet followed by the all-frontier view of its exact
reverse-negated raw transient packet.
-/
def transientTermsContextual
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight) :
    List (SOTerm H inputWeight) :=
  packet.transientClassifiedTerms hinputWeight B A ++
    SOTerm.frontierTerms
      (TWExp.inverseList
        (packet.transientWordExpansions hinputWeight B A))

/-- The classified-packet inverse contextual kernel has trivial value. -/
lemma list_classified_contextual
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (q : ℕ) :
    SOTerm.listValue (n := n) q
        (packet.transientTermsContextual hinputWeight
          B A) =
      1 := by
  rw [transientTermsContextual,
    SOTerm.listValue_append,
    packet.value_transient_terms,
    SOTerm.value_frontier_terms,
    TWExp.list_value_inverse,
    packet.transient_word_expansions]
  group

/-- Recollect the classified-packet inverse contextual kernel to empty. -/
def source_classified_contextual
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight) :
    TTRecol
      n lowerWeight H
        (packet.transientTermsContextual hinputWeight
          B A) :=
  TTRecol.empty_list_value
    _ fun q =>
      packet.list_classified_contextual
        hinputWeight B A q

/--
Erase a classified-packet inverse cancellation kernel in the middle of an
already recollected mixed context.
-/
def splice_terms_contextual
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (leftContext rightContext :
      List (SOTerm H inputWeight))
    (contextRecollection :
      TTRecol
        n lowerWeight H (leftContext ++ rightContext)) :
    TTRecol
      n lowerWeight H
        (leftContext ++
          packet.transientTermsContextual hinputWeight
            B A ++
          rightContext) :=
  TTRecol.list_value
    contextRecollection fun q => by
      simp only [SOTerm.listValue_append]
      rw [packet.list_classified_contextual]
      group

/--
The reworded inner-reduction contextual expansion is a generic
classified-packet inverse kernel followed by the original outer frontier.
-/
lemma contextual_terms_append
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    packet.transientInnerContextual hinputWeight
        outerExpansion innerWord rightWord =
      packet.transientTermsContextual hinputWeight
          (outerExpansion.reword innerWord)
          (TWExp.wordUnit rightWord) ++
        [.frontier outerExpansion] := by
  simp [transientInnerContextual,
    transientTermsContextual,
    transientInnerTerms,
    transientInnerReduction,
    SOTerm.frontierTerms]

/--
Expand one transient outer frontier inside an already recollected mixed
context.  The expanded block is semantically equal to the original frontier.
-/
def splice_transient_terms
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (leftContext rightContext :
      List (SOTerm H inputWeight))
    (contextRecollection :
      TTRecol
        n lowerWeight H
          (leftContext ++ [.frontier outerExpansion] ++ rightContext)) :
    TTRecol
      n lowerWeight H
        (leftContext ++
          packet.transientInnerContextual hinputWeight
            outerExpansion innerWord rightWord ++
          rightContext) :=
  TTRecol.list_value
    contextRecollection fun q => by
      simp only [SOTerm.listValue_append,
        SOTerm.value_singleton_frontier]
      rw [packet.inner_contextual_terms]

/--
Contract one reworded contextual expansion inside an already recollected
mixed context back to its original transient outer frontier.
-/
def splice_frontier_contextual
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (leftContext rightContext :
      List (SOTerm H inputWeight))
    (contextRecollection :
      TTRecol
        n lowerWeight H
          (leftContext ++
            packet.transientInnerContextual hinputWeight
              outerExpansion innerWord rightWord ++
            rightContext)) :
    TTRecol
      n lowerWeight H
        (leftContext ++ [.frontier outerExpansion] ++ rightContext) :=
  TTRecol.list_value
    contextRecollection fun q => by
      simp only [SOTerm.listValue_append,
        SOTerm.value_singleton_frontier]
      rw [packet.inner_contextual_terms]

end PFSubsti.TAPkt

end TCTex
end Submission

-- Merged from TransientOperationalCorrectionStrictTailObstruction.lean

/-!
# Obstruction to splitting an occurrence-level universal raw vocabulary

The retained universal raw-source vocabulary is occurrence-level data.  An
ordered transient split around `basic` can be extended through recursive
operational corrections, but the raw-source split itself is possible only
when the raw vocabulary contains exactly one `basic` occurrence.

This file records that diagnostic boundary.  It is intentionally not imported
by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

open BRSpec

namespace URVocabu
namespace SBSplit

/--
A strict ordered split of the retained raw-source vocabulary forces exactly
one occurrence of the principal bidegree `(1, 1)`.
-/
lemma count_p_bidegree
    {n leftWeight rightWeight : ℕ}
    (split : SBSplit n leftWeight rightWeight) :
    (sourceRecipes n leftWeight rightWeight).countP
        (fun R => R.leftDegree == 1 && R.rightDegree == 1) =
      1 := by
  have hbefore :
      split.beforeBasic.countP
          (fun R => R.leftDegree == 1 && R.rightDegree == 1) =
        0 := by
    rw [List.countP_eq_zero]
    intro R hR
    rcases split.before_strict_tail R hR with hleft | hright
    · simp [hleft]
    · simp [hright]
  have hafter :
      split.afterBasic.countP
          (fun R => R.leftDegree == 1 && R.rightDegree == 1) =
        0 := by
    rw [List.countP_eq_zero]
    intro R hR
    rcases split.after_strict_tail R hR with hleft | hright
    · simp [hleft]
    · simp [hright]
  rw [split.recipes_eq, List.countP_append, List.countP_cons_of_pos,
    hbefore, hafter]
  · rfl

end SBSplit

/--
Two retained raw occurrences collapsing to `basic` obstruct the source-level
ordered split.  Such multiplicity must be compressed before transient
structural restart consumes the vocabulary.
-/
lemma not_split_bidegree
    {n leftWeight rightWeight : ℕ}
    (hcount :
      2 ≤
        (sourceRecipes n leftWeight rightWeight).countP
          (fun R => R.leftDegree == 1 && R.rightDegree == 1)) :
    SBSplit n leftWeight rightWeight →
      False := by
  intro split
  rw [split.count_p_bidegree] at hcount
  omega

end URVocabu

end TCTex
end Submission

-- Merged from TransientPacketContextualRecollection.lean

/-!
# Contextual recollection of generic transient packets

Arbitrary transient Hall-Petresco packets retain attached and frontier terms
in their original order.  This file records their common physical support
bound and closes a complete mixed packet once every retained frontier term has
reached the nilpotent cutoff.

The left- and right-parent terminal constructors are useful base cases for
the eventual contextual recursive collector.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

open HACoeff

namespace SOTerm

/-- The physical Hall-word weight of one attached-or-frontier packet term. -/
def wordWeight
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r} :
    SOTerm H inputWeight → ℕ
  | .attached wordExpansion =>
      wordExpansion.word.weight PEAddres.weight
  | .frontier wordExpansion =>
      wordExpansion.word.weight PEAddres.weight

@[simp]
lemma wordWeight_attached
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : SWExp H inputWeight) :
    wordWeight (.attached wordExpansion) =
      wordExpansion.word.weight PEAddres.weight :=
  rfl

@[simp]
lemma wordWeight_frontier
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight) :
    wordWeight (.frontier wordExpansion) =
      wordExpansion.word.weight PEAddres.weight :=
  rfl

end SOTerm

namespace TTRecol

/--
Recollect one mixed packet term whose physical support is high enough and
whose frontier case, if any, has reached the cutoff.
-/
noncomputable def singleton_least_frontier
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (term : SOTerm H inputWeight)
    (hweight :
      lowerWeight ≤ SOTerm.wordWeight term)
    (hfrontier :
      ∀ wordExpansion,
        term = .frontier wordExpansion →
          n ≤ wordExpansion.word.weight PEAddres.weight) :
    TTRecol
      n lowerWeight H [term] := by
  cases term with
  | attached wordExpansion =>
      exact singleton_attached wordExpansion hweight
  | frontier wordExpansion =>
      exact
        singleton_frontier wordExpansion
          (TTRecola.singleton_n_weight
              wordExpansion
              (hfrontier wordExpansion rfl))

/--
Recollect a complete mixed packet in place when its physical support is high
enough and every retained frontier term has reached the cutoff.
-/
noncomputable def word_frontier_cutoff
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (rawSource :
      List (SOTerm H inputWeight))
    (hweight :
      ∀ term ∈ rawSource,
        lowerWeight ≤
          SOTerm.wordWeight term)
    (hfrontier :
      ∀ wordExpansion,
        .frontier wordExpansion ∈ rawSource →
          n ≤ wordExpansion.word.weight PEAddres.weight) :
    TTRecol
      n lowerWeight H rawSource :=
  of_singletons rawSource fun term hterm =>
    singleton_least_frontier term
      (hweight term hterm) fun wordExpansion hterm_eq =>
        hfrontier wordExpansion (hterm_eq ▸ hterm)

end TTRecol

namespace PTSubsti

/-- Every generic classified output is physically above its left parent. -/
lemma left_classified_transient
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : TWExp H inputWeight) :
    B.word.weight PEAddres.weight <
      (classifiedTransientTerm hinputWeight R B A).wordWeight := by
  by_cases hweight :
      (wordExpansion hinputWeight R B A).exponentWeight ≤
        (wordExpansion hinputWeight R B A).word.weight
          PEAddres.weight
  · rw [classified_attached_exponent
      hinputWeight R B A hweight]
    exact left_weight_expansion hinputWeight R B A
  · rw [classified_transient_exponent
      hinputWeight R B A hweight]
    exact left_weight_expansion hinputWeight R B A

/-- Every generic classified output is physically above its right parent. -/
lemma classified_transient_term
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : TWExp H inputWeight) :
    A.word.weight PEAddres.weight <
      (classifiedTransientTerm hinputWeight R B A).wordWeight := by
  by_cases hweight :
      (wordExpansion hinputWeight R B A).exponentWeight ≤
        (wordExpansion hinputWeight R B A).word.weight
          PEAddres.weight
  · rw [classified_attached_exponent
      hinputWeight R B A hweight]
    exact right_weight_expansion hinputWeight R B A
  · rw [classified_transient_exponent
      hinputWeight R B A hweight]
    exact right_weight_expansion hinputWeight R B A

end PTSubsti

namespace PFSubsti.TAPkt

open PTSubsti
open TTRecol

/-- Every term in a generic classified packet is physically above its left
parent. -/
lemma left_transient_terms
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (term : SOTerm H inputWeight)
    (hterm : term ∈ packet.transientClassifiedTerms hinputWeight B A) :
    B.word.weight PEAddres.weight < term.wordWeight := by
  rw [transientClassifiedTerms] at hterm
  rcases List.mem_map.mp hterm with ⟨R, _, rfl⟩
  exact left_classified_transient
    hinputWeight R B A

/-- Every term in a generic classified packet is physically above its right
parent. -/
lemma right_classified_terms
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (term : SOTerm H inputWeight)
    (hterm : term ∈ packet.transientClassifiedTerms hinputWeight B A) :
    A.word.weight PEAddres.weight < term.wordWeight := by
  rw [transientClassifiedTerms] at hterm
  rcases List.mem_map.mp hterm with ⟨R, _, rfl⟩
  exact classified_transient_term
    hinputWeight R B A

/--
Normalize a complete generic classified packet when the left parent is one
stratum below the cutoff.
-/
noncomputable def source_transient_terminal
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (hcutoff :
      n ≤ B.word.weight PEAddres.weight + 1) :
    TTRecol
      n (B.word.weight PEAddres.weight) H
        (packet.transientClassifiedTerms hinputWeight B A) :=
  word_frontier_cutoff _
      (fun term hterm =>
        Nat.le_of_lt
          (packet.left_transient_terms
            hinputWeight B A term hterm))
      (fun wordExpansion hwordExpansion =>
        hcutoff.trans
          (Nat.succ_le_of_lt
            (packet.left_transient_frontier
              hinputWeight B A wordExpansion hwordExpansion)))

/--
Normalize a complete generic classified packet when the right parent is one
stratum below the cutoff.
-/
noncomputable def recollection_terms_terminal
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (hcutoff :
      n ≤ A.word.weight PEAddres.weight + 1) :
    TTRecol
      n (A.word.weight PEAddres.weight) H
        (packet.transientClassifiedTerms hinputWeight B A) :=
  word_frontier_cutoff _
      (fun term hterm =>
        Nat.le_of_lt
          (packet.right_classified_terms
            hinputWeight B A term hterm))
      (fun wordExpansion hwordExpansion =>
        hcutoff.trans
          (Nat.succ_le_of_lt
            (packet.right_classified_frontier
              hinputWeight B A wordExpansion hwordExpansion)))

/-- The left-terminal generic recollection still evaluates to the parent
commutator. -/
lemma
    recollection_classified_terminal
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (hcutoff :
      n ≤ B.word.weight PEAddres.weight + 1)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (packet
          |>.source_transient_terminal
            hinputWeight B A hcutoff).higherSource =
      ⁅B.value (n := n) q, A.value (n := n) q⁆ := by
  rw [(packet
    |>.source_transient_terminal
      hinputWeight B A hcutoff).list_higher_raw]
  exact packet.value_transient_terms hinputWeight B A q

/-- The right-terminal generic recollection still evaluates to the parent
commutator. -/
lemma
    higher_transient_terminal
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A : TWExp H inputWeight)
    (hcutoff :
      n ≤ A.word.weight PEAddres.weight + 1)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (packet
          |>.recollection_terms_terminal
            hinputWeight B A hcutoff).higherSource =
      ⁅B.value (n := n) q, A.value (n := n) q⁆ := by
  rw [(packet
    |>.recollection_terms_terminal
      hinputWeight B A hcutoff).list_higher_raw]
  exact packet.value_transient_terms hinputWeight B A q

end PFSubsti.TAPkt

end TCTex
end Submission

-- Merged from TransientOperationalCorrectionStrictTailConcreteObstruction.lean

/-!
# Concrete raw-source obstruction to an ordered principal split

The cutoff-three raw inverse vocabulary still records labelled occurrences.
Its final right row contains two retained basic histories, and both
standardize to bidegree `(1, 1)`.  Thus the occurrence-level source vocabulary
cannot support the ordered split expected after multiplicity compression.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

open URVocabu

/--
Already at cutoff three, the occurrence-level raw source vocabulary has at
least two retained bidegree `(1, 1)` entries.
-/
lemma count_bidegree_recipes :
    2 ≤
      (sourceRecipes 3 1 1).countP
        (fun recipe => recipe.leftDegree == 1 && recipe.rightDegree == 1) := by
  have hleft :
      HACoeff.labelledLeftAtoms 3 3 =
        [Sum.inl 0, Sum.inl 1, Sum.inl 2] := by
    decide
  have hright :
      HACoeff.labelledRightAtoms 3 3 =
        [Sum.inr 0, Sum.inr 1, Sum.inr 2] := by
    decide
  let history₀ :
      RHRecurs.RHistor 3 3 :=
    .hallPair (Sum.inl 0) (Sum.inr 0)
  let history₁ :
      RHRecurs.RHistor 3 3 :=
    .hallPair (Sum.inl 0) (Sum.inr 1)
  have hrow :
      List.Sublist [history₀, history₁]
        (RHRecurs.inverseRightHistories
          (Sum.inl 0) [Sum.inr 0, Sum.inr 1, Sum.inr 2]) := by
    simp [history₀, history₁,
      RHRecurs.inverseRightHistories,
      RHRecurs.inverseConjHistory,
      RHRecurs.inverseConjHistories,
      RHRecurs.conjugateAtomHistories]
  have hraw :
      List.Sublist [history₀, history₁]
        (RHRecipe.inverseRawHistories 3 3) := by
    rw [RHRecipe.inverseRawHistories, hleft, hright]
    rw [RHRecurs.inverseLeftHistories]
    exact hrow.trans (List.sublist_append_right _ _)
  have hraw_attach_vals :
      List.Sublist [history₀, history₁]
        ((RHRecipe.inverseRawHistories 3 3).attach.map
          Subtype.val) := by
    simpa only [List.attach_map_subtype_val] using hraw
  obtain ⟨selected, hselected, hselected_val⟩ :=
    List.sublist_map_iff.mp hraw_attach_vals
  have history₀_mem :
      history₀ ∈ RHRecipe.inverseRawHistories 3 3 :=
    hraw.subset (by simp)
  have history₁_mem :
      history₁ ∈ RHRecipe.inverseRawHistories 3 3 :=
    hraw.subset (by simp)
  let attached₀ :
      { history //
        history ∈ RHRecipe.inverseRawHistories 3 3 } :=
    ⟨history₀, history₀_mem⟩
  let attached₁ :
      { history //
        history ∈ RHRecipe.inverseRawHistories 3 3 } :=
    ⟨history₁, history₁_mem⟩
  have selected_eq : selected = [attached₀, attached₁] := by
    apply Subtype.val_injective.list_map
    rw [← hselected_val]
    rfl
  have hattach :
      List.Sublist [attached₀, attached₁]
        (RHRecipe.inverseRawHistories 3 3).attach := by
    simpa only [← selected_eq] using hselected
  let initialOf :=
    fun history :
        { history //
          history ∈ RHRecipe.inverseRawHistories 3 3 } =>
      RRVocabu.RHistor.initialRecipe
        history.1 history.2
  let recipe₀ := initialOf attached₀
  let recipe₁ := initialOf attached₁
  have hinitial :
      List.Sublist [recipe₀, recipe₁]
        (RRVocabu.initialRecipes 3) := by
    simpa only [RRVocabu.initialRecipes,
      recipe₀, recipe₁, List.map_cons, List.map_nil] using
        hattach.map initialOf
  have recipe₀_weight : recipe₀.weight 1 1 = 2 := by
    simp [recipe₀, initialOf, attached₀, history₀,
      RRVocabu.RHistor.initial_recipe_weight,
      HACoeff.collapseLabel, HPAtom.weight]
  have recipe₁_weight : recipe₁.weight 1 1 = 2 := by
    simp [recipe₁, initialOf, attached₁, history₁,
      RRVocabu.RHistor.initial_recipe_weight,
      HACoeff.collapseLabel, HPAtom.weight]
  have bidegree_of_weight_two
      (recipe : RRVocabu.IRecipe)
      (hweight : recipe.weight 1 1 = 2) :
      recipe.blockRecipe.leftDegree = 1 ∧
        recipe.blockRecipe.rightDegree = 1 := by
    have hleftDegree :=
      BRSpec.leftDegree_pos recipe.blockRecipe
    have hrightDegree :=
      BRSpec.rightDegree_pos recipe.blockRecipe
    unfold RRVocabu.IRecipe.weight at hweight
    rw [BRSpec.weighted_word_weight] at hweight
    omega
  have recipe₀_bidegree := bidegree_of_weight_two recipe₀ recipe₀_weight
  have recipe₁_bidegree := bidegree_of_weight_two recipe₁ recipe₁_weight
  have hretained :
      List.Sublist [recipe₀, recipe₁]
        (RRVocabu.retainedInitialRecipes 3 3 1 1) := by
    simpa [RRVocabu.retainedInitialRecipes,
      recipe₀_weight, recipe₁_weight] using
        hinitial.filter (fun recipe => decide (recipe.weight 1 1 < 3))
  have hsource :
      List.Sublist [recipe₀.blockRecipe, recipe₁.blockRecipe]
        (sourceRecipes 3 1 1) := by
    simpa only [sourceRecipes, List.map_cons, List.map_nil] using
      hretained.map RRVocabu.IRecipe.blockRecipe
  have hcount :
      [recipe₀.blockRecipe, recipe₁.blockRecipe].countP
          (fun recipe => recipe.leftDegree == 1 && recipe.rightDegree == 1) ≤
        (sourceRecipes 3 1 1).countP
          (fun recipe => recipe.leftDegree == 1 && recipe.rightDegree == 1) :=
    hsource.countP_le
  simpa [recipe₀_bidegree.1, recipe₀_bidegree.2,
    recipe₁_bidegree.1, recipe₁_bidegree.2] using hcount

/--
Consequently, the raw cutoff-three source vocabulary cannot itself provide
the post-compression ordered basic split.
-/
lemma not_basic_split :
    SBSplit 3 1 1 →
      False :=
  not_split_bidegree
    count_bidegree_recipes

end TCTex
end Submission
