import Submission.Group.Zassenhaus.Transient
import Submission.Group.Zassenhaus.PacketClassification
import Submission.Group.Zassenhaus.ReductionPoweredBridge
import Submission.Group.Zassenhaus.SourceRecollectionCongruence
import Submission.Group.Zassenhaus.ReductionOuter
import Submission.Group.Zassenhaus.SemanticallyHigherRecollection
import Submission.Group.Zassenhaus.SharpNormalizerFamilies
import Submission.Group.Zassenhaus.ResidualBranchCases


-- Merged from ClassThreeFrontier.lean

/-!
# The first transient inner-reduction frontier

The cutoff-four Hall-Petresco packet consists of the left triple, the basic
bracket, and the right triple.  After rewording an outer exponent onto its
inner word, the latter two terms immediately return to the ordinary bounded
symbolic language.  The left triple is the unique transient frontier term.

This file records that first nontrivial frontier explicitly.  Its word is
`[inner, [inner, right]]`, its arithmetic weight is twice the original parent
weight, and its exponent is `choose (factor.exponent q) 2`.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HACoeff
open BRSpec

namespace PTSubsti

/-- The cutoff-four excess-left frontier word is `[inner, [inner, right]]`. -/
@[simp]
lemma inner_expansion_triple
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    (innerReductionExpansion hinputWeight leftTriple factor innerWord
      rightWord).word =
        .commutator innerWord (.commutator innerWord rightWord) :=
  rfl

/-- The cutoff-four excess-left frontier has arithmetic weight twice the parent weight. -/
@[simp]
lemma exponent_expansion_triple
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    (innerReductionExpansion hinputWeight leftTriple factor innerWord
      rightWord).exponentWeight =
        2 * factor.word.weight PEAddres.weight := by
  simp [exponent_outer_expansion, leftTriple,
    BRecipe.leftDegree]

/-- The cutoff-four excess-left frontier exponent is `choose (factor.exponent q) 2`. -/
@[simp]
lemma exponent_outer_triple
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    (innerReductionExpansion hinputWeight leftTriple factor innerWord
      rightWord).exponent =
        fun q : ℕ => Ring.choose (factor.exponent q) 2 := by
  rw [exponent_reduction_expansion]
  funext q
  simp

/-- The cutoff-four left triple is classified as a transient frontier term. -/
lemma classified_outer_triple
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    classifiedOuterTerm hinputWeight leftTriple factor innerWord
        rightWord hword =
      .frontier
        (innerReductionExpansion hinputWeight leftTriple factor
          innerWord rightWord) := by
  exact classified_inner_degree
    hinputWeight leftTriple factor innerWord rightWord hword
      (by simp [leftTriple, BRecipe.leftDegree, BRecipe.rightDegree])

/-- The cutoff-four basic term is classified as an attached ordinary term. -/
lemma classified_inner_pair
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    classifiedOuterTerm hinputWeight hallPair factor innerWord
        rightWord hword =
      .attached
        (attachedInnerExpansion hinputWeight hallPair factor
          innerWord rightWord hword left_degree_pair) := by
  exact classified_outer_degree
    hinputWeight hallPair factor innerWord rightWord hword
      left_degree_pair

/-- The cutoff-four right triple is classified as an attached ordinary term. -/
lemma classified_inner_triple
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    classifiedOuterTerm hinputWeight rightTriple factor innerWord
        rightWord hword =
      .attached
        (attachedInnerExpansion hinputWeight rightTriple
          factor innerWord rightWord hword
            left_degree_triple) := by
  exact classified_outer_degree
    hinputWeight rightTriple factor innerWord rightWord hword
      left_degree_triple

end PTSubsti

namespace PFSubsti.TAPkt

/-- The cutoff-four balanced recipe subsequence is `[basic, rightTriple]`. -/
@[simp]
lemma balanced_recipes_four
    {d n : ℕ}
    (hn : n ≤ 4) :
    (n_four (d := d) hn :
      TAPkt.{u} d n).innerBalancedRecipes =
        [hallPair, rightTriple] := by
  simp [innerBalancedRecipes, n_four, hallPair, leftTriple,
    rightTriple, BRecipe.leftDegree, BRecipe.rightDegree]

/-- The cutoff-four transient frontier recipe subsequence is `[leftTriple]`. -/
@[simp]
lemma inner_recipes_four
    {d n : ℕ}
    (hn : n ≤ 4) :
    (n_four (d := d) hn :
      TAPkt.{u} d n).innerReductionRecipes =
        [leftTriple] := by
  simp [innerReductionRecipes, n_four, hallPair, leftTriple,
    rightTriple, BRecipe.leftDegree, BRecipe.rightDegree]

/--
The cutoff-four order-preserving mixed packet has one transient left-triple
frontier followed by the attached basic and right-triple terms.
-/
lemma inner_n_four
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hn : n ≤ 4)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    (n_four (d := d) hn :
      TAPkt.{u} d n).innerOuterTerms
        hinputWeight factor innerWord rightWord hword =
      [ .frontier
          (PTSubsti.innerReductionExpansion
            hinputWeight leftTriple factor
              innerWord rightWord),
        .attached
          (PTSubsti.attachedInnerExpansion
            hinputWeight hallPair factor
              innerWord rightWord hword left_degree_pair),
        .attached
          (PTSubsti.attachedInnerExpansion
            hinputWeight rightTriple
              factor innerWord rightWord hword
                left_degree_triple) ] := by
  simp [innerOuterTerms, n_four,
    PTSubsti.classified_outer_triple,
    PTSubsti.classified_inner_pair,
    PTSubsti.classified_inner_triple]

end PFSubsti.TAPkt

end TCTex
end Submission

-- Merged from ClassThreeBridge.lean

/-!
# Class-three powered-commutator bridge

At cutoff four, the discrepancy between `[x ^ e, y]` and `[x, y] ^ e` is
exactly the inverse left-triple frontier term.  This is the first concrete
post-cancellation bridge identity for transient inner reduction.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement
open BRSpec

namespace HCThree

/--
At cutoff four, dividing `[left ^ exponent, right]` by
`[left, right] ^ exponent` leaves the inverse left-triple power.
-/
lemma element_zpow_triple
    {d n : ℕ}
    (hn : n ≤ 4)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (exponent : ℤ) :
    ⁅left ^ exponent, right⁆⁻¹ * ⁅left, right⁆ ^ exponent =
      (⁅left, ⁅left, right⁆⁆ ^ Ring.choose exponent 2)⁻¹ := by
  let C := ⁅left, right⁆
  let D := ⁅left, ⁅left, right⁆⁆
  have hleft :
      left ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hright :
      right ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hC :
      C ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
    simpa [C] using
      element_lower_series hleft hright
  have hD :
      D ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
    simpa [D] using
      element_lower_series hleft hC
  have hCD : Commute C D :=
    commute_series_four hn C hD
  have hswap :
      Commute (D ^ Ring.choose exponent 2)⁻¹ (C ^ exponent) :=
    (hCD.symm.zpow_zpow (Ring.choose exponent 2) exponent).inv_left
  have hchooseOneTwo : Ring.choose (1 : ℤ) 2 = 0 := by
    norm_num [Ring.choose]
  have hexpansion :
      ⁅left ^ exponent, right⁆ =
        D ^ Ring.choose exponent 2 * C ^ exponent := by
    simpa [C, D, hchooseOneTwo] using
      (element_zpow_class
        hn left right exponent 1)
  change ⁅left ^ exponent, right⁆⁻¹ * C ^ exponent =
    (D ^ Ring.choose exponent 2)⁻¹
  rw [hexpansion, mul_inv_rev, mul_assoc, hswap.eq]
  group

end HCThree

namespace PTSubsti

/--
For an inner-reduction factor at cutoff four, the powered bridge quotient is
the inverse value of the unique transient left-triple frontier expansion.
-/
lemma zpow_frontier_value
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hn : n ≤ 4)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (q : ℕ) :
    ⁅innerWord.eval
          (PEAddres.freeLowerTruncation
            (n := n)) ^
        factor.exponent q,
      rightWord.eval
        (PEAddres.freeLowerTruncation
          (n := n))⁆⁻¹ *
        ⁅innerWord.eval
              (PEAddres.freeLowerTruncation
                (n := n)),
          rightWord.eval
            (PEAddres.freeLowerTruncation
              (n := n))⁆ ^
          factor.exponent q =
      ((innerReductionExpansion hinputWeight leftTriple factor
        innerWord rightWord).value (n := n) q)⁻¹ := by
  rw [TWExp.value,
    inner_expansion_triple,
    exponent_outer_triple]
  exact HCThree.element_zpow_triple hn
      (innerWord.eval
        (PEAddres.freeLowerTruncation (n := n)))
      (rightWord.eval
        (PEAddres.freeLowerTruncation (n := n)))
      (factor.exponent q)

end PTSubsti

end TCTex
end Submission

-- Merged from ClassThreeFrontierSemantics.lean

/-!
# Semantics of the first transient inner-reduction frontier

The cutoff-four left-triple term is the first output that cannot immediately
return to the ordinary bounded symbolic language.  This file measures its
failure exactly: its arithmetic exponent bound exceeds its physical Hall-word
weight by one copy of the right-word weight.

The file also packages the explicit cutoff-four mixed term list and proves
that it evaluates to the intended outer commutator.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

open HACoeff
open BRSpec
open PTSubsti

namespace PTSubsti

/-- The cutoff-four frontier word has physical weight `2 * inner + right`. -/
@[simp]
lemma inner_reduction_triple
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    (innerReductionExpansion hinputWeight leftTriple factor innerWord
      rightWord).word.weight PEAddres.weight =
        2 * innerWord.weight PEAddres.weight +
          rightWord.weight PEAddres.weight := by
  rw [inner_reduction_expansion]
  simp [leftTriple, BRecipe.leftDegree, BRecipe.rightDegree]

/--
The left-triple arithmetic bound exceeds its physical word weight by exactly
one right-word weight.
-/
lemma exponent_triple_add
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    (innerReductionExpansion hinputWeight leftTriple factor innerWord
        rightWord).exponentWeight =
      (innerReductionExpansion hinputWeight leftTriple factor
          innerWord rightWord).word.weight PEAddres.weight +
        rightWord.weight PEAddres.weight := by
  rw [exponent_expansion_triple,
    inner_reduction_triple, hword]
  simp [Nat.mul_add, Nat.add_assoc]
  omega

/-- The left-triple frontier bound is strictly above its physical word weight. -/
lemma exponent_inner_triple
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    (innerReductionExpansion hinputWeight leftTriple factor innerWord
        rightWord).word.weight PEAddres.weight <
      (innerReductionExpansion hinputWeight leftTriple factor
        innerWord rightWord).exponentWeight := by
  rw [
    exponent_triple_add
      hinputWeight factor innerWord rightWord hword]
  exact Nat.lt_add_of_pos_right
    (CWord.weight_pos
      PEAddres.weight PEAddres.weight_pos
      rightWord)

/-- Consequently, the cutoff-four left-triple frontier cannot attach yet. -/
lemma not_inner_triple
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    ¬ (innerReductionExpansion hinputWeight leftTriple factor
        innerWord rightWord).exponentWeight ≤
      (innerReductionExpansion hinputWeight leftTriple factor
        innerWord rightWord).word.weight PEAddres.weight :=
  Nat.not_le_of_lt
    (exponent_inner_triple
      hinputWeight factor innerWord rightWord hword)

end PTSubsti

namespace PFSubsti.TAPkt

/--
The explicit cutoff-four ordered term list: one transient frontier term,
followed by the two terms already returned to the ordinary bounded API.
-/
def innerReductionTerms
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    List (SOTerm H inputWeight) :=
  [.frontier
      (innerReductionExpansion hinputWeight leftTriple factor innerWord
        rightWord),
    .attached
      (attachedInnerExpansion hinputWeight hallPair factor
        innerWord rightWord hword left_degree_pair),
    .attached
      (attachedInnerExpansion hinputWeight rightTriple factor
        innerWord rightWord hword left_degree_triple)]

/-- The classified cutoff-four packet is the explicit class-three term list. -/
lemma inner_classified_four
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hn : n ≤ 4)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    (n_four (d := d) hn :
      TAPkt.{u} d n).innerOuterTerms
        hinputWeight factor innerWord rightWord hword =
      innerReductionTerms hinputWeight factor innerWord
        rightWord hword := by
  simpa only [innerReductionTerms] using
    inner_n_four hn hinputWeight factor
      innerWord rightWord hword

/--
The explicit cutoff-four mixed term list evaluates exactly to
`[inner ^ factor.exponent, right]`.
-/
lemma terms_n_four
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hn : n ≤ 4)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SOTerm.listValue (n := n) q
        (innerReductionTerms hinputWeight factor innerWord
          rightWord hword) =
      ⁅innerWord.eval
            (PEAddres.freeLowerTruncation
              (n := n)) ^
          factor.exponent q,
        rightWord.eval
          (PEAddres.freeLowerTruncation
            (n := n))⁆ := by
  rw [←
    inner_classified_four
      hn hinputWeight factor innerWord rightWord hword]
  exact
    (n_four (d := d) hn :
      TAPkt.{u} d n)
      |>.inner_reduction_terms hinputWeight factor
        innerWord rightWord hword q

end PFSubsti.TAPkt

end TCTex
end Submission

-- Merged from ClassThreeCancellation.lean

/-!
# Canceling the first transient inner-reduction frontier

At cutoff four, the classified transient packet for `[inner ^ e, right]`
begins with one excess-left frontier term.  The powered-commutator bridge
quotient is exactly its inverse.  After that cancellation, the bounded basic
word expansion evaluates to the original outer factor.

This file packages the first concrete bounded post-cancellation adapter.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement
open BRSpec
open PFSubsti.TAPkt

namespace PTSubsti

/-- The bounded basic expansion retained after the cutoff-four frontier cancels. -/
def classCanceledExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    SWExp H inputWeight :=
  attachedInnerExpansion hinputWeight hallPair factor innerWord
    rightWord hword left_degree_pair

@[simp]
lemma canceled_basic_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    (classCanceledExpansion hinputWeight factor innerWord
      rightWord hword).word = factor.word := by
  rw [classCanceledExpansion,
    attached_inner_expansion]
  exact hword.symm

@[simp]
lemma exponent_canceled_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    (classCanceledExpansion hinputWeight factor innerWord
      rightWord hword).exponent = factor.exponent := by
  rw [classCanceledExpansion,
    exponent_attached_expansion]
  funext q
  simp

/-- Emit ordinary bounded factors for the retained basic expansion. -/
def canceledBasicFactors
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord) :
    List (SPFactora H inputWeight) :=
  (classCanceledExpansion hinputWeight factor innerWord
    rightWord hword).factors

/-- The retained bounded factors evaluate exactly to the original outer factor. -/
lemma list_canceled_factors
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (canceledBasicFactors hinputWeight factor innerWord rightWord
          hword) =
      factor.eval q := by
  rw [canceledBasicFactors,
    SWExp.listEval_factors,
    canceled_basic_expansion,
    exponent_canceled_expansion]
  rfl

/--
At cutoff four, the classified packet followed by the bridge quotient
cancels to the retained ordinary bounded basic factors.
-/
lemma classified_canceled_factors
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hn : n ≤ 4)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SOTerm.listValue (n := n) q
          ((PFSubsti.TAPkt.n_four
            (d := d) hn :
              PFSubsti.TAPkt.{u}
                d n)
            |>.innerOuterTerms hinputWeight factor innerWord
              rightWord hword) *
        ((innerReductionExpansion hinputWeight leftTriple factor
          innerWord rightWord).value (n := n) q)⁻¹ =
      SPFactora.listEval q
        (canceledBasicFactors hinputWeight factor innerWord rightWord
          hword) := by
  rw [
    inner_reduction_terms,
    ← zpow_frontier_value
      hn hinputWeight factor innerWord rightWord q,
    list_canceled_factors]
  simp only [commutatorElement_inv]
  rw [← commutatorElement_inv
    (innerWord.eval
      (PEAddres.freeLowerTruncation (n := n)) ^
        factor.exponent q)
    (rightWord.eval
      (PEAddres.freeLowerTruncation (n := n)))]
  rw [SPFactora.eval, SPFactora.wordValue, hword,
    CWord.eval_commutator, commutatorElement_def]
  group

end PTSubsti

end TCTex
end Submission

-- Merged from ClassThreeCanceledFactorSupport.lean

/-!
# Support of cutoff-four canceled factors

After the unique cutoff-four transient frontier cancels, the retained bounded
basic expansion emits ordinary symbolic factors.  This file records the
support facts needed by an operational collector: every emitted factor has
exactly the original outer Hall word, so lower bounds and truncation-endpoint
vanishing transfer immediately.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace PTSubsti

/-- Every canceled basic factor has exactly the original outer Hall word. -/
lemma word_canceled_factors
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    {replacement : SPFactora H inputWeight}
    (hreplacement :
      replacement ∈
        canceledBasicFactors hinputWeight factor innerWord rightWord
          hword) :
    replacement.word = factor.word := by
  rw [canceledBasicFactors] at hreplacement
  exact
    ((classCanceledExpansion hinputWeight factor innerWord
      rightWord hword).of_mem_factors hreplacement).trans
        (canceled_basic_expansion hinputWeight factor
          innerWord rightWord hword)

/-- Every canceled basic factor has the original outer Hall-word weight. -/
lemma canceled_basic_factors
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    {replacement : SPFactora H inputWeight}
    (hreplacement :
      replacement ∈
        canceledBasicFactors hinputWeight factor innerWord rightWord
          hword) :
    replacement.word.weight PEAddres.weight =
      factor.word.weight PEAddres.weight := by
  rw [word_canceled_factors hinputWeight factor
    innerWord rightWord hword hreplacement]

/-- Any lower bound on the original outer word transfers to canceled factors. -/
lemma least_canceled_factors
    {d inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactor :
      lowerWeight ≤ factor.word.weight PEAddres.weight) :
    ∀ replacement ∈
        canceledBasicFactors hinputWeight factor innerWord rightWord
          hword,
      lowerWeight ≤
        replacement.word.weight PEAddres.weight := by
  intro replacement hreplacement
  rw [canceled_basic_factors hinputWeight factor
    innerWord rightWord hword hreplacement]
  exact hfactor

/-- Canceled factors evaluate in every inherited one-based lower-central layer. -/
lemma list_canceled_series
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactor :
      lowerWeight ≤ factor.word.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (canceledBasicFactors hinputWeight factor innerWord rightWord
          hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (lowerWeight - 1) := by
  exact
    SPFactora.list_series_weight q
      _ (least_canceled_factors hinputWeight
        factor innerWord rightWord hword hfactor)

/-- At or above the truncation weight, the canceled factor list is trivial. -/
lemma canceled_n_weight
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactor :
      n ≤ factor.word.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (canceledBasicFactors hinputWeight factor innerWord rightWord
          hword) = 1 := by
  exact
    SPFactora.list_n_weight q _
      (least_canceled_factors hinputWeight factor
        innerWord rightWord hword hfactor)

end PTSubsti

end TCTex
end Submission

-- Merged from ClassThreeConcreteBridgeResidual.lean

/-!
# Concrete cutoff-four powered-bridge residual

The concrete outer-residual pipeline packages the powered-commutator bridge
as an ordinary symbolic raw source.  At cutoff four, its value is exactly the
inverse value of the unique transient left-triple frontier.  Appending the
concrete correction packet therefore cancels back to the bounded retained
basic factors.

This file connects the transient calculation to that concrete raw-source API.
It is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement
open BRSpec
open PTSubsti
open PFSubsti.TAPkt

namespace IPBridge

/--
At cutoff four, the concrete powered-bridge residual is the inverse value of
the unique transient left-triple frontier.
-/
lemma inv_n_four
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hn : n ≤ 4)
    (packet :
      PFSubsti.TAPkt d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (residualRawSource packet hinputWeight factor innerWord rightWord
          hrecipe) =
      ((innerReductionExpansion hinputWeight leftTriple factor
        innerWord rightWord).value (n := n) q)⁻¹ := by
  rw [list_raw_source]
  simpa [SPFactora.eval, SPFactora.wordValue,
    hword] using
      (zpow_frontier_value
        hn hinputWeight factor innerWord rightWord q)

/--
The concrete correction packet followed by its cutoff-four bridge residual
has the same value as the bounded canceled basic factors.
-/
lemma append_canceled_basic
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hn : n ≤ 4)
    (packet :
      PFSubsti.TAPkt d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        ((correctionPacket packet hinputWeight factor innerWord rightWord
          hrecipe).factors ++
            residualRawSource packet hinputWeight factor innerWord rightWord
              hrecipe) =
      SPFactora.listEval q
        (canceledBasicFactors hinputWeight factor innerWord rightWord
          hword) := by
  rw [SPFactora.listEval_append,
    list_packet_factors,
    inv_n_four
      hn packet hinputWeight factor innerWord rightWord hword hrecipe]
  calc
    _ =
        SOTerm.listValue (n := n) q
            ((PFSubsti.TAPkt.n_four
              (d := d) hn :
                PFSubsti.TAPkt.{u}
                  d n)
              |>.innerOuterTerms hinputWeight factor
                innerWord rightWord hword) *
          ((innerReductionExpansion hinputWeight leftTriple factor
            innerWord rightWord).value (n := n) q)⁻¹ := by
      rw [inner_reduction_terms]
    _ =
        SPFactora.listEval q
          (canceledBasicFactors hinputWeight factor innerWord rightWord
            hword) :=
      classified_canceled_factors
        hn hinputWeight factor innerWord rightWord hword q

end IPBridge

namespace TSRecol

open IPBridge

/--
Reuse any recollection of the bounded canceled factors for the concrete
correction packet followed by its cutoff-four bridge residual.
-/
noncomputable def
    correction_canceled_basic
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hn : n ≤ 4)
    (packet :
      PFSubsti.TAPkt d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (canceled :
      TSRecol
        (n := n) (lowerWeight := lowerWeight) H
        (canceledBasicFactors hinputWeight factor innerWord rightWord
          hword)) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight) H
      ((correctionPacket packet hinputWeight factor innerWord rightWord
        hrecipe).factors ++
          residualRawSource packet hinputWeight factor innerWord rightWord
            hrecipe) :=
  canceled.of_list_eq fun q =>
    (append_canceled_basic
      hn packet hinputWeight factor innerWord rightWord hword hrecipe q).symm

/--
At or above the outer word's truncation weight, the concrete packet followed
by its cutoff-four bridge residual recollects to the empty source.
-/
def
    correction_append_n
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hn : n ≤ 4)
    (packet :
      PFSubsti.TAPkt d n)
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (hfactor :
      n ≤ factor.word.weight PEAddres.weight) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight) H
      ((correctionPacket packet hinputWeight factor innerWord rightWord
        hrecipe).factors ++
          residualRawSource packet hinputWeight factor innerWord rightWord
            hrecipe) where
  higherSource := []
  higher_source_truncated := by
    intro replacement hreplacement
    simp at hreplacement
  higher_weight_least := by
    intro replacement hreplacement
    simp at hreplacement
  list_higher_raw := by
    intro q
    rw [
      append_canceled_basic
        hn packet hinputWeight factor innerWord rightWord hword hrecipe,
      canceled_n_weight
        hinputWeight factor innerWord rightWord hword hfactor]
    rfl

end TSRecol

end TCTex
end Submission

-- Merged from ClassThreeConcreteOuterResidual.lean

/-!
# Concrete cutoff-four outer residual

At cutoff four, the transient left-triple frontier cancels against the
powered-commutator bridge residual.  The full powered outer decomposition can
therefore be replaced by an ordinary source: the inverse child packet followed
by the bounded retained basic factors.

This file lifts the local cancellation adapter through the concrete
child-to-parent residual pipeline.  It is intentionally not imported by the
existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HEWord
open PTSubsti
open IPBridge

namespace HEWord

/--
Ordinary bounded child-to-parent residual after the cutoff-four transient
frontier has canceled.
-/
noncomputable def innerCanceledSource
    {d inputWeight : ℕ}
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  SPFactora.inverseList
      (innerOuterFactors factor innerWord rightWord hword) ++
    canceledBasicFactors hinputWeight factor innerWord rightWord hword

/--
The bounded canceled residual evaluates exactly like the existing concrete
child-to-parent residual.
-/
theorem
    inner_canceled_source
    {d n inputWeight : ℕ}
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerCanceledSource hinputWeight
          factor innerWord rightWord hword) =
      SPFactora.listEval q
        (innerRawSource factor innerWord rightWord
          hword) := by
  rw [innerCanceledSource,
    SPFactora.listEval_append,
    SPFactora.list_eval_inverse,
    list_canceled_factors,
    inner_raw_source]

/--
At cutoff four, the powered outer decomposition evaluates exactly like its
ordinary bounded canceled residual.
-/
theorem
    powered_decomposition_canceled
    {d n inputWeight : ℕ}
    (hn : n ≤ 4)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerPoweredDecomposition packet
          hinputWeight factor innerWord rightWord hword hrecipe) =
      SPFactora.listEval q
        (innerCanceledSource hinputWeight
          factor innerWord rightWord hword) := by
  rw [innerPoweredDecomposition,
    innerPoweredComparison, List.append_assoc,
    innerCanceledSource,
    SPFactora.listEval_append,
    append_canceled_basic
      hn packet hinputWeight factor innerWord rightWord hword hrecipe,
    SPFactora.listEval_append]

end HEWord

namespace TSRecol

/--
Reuse a recollection of the bounded canceled source for the existing concrete
child-to-parent residual.
-/
noncomputable def
    inner_reduction_canceled
    {d n inputWeight lowerWeight : ℕ}
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (canceled :
      TSRecol
        (n := n) (lowerWeight := lowerWeight)
        (concreteBasicCommutators.{u} d)
        (HEWord.innerCanceledSource
          hinputWeight factor innerWord rightWord hword)) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerRawSource
        factor innerWord rightWord hword) :=
  canceled.of_list_eq fun q =>
    inner_canceled_source
      hinputWeight factor innerWord rightWord hword q

/--
Reuse a recollection of the bounded canceled source for the powered
decomposition which produced it.
-/
noncomputable def
    inner_powered_canceled
    {d n inputWeight lowerWeight : ℕ}
    (hn : n ≤ 4)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (canceled :
      TSRecol
        (n := n) (lowerWeight := lowerWeight)
        (concreteBasicCommutators.{u} d)
        (HEWord.innerCanceledSource
          hinputWeight factor innerWord rightWord hword)) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerPoweredDecomposition
        packet hinputWeight factor innerWord rightWord hword hrecipe) :=
  canceled.of_list_eq fun q =>
    (powered_decomposition_canceled
      hn packet hinputWeight factor innerWord rightWord hword hrecipe q).symm

end TSRecol

end TCTex
end Submission

-- Merged from ClassThreeConcreteOuterResidualSupport.lean

/-!
# Support of the concrete cutoff-four canceled outer residual

After the unique transient left-triple frontier cancels, the concrete outer
residual is represented by an ordinary bounded source: inverse Hall children
followed by retained basic factors.  This file proves the physical and
lower-central support facts needed to feed that source back into the ordinary
semantic normalizer.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open PTSubsti

namespace HEWord

/-- The bounded canceled residual inherits physical truncation from its parent. -/
theorem truncated_inner_canceled
    {d n inputWeight : ℕ}
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (innerCanceledSource hinputWeight factor
        innerWord rightWord hword) := by
  intro replacement hreplacement
  rw [innerCanceledSource] at hreplacement
  rcases List.mem_append.mp hreplacement with hreplacement | hreplacement
  · exact
      SPFactora.truncated_inverse_list
        (truncated_inner_factors factor innerWord rightWord hword
          hfactorTruncated) replacement hreplacement
  · rw [word_canceled_factors hinputWeight factor
      innerWord rightWord hword hreplacement]
    exact hfactorTruncated

/-- Every bounded canceled residual factor remains in the parent word stratum. -/
theorem least_inner_canceled
    {d inputWeight : ℕ}
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    SPFactora.WordWeightLeast
      (factor.word.weight PEAddres.weight)
      (innerCanceledSource hinputWeight factor
        innerWord rightWord hword) := by
  intro replacement hreplacement
  rw [innerCanceledSource] at hreplacement
  rcases List.mem_append.mp hreplacement with hreplacement | hreplacement
  · exact
      SPFactora.least_inverse_list
        (least_inner_factors factor innerWord
          rightWord hword) replacement hreplacement
  · exact
      least_canceled_factors hinputWeight factor
        innerWord rightWord hword (Nat.le_refl _) replacement hreplacement

/-- The bounded canceled residual still evaluates one lower-central layer deeper. -/
theorem
    inner_canceled_series
    {d n inputWeight : ℕ}
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerCanceledSource hinputWeight factor
          innerWord rightWord hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight PEAddres.weight) := by
  rw [
    inner_canceled_source]
  exact
    inner_reduction_series
      factor innerWord rightWord hword q

end HEWord

namespace TSNormalb

open HEWord
open TSRecol

/--
An ordinary current-stratum normalizer recollects the bounded canceled residual
into the next support stratum.
-/
noncomputable def
    recollection_canceled_raw
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight + 1)
      (concreteBasicCommutators.{u} d)
      (innerCanceledSource hinputWeight factor
        innerWord rightWord hword) :=
  normalizer.source_recollection_series hn
    (concreteBasicCommutators.{u} d) hH
    (innerCanceledSource hinputWeight factor
      innerWord rightWord hword)
    hlowerWeightPos hlowerWeightTruncated
    (truncated_inner_canceled
      hinputWeight factor innerWord rightWord hword (by
        rw [hfactorWeight]
        exact hlowerWeightTruncated))
    (by
      rw [← hfactorWeight]
      exact
        least_inner_canceled
          hinputWeight factor innerWord rightWord hword)
    (fun q => by
      rw [← hfactorWeight]
      exact
        inner_canceled_series
          hinputWeight factor innerWord rightWord hword q)

/--
Expose the existing concrete outer residual through the bounded cutoff-four
canceled source.
-/
noncomputable def
    recollection_inner_canceled
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight + 1)
      (concreteBasicCommutators.{u} d)
      (innerRawSource factor innerWord rightWord
        hword) :=
  inner_reduction_canceled
    hinputWeight factor innerWord rightWord hword
    (normalizer.recollection_canceled_raw
      hn hH hinputWeight factor innerWord rightWord hword hfactorWeight
        hlowerWeightPos hlowerWeightTruncated)

/--
At cutoff four, expose the powered residual decomposition through the same
bounded canceled source.
-/
noncomputable def
    recollection_powered_canceled
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight + 1)
      (concreteBasicCommutators.{u} d)
      (innerPoweredDecomposition packet
        hinputWeight factor innerWord rightWord hword hrecipe) :=
  inner_powered_canceled
    hn4 packet hinputWeight factor innerWord rightWord hword hrecipe
    (normalizer.recollection_canceled_raw
      hn hH hinputWeight factor innerWord rightWord hword hfactorWeight
        hlowerWeightPos hlowerWeightTruncated)

end TSNormalb

end TCTex
end Submission

-- Merged from ClassThreeConcreteOuterResidualFamilyRouting.lean

/-!
# Family routing for the cutoff-four canceled outer residual

A normalizer family already contains the current-stratum normalizer required
by the bounded cutoff-four canceled residual.  This file selects that stratum
at the original factor's Hall-word weight and exposes the resulting
next-stratum recollections through the ordinary outer-residual interfaces.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HEWord

namespace SSNormala

/-- Select the factor-weight normalizer for the bounded canceled residual. -/
noncomputable def
    recollection_canceled_residual
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
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (innerCanceledSource hinputWeight factor
        innerWord rightWord hword) :=
  (family.normalizer (factor.word.weight PEAddres.weight))
    |>.recollection_canceled_raw
      hn hH hinputWeight factor innerWord rightWord hword rfl
        factor.word_weight_pos hfactorTruncated

/-- Route the ordinary outer residual through its bounded canceled source. -/
noncomputable def
    recollection_outer_canceled
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
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (innerRawSource factor innerWord rightWord
        hword) :=
  (family.normalizer (factor.word.weight PEAddres.weight))
    |>.recollection_inner_canceled
      hn hH hinputWeight factor innerWord rightWord hword rfl
        factor.word_weight_pos hfactorTruncated

/-- Route the cutoff-four powered decomposition through its bounded source. -/
noncomputable def
    recollection_powered_canceled
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
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
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRecol
      (n := n)
      (lowerWeight :=
        factor.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (innerPoweredDecomposition packet
        hinputWeight factor innerWord rightWord hword hrecipe) :=
  (family.normalizer (factor.word.weight PEAddres.weight))
    |>.recollection_powered_canceled
      hn hn4 hH packet hinputWeight factor innerWord rightWord hword hrecipe rfl
        factor.word_weight_pos hfactorTruncated

end SSNormala

end TCTex
end Submission

-- Merged from ClassThreeConcreteOuterResidualTerminal.lean

/-!
# Terminal cutoff-four canceled outer residuals

In the Hall-ranked inner-reduction branch, the inner word is itself a
commutator.  The enclosing parent therefore has word weight at least three.
At cutoff four its semantically next-stratum residual vanishes.

This file applies that observation to the bounded canceled residual and
transports the resulting empty recollection back to the ordinary outer
residual and its powered decomposition.  It is intentionally not imported by
the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HEWord

namespace HEWord

/-- A bracket whose left child is itself a bracket has weight at least three. -/
theorem four_tree_commutator
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (added originalRight : HallTree (FreeGenerator.{u} d))
    (hinnerTree : tree innerWord = .commutator added originalRight) :
    4 ≤ factor.word.weight PEAddres.weight + 1 := by
  have hadd := added.weight_pos
  have horiginalRight := originalRight.weight_pos
  have hright :=
    CWord.weight_pos PEAddres.weight
      PEAddres.weight_pos rightWord
  rw [hword, CWord.weight_commutator, ← tree_weight innerWord,
    hinnerTree, HallTree.weight_commutator]
  omega

/--
At cutoff four, the bounded canceled residual of a nested inner reduction
evaluates trivially.
-/
theorem
    canceled_tree_commutator
    {d n inputWeight : ℕ}
    (hn4 : n ≤ 4)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (added originalRight : HallTree (FreeGenerator.{u} d))
    (hinnerTree : tree innerWord = .commutator added originalRight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerCanceledSource hinputWeight
          factor innerWord rightWord hword) =
      1 := by
  apply eq_bot_iff.mp
    SPFactora.trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (by
    have hweight :=
      four_tree_commutator factor innerWord
        rightWord hword added originalRight hinnerTree
    omega)
    (inner_canceled_series
      hinputWeight factor innerWord rightWord hword q)

end HEWord

namespace TSRecol

/--
The bounded canceled residual of a nested cutoff-four inner reduction
recollects to the empty source without a parent-stratum normalizer.
-/
def
    canceled_inner_tree
    {d n inputWeight lowerWeight : ℕ}
    (hn4 : n ≤ 4)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (added originalRight : HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      HEWord.tree innerWord =
        .commutator added originalRight) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerCanceledSource
        hinputWeight factor innerWord rightWord hword) where
  higherSource := []
  higher_source_truncated := by
    intro replacement hreplacement
    simp at hreplacement
  higher_weight_least := by
    intro replacement hreplacement
    simp at hreplacement
  list_higher_raw := by
    intro q
    simpa using
      (canceled_tree_commutator
        hn4 hinputWeight factor innerWord rightWord hword added originalRight
          hinnerTree q).symm

/--
The ordinary nested outer residual recollects to the empty source through the
bounded canceled residual, without a parent-stratum normalizer.
-/
def
    inner_tree_commutator
    {d n inputWeight lowerWeight : ℕ}
    (hn4 : n ≤ 4)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (added originalRight : HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      HEWord.tree innerWord =
        .commutator added originalRight) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerRawSource
        factor innerWord rightWord hword) :=
  inner_reduction_canceled
    hinputWeight factor innerWord rightWord hword
      (canceled_inner_tree
        hn4 hinputWeight factor innerWord rightWord hword added originalRight
          hinnerTree)

/--
The powered nested outer decomposition also recollects to the empty source
through the bounded canceled residual.
-/
def
    powered_decomposition_tree
    {d n inputWeight lowerWeight : ℕ}
    (hn4 : n ≤ 4)
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hrecipe :
      factor.recipe.outputWeight ≤
        innerWord.weight PEAddres.weight)
    (added originalRight : HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      HEWord.tree innerWord =
        .commutator added originalRight) :
    TSRecol
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d)
      (HEWord.innerPoweredDecomposition
        packet hinputWeight factor innerWord rightWord hword hrecipe) :=
  inner_powered_canceled
    hn4 packet hinputWeight factor innerWord rightWord hword hrecipe
      (canceled_inner_tree
        hn4 hinputWeight factor innerWord rightWord hword added originalRight
          hinnerTree)

end TSRecol

end TCTex
end Submission

-- Merged from ClassThreeRankedRouting.lean

/-!
# Ranked routing for cutoff-four canceled inner-reduction residuals

At cutoff four, the nested inner-reduction branch no longer needs a
parent-stratum semantic normalizer or an outer-residual factory.  Recursive
children normalize through the active-atomic comparison router, while the
child-to-parent quotient vanishes through the bounded canceled residual.

This file compiles that non-circular local branch into the ranked scheduler
interface.  It is intentionally not imported by the existing collection
proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open HEWord
open TSRecol

namespace
  TSRecollb

/--
Recollect a nested cutoff-four inner-reduction residual using only sharp
comparison routing and a strictly deeper normalizer.
-/
noncomputable def
    ranked_residuals_canceled
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)
            (factor.word.weight PEAddres.weight))
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight)
              (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight + 1)
              (concreteBasicCommutators.{u} d))
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree : tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (residual :
      ∀ task ∈
          CIChildr.rankedTasks
            factor innerWord rightWord hword unchanged,
        TSRecollb
          (n := n) task.1) :
    TSRecollb
      (n := n) factor := by
  let children :=
    CIChildr.atoms_recollect_residuals
      factor innerWord rightWord hword hfactorTruncated added originalRight
        unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
          hunchangedBasic residual
  let comparison :=
    factory.child_normalized_raw
      hn hH factor sharp nextNormalizer innerWord rightWord hword
        hfactorTruncated children
  let outer :
      TSRecol
        (n := n)
        (lowerWeight :=
          factor.word.weight PEAddres.weight + 1)
        (concreteBasicCommutators.{u} d)
        (innerRawSource factor innerWord rightWord
          hword) :=
    inner_tree_commutator
      hn4 hinputWeight factor innerWord rightWord hword added originalRight
        hinnerTree
  exact
    inner_child_normalization factor innerWord rightWord
      hword children.recollection
      (by
        simpa only [
          innerChildNormalized] using
            comparison)
      outer

/--
Scheduler-facing specialization over the exact ranked task source emitted by
the nested cutoff-four branch.
-/
noncomputable def
    task_residuals_canceled
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (hinputWeight : 0 < inputWeight)
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d)
            (factor.word.weight PEAddres.weight))
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight)
              (concreteBasicCommutators.{u} d))
    (nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            factor.word.weight PEAddres.weight + 1)
              (concreteBasicCommutators.{u} d))
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree : tree innerWord = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic)
    (residual :
      ∀ task ∈
          (CIChildr.rankedTaskSource
            (n := n) factor innerWord rightWord hword added originalRight
              unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
                hunchangedBasic).tasks,
        TSRecollb
          (n := n) task.1) :
    TSRecollb
      (n := n) factor :=
  ranked_residuals_canceled
    hn hn4 hH hinputWeight factor factory sharp nextNormalizer innerWord
      rightWord hword hfactorTruncated added originalRight unchanged
        originalLeft hinnerTree hRightLeft hRightUnchanged hunchangedBasic
          (fun task htask => residual task (by simpa using htask))

end
  TSRecollb

/--
Non-circular local routing inputs for the cutoff-four concrete ranked
collector.  Every normalizer is selected strictly above the active factor.
-/
structure RRData
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

namespace RRData

/--
A correction schedule and strictly deeper normalizers supply all local
cutoff-four routing inputs.
-/
noncomputable def factoryNormalizerAbove
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
                (concreteBasicCommutators.{u} d)) :
    RRData
      (d := d) (n := n) (inputWeight := inputWeight) where
  factory factor :=
    schedule.factory (factor.word.weight PEAddres.weight)
  sharp factor :=
    SSNormal.ofNormalizerAbove
      (normalizerAbove (factor.word.weight PEAddres.weight))
  nextNormalizer factor :=
    normalizerAbove
      (factor.word.weight PEAddres.weight)
      (factor.word.weight PEAddres.weight + 1) (by omega)

end RRData

namespace RRBrancha

open
  TSRecollb

/-- Compile one indexed nested cutoff-four inner-reduction case. -/
noncomputable def innerCanceledCase
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (hinputWeight : 0 < inputWeight)
    (routing :
      RRData
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
    {
      children :=
        CIChildr.rankedTaskSource
          (n := n) factor innerWord rightWord hword added originalRight
            unchanged originalLeft hinnerTree hRightLeft hRightUnchanged
              hunchangedBasic
      recollect := fun residual =>
        task_residuals_canceled
          hn hn4 hH hinputWeight factor (routing.factory factor)
            (routing.sharp factor) (routing.nextNormalizer factor) innerWord
              rightWord hword hfactorTruncated added originalRight unchanged
                originalLeft hinnerTree hRightLeft hRightUnchanged
                  hunchangedBasic residual
    }

/-- Compile either a leaf or a nested cutoff-four local case. -/
noncomputable def classCanceledCase
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (hinputWeight : 0 < inputWeight)
    (routing :
      RRData
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
        innerCanceledCase hn hn4 hH hinputWeight routing
          factor rankDefect innerCase

end RRBrancha

namespace
  RRSchedua

/--
Compile classified cutoff-four local cases into a global Hall-ranked residual
scheduler without a parent-stratum normalizer.
-/
noncomputable def classCanceledCases
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (hinputWeight : 0 < inputWeight)
    (routing :
      RRData
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
    RRBrancha.classCanceledCase
      hn hn4 hH hinputWeight routing factor rankDefect
        (cases factor rankDefect)

/--
Run Hall-ranked residual recursion directly from classified cutoff-four local
cases and non-circular routing data.
-/
noncomputable def recollection_canceled_cases
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (hinputWeight : 0 < inputWeight)
    (routing :
      RRData
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
  (classCanceledCases hn hn4 hH hinputWeight routing cases)
    |>.residualRecollection factor rankDefect

end
  RRSchedua

end TCTex
end Submission
