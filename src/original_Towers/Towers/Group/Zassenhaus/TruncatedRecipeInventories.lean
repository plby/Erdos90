import Towers.Group.Zassenhaus.AtomParentHistories
import Towers.Group.Zassenhaus.FamilyOperationalSupport
import Towers.Group.Zassenhaus.PositiveDegreeRecipes

/-!
# Exact recipe inventories for truncated inverse raw histories

The cutoff raw-history packet retains the genuine operational order of the
inverse trace.  The indexed raw family terms retain the exact realization-slot
inventory needed by later polynomial compression.  Weighted Hall degree
depends only on the labelled word after collapse, so cutoff filtering agrees
on both presentations.

This file packages the shared retained endpoint: one finite ordered list with
quotient semantics and one complete multiplicity-preserving family inventory.
The endpoint is still precollection: equal erased shapes need not yet occur in
canonical adjacent blocks.  It is intentionally not imported by the existing
collection proof.
-/

namespace Towers
namespace TCTex
namespace RRTrunc

open scoped commutatorElement

open HACoeff
open BFTrunc
open BRSpec
open ICFilter
open IMPropag
open OCPartit
open RHRecurs
open RHRecipe
open HHTrunc

/-- A decorated family term has the weighted degree of its concrete word. -/
lemma decorated_family_term
    {M N K leftWeight rightWeight : ℕ}
    (term : DFTerm M N K) :
    decoratedFamilyWeight leftWeight rightWeight term =
      (collapseWord term.decorated.word).weight
        (HPAtom.weight leftWeight rightWeight) := by
  rw [decoratedFamilyWeight, weightedWordWeight,
    ← term.erased_shape_family]
  rfl

/-- Filtering exact histories commutes with forgetting history provenance. -/
lemma history_retained_histories
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (histories : List (RHistor M N)) :
    historyWords (retainedHistories n leftWeight rightWeight histories) =
      (historyWords histories).filter fun word =>
        decide
          ((collapseWord word).weight
            (HPAtom.weight leftWeight rightWeight) < n) := by
  rw [historyWords, retainedHistories, historyWords, List.filter_map]
  rfl

/-- Filtering indexed family terms commutes with forgetting family provenance. -/
lemma decorated_below_terms
    {M N K : ℕ}
    (n leftWeight rightWeight : ℕ)
    (terms : List (DFTerm M N K)) :
    decoratedFamilyList
        (belowCutoffTerms n leftWeight rightWeight terms) =
      (decoratedFamilyList terms).filter fun word =>
        decide
          ((collapseWord word).weight
            (HPAtom.weight leftWeight rightWeight) < n) := by
  rw [decoratedFamilyList, belowCutoffTerms,
    decoratedFamilyList, List.filter_map]
  simp_rw [decorated_family_term]
  rfl

/-- Indexed raw recipe occurrences retained below the quotient cutoff. -/
noncomputable def retainedRawTerms
    (M N n leftWeight rightWeight : ℕ) :
    List (DFTerm M N
      (inverseLabelledCollection M N).factors.length) :=
  belowCutoffTerms n leftWeight rightWeight
    (inverseDecoratedTerms M N)

/--
The cutoff-filtered history presentation and cutoff-filtered indexed recipe
presentation retain exactly the same ordered labelled words.
-/
lemma history_words_histories
    (M N n leftWeight rightWeight : ℕ) :
    historyWords
        (retainedHistories n leftWeight rightWeight
          (inverseRawHistories M N)) =
      decoratedFamilyList
        (retainedRawTerms M N n leftWeight rightWeight) := by
  rw [history_retained_histories,
    retainedRawTerms, decorated_below_terms,
    historyWords,
    raw_histories_decorated]

/-- The retained indexed raw recipe occurrences form a complete family inventory. -/
noncomputable def multiplicityInventoryBlock
    (M N n leftWeight rightWeight : ℕ) :
    MIBlock
      (retainedRawTerms M N n leftWeight rightWeight) :=
  MIBlock.filterBelowCutoff
    (MIBlock.inverseRaw M N)
      n leftWeight rightWeight

/-- Every retained raw family has weighted Hall degree below the cutoff. -/
lemma block_raw_families
    {M N n leftWeight rightWeight : ℕ}
    {family : BFam M N}
    (hfamily :
      family ∈
        (multiplicityInventoryBlock
          M N n leftWeight rightWeight).families) :
    blockFamilyWeight leftWeight rightWeight family < n :=
  MIBlock.filter_below_cutoff
    (MIBlock.inverseRaw M N) hfamily

/--
Finite cutoff packet carrying both exact inverse-history order and complete
family-slot inventory.
-/
structure TruncatedRawPacket
    (M N n leftWeight rightWeight : ℕ) where
  histories :
    List (RHistor M N)
  terms :
    List (DFTerm M N
      (inverseLabelledCollection M N).factors.length)
  histories_eq :
    histories =
      retainedHistories n leftWeight rightWeight (inverseRawHistories M N)
  terms_eq :
    terms = retainedRawTerms M N n leftWeight rightWeight
  history_words_term :
    historyWords histories = decoratedFamilyList terms
  inventory :
    MIBlock terms
  history_weight_cutoff :
    ∀ history ∈ histories,
      RHistor.weight leftWeight rightWeight history < n
  term_weight_cutoff :
    ∀ term ∈ terms,
      decoratedFamilyWeight leftWeight rightWeight term < n
  collapsed_list_eval :
    ∀ {G : Type*} [Group G]
      (x y : G),
      x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1) →
      y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1) →
      Subgroup.lowerCentralSeries G (n - 1) = ⊥ →
      collapsedList x y (decoratedFamilyList terms) =
        ⁅x ^ M, y ^ N⁆

/-- Canonical retained indexed-recipe endpoint of the genuine raw inverse trace. -/
noncomputable def truncatedRawPacket
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    TruncatedRawPacket M N n leftWeight rightWeight := by
  let rawPacket :=
    truncatedHistoryPacket
      M N n leftWeight rightWeight hleftWeight hrightWeight
  exact {
    histories := rawPacket.histories
    terms := retainedRawTerms M N n leftWeight rightWeight
    histories_eq := rawPacket.histories_eq
    terms_eq := rfl
    history_words_term := by
      rw [rawPacket.histories_eq]
      exact
        history_words_histories
          M N n leftWeight rightWeight
    inventory :=
      multiplicityInventoryBlock M N n leftWeight rightWeight
    history_weight_cutoff := rawPacket.weight_lt_cutoff
    term_weight_cutoff := by
      intro term hterm
      exact (below_cutoff_terms.mp hterm).2
    collapsed_list_eval := by
      intro G _ x y hx hy hbot
      rw [← history_words_histories,
        ← rawPacket.histories_eq]
      exact rawPacket.collapsed_list_eval x y hx hy hbot }

end RRTrunc
end TCTex
end Towers

/-!
# Multiplicity-independent source recipes for the inverse raw trace

The inverse raw trace is built from concrete source labels, but every retained
word is standardized to a one-block `LRecipe` before the positive-family
collector starts.  This file packages that standardized source recipe without
retaining the ambient source multiplicities and records its exact weighted
degree.

A finite cutoff vocabulary is obtained by running the raw trace once at a
cutoff-sized dummy multiplicity.  Coverage of arbitrary retained traces by
that vocabulary is proved separately.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace RRVocabu

open HACoeff
open BRSpec
open RHRecurs
open RHRecipe
open HHTrunc

/-- Standardization does not change the erased Hall-pair word. -/
@[simp]
lemma erased_label_linear
    {M N : ℕ}
    (w : CWord (LabelledAtom M N))
    (hpositive : (collapseWord w).PBPos)
    (hlinear : LabelLinear w) :
    (LRecipe.ofLabelLinear w hpositive hlinear).erasedShape =
      collapseWord w := by
  simp [LRecipe.ofLabelLinear, LRecipe.erasedShape]

/-- Standardizing an order-preserving realization preserves its left degree. -/
@[simp]
lemma LRecipe.left_degre_linin
    {M N : ℕ}
    (R : LRecipe)
    (left : Fin R.leftDegree ↪o Fin M)
    (right : Fin R.rightDegree ↪o Fin N) :
    (LRecipe.ofLabelLinear (R.instantiate left right)
      (by simpa using R.positive)
      (label_linear_relabel left.toEmbedding right.toEmbedding R.linear)).leftDegree =
        R.leftDegree := by
  simp only [LRecipe.ofLabelLinear, LRecipe.instantiate]
  rw [label_support_relabel left right, R.left_support_full,
    Finset.card_image_iff.mpr left.injective.injOn]
  simp

/-- Standardizing an order-preserving realization preserves its right degree. -/
@[simp]
lemma LRecipe.right_degre_linin
    {M N : ℕ}
    (R : LRecipe)
    (left : Fin R.leftDegree ↪o Fin M)
    (right : Fin R.rightDegree ↪o Fin N) :
    (LRecipe.ofLabelLinear (R.instantiate left right)
      (by simpa using R.positive)
      (label_linear_relabel left.toEmbedding right.toEmbedding R.linear)).rightDegree =
        R.rightDegree := by
  simp only [LRecipe.ofLabelLinear, LRecipe.instantiate]
  rw [label_relabel_image left right, R.right_support_full,
    Finset.card_image_iff.mpr right.injective.injOn]
  simp

/--
One standardized source recipe arising from the raw inverse trace.  The
ambient multiplicities have disappeared: membership is checked in the
minimal labelled trace determined by the recipe's own support degrees.
-/
structure IRecipe where
  linear :
    LRecipe
  mem_trace :
    linear.word ∈
      inverseLeftTrace
        (labelledLeftAtoms linear.leftDegree linear.rightDegree)
        (labelledRightAtoms linear.leftDegree linear.rightDegree)

namespace IRecipe

/-- Regard a standardized raw source recipe as a positive one-block recipe. -/
def blockRecipe
    (R : IRecipe) :
    BRecipe :=
  BRecipe.ofLinear R.linear

/-- Weighted degree of one multiplicity-independent source recipe. -/
def weight
    (leftWeight rightWeight : ℕ)
    (R : IRecipe) :
    ℕ :=
  weightedWordWeight leftWeight rightWeight R.blockRecipe

/--
Two raw source representatives carry the same symbolic one-block factor data.
They may use different placeholder alphabets internally.
-/
def PolynomialEquivalent
    (R S : IRecipe) :
    Prop :=
  R.blockRecipe.leftBlocks = S.blockRecipe.leftBlocks ∧
    R.blockRecipe.rightBlocks = S.blockRecipe.rightBlocks ∧
      R.blockRecipe.erasedShape = S.blockRecipe.erasedShape

@[refl]
lemma polynomialEquivalent_refl
    (R : IRecipe) :
    PolynomialEquivalent R R :=
  ⟨rfl, rfl, rfl⟩

@[symm]
lemma polynomialEquivalent_symm
    {R S : IRecipe}
    (h : PolynomialEquivalent R S) :
    PolynomialEquivalent S R :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

@[trans]
lemma polynomialEquivalent_trans
    {R S T : IRecipe}
    (hRS : PolynomialEquivalent R S)
    (hST : PolynomialEquivalent S T) :
    PolynomialEquivalent R T :=
  ⟨hRS.1.trans hST.1, hRS.2.1.trans hST.2.1,
    hRS.2.2.trans hST.2.2⟩

/-- Polynomial-equivalent source recipes have equal symbolic coefficients. -/
lemma coeff_poly_equivalent
    {R S : IRecipe}
    (h : PolynomialEquivalent R S)
    (leftExponent rightExponent : ℤ) :
    coefficientValue R.blockRecipe leftExponent rightExponent =
      coefficientValue S.blockRecipe leftExponent rightExponent := by
  simp only [coefficientValue]
  rw [h.1, h.2.1]

/-- Polynomial-equivalent source recipes have equal weighted degree. -/
lemma weight_poly_equivalent
    {leftWeight rightWeight : ℕ}
    {R S : IRecipe}
    (h : PolynomialEquivalent R S) :
    R.weight leftWeight rightWeight =
      S.weight leftWeight rightWeight := by
  rw [weight, weight, weightedWordWeight, weightedWordWeight, h.2.2]

/-- Raw-source equivalence is the general block-recipe polynomial relation. -/
lemma block_recipe_equivalent
    {R S : IRecipe}
    (h : PolynomialEquivalent R S) :
    RPEquiv.BRecipe.PolynomialEquivalent
      R.blockRecipe S.blockRecipe :=
  h

/--
Embed one minimal source recipe into a larger labelled inverse trace and
standardize the resulting realization.
-/
noncomputable def instantiate
    {M N : ℕ}
    (R : IRecipe)
    (left : Fin R.linear.leftDegree ↪o Fin M)
    (right : Fin R.linear.rightDegree ↪o Fin N) :
    IRecipe where
  linear :=
    LRecipe.ofLabelLinear (R.linear.instantiate left right)
      (by simpa using R.linear.positive)
      (label_linear_relabel left.toEmbedding right.toEmbedding R.linear.linear)
  mem_trace :=
    LRecipe.labellinword_meminvleft_rigtralabato
      (R.linear.instantiate left right)
      (by simpa using R.linear.positive)
      (label_linear_relabel left.toEmbedding right.toEmbedding R.linear.linear)
      (LRecipe.instme_leftr_labea
        R.linear R.mem_trace left right)

/-- Enlarging the ambient dummy trace preserves the symbolic source factor. -/
lemma polynomia_instanti
    {M N : ℕ}
    (R : IRecipe)
    (left : Fin R.linear.leftDegree ↪o Fin M)
    (right : Fin R.linear.rightDegree ↪o Fin N) :
    PolynomialEquivalent (R.instantiate left right) R := by
  constructor
  · simp [instantiate, blockRecipe, BRecipe.ofLinear]
  constructor
  · simp [instantiate, blockRecipe, BRecipe.ofLinear]
  · simp [instantiate, blockRecipe, BRecipe.erased_shape_linear]

end IRecipe

namespace RHistor

/--
Standardize one actual raw inverse history and forget its ambient source
multiplicities.
-/
noncomputable def initialRecipe
    {M N : ℕ}
    (history : RHistor M N)
    (hhistory : history ∈ inverseRawHistories M N) :
    IRecipe where
  linear :=
    LRecipe.ofLabelLinear history.word
      (RHRecipe.RHistor.positive_raw_histories
        hhistory)
      (RHRecipe.RHistor.inverse_raw_histories
        hhistory)
  mem_trace :=
    LRecipe.labellinword_meminvleft_rigtralabato
      history.word
      (RHRecipe.RHistor.positive_raw_histories
        hhistory)
      (RHRecipe.RHistor.inverse_raw_histories
        hhistory)
      (inverse_labelled_histories hhistory)

@[simp]
lemma block_recipe_initial
    {M N : ℕ}
    (history : RHistor M N)
    (hhistory : history ∈ inverseRawHistories M N) :
    (initialRecipe history hhistory).blockRecipe =
      (RHRecipe.RHistor.initialFamily
        history hhistory).recipe :=
  rfl

/--
The standardized one-block recipe has exactly the weighted degree of its raw
history word.
-/
lemma initial_recipe_weight
    {M N leftWeight rightWeight : ℕ}
    (history : RHistor M N)
    (hhistory : history ∈ inverseRawHistories M N) :
    (initialRecipe history hhistory).weight leftWeight rightWeight =
      HHTrunc.RHistor.weight
        leftWeight rightWeight history := by
  rw [IRecipe.weight, IRecipe.blockRecipe,
    initialRecipe, weightedWordWeight, BRecipe.erased_shape_linear,
    erased_label_linear]
  rfl

end RHistor

/--
Finite multiplicity-independent source vocabulary read from one dummy inverse
trace.
-/
noncomputable def initialRecipes
    (dummyMultiplicity : ℕ) :
    List IRecipe :=
  (inverseRawHistories dummyMultiplicity dummyMultiplicity).attach.map
    fun history =>
      RRVocabu.RHistor.initialRecipe
        history.1 history.2

/-- Keep only dummy source recipes whose weighted words survive the cutoff. -/
noncomputable def retainedInitialRecipes
    (dummyMultiplicity n leftWeight rightWeight : ℕ) :
    List IRecipe :=
  (initialRecipes dummyMultiplicity).filter fun recipe =>
    decide (recipe.weight leftWeight rightWeight < n)

@[simp]
lemma retained_initial_recipes
    {dummyMultiplicity n leftWeight rightWeight : ℕ}
    {recipe : IRecipe} :
    recipe ∈
        retainedInitialRecipes dummyMultiplicity n leftWeight rightWeight ↔
      recipe ∈ initialRecipes dummyMultiplicity ∧
        recipe.weight leftWeight rightWeight < n := by
  simp [retainedInitialRecipes]

/-- The retained source vocabulary consists only of below-cutoff recipes. -/
lemma weight_initial_recipes
    {dummyMultiplicity n leftWeight rightWeight : ℕ}
    {recipe : IRecipe}
    (hrecipe :
      recipe ∈
        retainedInitialRecipes dummyMultiplicity n leftWeight rightWeight) :
    recipe.weight leftWeight rightWeight < n :=
  (retained_initial_recipes.mp hrecipe).2

/--
Every below-cutoff raw inverse history is represented, up to symbolic
one-block factor data, by the finite cutoff-sized dummy vocabulary.
-/
lemma equivalent_initial_recipes
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (history : RHistor M N)
    (hhistory : history ∈ inverseRawHistories M N)
    (hweight :
      HHTrunc.RHistor.weight
        leftWeight rightWeight history < n) :
    ∃ recipe ∈ retainedInitialRecipes n n leftWeight rightWeight,
      IRecipe.PolynomialEquivalent recipe
        (RRVocabu.RHistor.initialRecipe
          history hhistory) := by
  let source :=
    RRVocabu.RHistor.initialRecipe
      history hhistory
  have hsourceWeight : source.weight leftWeight rightWeight < n := by
    simpa [source] using
      RRVocabu.RHistor.initial_recipe_weight
        history hhistory ▸ hweight
  have hweightFormula :
      source.weight leftWeight rightWeight =
        source.linear.leftDegree * leftWeight +
          source.linear.rightDegree * rightWeight := by
    simp [IRecipe.weight, IRecipe.blockRecipe,
      weighted_word_weight, BRecipe.leftDegree, BRecipe.rightDegree,
      BRecipe.ofLinear]
  have hleftDegree : source.linear.leftDegree < n := by
    have hle :
        source.linear.leftDegree ≤
          source.linear.leftDegree * leftWeight :=
      Nat.le_mul_of_pos_right source.linear.leftDegree hleftWeight
    omega
  have hrightDegree : source.linear.rightDegree < n := by
    have hle :
        source.linear.rightDegree ≤
          source.linear.rightDegree * rightWeight :=
      Nat.le_mul_of_pos_right source.linear.rightDegree hrightWeight
    omega
  let left : Fin source.linear.leftDegree ↪o Fin n :=
    Fin.castLEOrderEmb hleftDegree.le
  let right : Fin source.linear.rightDegree ↪o Fin n :=
    Fin.castLEOrderEmb hrightDegree.le
  have hwordTrace :
      source.linear.instantiate left right ∈
        inverseLeftTrace
          (labelledLeftAtoms n n)
          (labelledRightAtoms n n) :=
    LRecipe.instme_leftr_labea
      source.linear source.mem_trace left right
  have hword :
      source.linear.instantiate left right ∈
        (inverseLabelledCollection n n).factors := by
    simpa [inverseLabelledCollection] using hwordTrace
  rw [← word_raw_histories] at hword
  rcases List.mem_map.mp hword with
    ⟨dummyHistory, hdummyHistory, hwordEq⟩
  let dummyRecipe :=
    RRVocabu.RHistor.initialRecipe
      dummyHistory hdummyHistory
  have hdummyRecipe : dummyRecipe ∈ initialRecipes n := by
    rw [initialRecipes, List.mem_map]
    exact
      ⟨⟨dummyHistory, hdummyHistory⟩,
        by simp, rfl⟩
  have hequivalent :
      IRecipe.PolynomialEquivalent dummyRecipe source := by
    have hdummyLinear :
        dummyRecipe.linear = (source.instantiate left right).linear := by
      dsimp [dummyRecipe, IRecipe.instantiate,
        RRVocabu.RHistor.initialRecipe]
      simp [hwordEq]
    have hdummyEquivalent :
        IRecipe.PolynomialEquivalent dummyRecipe
          (source.instantiate left right) := by
      simp [IRecipe.PolynomialEquivalent, IRecipe.blockRecipe,
        hdummyLinear]
    exact IRecipe.polynomialEquivalent_trans hdummyEquivalent
      (source.polynomia_instanti left right)
  refine ⟨dummyRecipe, retained_initial_recipes.mpr ⟨hdummyRecipe, ?_⟩,
    hequivalent⟩
  rw [IRecipe.weight_poly_equivalent hequivalent]
  exact hsourceWeight

/--
Every retained occurrence of an arbitrary raw trace is covered by the finite
cutoff-sized dummy vocabulary.
-/
lemma polynomial_equivalent_histories
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {history : RHistor M N}
    (hhistory :
      history ∈
        retainedHistories n leftWeight rightWeight
          (inverseRawHistories M N)) :
    ∃ recipe ∈ retainedInitialRecipes n n leftWeight rightWeight,
      IRecipe.PolynomialEquivalent recipe
        (RRVocabu.RHistor.initialRecipe
          history (mem_retainedHistories.mp hhistory).1) := by
  exact equivalent_initial_recipes
    hleftWeight hrightWeight history
      (mem_retainedHistories.mp hhistory).1
      (mem_retainedHistories.mp hhistory).2

end RRVocabu
end TCTex
end Towers
