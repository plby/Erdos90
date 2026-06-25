import Towers.Group.Zassenhaus.Data

/-!
# Repeated-block recipes for Hall power collection

A symbolic Hall power collector can accumulate correction histories before it
forgets their Hall-theoretic decorations.  This file formalizes the arithmetic
part of such a history.  Selecting a group of `k` repeated input blocks records
the factor `Nat.choose q k`; composing histories appends their selections and
adds their ordinary weights.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

/--
The arithmetic shadow of one repeated-block correction history.

`outputWeight` is a lower bound for the ordinary weight at which the history
may contribute.  The inequality records the weight already forced by its
selected groups of repeated input blocks.
-/
structure PBRecipe
    (inputWeight : ℕ) where
  indices :
    List ℕ
  indices_pos :
    ∀ k ∈ indices, 0 < k
  outputWeight :
    ℕ
  weighted_degree_le :
    inputWeight * indices.sum ≤ outputWeight

namespace PBRecipe

/-- Evaluate the binomial coefficient product attached to a recipe. -/
def eval
    {inputWeight : ℕ}
    (recipe : PBRecipe inputWeight)
    (q : ℕ) :
    ℤ :=
  (recipe.indices.map fun k => (Nat.choose q k : ℤ)).prod

/-- Forget the recipe's history while retaining its intrinsic output weight. -/
def toWeightedMonomial
    {inputWeight : ℕ}
    (recipe : PBRecipe inputWeight) :
    WBMono inputWeight recipe.outputWeight where
  indices := recipe.indices
  indices_pos := recipe.indices_pos
  weighted_degree_le := recipe.weighted_degree_le

lemma eval_weighted_monomial
    {inputWeight : ℕ}
    (recipe : PBRecipe inputWeight) :
    recipe.toWeightedMonomial.eval = recipe.eval :=
  rfl

/-- The empty history contributes the constant binomial monomial `1`. -/
def empty
    (inputWeight : ℕ) :
    PBRecipe inputWeight where
  indices := []
  indices_pos := by simp
  outputWeight := 0
  weighted_degree_le := by simp

/--
Selecting one independent group of `k` repeated input blocks forces ordinary
weight `inputWeight * k`.
-/
def select
    (inputWeight k : ℕ)
    (hk : 0 < k) :
    PBRecipe inputWeight where
  indices := [k]
  indices_pos := by
    intro j hj
    simp only [List.mem_singleton] at hj
    simpa [hj] using hk
  outputWeight := inputWeight * k
  weighted_degree_le := by simp

/--
Composing correction histories multiplies their binomial monomials and adds
their forced ordinary weights.
-/
def append
    {inputWeight : ℕ}
    (left right : PBRecipe inputWeight) :
    PBRecipe inputWeight where
  indices := left.indices ++ right.indices
  indices_pos := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact left.indices_pos k hk
    · exact right.indices_pos k hk
  outputWeight := left.outputWeight + right.outputWeight
  weighted_degree_le := by
    simpa [List.sum_append, Nat.mul_add] using
      Nat.add_le_add left.weighted_degree_le right.weighted_degree_le

lemma eval_empty
    (inputWeight q : ℕ) :
    (empty inputWeight).eval q = 1 := by
  simp [empty, eval]

lemma eval_select
    (inputWeight k q : ℕ)
    (hk : 0 < k) :
    (select inputWeight k hk).eval q = Nat.choose q k := by
  simp [select, eval]

lemma eval_append
    {inputWeight : ℕ}
    (left right : PBRecipe inputWeight)
    (q : ℕ) :
    (left.append right).eval q = left.eval q * right.eval q := by
  simp [append, eval, List.map_append]

lemma append_assoc
    {inputWeight : ℕ}
    (first second third : PBRecipe inputWeight) :
    (first.append second).append third =
      first.append (second.append third) := by
  cases first
  cases second
  cases third
  simp [append, List.append_assoc, Nat.add_assoc]

end PBRecipe

/--
A repeated-block recipe certified to contribute no later than `targetWeight`.
-/
structure BBRecipe
    (inputWeight targetWeight : ℕ)
    extends PBRecipe inputWeight where
  outputWeight_le :
    outputWeight ≤ targetWeight

namespace BBRecipe

/-- Evaluate the binomial coefficient product attached to a bounded recipe. -/
def eval
    {inputWeight targetWeight : ℕ}
    (recipe : BBRecipe inputWeight targetWeight)
    (q : ℕ) :
    ℤ :=
  recipe.toPBRecipe.eval q

/-- Forget the intermediate output weight of a bounded recipe. -/
def toWeightedMonomial
    {inputWeight targetWeight : ℕ}
    (recipe : BBRecipe inputWeight targetWeight) :
    WBMono inputWeight targetWeight where
  indices := recipe.indices
  indices_pos := recipe.indices_pos
  weighted_degree_le := recipe.weighted_degree_le.trans recipe.outputWeight_le

lemma eval_weighted_monomial
    {inputWeight targetWeight : ℕ}
    (recipe : BBRecipe inputWeight targetWeight) :
    recipe.toWeightedMonomial.eval = recipe.eval :=
  rfl

/-- The empty history is bounded by every target weight. -/
def empty
    (inputWeight targetWeight : ℕ) :
    BBRecipe inputWeight targetWeight where
  toPBRecipe := PBRecipe.empty inputWeight
  outputWeight_le := Nat.zero_le targetWeight

/-- A singleton selection can be used at every target above its forced weight. -/
def select
    (inputWeight targetWeight k : ℕ)
    (hk : 0 < k)
    (hweight : inputWeight * k ≤ targetWeight) :
    BBRecipe inputWeight targetWeight where
  toPBRecipe := PBRecipe.select inputWeight k hk
  outputWeight_le := hweight

/-- Bounded correction histories compose into a history bounded by the sum. -/
def append
    {inputWeight leftWeight rightWeight : ℕ}
    (left : BBRecipe inputWeight leftWeight)
    (right : BBRecipe inputWeight rightWeight) :
    BBRecipe inputWeight (leftWeight + rightWeight) where
  toPBRecipe :=
    left.toPBRecipe.append right.toPBRecipe
  outputWeight_le :=
    Nat.add_le_add left.outputWeight_le right.outputWeight_le

lemma eval_append
    {inputWeight leftWeight rightWeight : ℕ}
    (left : BBRecipe inputWeight leftWeight)
    (right : BBRecipe inputWeight rightWeight)
    (q : ℕ) :
    (left.append right).eval q = left.eval q * right.eval q := by
  exact PBRecipe.eval_append
    left.toPBRecipe right.toPBRecipe q

end BBRecipe

/--
The integer span of repeated-block histories bounded by one target weight.
-/
def IntCombinationRecipes
    (inputWeight targetWeight : ℕ)
    (f : ℕ → ℤ) :
    Prop :=
  f ∈ Submodule.span ℤ
    (Set.range fun recipe :
      BBRecipe inputWeight targetWeight => recipe.eval)

/--
Every bounded repeated-block recipe combination belongs to the weighted
binomial language consumed by the Claim 5 adapter.
-/
theorem weighted_combination_recipe
    {inputWeight targetWeight : ℕ}
    {f : ℕ → ℤ}
    (hf :
      IntCombinationRecipes
        inputWeight targetWeight f) :
    CombinationBinomialMonomials
      inputWeight targetWeight f := by
  refine Submodule.span_induction
    (p := fun g _ =>
      CombinationBinomialMonomials
        inputWeight targetWeight g)
    ?_ (Submodule.zero_mem _) ?_ ?_ hf
  · intro g hg
    rcases hg with ⟨recipe, rfl⟩
    exact Submodule.subset_span ⟨recipe.toWeightedMonomial, rfl⟩
  · intro g h _hg _hh hg hh
    exact Submodule.add_mem _ hg hh
  · intro a g _hg hg
    exact Submodule.smul_mem _ a hg

/--
Bounded repeated-block recipe combinations are integer-valued polynomials with
the expected weight-controlled degree.
-/
theorem nat_most_combination
    {inputWeight targetWeight : ℕ}
    (hinputWeight : 0 < inputWeight)
    {f : ℕ → ℤ}
    (hf :
      IntCombinationRecipes
        inputWeight targetWeight f) :
    IVMost
      f (targetWeight / inputWeight) := by
  exact
    valued_most_combination
      hinputWeight
      (weighted_combination_recipe hf)

/--
Collector-facing output in terms of repeated-block histories, before those
histories are compressed to weighted binomial monomials.
-/
def CRData
    {d n : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (e : HEFam H)
    (r : ℕ) :
    Prop :=
  (∀ s : ℕ, 1 ≤ s → s < r → s < n → e s = 0) →
    ∃ E : ℕ → HEFam H,
      (∀ q : ℕ,
        collectedHallProduct (n := n) H (E q) =
          collectedHallProduct (n := n) H e ^ q) ∧
        ∀ s : ℕ,
          1 ≤ s →
            s < n →
              ∀ i : (H s).index,
                IntCombinationRecipes
                  r s
                  (fun q : ℕ => E q s i)

/--
Repeated-block recipe output compresses to the weighted binomial collector
output accepted by `PowerCollectionData`.
-/
lemma CRData.toBinomialData
    {d n r : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (hdata : CRData (n := n) H e r) :
    CBData (n := n) H e r := by
  intro heBelow
  obtain ⟨E, hEproduct, hEcoordinate⟩ := hdata heBelow
  refine ⟨E, hEproduct, ?_⟩
  intro s hs hsn i
  exact
    weighted_combination_recipe
      (hEcoordinate s hs hsn i)

/--
Repeated-block recipe output therefore supplies the polynomial data consumed
by Claim 5.
-/
lemma CRData.toPolynomialData
    {d n r : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (hr : 1 ≤ r)
    (hdata : CRData (n := n) H e r) :
    CollectedPolynomialData (n := n) H e r :=
  hdata.toBinomialData.toPolynomialData hr

end TCTex
end Towers
