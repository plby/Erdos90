import Submission.Group.Zassenhaus.Counting

universe u

/-!
# Finite repeated-block expansions for Hall power collection

The symbolic collector should return explicit finite sums of repeated-block
recipes.  This file packages that constructive output and proves that it feeds
the span-based recipe API, hence the polynomial package required by Claim 5.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

/-- One integer-weighted term in a finite repeated-block expansion. -/
abbrev BRTerm
    (inputWeight targetWeight : ℕ) :=
  ℤ × BBRecipe inputWeight targetWeight

namespace BRTerm

/-- Evaluate one integer-weighted repeated-block expansion term. -/
def eval
    {inputWeight targetWeight : ℕ}
    (term : BRTerm inputWeight targetWeight) :
    ℕ → ℤ :=
  term.1 • term.2.eval

/-- Every weighted recipe term belongs to the integer span of bounded recipes. -/
lemma eval_recipe_span
    {inputWeight targetWeight : ℕ}
    (term : BRTerm inputWeight targetWeight) :
    IntCombinationRecipes
      inputWeight targetWeight term.eval := by
  exact Submodule.smul_mem _ term.1
    (Submodule.subset_span ⟨term.2, rfl⟩)

/--
Multiply two weighted recipe terms by appending their independent block
histories.
-/
def mul
    {inputWeight leftWeight rightWeight : ℕ}
    (left : BRTerm inputWeight leftWeight)
    (right : BRTerm inputWeight rightWeight) :
    BRTerm inputWeight (leftWeight + rightWeight) :=
  (left.1 * right.1, left.2.append right.2)

lemma eval_mul
    {inputWeight leftWeight rightWeight : ℕ}
    (left : BRTerm inputWeight leftWeight)
    (right : BRTerm inputWeight rightWeight)
    (q : ℕ) :
    (left.mul right).eval q = left.eval q * right.eval q := by
  simp [mul, eval, BBRecipe.eval_append]
  ring

end BRTerm

/-- An explicit finite sum of integer-weighted repeated-block recipes. -/
structure BCExp
    (inputWeight targetWeight : ℕ) where
  terms :
    List (BRTerm inputWeight targetWeight)

namespace BCExp

/-- Evaluate a finite repeated-block coordinate expansion. -/
def eval
    {inputWeight targetWeight : ℕ}
    (expansion : BCExp inputWeight targetWeight) :
    ℕ → ℤ :=
  (expansion.terms.map BRTerm.eval).sum

/-- An empty repeated-block expansion represents the zero coordinate. -/
def zero
    (inputWeight targetWeight : ℕ) :
    BCExp inputWeight targetWeight where
  terms := []

/-- Add one weighted recipe term to the front of an expansion. -/
def cons
    {inputWeight targetWeight : ℕ}
    (term : BRTerm inputWeight targetWeight)
    (expansion : BCExp inputWeight targetWeight) :
    BCExp inputWeight targetWeight where
  terms := term :: expansion.terms

/-- Multiply every term in an expansion by one fixed recipe term. -/
def mulTerm
    {inputWeight leftWeight rightWeight : ℕ}
    (term : BRTerm inputWeight leftWeight)
    (expansion : BCExp inputWeight rightWeight) :
    BCExp inputWeight (leftWeight + rightWeight) where
  terms := expansion.terms.map term.mul

/--
Multiply two finite repeated-block expansions by taking all pairwise appended
recipe histories.
-/
def mul
    {inputWeight leftWeight rightWeight : ℕ}
    (left : BCExp inputWeight leftWeight)
    (right : BCExp inputWeight rightWeight) :
    BCExp inputWeight (leftWeight + rightWeight) where
  terms := left.terms.flatMap fun term => (mulTerm term right).terms

lemma eval_zero
    (inputWeight targetWeight : ℕ) :
    (zero inputWeight targetWeight).eval = 0 := by
  simp [zero, eval]

lemma eval_cons
    {inputWeight targetWeight : ℕ}
    (term : BRTerm inputWeight targetWeight)
    (expansion : BCExp inputWeight targetWeight) :
    (cons term expansion).eval = term.eval + expansion.eval := by
  simp [cons, eval]

lemma eval_mulTerm
    {inputWeight leftWeight rightWeight : ℕ}
    (term : BRTerm inputWeight leftWeight)
    (expansion : BCExp inputWeight rightWeight)
    (q : ℕ) :
    (mulTerm term expansion).eval q = term.eval q * expansion.eval q := by
  cases expansion with
  | mk terms =>
      induction terms with
      | nil =>
          simp [mulTerm, eval]
      | cons head tail ih =>
          let tailExpansion :
              BCExp inputWeight rightWeight :=
            ⟨tail⟩
          have ih' :
              (mulTerm term tailExpansion).eval q =
                term.eval q * tailExpansion.eval q :=
            ih
          change
            (term.mul head).eval q + (mulTerm term tailExpansion).eval q =
              term.eval q * (head.eval q + tailExpansion.eval q)
          rw [BRTerm.eval_mul, ih', mul_add]

lemma eval_mul
    {inputWeight leftWeight rightWeight : ℕ}
    (left : BCExp inputWeight leftWeight)
    (right : BCExp inputWeight rightWeight)
    (q : ℕ) :
    (left.mul right).eval q = left.eval q * right.eval q := by
  cases left with
  | mk terms =>
      induction terms with
      | nil =>
          simp [mul, eval]
      | cons head tail ih =>
          let tailExpansion :
              BCExp inputWeight leftWeight :=
            ⟨tail⟩
          have ih' :
              (tailExpansion.mul right).eval q =
                tailExpansion.eval q * right.eval q :=
            ih
          calc
            (({ terms := head :: tail } :
                BCExp inputWeight leftWeight).mul right).eval q =
                (mulTerm head right).eval q +
                  (tailExpansion.mul right).eval q := by
              simp [mul, eval, tailExpansion]
            _ = head.eval q * right.eval q +
                tailExpansion.eval q * right.eval q := by
              rw [eval_mulTerm, ih']
            _ = (head.eval q + tailExpansion.eval q) * right.eval q := by
              rw [add_mul]
            _ = ({ terms := head :: tail } :
                BCExp inputWeight leftWeight).eval q *
                  right.eval q := by
              rfl

/-- Every explicit finite expansion belongs to the bounded-recipe span. -/
lemma eval_recipe_span
    {inputWeight targetWeight : ℕ}
    (expansion : BCExp inputWeight targetWeight) :
    IntCombinationRecipes
      inputWeight targetWeight expansion.eval := by
  change
    (expansion.terms.map BRTerm.eval).sum ∈
      Submodule.span ℤ
        (Set.range fun recipe :
          BBRecipe inputWeight targetWeight => recipe.eval)
  induction expansion.terms with
  | nil =>
      simp
  | cons term terms ih =>
      simpa using Submodule.add_mem _ term.eval_recipe_span ih

/--
Every explicit finite repeated-block expansion is an integer-valued
polynomial with the expected weight-controlled degree.
-/
lemma integerValuedMost
    {inputWeight targetWeight : ℕ}
    (hinputWeight : 0 < inputWeight)
    (expansion : BCExp inputWeight targetWeight) :
    IVMost
      expansion.eval (targetWeight / inputWeight) :=
  nat_most_combination
    hinputWeight expansion.eval_recipe_span

end BCExp

/--
Constructive collector-facing output for powers of one collected Hall normal
form.  Every coordinate is supplied as an explicit finite recipe expansion.
-/
def CEData
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
                ∃ expansion : BCExp r s,
                  expansion.eval = fun q : ℕ => E q s i

/--
Explicit finite coordinate expansions supply the span-based recipe output.
-/
lemma CEData.toRecipeData
    {d n r : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (hdata : CEData (n := n) H e r) :
    CRData (n := n) H e r := by
  intro heBelow
  obtain ⟨E, hEproduct, hEcoordinate⟩ := hdata heBelow
  refine ⟨E, hEproduct, ?_⟩
  intro s hs hsn i
  obtain ⟨expansion, hexpansion⟩ := hEcoordinate s hs hsn i
  rw [← hexpansion]
  exact expansion.eval_recipe_span

/--
Explicit finite coordinate expansions therefore imply the polynomial data
consumed by Claim 5.
-/
lemma CEData.toPolynomialData
    {d n r : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (hr : 1 ≤ r)
    (hdata : CEData (n := n) H e r) :
    CollectedPolynomialData (n := n) H e r :=
  hdata.toRecipeData.toPolynomialData hr

end TCTex
end Submission
