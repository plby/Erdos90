import Submission.Group.Zassenhaus.ChooseCorrections
import Submission.Group.Zassenhaus.Coordinates

/-!
# Finite higher-correction formulas for symbolic Hall powers

A recursive Hall swap emits finite integral linear combinations of generalized
binomial correction monomials.  This file weakens exact-weight expansions to a
common target and sums finite correction formulas into one explicit
repeated-block recipe expansion.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace BRTerm

/-- Reuse one weighted recipe term at any larger target weight. -/
def weaken
    {inputWeight targetWeight largerWeight : ℕ}
    (term : BRTerm inputWeight targetWeight)
    (hweight : targetWeight ≤ largerWeight) :
    BRTerm inputWeight largerWeight :=
  (term.1, term.2.weaken hweight)

@[simp]
lemma eval_weaken
    {inputWeight targetWeight largerWeight : ℕ}
    (term : BRTerm inputWeight targetWeight)
    (hweight : targetWeight ≤ largerWeight) :
    (term.weaken hweight).eval = term.eval :=
  rfl

end BRTerm

namespace BCExp

/-- Reuse an explicit recipe expansion at any larger target weight. -/
def weaken
    {inputWeight targetWeight largerWeight : ℕ}
    (expansion : BCExp inputWeight targetWeight)
    (hweight : targetWeight ≤ largerWeight) :
    BCExp inputWeight largerWeight where
  terms := expansion.terms.map fun term => term.weaken hweight

@[simp]
lemma eval_weaken
    {inputWeight targetWeight largerWeight : ℕ}
    (expansion : BCExp inputWeight targetWeight)
    (hweight : targetWeight ≤ largerWeight) :
    (expansion.weaken hweight).eval = expansion.eval := by
  ext q
  simp [weaken, eval, Function.comp_def]

/-- Add two explicit recipe expansions with the same target weight. -/
def add
    {inputWeight targetWeight : ℕ}
    (left right : BCExp inputWeight targetWeight) :
    BCExp inputWeight targetWeight where
  terms := left.terms ++ right.terms

@[simp]
lemma eval_add
    {inputWeight targetWeight : ℕ}
    (left right : BCExp inputWeight targetWeight) :
    (left.add right).eval = left.eval + right.eval := by
  ext q
  simp [add, eval]

/-- Sum a finite list of explicit recipe expansions with a common target. -/
def listSum
    (inputWeight targetWeight : ℕ) :
    List (BCExp inputWeight targetWeight) →
      BCExp inputWeight targetWeight
  | [] => zero inputWeight targetWeight
  | expansion :: expansions => expansion.add (listSum inputWeight targetWeight expansions)

@[simp]
lemma eval_listSum
    (inputWeight targetWeight : ℕ)
    (expansions : List (BCExp inputWeight targetWeight)) :
    (listSum inputWeight targetWeight expansions).eval =
      (expansions.map fun expansion => expansion.eval).sum := by
  induction expansions with
  | nil =>
      simp [listSum, eval_zero]
  | cons expansion expansions ih =>
      simp [listSum, ih]

end BCExp

/--
One integral generalized-binomial correction monomial, certified to contribute
no later than `targetWeight`.
-/
structure SCTerm
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (inputWeight targetWeight : ℕ) where
  coefficient : ℤ
  left : SPFactora H inputWeight
  right : SPFactora H inputWeight
  leftIndex : ℕ
  rightIndex : ℕ
  leftIndex_pos : 0 < leftIndex
  rightIndex_pos : 0 < rightIndex
  weightedWeight_le :
    leftIndex * left.word.weight PEAddres.weight +
      rightIndex * right.word.weight PEAddres.weight ≤
        targetWeight

namespace SCTerm

/-- Evaluate one signed higher-correction monomial. -/
def eval
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (term : SCTerm H inputWeight targetWeight) :
    ℕ → ℤ :=
  fun q : ℕ =>
    term.coefficient *
      (Ring.choose (term.left.exponent q) term.leftIndex *
        Ring.choose (term.right.exponent q) term.rightIndex)

/--
Normalize one higher-correction monomial into an explicit recipe expansion at
its certified target weight.
-/
noncomputable def expansion
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (term : SCTerm H inputWeight targetWeight) :
    BCExp inputWeight targetWeight :=
  (term.left.ringChooseExpansion hinputWeight
    term.coefficient term.right term.leftIndex term.rightIndex).weaken
      term.weightedWeight_le

@[simp]
lemma expansion_eval
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (term : SCTerm H inputWeight targetWeight) :
    (term.expansion hinputWeight).eval = term.eval := by
  rw [expansion, BCExp.eval_weaken,
    SPFactora.choose_exponent_expansion]
  rfl

end SCTerm

/--
A finite integral linear combination of higher generalized-binomial correction
monomials with one common target weight.
-/
structure SCForm
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (inputWeight targetWeight : ℕ) where
  terms :
    List (SCTerm H inputWeight targetWeight)

namespace SCForm

/-- The empty higher-correction formula. -/
def zero
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (inputWeight targetWeight : ℕ) :
    SCForm H inputWeight targetWeight where
  terms := []

/-- A higher-correction formula containing one certified monomial. -/
def singleton
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (term : SCTerm H inputWeight targetWeight) :
    SCForm H inputWeight targetWeight where
  terms := [term]

/-- Concatenate two finite higher-correction formulas. -/
def append
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (left right : SCForm H inputWeight targetWeight) :
    SCForm H inputWeight targetWeight where
  terms := left.terms ++ right.terms

/-- Evaluate a finite higher-correction formula. -/
def eval
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (formula : SCForm H inputWeight targetWeight) :
    ℕ → ℤ :=
  (formula.terms.map fun term => term.eval).sum

@[simp]
lemma eval_zero
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (inputWeight targetWeight : ℕ) :
    (zero H inputWeight targetWeight).eval = 0 := by
  simp [zero, eval]

@[simp]
lemma eval_singleton
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (term : SCTerm H inputWeight targetWeight) :
    (singleton term).eval = term.eval := by
  simp [singleton, eval]

@[simp]
lemma eval_append
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (left right : SCForm H inputWeight targetWeight) :
    (left.append right).eval = left.eval + right.eval := by
  simp [append, eval]

/-- The explicit recipe expansion represented by a finite correction formula. -/
noncomputable def expansion
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (formula : SCForm H inputWeight targetWeight) :
    BCExp inputWeight targetWeight :=
  BCExp.listSum inputWeight targetWeight
    (formula.terms.map fun term => term.expansion hinputWeight)

@[simp]
lemma expansion_eval
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (formula : SCForm H inputWeight targetWeight) :
    (formula.expansion hinputWeight).eval = formula.eval := by
  simp [expansion, eval, Function.comp_def]

/--
A finite higher-correction formula belongs to the bounded repeated-block recipe
span.
-/
lemma eval_recipe_span
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (formula : SCForm H inputWeight targetWeight) :
    IntCombinationRecipes
      inputWeight targetWeight formula.eval := by
  rw [← formula.expansion_eval hinputWeight]
  exact (formula.expansion hinputWeight).eval_recipe_span

/--
A finite higher-correction formula is an integer-valued polynomial with the
Claim 5 weight-controlled degree bound.
-/
lemma nat_valued_most
    {d inputWeight targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (formula : SCForm H inputWeight targetWeight) :
    IVMost
      formula.eval (targetWeight / inputWeight) :=
  nat_most_combination
    hinputWeight (formula.eval_recipe_span hinputWeight)

end SCForm

end TCTex
end Submission
