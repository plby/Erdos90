import Submission.Group.Zassenhaus.RewordingCore

/-!
# Inverting transient symbolic Hall powers

Transient exponent carriers retain explicit integral coordinate expansions,
so they remain closed under negation even when their arithmetic bound does not
yet fit the physical Hall word.  This file packages that signed operation and
the corresponding inverse operation on finite transient source lists.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace SECarrie

/-- Negate a transient exponent without changing its arithmetic bound. -/
def neg
    {inputWeight exponentWeight : ℕ}
    (carrier : SECarrie inputWeight exponentWeight) :
    SECarrie inputWeight exponentWeight where
  expansion := carrier.expansion.scale (-1)

@[simp]
lemma eval_neg
    {inputWeight exponentWeight : ℕ}
    (carrier : SECarrie inputWeight exponentWeight) :
    carrier.neg.eval = -carrier.eval := by
  funext q
  simp [neg, eval]

end SECarrie

namespace TWExp

/-- Negate the transient exponent without changing its physical Hall word. -/
def neg
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight) :
    TWExp H inputWeight where
  word := wordExpansion.word
  exponentWeight := wordExpansion.exponentWeight
  carrier := wordExpansion.carrier.neg

@[simp]
lemma word_neg
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight) :
    wordExpansion.neg.word = wordExpansion.word :=
  rfl

@[simp]
lemma exponentWeight_neg
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight) :
    wordExpansion.neg.exponentWeight = wordExpansion.exponentWeight :=
  rfl

@[simp]
lemma exponent_neg
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight) :
    wordExpansion.neg.exponent = -wordExpansion.exponent := by
  simp [neg, exponent]

@[simp]
lemma value_neg
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight)
    (q : ℕ) :
    wordExpansion.neg.value (n := n) q = (wordExpansion.value q)⁻¹ := by
  simp [value]

/-- Reverse a transient source list while negating every signed exponent. -/
def inverseList
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (source : List (TWExp H inputWeight)) :
    List (TWExp H inputWeight) :=
  source.reverse.map neg

/-- The transient inverse list evaluates to the inverse group element. -/
lemma list_value_inverse
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (source : List (TWExp H inputWeight))
    (q : ℕ) :
    listValue (n := n) q (inverseList source) = (listValue q source)⁻¹ := by
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
        listValue (n := n) q (inverseList source) *
              wordExpansion.neg.value (n := n) q =
          (wordExpansion.value (n := n) q * listValue (n := n) q source)⁻¹
      rw [ih, value_neg]
      group

@[simp]
lemma neg_reword
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight)
    (word : CWord (HEAddres H)) :
    (wordExpansion.reword word).neg = wordExpansion.neg.reword word :=
  rfl

end TWExp

end TCTex
end Submission
