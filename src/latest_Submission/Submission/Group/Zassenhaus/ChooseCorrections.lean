import Submission.Group.Zassenhaus.ChooseNormalization
import Submission.Group.Zassenhaus.Factors

/-!
# Generalized-binomial correction terms for symbolic Hall powers

Higher Hall swaps produce integral linear combinations of products
`choose(A, a) * choose(B, b)`, where `A` and `B` are signed symbolic
exponents already collected at lower weight.  This file packages those terms
as explicit repeated-block recipe expansions with the expected weighted bound.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace BRTerm

/-- Scale the integer coefficient of one repeated-block recipe term. -/
def scale
    {inputWeight targetWeight : ℕ}
    (coefficient : ℤ)
    (term : BRTerm inputWeight targetWeight) :
    BRTerm inputWeight targetWeight :=
  (coefficient * term.1, term.2)

@[simp]
lemma eval_scale
    {inputWeight targetWeight : ℕ}
    (coefficient : ℤ)
    (term : BRTerm inputWeight targetWeight)
    (q : ℕ) :
    (term.scale coefficient).eval q = coefficient * term.eval q := by
  simp [scale, eval]
  ring

end BRTerm

namespace BCExp

/-- Scale every coefficient in an explicit repeated-block expansion. -/
def scale
    {inputWeight targetWeight : ℕ}
    (coefficient : ℤ)
    (expansion : BCExp inputWeight targetWeight) :
    BCExp inputWeight targetWeight where
  terms := expansion.terms.map fun term => term.scale coefficient

@[simp]
lemma eval_scale
    {inputWeight targetWeight : ℕ}
    (coefficient : ℤ)
    (expansion : BCExp inputWeight targetWeight)
    (q : ℕ) :
    (expansion.scale coefficient).eval q =
      coefficient * expansion.eval q := by
  cases expansion with
  | mk terms =>
      induction terms with
      | nil =>
          simp [scale, eval]
      | cons head tail ih =>
          change
            (head.scale coefficient).eval q +
                (scale coefficient
                  ({ terms := tail } :
                    BCExp inputWeight targetWeight)).eval q =
              coefficient *
                (head.eval q +
                  ({ terms := tail } :
                    BCExp inputWeight targetWeight).eval q)
          rw [BRTerm.eval_scale, ih, mul_add]

end BCExp

namespace SPFactora

/--
An explicit scaled-weight recipe expansion for a generalized binomial
coefficient of one symbolic Hall exponent.
-/
noncomputable def ringExponentExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (x : SPFactora H inputWeight)
    (k : ℕ) :
    BCExp inputWeight
      (k * x.word.weight PEAddres.weight) :=
  BCExp.ringChoose inputWeight
    (x.word.weight PEAddres.weight) k hinputWeight x.exponent

@[simp]
lemma eval_choose_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (x : SPFactora H inputWeight)
    (k : ℕ) :
    (x.ringExponentExpansion hinputWeight k).eval =
      fun q : ℕ => Ring.choose (x.exponent q) k := by
  exact BCExp.eval_ringChoose hinputWeight
    (x.exponent_valued_most hinputWeight)

/--
An explicit weighted recipe expansion for one higher Hall correction
monomial.
-/
noncomputable def chooseExponentExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (x y : SPFactora H inputWeight)
    (a b : ℕ) :
    BCExp inputWeight
      (a * x.word.weight PEAddres.weight +
        b * y.word.weight PEAddres.weight) :=
  (x.ringExponentExpansion hinputWeight a).mul
    (y.ringExponentExpansion hinputWeight b)

@[simp]
lemma ring_choose_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (x y : SPFactora H inputWeight)
    (a b : ℕ) :
    (x.chooseExponentExpansion hinputWeight y a b).eval =
      fun q : ℕ =>
        Ring.choose (x.exponent q) a * Ring.choose (y.exponent q) b := by
  ext q
  rw [chooseExponentExpansion,
    BCExp.eval_mul,
    eval_choose_expansion, eval_choose_expansion]

/--
Include the integral coefficient carried by one higher Hall correction
monomial.
-/
noncomputable def ringChooseExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (coefficient : ℤ)
    (x y : SPFactora H inputWeight)
    (a b : ℕ) :
    BCExp inputWeight
      (a * x.word.weight PEAddres.weight +
        b * y.word.weight PEAddres.weight) :=
  (x.chooseExponentExpansion hinputWeight y a b).scale coefficient

@[simp]
lemma choose_exponent_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (coefficient : ℤ)
    (x y : SPFactora H inputWeight)
    (a b : ℕ) :
    (x.ringChooseExpansion
      hinputWeight coefficient y a b).eval =
        fun q : ℕ =>
          coefficient *
            (Ring.choose (x.exponent q) a *
              Ring.choose (y.exponent q) b) := by
  ext q
  rw [ringChooseExpansion,
    BCExp.eval_scale,
    ring_choose_expansion]

/--
Every higher Hall correction monomial belongs to the bounded repeated-block
recipe span at its weighted target.
-/
lemma ring_choose_span
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (coefficient : ℤ)
    (x y : SPFactora H inputWeight)
    (a b : ℕ) :
    IntCombinationRecipes inputWeight
      (a * x.word.weight PEAddres.weight +
        b * y.word.weight PEAddres.weight)
      (fun q : ℕ =>
        coefficient *
          (Ring.choose (x.exponent q) a *
            Ring.choose (y.exponent q) b)) := by
  rw [← choose_exponent_expansion
    hinputWeight coefficient x y a b]
  exact
    (x.ringChooseExpansion
      hinputWeight coefficient y a b).eval_recipe_span

end SPFactora

end TCTex
end Submission
