import Towers.Group.Zassenhaus.Polynomial
import Towers.Group.Zassenhaus.UniversalCorrectionFactories


/-!
# Substituting powered factors into Hall-Petresco block recipes

Complete Hall-Petresco block recipes are expressed using generalized binomial
coefficients of their two parent exponents.  During repeated-power collection,
those exponents are already bounded repeated-block expansions.

This file normalizes every positive block degree in a Hall-Petresco recipe,
attaches the resulting exponent expansion to the recipe's bound Hall word, and
compiles a cutoff all-integral packet into the powered correction factory
consumed by semantic collection.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open HACoeff

namespace BCExp

/-- Change only the propositionally equal target-weight index of an expansion. -/
def reweight
    {inputWeight leftWeight rightWeight : ℕ}
    (hweight : leftWeight = rightWeight)
    (expansion : BCExp inputWeight leftWeight) :
    BCExp inputWeight rightWeight :=
  hweight ▸ expansion

@[simp]
lemma eval_reweight
    {inputWeight leftWeight rightWeight : ℕ}
    (hweight : leftWeight = rightWeight)
    (expansion : BCExp inputWeight leftWeight) :
    (reweight hweight expansion).eval = expansion.eval := by
  subst rightWeight
  rfl

/--
Normalize the product of the positive generalized binomial coefficients
listed by one nonempty block history.
-/
noncomputable def ringChooseExponent
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight) :
    ∀ (degrees : List ℕ),
      degrees ≠ [] →
        (∀ degree ∈ degrees, 0 < degree) →
          BCExp inputWeight
            (degrees.sum *
              factor.word.weight PEAddres.weight)
  | [], hdegrees, _ => False.elim (hdegrees rfl)
  | [degree], _, hpositive => by
      simpa using
        factor.ringExponentExpansion hinputWeight degree
  | degree :: nextDegree :: degrees, _, hpositive => by
      exact reweight (by simp [Nat.add_mul])
        ((factor.ringExponentExpansion hinputWeight degree).mul
          (ringChooseExponent hinputWeight factor
            (nextDegree :: degrees) (by simp)
              (fun next hnext => hpositive next (by simp [hnext]))))

@[simp]
lemma choose_exponent_product
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight) :
    ∀ (degrees : List ℕ)
      (hdegrees : degrees ≠ [])
      (hpositive : ∀ degree ∈ degrees, 0 < degree),
        (ringChooseExponent
          hinputWeight factor degrees hdegrees hpositive).eval =
            fun q : ℕ =>
              (degrees.map fun degree =>
                Ring.choose (factor.exponent q) degree).prod
  | [], hdegrees, _ => False.elim (hdegrees rfl)
  | [degree], _, hpositive => by
      simp only [ringChooseExponent]
      simp
  | degree :: nextDegree :: degrees, _, hpositive => by
      funext q
      simp only [ringChooseExponent, eval_reweight,
        BCExp.eval_mul,
        SPFactora.eval_choose_expansion,
        choose_exponent_product hinputWeight factor
          (nextDegree :: degrees) (by simp)
            (fun next hnext => hpositive next (by simp [hnext])),
        List.map_cons, List.prod_cons]

end BCExp

namespace PFSubstia

/-- Substitute two powered Hall words into one complete block recipe. -/
def boundWord
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (R : BRecipe)
    (B A : SPFactora H inputWeight) :
    CWord (HEAddres H) :=
  CWord.hallPairBind B.word A.word R.erasedShape

@[simp]
lemma weight_boundWord
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (R : BRecipe)
    (B A : SPFactora H inputWeight) :
    (boundWord R B A).weight PEAddres.weight =
      R.leftDegree *
          B.word.weight PEAddres.weight +
        R.rightDegree *
          A.word.weight PEAddres.weight := by
  rw [boundWord, CWord.weight_pair_bind,
    CWord.pair_atom_degree,
    R.erased_left_degree, R.erased_shape_degree]

/--
Normalize the generalized-binomial exponent attached to one complete block
recipe after substituting powered parent factors.
-/
noncomputable def coefficientExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : SPFactora H inputWeight) :
    BCExp inputWeight
      (R.leftDegree *
          B.word.weight PEAddres.weight +
        R.rightDegree *
          A.word.weight PEAddres.weight) := by
  let left :=
    BCExp.ringChooseExponent
      hinputWeight B
        (BRSpec.positiveDegrees R.leftBlocks)
          (by
            apply List.ne_nil_of_length_pos
            exact
              BRSpec.length_degrees_pos
                (by
                  simpa [BRecipe.leftDegree] using
                    BRSpec.leftDegree_pos R))
          (fun degree hdegree =>
            BRSpec.positive_degrees_pos
              hdegree)
  let right :=
    BCExp.ringChooseExponent
      hinputWeight A
        (BRSpec.positiveDegrees R.rightBlocks)
          (by
            apply List.ne_nil_of_length_pos
            exact
              BRSpec.length_degrees_pos
                (by
                  simpa [BRecipe.rightDegree] using
                    BRSpec.rightDegree_pos R))
          (fun degree hdegree =>
            BRSpec.positive_degrees_pos
              hdegree)
  exact BCExp.reweight (by
    simp only [BRSpec.sum_positiveDegrees]
    rfl)
      (left.mul right)

@[simp]
lemma eval_coefficientExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : SPFactora H inputWeight) :
    (coefficientExpansion hinputWeight R B A).eval =
      fun q : ℕ =>
        BRSpec.coefficientValue R
          (B.exponent q) (A.exponent q) := by
  funext q
  simp only [coefficientExpansion, BCExp.eval_reweight,
    BCExp.eval_mul,
    BCExp.choose_exponent_product,
    BRSpec.coefficientValue,
    BRSpec.choose_positive_degrees]

/-- Attach one normalized block recipe to its substituted Hall word. -/
noncomputable def wordExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : SPFactora H inputWeight) :
    SWExp H inputWeight where
  word := boundWord R B A
  expansion := by
    exact BCExp.reweight
      (weight_boundWord R B A).symm
        (coefficientExpansion hinputWeight R B A)

@[simp]
lemma word_wordExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : SPFactora H inputWeight) :
    (wordExpansion hinputWeight R B A).word = boundWord R B A :=
  rfl

@[simp]
lemma word_weight_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : SPFactora H inputWeight) :
    (wordExpansion hinputWeight R B A).word.weight
        PEAddres.weight =
      R.leftDegree *
          B.word.weight PEAddres.weight +
        R.rightDegree *
          A.word.weight PEAddres.weight :=
  weight_boundWord R B A

@[simp]
lemma exponent_wordExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : SPFactora H inputWeight) :
    (wordExpansion hinputWeight R B A).exponent =
      fun q : ℕ =>
        BRSpec.coefficientValue R
          (B.exponent q) (A.exponent q) := by
  simp [wordExpansion, SWExp.exponent]

@[simp]
lemma word_eval_expansion
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : SPFactora H inputWeight) :
    (wordExpansion hinputWeight R B A).word.eval
        PEAddres.freeLowerTruncation =
      R.erasedShape.eval
        (HPAtom.eval (B.wordValue (n := n)) (A.wordValue (n := n))) := by
  simp [wordExpansion, boundWord, SPFactora.wordValue,
    CWord.eval_pair_bind]

/-- Attach a finite ordered recipe list to two arbitrary powered parents. -/
noncomputable def wordExpansions
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (recipes : List BRecipe)
    (B A : SPFactora H inputWeight) :
    List (SWExp H inputWeight) :=
  recipes.map fun R => wordExpansion hinputWeight R B A

/-- Evaluate a finite ordered list of substituted powered block recipes. -/
lemma list_value_expansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (recipes : List BRecipe)
    (B A : SPFactora H inputWeight)
    (q : ℕ) :
    SWExp.listValue (n := n) q
        (wordExpansions hinputWeight recipes B A) =
      (recipes.map fun R =>
        R.erasedShape.eval
            (HPAtom.eval (B.wordValue (n := n)) (A.wordValue (n := n))) ^
          BRSpec.coefficientValue R
            (B.exponent q) (A.exponent q)).prod := by
  induction recipes with
  | nil =>
      rfl
  | cons R recipes ih =>
      change
        (wordExpansion hinputWeight R B A).word.eval
              PEAddres.freeLowerTruncation ^
            (wordExpansion hinputWeight R B A).exponent q *
          SWExp.listValue q
            (wordExpansions hinputWeight recipes B A) =
        _ * _
      rw [word_eval_expansion, exponent_wordExpansion, ih]
      rfl

/-- Every substituted recipe word remembers its source block recipe. -/
lemma recipe_word_expansions
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hinputWeight : 0 < inputWeight}
    {recipes : List BRecipe}
    {B A : SPFactora H inputWeight}
    {expansion : SWExp H inputWeight}
    (hexpansion :
      expansion ∈ wordExpansions hinputWeight recipes B A) :
    ∃ R ∈ recipes, expansion = wordExpansion hinputWeight R B A := by
  rcases List.mem_map.mp hexpansion with ⟨R, hR, rfl⟩
  exact ⟨R, hR, rfl⟩

/-- Substituted recipe words are strictly above their left parent. -/
lemma left_word_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : SPFactora H inputWeight) :
    B.word.weight PEAddres.weight <
      (wordExpansion hinputWeight R B A).word.weight
        PEAddres.weight := by
  rw [word_weight_expansion]
  refine lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _
      (BRSpec.leftDegree_pos R)) ?_
  exact Nat.lt_add_of_pos_right
    (Nat.mul_pos
      (BRSpec.rightDegree_pos R)
      A.word_weight_pos)

/-- Substituted recipe words are strictly above their right parent. -/
lemma right_word_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : SPFactora H inputWeight) :
    A.word.weight PEAddres.weight <
      (wordExpansion hinputWeight R B A).word.weight
        PEAddres.weight := by
  rw [word_weight_expansion]
  refine lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _
      (BRSpec.rightDegree_pos R)) ?_
  rw [Nat.add_comm]
  exact Nat.lt_add_of_pos_right
    (Nat.mul_pos
      (BRSpec.leftDegree_pos R)
      B.word_weight_pos)

end PFSubstia

namespace PFSubsti.TAPkt

/--
A cutoff Hall-Petresco packet compiles to the powered word-expansion factory
needed at every support stratum.
-/
noncomputable def powerSupportedFactory
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt d n)
    (hinputWeight : 0 < inputWeight)
    (lowerWeight : ℕ) :
    SEFtry
      (n := n) (inputWeight := inputWeight) H lowerWeight where
  wordExpansions B A _hB _hA :=
    PFSubstia.wordExpansions
      hinputWeight packet.recipes B A
  listValue_eq B A _hB _hA q := by
    rw [PFSubstia.list_value_expansions]
    simpa [SPFactora.eval] using
      packet.listEval_eq (B.wordValue (n := n)) (A.wordValue (n := n))
        (B.exponent q) (A.exponent q)
  word_weight_left B A _hB _hA wordExpansion hwordExpansion := by
    rcases
        PFSubstia.recipe_word_expansions
          hwordExpansion with
      ⟨R, _hR, rfl⟩
    exact
      PFSubstia.left_word_expansion
        hinputWeight R B A
  word_weight_right B A _hB _hA wordExpansion hwordExpansion := by
    rcases
        PFSubstia.recipe_word_expansions
          hwordExpansion with
      ⟨R, _hR, rfl⟩
    exact
      PFSubstia.right_word_expansion
        hinputWeight R B A

end PFSubsti.TAPkt

namespace PFSubsti.UAInt

/--
A genuinely universal Hall-Petresco packet specializes to the powered
word-expansion correction factory at every lower-central cutoff.
-/
noncomputable def powerSupportedFactory
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.UAInt.{u})
    (hinputWeight : 0 < inputWeight)
    (lowerWeight : ℕ) :
    SEFtry
      (n := n) (inputWeight := inputWeight) H lowerWeight :=
  (packet.truncatedAll (d := d) (n := n))
    |>.powerSupportedFactory hinputWeight lowerWeight

end PFSubsti.UAInt

end TCTex
end Towers
