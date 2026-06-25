import Towers.Group.Zassenhaus.FormulaChooseSubstitution

/-!
# Transient exponent carriers for symbolic Hall powers

The ordinary symbolic Hall factor type requires the arithmetic recipe bound to
fit the physical weight of its attached Hall word.  Intermediate
powered-commutator expansions need a slightly looser object: the exponent
still has an explicit bounded repeated-block expansion, but its arithmetic
bound may temporarily exceed the weight of the word carrying it.

This file separates those two weights.  It also provides multiplication,
generalized-binomial normalization, Hall-Petresco block substitution, and the
guarded attachment map back to ordinary symbolic Hall word expansions.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HACoeff

/--
An explicit repeated-block exponent expansion with an arithmetic weight bound
independent of any Hall word to which the exponent may later be attached.
-/
structure SECarrie
    (inputWeight exponentWeight : ℕ) where
  expansion :
    BCExp inputWeight exponentWeight

namespace SECarrie

/-- Evaluate the represented exponent at repetition count `q`. -/
def eval
    {inputWeight exponentWeight : ℕ}
    (carrier : SECarrie inputWeight exponentWeight) :
    ℕ → ℤ :=
  carrier.expansion.eval

/-- The constant exponent one has arithmetic weight zero. -/
def one
    (inputWeight : ℕ) :
    SECarrie inputWeight 0 where
  expansion :=
    { terms := [(1, BBRecipe.empty inputWeight 0)] }

@[simp]
lemma eval_one
    (inputWeight : ℕ) :
    (one inputWeight).eval = 1 := by
  ext q
  simp [one, eval, BCExp.eval,
    BRTerm.eval, BBRecipe.eval,
    BBRecipe.empty, PBRecipe.eval,
    PBRecipe.empty]

/-- Forget the attached word of an ordinary factor while retaining its exponent. -/
def ofFactor
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factor : SPFactora H inputWeight) :
    SECarrie inputWeight
      (factor.word.weight PEAddres.weight) where
  expansion := factor.coordinateExpansion

@[simp]
lemma eval_ofFactor
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factor : SPFactora H inputWeight) :
    (ofFactor factor).eval = factor.exponent :=
  factor.coordinateExpansion_eval

/-- Enlarge the arithmetic weight bound without changing the exponent. -/
def weaken
    {inputWeight exponentWeight largerWeight : ℕ}
    (carrier : SECarrie inputWeight exponentWeight)
    (hweight : exponentWeight ≤ largerWeight) :
    SECarrie inputWeight largerWeight where
  expansion := carrier.expansion.weaken hweight

@[simp]
lemma eval_weaken
    {inputWeight exponentWeight largerWeight : ℕ}
    (carrier : SECarrie inputWeight exponentWeight)
    (hweight : exponentWeight ≤ largerWeight) :
    (carrier.weaken hweight).eval = carrier.eval := by
  simp [weaken, eval]

/-- Change only a propositionally equal arithmetic weight index. -/
def reweight
    {inputWeight leftWeight rightWeight : ℕ}
    (hweight : leftWeight = rightWeight)
    (carrier : SECarrie inputWeight leftWeight) :
    SECarrie inputWeight rightWeight where
  expansion := carrier.expansion.reweight hweight

@[simp]
lemma eval_reweight
    {inputWeight leftWeight rightWeight : ℕ}
    (hweight : leftWeight = rightWeight)
    (carrier : SECarrie inputWeight leftWeight) :
    (carrier.reweight hweight).eval = carrier.eval := by
  simp [reweight, eval]

/-- Multiply two transient exponents, adding their arithmetic weight bounds. -/
def mul
    {inputWeight leftWeight rightWeight : ℕ}
    (left : SECarrie inputWeight leftWeight)
    (right : SECarrie inputWeight rightWeight) :
    SECarrie inputWeight (leftWeight + rightWeight) where
  expansion := left.expansion.mul right.expansion

@[simp]
lemma eval_mul
    {inputWeight leftWeight rightWeight : ℕ}
    (left : SECarrie inputWeight leftWeight)
    (right : SECarrie inputWeight rightWeight) :
    (left.mul right).eval = left.eval * right.eval := by
  ext q
  simp [mul, eval, BCExp.eval_mul]

/--
Normalize a generalized binomial coefficient of a transient exponent.  The
arithmetic weight bound scales by its positive-block degree, independently of
any Hall word.
-/
def ringChoose
    {inputWeight exponentWeight : ℕ}
    (hinputWeight : 0 < inputWeight)
    (carrier : SECarrie inputWeight exponentWeight)
    (k : ℕ) :
    SECarrie inputWeight (k * exponentWeight) where
  expansion :=
    BCExp.ringChoose inputWeight exponentWeight k
      hinputWeight carrier.eval

@[simp]
lemma eval_ringChoose
    {inputWeight exponentWeight : ℕ}
    (hinputWeight : 0 < inputWeight)
    (carrier : SECarrie inputWeight exponentWeight)
    (k : ℕ) :
    (carrier.ringChoose hinputWeight k).eval =
      fun q : ℕ => Ring.choose (carrier.eval q) k := by
  exact
    BCExp.eval_ringChoose hinputWeight
      (carrier.expansion.integerValuedMost
        hinputWeight)

/--
Normalize the product of generalized binomial coefficients listed by one
nonempty positive block history.
-/
def ringChooseProduct
    {inputWeight exponentWeight : ℕ}
    (hinputWeight : 0 < inputWeight)
    (carrier : SECarrie inputWeight exponentWeight) :
    ∀ (degrees : List ℕ),
      degrees ≠ [] →
        (∀ degree ∈ degrees, 0 < degree) →
          SECarrie inputWeight
            (degrees.sum * exponentWeight)
  | [], hdegrees, _ => False.elim (hdegrees rfl)
  | [degree], _, _ => carrier.ringChoose hinputWeight degree
  | degree :: nextDegree :: degrees, _, hpositive => by
      exact reweight (by simp [Nat.add_mul])
        ((carrier.ringChoose hinputWeight degree).mul
          (ringChooseProduct hinputWeight carrier
            (nextDegree :: degrees) (by simp)
              (fun next hnext => hpositive next (by simp [hnext]))))

@[simp]
lemma ring_choose_product
    {inputWeight exponentWeight : ℕ}
    (hinputWeight : 0 < inputWeight)
    (carrier : SECarrie inputWeight exponentWeight) :
    ∀ (degrees : List ℕ)
      (hdegrees : degrees ≠ [])
      (hpositive : ∀ degree ∈ degrees, 0 < degree),
        (ringChooseProduct hinputWeight carrier degrees hdegrees
          hpositive).eval =
            fun q : ℕ =>
              (degrees.map fun degree =>
                Ring.choose (carrier.eval q) degree).prod
  | [], hdegrees, _ => False.elim (hdegrees rfl)
  | [degree], _, _ => by
      simp only [ringChooseProduct, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]
      exact carrier.eval_ringChoose hinputWeight degree
  | degree :: nextDegree :: degrees, _, hpositive => by
      funext q
      simp only [ringChooseProduct, eval_reweight, eval_mul,
        eval_ringChoose,
        ring_choose_product hinputWeight carrier
          (nextDegree :: degrees) (by simp)
            (fun next hnext => hpositive next (by simp [hnext])),
        Pi.mul_apply, List.map_cons, List.prod_cons]

end SECarrie

/--
A Hall word carrying an explicit transient exponent.  `exponentWeight` is an
arithmetic bound, not necessarily a bound on the physical Hall word.
-/
structure TWExp
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (inputWeight : ℕ) where
  word :
    CWord (HEAddres H)
  exponentWeight :
    ℕ
  carrier :
    SECarrie inputWeight exponentWeight

namespace TWExp

/-- Evaluate the transient exponent. -/
def exponent
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight) :
    ℕ → ℤ :=
  wordExpansion.carrier.eval

/--
Reattach an ordinary factor exponent to an arbitrary word without pretending
that the original arithmetic bound fits that word.
-/
def rewordFactor
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factor : SPFactora H inputWeight)
    (word : CWord (HEAddres H)) :
    TWExp H inputWeight where
  word := word
  exponentWeight := factor.word.weight PEAddres.weight
  carrier := SECarrie.ofFactor factor

@[simp]
lemma exponent_rewordFactor
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factor : SPFactora H inputWeight)
    (word : CWord (HEAddres H)) :
    (rewordFactor factor word).exponent = factor.exponent :=
  factor.coordinateExpansion_eval

/-- Attach exponent one to an arbitrary word with arithmetic weight zero. -/
def wordUnit
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (word : CWord (HEAddres H)) :
    TWExp H inputWeight where
  word := word
  exponentWeight := 0
  carrier := SECarrie.one inputWeight

@[simp]
lemma exponent_wordUnit
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (word : CWord (HEAddres H)) :
    (wordUnit (inputWeight := inputWeight) word).exponent = 1 :=
  SECarrie.eval_one inputWeight

/--
Return to the ordinary bounded symbolic word-expansion type once the transient
arithmetic bound fits the physical Hall word.
-/
def toWordExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight)
    (hweight :
      wordExpansion.exponentWeight ≤
        wordExpansion.word.weight PEAddres.weight) :
    SWExp H inputWeight where
  word := wordExpansion.word
  expansion := wordExpansion.carrier.expansion.weaken hweight

@[simp]
lemma exponent_word_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : TWExp H inputWeight)
    (hweight :
      wordExpansion.exponentWeight ≤
        wordExpansion.word.weight PEAddres.weight) :
    (wordExpansion.toWordExpansion hweight).exponent =
      wordExpansion.exponent := by
  simp [toWordExpansion, SWExp.exponent, exponent,
    SECarrie.eval]

end TWExp

namespace PTSubsti

/-- Substitute two transiently powered Hall words into one block recipe. -/
def boundWord
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (R : BRecipe)
    (B A : TWExp H inputWeight) :
    CWord (HEAddres H) :=
  CWord.hallPairBind B.word A.word R.erasedShape

@[simp]
lemma weight_boundWord
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (R : BRecipe)
    (B A : TWExp H inputWeight) :
    (boundWord R B A).weight PEAddres.weight =
      R.leftDegree *
          B.word.weight PEAddres.weight +
        R.rightDegree *
          A.word.weight PEAddres.weight := by
  rw [boundWord, CWord.weight_pair_bind,
    CWord.pair_atom_degree,
    R.erased_left_degree, R.erased_shape_degree]

/--
Normalize the coefficient of one Hall-Petresco block while keeping arithmetic
and physical Hall weights separate.
-/
def coefficientCarrier
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : TWExp H inputWeight) :
    SECarrie inputWeight
      (R.leftDegree * B.exponentWeight +
        R.rightDegree * A.exponentWeight) := by
  let left :=
    B.carrier.ringChooseProduct hinputWeight
      (BRSpec.positiveDegrees R.leftBlocks)
      (by
        apply List.ne_nil_of_length_pos
        exact
          BRSpec.length_degrees_pos
            (by
              simpa [BRecipe.leftDegree] using
                BRSpec.leftDegree_pos R))
      (fun degree hdegree =>
        BRSpec.positive_degrees_pos hdegree)
  let right :=
    A.carrier.ringChooseProduct hinputWeight
      (BRSpec.positiveDegrees R.rightBlocks)
      (by
        apply List.ne_nil_of_length_pos
        exact
          BRSpec.length_degrees_pos
            (by
              simpa [BRecipe.rightDegree] using
                BRSpec.rightDegree_pos R))
      (fun degree hdegree =>
        BRSpec.positive_degrees_pos hdegree)
  exact SECarrie.reweight (by
    simp only [BRSpec.sum_positiveDegrees]
    rfl)
      (left.mul right)

@[simp]
lemma eval_coefficientCarrier
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : TWExp H inputWeight) :
    (coefficientCarrier hinputWeight R B A).eval =
      fun q : ℕ =>
        BRSpec.coefficientValue R
          (B.exponent q) (A.exponent q) := by
  funext q
  simp only [coefficientCarrier,
    SECarrie.eval_reweight,
    SECarrie.eval_mul,
    SECarrie.ring_choose_product,
    BRSpec.coefficientValue,
    BRSpec.choose_positive_degrees,
    TWExp.exponent,
    Pi.mul_apply]

/--
One Hall-Petresco output word with its honest transient arithmetic bound.
-/
def wordExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : TWExp H inputWeight) :
    TWExp H inputWeight where
  word := boundWord R B A
  exponentWeight :=
    R.leftDegree * B.exponentWeight +
      R.rightDegree * A.exponentWeight
  carrier := coefficientCarrier hinputWeight R B A

@[simp]
lemma exponent_wordExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : TWExp H inputWeight) :
    (wordExpansion hinputWeight R B A).exponent =
      fun q : ℕ =>
        BRSpec.coefficientValue R
          (B.exponent q) (A.exponent q) :=
  eval_coefficientCarrier hinputWeight R B A

/--
Specialize one block recipe to an arbitrary rewording of an ordinary parent
factor and a fixed right Hall word.  This construction is unconditional: its
arithmetic bound remains the original parent weight.
-/
def innerReductionExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    TWExp H inputWeight :=
  wordExpansion hinputWeight R
    (TWExp.rewordFactor factor innerWord)
    (TWExp.wordUnit rightWord)

@[simp]
lemma exponent_reduction_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (factor : SPFactora H inputWeight)
    (innerWord rightWord : CWord (HEAddres H)) :
    (innerReductionExpansion hinputWeight R factor innerWord
      rightWord).exponent =
        fun q : ℕ =>
          BRSpec.coefficientValue R
            (factor.exponent q) 1 := by
  simp [innerReductionExpansion]

end PTSubsti

end TCTex
end Towers
