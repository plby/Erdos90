import Towers.Group.HallPetrescoClaim
import Towers.Group.Zassenhaus.FiniteSignedFormulas
import Towers.Group.Zassenhaus.SymbolicHallFactors


/-!
# Specializing Hall-Petresco block recipes to Claim 8 formulas

The Hall-Petresco collector records independent left and right source blocks.
Claim 8 asks for products of positive-index generalized binomial coefficients
whose weighted cost is bounded by the output Hall weight.  This file connects
the two languages.

A block recipe can contain degree-zero blocks.  They contribute
`Ring.choose z 0 = 1`, so they are erased before constructing a Claim 8
monomial.  The lemmas below prove that this erasure preserves sums and
evaluations.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open HACoeff

namespace BRSpec

/-- Discard degree-zero source blocks before building a Claim 8 monomial. -/
def positiveDegrees
    (degrees : List ℕ) :
    List ℕ :=
  match degrees with
  | [] => []
  | degree :: degrees =>
      if 0 < degree then
        degree :: positiveDegrees degrees
      else
        positiveDegrees degrees

lemma positive_degrees_pos
    {degrees : List ℕ}
    {degree : ℕ}
    (hdegree : degree ∈ positiveDegrees degrees) :
    0 < degree := by
  induction degrees with
  | nil =>
      simp [positiveDegrees] at hdegree
  | cons head degrees ih =>
      by_cases hhead : 0 < head
      · simp only [positiveDegrees, if_pos hhead, List.mem_cons] at hdegree
        rcases hdegree with rfl | hdegree
        · exact hhead
        · exact ih hdegree
      · simp only [positiveDegrees, if_neg hhead] at hdegree
        exact ih hdegree

@[simp]
lemma sum_positiveDegrees
    (degrees : List ℕ) :
    (positiveDegrees degrees).sum = degrees.sum := by
  induction degrees with
  | nil =>
      simp [positiveDegrees]
  | cons degree degrees ih =>
      by_cases hdegree : 0 < degree
      · simp [positiveDegrees, hdegree, ih]
      · have hdegreeZero : degree = 0 := Nat.eq_zero_of_not_pos hdegree
        simp [positiveDegrees, hdegreeZero, ih]

lemma length_degrees_pos
    {degrees : List ℕ}
    (hdegrees : 0 < degrees.sum) :
    0 < (positiveDegrees degrees).length := by
  rw [List.length_pos_iff]
  intro hnil
  have hsum : degrees.sum = 0 := by
    rw [← sum_positiveDegrees degrees, hnil]
    rfl
  omega

@[simp]
lemma choose_positive_degrees
    (z : ℤ)
    (degrees : List ℕ) :
    ((positiveDegrees degrees).map fun degree => Ring.choose z degree).prod =
      (degrees.map fun degree => Ring.choose z degree).prod := by
  induction degrees with
  | nil =>
      simp [positiveDegrees]
  | cons degree degrees ih =>
      by_cases hdegree : 0 < degree
      · simp [positiveDegrees, hdegree, ih]
      · have hdegreeZero : degree = 0 := Nat.eq_zero_of_not_pos hdegree
        simp [positiveDegrees, hdegreeZero, ih]

lemma sum_get_mul
    (degrees : List ℕ)
    (weight : ℕ) :
    (∑ index : Fin degrees.length, degrees.get index * weight) =
      degrees.sum * weight := by
  calc
    (∑ index : Fin degrees.length, degrees.get index * weight) =
        (degrees.map fun degree => degree * weight).sum := by
          simpa using
            Fin.sum_univ_fun_getElem degrees (fun degree => degree * weight)
    _ = degrees.sum * weight := by
      simpa using
        List.sum_map_mul_right degrees (fun degree : ℕ => degree) weight

lemma leftDegree_pos
    (R : HACoeff.BRecipe) :
    0 < R.leftDegree := by
  have hpositive := R.positive.1
  change 0 < R.erasedShape.pairLeftDegree at hpositive
  simpa only [R.erased_left_degree] using hpositive

lemma rightDegree_pos
    (R : HACoeff.BRecipe) :
    0 < R.rightDegree := by
  have hpositive := R.positive.2
  change 0 < R.erasedShape.pairRightDegree at hpositive
  simpa only [R.erased_shape_degree] using hpositive

/--
Specialize one Hall-Petresco block history to one admissible Claim 8
generalized-binomial monomial.
-/
def weightedBinomialMonomial
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : HACoeff.BRecipe)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H)
    (hweight :
      R.leftDegree * leftAddress.1 +
          R.rightDegree * rightAddress.1 ≤
        targetWeight) :
    WHMono H ι targetWeight where
  length :=
    (positiveDegrees R.leftBlocks).length +
      (positiveDegrees R.rightBlocks).length
  length_pos :=
    Nat.add_pos_left
      (length_degrees_pos
        (by simpa [HACoeff.BRecipe.leftDegree] using
          leftDegree_pos R)) _
  input :=
    Fin.append
      (fun _ => leftInput)
      (fun _ => rightInput)
  address :=
    Fin.append
      (fun _ => leftAddress)
      (fun _ => rightAddress)
  binomialIndex :=
    Fin.append
      (positiveDegrees R.leftBlocks).get
      (positiveDegrees R.rightBlocks).get
  binomialIndex_pos := by
    intro index
    refine Fin.addCases ?_ ?_ index
    · intro leftIndex
      simpa only [Fin.append_left] using
        positive_degrees_pos (List.get_mem _ leftIndex)
    · intro rightIndex
      simpa only [Fin.append_right] using
        positive_degrees_pos (List.get_mem _ rightIndex)
  weightedWeight_le := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [sum_get_mul, sum_get_mul, sum_positiveDegrees, sum_positiveDegrees]
    exact hweight

@[simp]
lemma weighted_binomial_monomial
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (R : HACoeff.BRecipe)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H)
    (hweight :
      R.leftDegree * leftAddress.1 +
          R.rightDegree * rightAddress.1 ≤
        targetWeight) :
    (weightedBinomialMonomial R leftInput rightInput
        leftAddress rightAddress hweight).eval e =
      (R.leftBlocks.map fun degree =>
        Ring.choose (e leftInput leftAddress.1 leftAddress.2) degree).prod *
      (R.rightBlocks.map fun degree =>
        Ring.choose (e rightInput rightAddress.1 rightAddress.2) degree).prod := by
  change
    (∏ index :
        Fin ((positiveDegrees R.leftBlocks).length +
          (positiveDegrees R.rightBlocks).length),
      Ring.choose
        (e
          (Fin.append
            (fun _ : Fin (positiveDegrees R.leftBlocks).length => leftInput)
            (fun _ : Fin (positiveDegrees R.rightBlocks).length => rightInput)
            index)
          (Fin.append
            (fun _ : Fin (positiveDegrees R.leftBlocks).length => leftAddress)
            (fun _ : Fin (positiveDegrees R.rightBlocks).length => rightAddress)
            index).1
          (Fin.append
            (fun _ : Fin (positiveDegrees R.leftBlocks).length => leftAddress)
            (fun _ : Fin (positiveDegrees R.rightBlocks).length => rightAddress)
            index).2)
        (Fin.append
          (positiveDegrees R.leftBlocks).get
          (positiveDegrees R.rightBlocks).get
          index)) =
      (R.leftBlocks.map fun degree =>
        Ring.choose (e leftInput leftAddress.1 leftAddress.2) degree).prod *
      (R.rightBlocks.map fun degree =>
        Ring.choose (e rightInput rightAddress.1 rightAddress.2) degree).prod
  rw [Fin.prod_univ_add]
  congr 1
  · calc
      (∏ index : Fin (positiveDegrees R.leftBlocks).length,
        Ring.choose
          (e
            (Fin.append
              (fun _ : Fin (positiveDegrees R.leftBlocks).length => leftInput)
              (fun _ : Fin (positiveDegrees R.rightBlocks).length => rightInput)
              (Fin.castAdd (positiveDegrees R.rightBlocks).length index))
            (Fin.append
              (fun _ : Fin (positiveDegrees R.leftBlocks).length => leftAddress)
              (fun _ : Fin (positiveDegrees R.rightBlocks).length => rightAddress)
              (Fin.castAdd (positiveDegrees R.rightBlocks).length index)).1
            (Fin.append
              (fun _ : Fin (positiveDegrees R.leftBlocks).length => leftAddress)
              (fun _ : Fin (positiveDegrees R.rightBlocks).length => rightAddress)
              (Fin.castAdd (positiveDegrees R.rightBlocks).length index)).2)
          (Fin.append
            (positiveDegrees R.leftBlocks).get
            (positiveDegrees R.rightBlocks).get
            (Fin.castAdd (positiveDegrees R.rightBlocks).length index))) =
          ∏ index : Fin (positiveDegrees R.leftBlocks).length,
            Ring.choose (e leftInput leftAddress.1 leftAddress.2)
              ((positiveDegrees R.leftBlocks).get index) := by
        apply Finset.prod_congr rfl
        intro index _hindex
        rw [Fin.append_left, Fin.append_left, Fin.append_left]
      _ =
          ((positiveDegrees R.leftBlocks).map fun degree =>
            Ring.choose (e leftInput leftAddress.1 leftAddress.2) degree).prod := by
        simp
      _ =
          (R.leftBlocks.map fun degree =>
            Ring.choose (e leftInput leftAddress.1 leftAddress.2) degree).prod := by
        exact choose_positive_degrees _ _
  · calc
      (∏ index : Fin (positiveDegrees R.rightBlocks).length,
        Ring.choose
          (e
            (Fin.append
              (fun _ : Fin (positiveDegrees R.leftBlocks).length => leftInput)
              (fun _ : Fin (positiveDegrees R.rightBlocks).length => rightInput)
              (Fin.natAdd (positiveDegrees R.leftBlocks).length index))
            (Fin.append
              (fun _ : Fin (positiveDegrees R.leftBlocks).length => leftAddress)
              (fun _ : Fin (positiveDegrees R.rightBlocks).length => rightAddress)
              (Fin.natAdd (positiveDegrees R.leftBlocks).length index)).1
            (Fin.append
              (fun _ : Fin (positiveDegrees R.leftBlocks).length => leftAddress)
              (fun _ : Fin (positiveDegrees R.rightBlocks).length => rightAddress)
              (Fin.natAdd (positiveDegrees R.leftBlocks).length index)).2)
          (Fin.append
            (positiveDegrees R.leftBlocks).get
            (positiveDegrees R.rightBlocks).get
            (Fin.natAdd (positiveDegrees R.leftBlocks).length index))) =
          ∏ index : Fin (positiveDegrees R.rightBlocks).length,
            Ring.choose (e rightInput rightAddress.1 rightAddress.2)
              ((positiveDegrees R.rightBlocks).get index) := by
        apply Finset.prod_congr rfl
        intro index _hindex
        rw [Fin.append_right, Fin.append_right, Fin.append_right]
      _ =
          ((positiveDegrees R.rightBlocks).map fun degree =>
            Ring.choose (e rightInput rightAddress.1 rightAddress.2) degree).prod := by
        simp
      _ =
          (R.rightBlocks.map fun degree =>
            Ring.choose (e rightInput rightAddress.1 rightAddress.2) degree).prod := by
        exact choose_positive_degrees _ _

/--
Regard one specialized Hall-Petresco block history as a one-term signed
Claim 8 formula.
-/
def weightedBinomialFormula
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : HACoeff.BRecipe)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H)
    (hweight :
      R.leftDegree * leftAddress.1 +
          R.rightDegree * rightAddress.1 ≤
        targetWeight) :
    WBForm H ι targetWeight :=
  WBForm.singleton
    (1, weightedBinomialMonomial R leftInput rightInput
      leftAddress rightAddress hweight)

@[simp]
lemma weighted_binomial_formula
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (R : HACoeff.BRecipe)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H)
    (hweight :
      R.leftDegree * leftAddress.1 +
          R.rightDegree * rightAddress.1 ≤
        targetWeight) :
    (weightedBinomialFormula R leftInput rightInput
        leftAddress rightAddress hweight).eval e =
      (R.leftBlocks.map fun degree =>
        Ring.choose (e leftInput leftAddress.1 leftAddress.2) degree).prod *
      (R.rightBlocks.map fun degree =>
        Ring.choose (e rightInput rightAddress.1 rightAddress.2) degree).prod := by
  simp [weightedBinomialFormula, WBTerm.eval]

end BRSpec
end TCTex
end Towers

/-!
# Well-founded recursion for complete Hall-Petresco block recipes

The correct nonterminal scheduler works with complete independent-history
packets.  Interchanging two packets forms pairwise correction histories via
`BRecipe.correction`.  Their weighted Hall degree is the sum of the parent
degrees, so every retained correction strictly decreases cutoff-minus-degree.

This file packages that recursion measure independently of any concrete batch
scheduler.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

open HACoeff

namespace BRSpec

/-- Ordinary Hall weight of one block recipe after assigning source weights. -/
def weightedWordWeight
    (leftWeight rightWeight : ℕ)
    (R : BRecipe) :
    ℕ :=
  R.erasedShape.weight (HPAtom.weight leftWeight rightWeight)

/-- Recipe weight is its weighted left/right source degree. -/
@[simp]
lemma weighted_word_weight
    (leftWeight rightWeight : ℕ)
    (R : BRecipe) :
    weightedWordWeight leftWeight rightWeight R =
      R.leftDegree * leftWeight + R.rightDegree * rightWeight := by
  rw [weightedWordWeight, CWord.pair_atom_degree,
    R.erased_left_degree, R.erased_shape_degree]

/-- Appending correction histories adds their total left degree. -/
@[simp]
lemma leftDegree_correction
    (B A : BRecipe) :
    (B.correction A).leftDegree = B.leftDegree + A.leftDegree := by
  simp [BRecipe.leftDegree, BRecipe.correction, List.sum_append]

/-- Appending correction histories adds their total right degree. -/
@[simp]
lemma rightDegree_correction
    (B A : BRecipe) :
    (B.correction A).rightDegree = B.rightDegree + A.rightDegree := by
  simp [BRecipe.rightDegree, BRecipe.correction, List.sum_append]

/-- A pairwise correction packet has the sum of its parents' weighted degrees. -/
@[simp]
lemma weighted_weight_correction
    (leftWeight rightWeight : ℕ)
    (B A : BRecipe) :
    weightedWordWeight leftWeight rightWeight (B.correction A) =
      weightedWordWeight leftWeight rightWeight B +
        weightedWordWeight leftWeight rightWeight A := by
  simp only [weighted_word_weight, leftDegree_correction, rightDegree_correction]
  simp [Nat.add_mul, Nat.add_assoc, Nat.add_left_comm]

/-- Positive source weights make every positive-bidegree recipe weight positive. -/
lemma weighted_weight_pos
    {leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (R : BRecipe) :
    0 < weightedWordWeight leftWeight rightWeight R := by
  rw [weighted_word_weight]
  have hleft := Nat.mul_pos (leftDegree_pos R) hleftWeight
  have hright := Nat.mul_pos (rightDegree_pos R) hrightWeight
  omega

/-- A pairwise correction lies strictly above its left parent. -/
lemma weighted_correction_left
    {leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (B A : BRecipe) :
    weightedWordWeight leftWeight rightWeight B <
      weightedWordWeight leftWeight rightWeight (B.correction A) := by
  rw [weighted_weight_correction]
  exact Nat.lt_add_of_pos_right
    (weighted_weight_pos hleftWeight hrightWeight A)

/-- A pairwise correction lies strictly above its right parent. -/
lemma weighted_correction_right
    {leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (B A : BRecipe) :
    weightedWordWeight leftWeight rightWeight A <
      weightedWordWeight leftWeight rightWeight (B.correction A) := by
  rw [weighted_weight_correction, Nat.add_comm]
  exact Nat.lt_add_of_pos_right
    (weighted_weight_pos hleftWeight hrightWeight B)

/-- Root-swapping a recipe does not change its weighted degree. -/
@[simp]
lemma weighted_root_swap
    (leftWeight rightWeight : ℕ)
    (R : BRecipe) :
    weightedWordWeight leftWeight rightWeight R.rootSwap =
      weightedWordWeight leftWeight rightWeight R := by
  rw [weightedWordWeight, weightedWordWeight, BRecipe.erased_shape_swap,
    weight_root_swap]

/-- Inverse-oriented correction also has the sum of its parents' weighted degrees. -/
@[simp]
lemma weighted_inverse_correction
    (leftWeight rightWeight : ℕ)
    (B A : BRecipe) :
    weightedWordWeight leftWeight rightWeight (B.inverseCorrection A) =
      weightedWordWeight leftWeight rightWeight B +
        weightedWordWeight leftWeight rightWeight A := by
  rw [BRecipe.inverseCorrection, weighted_weight_correction,
    weighted_root_swap, Nat.add_comm]

/-- Remaining room below a fixed nilpotent cutoff for one complete recipe. -/
def cutoffDefect
    (n leftWeight rightWeight : ℕ)
    (R : BRecipe) :
    ℕ :=
  n - weightedWordWeight leftWeight rightWeight R

/-- A complete correction history descends when its cutoff defect decreases. -/
def CorrectionDescends
    (n leftWeight rightWeight : ℕ)
    (child parent : BRecipe) :
    Prop :=
  cutoffDefect n leftWeight rightWeight child <
    cutoffDefect n leftWeight rightWeight parent

/-- Complete-recipe correction descent is well-founded. -/
lemma correction_well_founded
    (n leftWeight rightWeight : ℕ) :
    WellFounded (CorrectionDescends n leftWeight rightWeight) := by
  unfold CorrectionDescends
  exact InvImage.wf (cutoffDefect n leftWeight rightWeight) Nat.lt_wfRel.wf

/-- Any retained pairwise correction descends from its left parent. -/
lemma descends_left
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (B A : BRecipe)
    (hcutoff :
      weightedWordWeight leftWeight rightWeight (B.correction A) < n) :
    CorrectionDescends n leftWeight rightWeight (B.correction A) B := by
  unfold CorrectionDescends cutoffDefect
  have hweight :=
    weighted_correction_left hleftWeight hrightWeight B A
  omega

/-- Any retained pairwise correction descends from its right parent. -/
lemma descends_right
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (B A : BRecipe)
    (hcutoff :
      weightedWordWeight leftWeight rightWeight (B.correction A) < n) :
    CorrectionDescends n leftWeight rightWeight (B.correction A) A := by
  unfold CorrectionDescends cutoffDefect
  have hweight :=
    weighted_correction_right hleftWeight hrightWeight B A
  omega

/-- Recursion principle for cutoff-specific complete-recipe packet builders. -/
theorem correctionDescends_induction
    {n leftWeight rightWeight : ℕ}
    {motive : BRecipe → Prop}
    (step :
      ∀ parent,
        (∀ child,
          CorrectionDescends n leftWeight rightWeight child parent →
            motive child) →
          motive parent)
    (R : BRecipe) :
    motive R :=
  (correction_well_founded n leftWeight rightWeight).induction R step

end BRSpec
end TCTex
end Towers

/-!
# Attaching Hall-Petresco block recipes to symbolic Hall factors

Independent-block Hall-Petresco recipes retain the raw left and right source
histories needed by Claim 8.  This file attaches one such recipe to two raw
Hall-coordinate addresses.  Compression is intentionally delayed until this
endpoint: recursively applying `Ring.choose` to an already-compressed
polynomial coefficient would require a separate normalization theorem.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open HACoeff

namespace BRSpec

/-- Evaluate the generalized-binomial coefficient recorded by one block recipe. -/
def coefficientValue
    (R : BRecipe)
    (leftExponent rightExponent : ℤ) :
    ℤ :=
  (R.leftBlocks.map fun degree => Ring.choose leftExponent degree).prod *
    (R.rightBlocks.map fun degree => Ring.choose rightExponent degree).prod

/-- Substitute two raw Hall-coordinate atoms into one Hall-Petresco recipe. -/
def boundWord
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (R : BRecipe)
    (leftAddress rightAddress : HEAddres H) :
    CWord (HEAddres H) :=
  CWord.hallPairBind (.atom leftAddress) (.atom rightAddress)
    R.erasedShape

/--
The substituted word weight is exactly the recipe's weighted left/right
source degree.
-/
@[simp]
lemma weight_boundWord
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (R : BRecipe)
    (leftAddress rightAddress : HEAddres H) :
    (boundWord R leftAddress rightAddress).weight HEAddres.weight =
      R.leftDegree * leftAddress.1 + R.rightDegree * rightAddress.1 := by
  rw [boundWord, CWord.weight_pair_bind,
    CWord.pair_atom_degree,
    R.erased_left_degree, R.erased_shape_degree]
  rfl

/--
Attach one independent-block Hall-Petresco history to its substituted Hall
word and its explicit Claim 8 coefficient formula.
-/
def symbolicFactor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : BRecipe)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    SPFactor H ι where
  word := boundWord R leftAddress rightAddress
  coefficient :=
    weightedBinomialFormula R leftInput rightInput
      leftAddress rightAddress (by
        rw [weight_boundWord])

@[simp]
lemma word_symbolicFactor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : BRecipe)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    (symbolicFactor R leftInput rightInput leftAddress rightAddress).word =
      boundWord R leftAddress rightAddress :=
  rfl

/-- The specialized symbolic factor has the expected weighted recipe degree. -/
@[simp]
lemma word_symbolic_factor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : BRecipe)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    (symbolicFactor R leftInput rightInput leftAddress rightAddress).word.weight
        HEAddres.weight =
      R.leftDegree * leftAddress.1 + R.rightDegree * rightAddress.1 := by
  exact weight_boundWord R leftAddress rightAddress

/-- Evaluate the explicit generalized-binomial coefficient of one recipe. -/
@[simp]
lemma coefficient_symbolic_factor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (R : BRecipe)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    (symbolicFactor R leftInput rightInput leftAddress rightAddress).coefficient.eval e =
      coefficientValue R
        (e leftInput leftAddress.1 leftAddress.2)
        (e rightInput rightAddress.1 rightAddress.2) := by
  exact weighted_binomial_formula e R leftInput rightInput
    leftAddress rightAddress _

/-- Evaluate one specialized block recipe as a substituted Hall-word power. -/
@[simp]
lemma eval_symbolicFactor
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (R : BRecipe)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    (symbolicFactor R leftInput rightInput leftAddress rightAddress).eval (n := n) e =
      R.erasedShape.eval
          (HPAtom.eval
            (HEAddres.freeLowerTruncation leftAddress)
            (HEAddres.freeLowerTruncation rightAddress)) ^
        coefficientValue R
          (e leftInput leftAddress.1 leftAddress.2)
          (e rightInput rightAddress.1 rightAddress.2) := by
  rw [SPFactor.eval, coefficient_symbolic_factor]
  exact congrArg
    (fun g =>
      g ^
        coefficientValue R
          (e leftInput leftAddress.1 leftAddress.2)
          (e rightInput rightAddress.1 rightAddress.2))
    (CWord.eval_pair_bind
      HEAddres.freeLowerTruncation
      (.atom leftAddress) (.atom rightAddress) R.erasedShape)

/-- Attach a finite ordered endpoint list of independent-block recipes. -/
def symbolicFactors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (recipes : List BRecipe)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    List (SPFactor H ι) :=
  recipes.map fun R =>
    symbolicFactor R leftInput rightInput leftAddress rightAddress

/-- Evaluate a finite ordered list of attached Hall-Petresco recipes. -/
lemma listSymbolicFactors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (recipes : List BRecipe)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    SPFactor.listEval (n := n) e
        (symbolicFactors recipes leftInput rightInput leftAddress rightAddress) =
      (recipes.map fun R =>
        R.erasedShape.eval
            (HPAtom.eval
              (HEAddres.freeLowerTruncation leftAddress)
              (HEAddres.freeLowerTruncation rightAddress)) ^
          coefficientValue R
            (e leftInput leftAddress.1 leftAddress.2)
            (e rightInput rightAddress.1 rightAddress.2)).prod := by
  induction recipes with
  | nil =>
      rfl
  | cons R recipes ih =>
      change
        (symbolicFactor R leftInput rightInput leftAddress rightAddress).eval e *
            SPFactor.listEval e
              (symbolicFactors recipes leftInput rightInput leftAddress rightAddress) =
          R.erasedShape.eval
                (HPAtom.eval
                  (HEAddres.freeLowerTruncation leftAddress)
                  (HEAddres.freeLowerTruncation rightAddress)) ^
              coefficientValue R
                (e leftInput leftAddress.1 leftAddress.2)
                (e rightInput rightAddress.1 rightAddress.2) *
            (recipes.map fun nextR =>
              nextR.erasedShape.eval
                    (HPAtom.eval
                      (HEAddres.freeLowerTruncation leftAddress)
                      (HEAddres.freeLowerTruncation rightAddress)) ^
                  coefficientValue nextR
                    (e leftInput leftAddress.1 leftAddress.2)
                    (e rightInput rightAddress.1 rightAddress.2)).prod
      rw [eval_symbolicFactor, ih]

/-- Every attached endpoint factor remembers one source block recipe. -/
lemma recipe_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {recipes : List BRecipe}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    {x : SPFactor H ι}
    (hx :
      x ∈ symbolicFactors recipes leftInput rightInput
        leftAddress rightAddress) :
    ∃ R ∈ recipes,
      x = symbolicFactor R leftInput rightInput leftAddress rightAddress := by
  rcases List.mem_map.mp hx with ⟨R, hR, rfl⟩
  exact ⟨R, hR, rfl⟩

/--
Specialized Hall-Petresco recipes are strictly above the raw left source
weight.
-/
lemma left_address_factor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : BRecipe)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    leftAddress.1 <
      (symbolicFactor R leftInput rightInput leftAddress rightAddress).word.weight
        HEAddres.weight := by
  rw [word_symbolic_factor]
  refine lt_of_le_of_lt (Nat.le_mul_of_pos_left leftAddress.1 (leftDegree_pos R)) ?_
  exact Nat.lt_add_of_pos_right (Nat.mul_pos (rightDegree_pos R)
    (HEAddres.weight_pos rightAddress))

/--
Specialized Hall-Petresco recipes are strictly above the raw right source
weight.
-/
lemma right_address_factor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : BRecipe)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    rightAddress.1 <
      (symbolicFactor R leftInput rightInput leftAddress rightAddress).word.weight
        HEAddres.weight := by
  rw [word_symbolic_factor]
  refine lt_of_le_of_lt (Nat.le_mul_of_pos_left rightAddress.1 (rightDegree_pos R)) ?_
  rw [Nat.add_comm]
  exact Nat.lt_add_of_pos_right (Nat.mul_pos (leftDegree_pos R)
    (HEAddres.weight_pos leftAddress))

end BRSpec
end TCTex
end Towers

/-!
# Polynomial equivalence of Hall-Petresco block recipes

Two complete block recipes may use different dependent placeholder alphabets
while carrying the same symbolic Hall-Petresco factor.  The symbolic data is
exactly the left block-degree list, the right block-degree list, and the erased
Hall-pair shape.

This file records that equivalence and proves that pairwise correction
preserves it.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace RPEquiv

open HACoeff
open BRSpec

namespace BRecipe

/-- Equality of the symbolic polynomial data carried by two block recipes. -/
def PolynomialEquivalent
    (R S : BRecipe) :
    Prop :=
  R.leftBlocks = S.leftBlocks ∧
    R.rightBlocks = S.rightBlocks ∧
      R.erasedShape = S.erasedShape

@[refl]
lemma polynomialEquivalent_refl
    (R : BRecipe) :
    PolynomialEquivalent R R :=
  ⟨rfl, rfl, rfl⟩

@[symm]
lemma polynomialEquivalent_symm
    {R S : BRecipe}
    (h : PolynomialEquivalent R S) :
    PolynomialEquivalent S R :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

@[trans]
lemma polynomialEquivalent_trans
    {R S T : BRecipe}
    (hRS : PolynomialEquivalent R S)
    (hST : PolynomialEquivalent S T) :
    PolynomialEquivalent R T :=
  ⟨hRS.1.trans hST.1, hRS.2.1.trans hST.2.1,
    hRS.2.2.trans hST.2.2⟩

/-- Polynomial-equivalent recipes have equal total left degree. -/
lemma left_degree_equivalent
    {R S : BRecipe}
    (h : PolynomialEquivalent R S) :
    R.leftDegree = S.leftDegree := by
  simp only [BRecipe.leftDegree, h.1]

/-- Polynomial-equivalent recipes have equal total right degree. -/
lemma right_degree_equivalent
    {R S : BRecipe}
    (h : PolynomialEquivalent R S) :
    R.rightDegree = S.rightDegree := by
  simp only [BRecipe.rightDegree, h.2.1]

/-- Polynomial-equivalent recipes have equal symbolic coefficients. -/
lemma coeff_poly_equivalent
    {R S : BRecipe}
    (h : PolynomialEquivalent R S)
    (leftExponent rightExponent : ℤ) :
    coefficientValue R leftExponent rightExponent =
      coefficientValue S leftExponent rightExponent := by
  simp only [coefficientValue]
  rw [h.1, h.2.1]

/-- Polynomial-equivalent recipes have equal weighted Hall degree. -/
lemma weighted_poly_equivalent
    {leftWeight rightWeight : ℕ}
    {R S : BRecipe}
    (h : PolynomialEquivalent R S) :
    weightedWordWeight leftWeight rightWeight R =
      weightedWordWeight leftWeight rightWeight S := by
  rw [weightedWordWeight, weightedWordWeight, h.2.2]

/-- Pairwise complete correction preserves symbolic polynomial data. -/
lemma polynomia_correcti
    {B B' A A' : BRecipe}
    (hB : PolynomialEquivalent B B')
    (hA : PolynomialEquivalent A A') :
    PolynomialEquivalent (B.correction A) (B'.correction A') := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [BRecipe.correction]
    rw [hB.1, hA.1]
  · simp only [BRecipe.correction]
    rw [hB.2.1, hA.2.1]
  · simp only [BRecipe.erasedShape_corr]
    rw [hB.2.2, hA.2.2]

end BRecipe
end RPEquiv
end TCTex
end Towers

/-!
# Specializing polynomial-equivalent block recipes

Polynomial-equivalent block recipes may retain different placeholder
alphabets, but specialization forgets those placeholders.  Their substituted
Hall words and evaluated symbolic factors therefore agree.  The same is true
for ordered lists related pointwise by polynomial equivalence.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace RPEquiv

universe u

open HACoeff
open BRSpec

namespace BRecipe

/-- Polynomial-equivalent recipes specialize to the same substituted word. -/
lemma bound_word_equivalent
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {R S : BRecipe}
    (h : PolynomialEquivalent R S)
    (leftAddress rightAddress : HEAddres H) :
    boundWord R leftAddress rightAddress =
      boundWord S leftAddress rightAddress := by
  simp only [boundWord]
  rw [h.2.2]

/--
Polynomial-equivalent recipes specialize to factors with the same ordinary
Hall weight.
-/
lemma symbolic_factor_equivalent
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {R S : BRecipe}
    (h : PolynomialEquivalent R S)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    (symbolicFactor R leftInput rightInput leftAddress rightAddress).word.weight
          HEAddres.weight =
      (symbolicFactor S leftInput rightInput leftAddress rightAddress).word.weight
          HEAddres.weight := by
  rw [word_symbolic_factor, word_symbolic_factor,
    left_degree_equivalent h,
    right_degree_equivalent h]

/--
Polynomial-equivalent recipes have identical specialized evaluation for every
source exponent family.
-/
lemma eval_symbolic_equivalent
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {R S : BRecipe}
    (h : PolynomialEquivalent R S)
    (e : ι → HEFam H)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    (symbolicFactor R leftInput rightInput leftAddress rightAddress).eval
          (n := n) e =
      (symbolicFactor S leftInput rightInput leftAddress rightAddress).eval
          (n := n) e := by
  rw [eval_symbolicFactor, eval_symbolicFactor, h.2.2,
    coeff_poly_equivalent h]

end BRecipe

/--
Pointwise polynomial-equivalent recipe packets have identical ordered
specialized evaluation.
-/
lemma symbolic_factors_forall₂_polynomialEquivalent
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {leftRecipes rightRecipes : List BRecipe}
    (h :
      List.Forall₂ BRecipe.PolynomialEquivalent
        leftRecipes rightRecipes)
    (e : ι → HEFam H)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    SPFactor.listEval (n := n) e
        (symbolicFactors leftRecipes leftInput rightInput
          leftAddress rightAddress) =
      SPFactor.listEval (n := n) e
        (symbolicFactors rightRecipes leftInput rightInput
          leftAddress rightAddress) := by
  induction h with
  | nil =>
      rfl
  | cons hrecipe _ ih =>
      simp only [symbolicFactors, List.map_cons,
        SPFactor.listEval_cons]
      rw [BRecipe.eval_symbolic_equivalent
        hrecipe e leftInput rightInput leftAddress rightAddress]
      congr 1

end RPEquiv
end TCTex
end Towers
