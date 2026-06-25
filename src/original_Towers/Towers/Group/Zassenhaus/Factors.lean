import Towers.Group.Zassenhaus.Expansions

/-!
# Symbolic Hall factors for repeated powers

This file attaches the one-variable repeated-block recipes to the symbolic Hall
words used by the product collector.  A raw source packet is chosen from one
of `q` repeated copies, so it contributes `Nat.choose q 1`.  When collection
emits a commutator correction, its two independent packet histories append and
its ordinary Hall weight is the sum of the parent weights.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

namespace PEAddres

/-- The ordinary Hall weight attached to one exponent address. -/
def weight
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (a : HEAddres H) :
    ℕ :=
  a.1

/-- Evaluate the Hall commutator selected by one exponent address. -/
def freeLowerTruncation
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (a : HEAddres H) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  ((H a.1).commutator a.2).freeLowerTruncation

/-- Every selected Hall address has positive ordinary weight. -/
lemma weight_pos
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (a : HEAddres H) :
    0 < PEAddres.weight a :=
  ((H a.1).commutator a.2).weight_pos

/-- Address evaluation lies in the lower-central term selected by its weight. -/
lemma free_truncation_series
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (a : HEAddres H) :
    PEAddres.freeLowerTruncation (n := n) a ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (PEAddres.weight a - 1) :=
  ((H a.1).commutator a.2).free_truncation_series

end PEAddres

/--
One symbolic Hall factor occurring while recollecting repeated copies of a
collected Hall word whose nonzero coordinates begin at `inputWeight`.
-/
structure SPFactora
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (inputWeight : ℕ) where
  word :
    CWord (HEAddres H)
  coefficient :
    ℤ
  recipe :
    BBRecipe inputWeight
      (word.weight PEAddres.weight)

namespace SPFactora

/--
A raw Hall exponent from one repeated copy.  It can occur only when its
ordinary Hall weight is at least the initial nonzero weight.
-/
def source
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (coefficient : ℤ)
    (a : HEAddres H)
    (ha : inputWeight ≤ PEAddres.weight a) :
    SPFactora H inputWeight where
  word := .atom a
  coefficient := coefficient
  recipe :=
    BBRecipe.select inputWeight
      (PEAddres.weight a) 1
      (by simp)
      (by simpa using ha)

/--
The commutator correction emitted by swapping two packet families.  Its
repeated-block choices are made independently.
-/
def bracket
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x y : SPFactora H inputWeight) :
    SPFactora H inputWeight where
  word := .commutator x.word y.word
  coefficient := x.coefficient * y.coefficient
  recipe := x.recipe.append y.recipe

/-- The unpowered Hall commutator value carried by one symbolic power factor. -/
def wordValue
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x : SPFactora H inputWeight) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  x.word.eval PEAddres.freeLowerTruncation

/-- The signed exponent contributed by one symbolic power factor. -/
def exponent
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (x : SPFactora H inputWeight) :
    ℤ :=
  x.coefficient * x.recipe.eval q

/-- Evaluate a symbolic power factor at a natural repetition count. -/
def eval
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (x : SPFactora H inputWeight) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  x.wordValue ^ x.exponent q

/-- The finite coordinate expansion consisting of one symbolic packet family. -/
def coordinateExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x : SPFactora H inputWeight) :
    BCExp inputWeight
      (x.word.weight PEAddres.weight) where
  terms := [(x.coefficient, x.recipe)]

@[simp]
lemma recipe_eval_source
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (coefficient : ℤ)
    (a : HEAddres H)
    (ha : inputWeight ≤ PEAddres.weight a)
    (q : ℕ) :
    (source coefficient a ha).recipe.eval q = q := by
  change (PBRecipe.select inputWeight 1 (by simp)).eval q = q
  simpa using PBRecipe.eval_select inputWeight 1 q (by simp)

@[simp]
lemma wordValue_source
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (coefficient : ℤ)
    (a : HEAddres H)
    (ha : inputWeight ≤ PEAddres.weight a) :
    (source coefficient a ha).wordValue (n := n) =
      ((H a.1).commutator a.2).freeLowerTruncation :=
  rfl

@[simp]
lemma exponent_source
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (coefficient : ℤ)
    (a : HEAddres H)
    (ha : inputWeight ≤ PEAddres.weight a)
    (q : ℕ) :
    (source coefficient a ha).exponent q = coefficient * q := by
  change coefficient * (source coefficient a ha).recipe.eval q =
    coefficient * q
  rw [recipe_eval_source]

@[simp]
lemma eval_source
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (coefficient : ℤ)
    (a : HEAddres H)
    (ha : inputWeight ≤ PEAddres.weight a)
    (q : ℕ) :
    (source coefficient a ha).eval (n := n) q =
      ((H a.1).commutator a.2).freeLowerTruncation ^
        (coefficient * q) := by
  simp [eval]

@[simp]
lemma word_weight_bracket
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x y : SPFactora H inputWeight) :
    (x.bracket y).word.weight PEAddres.weight =
      x.word.weight PEAddres.weight +
        y.word.weight PEAddres.weight :=
  rfl

@[simp]
lemma recipe_eval_bracket
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x y : SPFactora H inputWeight)
    (q : ℕ) :
    (x.bracket y).recipe.eval q = x.recipe.eval q * y.recipe.eval q :=
  BBRecipe.eval_append x.recipe y.recipe q

@[simp]
lemma coefficient_bracket
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x y : SPFactora H inputWeight) :
    (x.bracket y).coefficient = x.coefficient * y.coefficient :=
  rfl

@[simp]
lemma exponent_bracket
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x y : SPFactora H inputWeight)
    (q : ℕ) :
    (x.bracket y).exponent q = x.exponent q * y.exponent q := by
  change (x.coefficient * y.coefficient) *
      (x.bracket y).recipe.eval q =
    (x.coefficient * x.recipe.eval q) *
      (y.coefficient * y.recipe.eval q)
  rw [recipe_eval_bracket]
  ring

@[simp]
lemma wordValue_bracket
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x y : SPFactora H inputWeight) :
    (x.bracket y).wordValue (n := n) =
      ⁅x.wordValue (n := n), y.wordValue (n := n)⁆ :=
  rfl

@[simp]
lemma eval_bracket
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x y : SPFactora H inputWeight)
    (q : ℕ) :
    (x.bracket y).eval (n := n) q =
      ⁅x.wordValue (n := n), y.wordValue (n := n)⁆ ^
        (x.exponent q * y.exponent q) := by
  simp [eval]

/-- Every symbolic power factor has positive ordinary Hall weight. -/
lemma word_weight_pos
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x : SPFactora H inputWeight) :
    0 < x.word.weight PEAddres.weight :=
  CWord.weight_pos
    PEAddres.weight PEAddres.weight_pos x.word

/-- The unpowered commutator word lies in its predicted lower-central term. -/
lemma value_lower_series
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x : SPFactora H inputWeight) :
    x.wordValue (n := n) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (x.word.weight PEAddres.weight - 1) := by
  exact
    CWord.eval_lower_series
      PEAddres.freeLowerTruncation
      PEAddres.weight
      PEAddres.weight_pos
      PEAddres.free_truncation_series
      x.word

/-- Applying the repeated-block multiplicity does not lower commutator depth. -/
lemma eval_lower_series
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (x : SPFactora H inputWeight) :
    x.eval (n := n) q ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (x.word.weight PEAddres.weight - 1) :=
  (Subgroup.lowerCentralSeries
    (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (x.word.weight PEAddres.weight - 1)).zpow_mem
      x.value_lower_series (x.exponent q)

/-- A correction has strictly larger weight than its left parent. -/
lemma word_bracket_left
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x y : SPFactora H inputWeight) :
    x.word.weight PEAddres.weight <
      (x.bracket y).word.weight PEAddres.weight := by
  rw [word_weight_bracket]
  exact Nat.lt_add_of_pos_right y.word_weight_pos

/-- A correction has strictly larger weight than its right parent. -/
lemma word_bracket_right
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x y : SPFactora H inputWeight) :
    y.word.weight PEAddres.weight <
      (x.bracket y).word.weight PEAddres.weight := by
  rw [word_weight_bracket]
  exact Nat.lt_add_of_pos_left x.word_weight_pos

/-- One packet-family expansion evaluates to its signed exponent. -/
lemma coordinateExpansion_eval
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (x : SPFactora H inputWeight) :
    x.coordinateExpansion.eval = x.exponent := by
  ext q
  simp [coordinateExpansion, BCExp.eval,
    BRTerm.eval, exponent]

/--
The multiplicity of one symbolic packet family is an integer-valued polynomial
with the weight-controlled degree required by Claim 5.
-/
lemma recipe_valued_most
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (x : SPFactora H inputWeight) :
    IVMost
      x.recipe.eval
      (x.word.weight PEAddres.weight / inputWeight) := by
  exact x.recipe.toWeightedMonomial.integerValuedMost
    hinputWeight

/--
The signed exponent of one packet family is an integer-valued polynomial with
the weight-controlled degree required by Claim 5.
-/
lemma exponent_valued_most
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (x : SPFactora H inputWeight) :
    IVMost
      x.exponent
      (x.word.weight PEAddres.weight / inputWeight) := by
  rw [← x.coordinateExpansion_eval]
  exact x.coordinateExpansion.integerValuedMost
    hinputWeight

/-- Evaluate a list of symbolic power factors in order. -/
def listEval
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (L : List (SPFactora H inputWeight)) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  (L.map fun x => x.eval q).prod

@[simp]
lemma listEval_nil
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ) :
    listEval (n := n) (H := H) (inputWeight := inputWeight) q [] = 1 :=
  rfl

@[simp]
lemma listEval_cons
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (x : SPFactora H inputWeight)
    (L : List (SPFactora H inputWeight)) :
    listEval (n := n) q (x :: L) = x.eval q * listEval q L :=
  rfl

@[simp]
lemma listEval_append
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (L M : List (SPFactora H inputWeight)) :
    listEval (n := n) q (L ++ M) = listEval q L * listEval q M := by
  simp [listEval]

/--
A list of packet families whose word weights are all at least `r` evaluates in
the `r`th one-based lower-central layer.
-/
lemma list_series_weight
    {d n inputWeight r : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (q : ℕ)
    (L : List (SPFactora H inputWeight))
    (hL :
      ∀ x ∈ L,
        r ≤ x.word.weight PEAddres.weight) :
    listEval (n := n) q L ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (r - 1) := by
  apply Subgroup.list_prod_mem
  intro y hy
  rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
  exact Subgroup.lowerCentralSeries_antitone (Nat.sub_le_sub_right (hL x hx) 1)
    (x.eval_lower_series q)

/-- The final lower-central term vanishes in the defining truncation quotient. -/
lemma trunc_last_bot
    {d n : ℕ} :
    Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (n - 1) =
      ⊥ := by
  simpa [LowerCentralTruncation] using
    (lower_last_bot
      (G := FreeGroup (FreeGenerator.{u} d)) (c := n))

/-- A symbolic power factor at or above the truncation weight is trivial. -/
lemma eval_n_weight
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (x : SPFactora H inputWeight)
    (hx : n ≤ x.word.weight PEAddres.weight) :
    x.eval (n := n) q = 1 := by
  apply eq_bot_iff.mp trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (Nat.sub_le_sub_right hx 1)
    (x.eval_lower_series q)

/--
A list consisting entirely of factors at or above the truncation weight
evaluates trivially.
-/
lemma list_n_weight
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (L : List (SPFactora H inputWeight))
    (hL :
      ∀ x ∈ L,
        n ≤ x.word.weight PEAddres.weight) :
    listEval (n := n) q L = 1 := by
  apply eq_bot_iff.mp trunc_last_bot
  exact list_series_weight q L hL

end SPFactora

end TCTex
end Towers
