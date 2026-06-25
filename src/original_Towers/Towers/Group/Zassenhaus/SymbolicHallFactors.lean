import Towers.Group.Zassenhaus.FiniteSignedFormulas
import Towers.Group.Zassenhaus.SymbolicHallCollection

/-!
# Signed polynomial factors for nonterminal Hall collection

The terminal symbolic collector can attach one generalized-binomial monomial
to each Hall word.  Nonterminal Hall-Petresco expansion needs a richer state:
one Hall word raised to a finite signed formula.  This file packages that state
and proves the lower-central and evaluation lemmas needed by a recursive
collector.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

/--
One Hall word raised to a finite signed Claim 8 generalized-binomial formula.
-/
structure SPFactor
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  word :
    CWord (HEAddres H)
  coefficient :
    WBForm H ι
      (word.weight HEAddres.weight)

namespace SPFactor

/-- One raw Hall exponent before any nonterminal collection swaps. -/
def source
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (j : ι)
    (a : HEAddres H) :
    SPFactor H ι where
  word := .atom a
  coefficient := WBForm.inputExponent j a

/-- Embed an earlier one-monomial symbolic factor into the signed formula state. -/
def ofMonomial
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x : SCFactor H ι) :
    SPFactor H ι where
  word := x.word
  coefficient := WBForm.singleton (1, x.coefficient)

/-- Relabel source blocks while preserving the Hall word and signed formula. -/
def mapInput
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    (f : ι → κ)
    (x : SPFactor H ι) :
    SPFactor H κ where
  word := x.word
  coefficient := x.coefficient.mapInput f

/--
Leading bracket correction of two signed polynomial factors.  Full
Hall-Petresco packets may also emit higher words, but their coefficient
formulas are built from this multiplicative operation.
-/
def bracket
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x y : SPFactor H ι) :
    SPFactor H ι where
  word := .commutator x.word y.word
  coefficient := x.coefficient.mul y.coefficient le_rfl

/-- The unpowered Hall word value carried by one polynomial factor. -/
def wordValue
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x : SPFactor H ι) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  x.word.eval HEAddres.freeLowerTruncation

/-- Evaluate one signed polynomial Hall factor on its source exponent families. -/
def eval
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (x : SPFactor H ι) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  x.wordValue ^ x.coefficient.eval e

@[simp]
lemma coefficient_eval_source
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (j : ι)
    (a : HEAddres H) :
    (source j a).coefficient.eval e = e j a.1 a.2 := by
  exact WBForm.eval_inputExponent e j a

@[simp]
lemma eval_source
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (j : ι)
    (a : HEAddres H) :
    (source j a).eval (n := n) e =
      ((H a.1).commutator a.2).freeLowerTruncation ^
        e j a.1 a.2 := by
  rw [eval, coefficient_eval_source]
  rfl

@[simp]
lemma coefficient_eval_monomial
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (x : SCFactor H ι) :
    (ofMonomial x).coefficient.eval e = x.coefficient.eval e := by
  simp [ofMonomial, WBTerm.eval]

@[simp]
lemma eval_ofMonomial
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (x : SCFactor H ι) :
    (ofMonomial x).eval (n := n) e = x.eval e := by
  rw [eval, coefficient_eval_monomial]
  rfl

@[simp]
lemma coefficient_eval_input
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    (e : κ → HEFam H)
    (f : ι → κ)
    (x : SPFactor H ι) :
    (x.mapInput f).coefficient.eval e = x.coefficient.eval (e ∘ f) := by
  simp [mapInput]

@[simp]
lemma eval_mapInput
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    (e : κ → HEFam H)
    (f : ι → κ)
    (x : SPFactor H ι) :
    (x.mapInput f).eval (n := n) e = x.eval (e ∘ f) := by
  simp [eval, mapInput, wordValue]

@[simp]
lemma word_weight_bracket
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x y : SPFactor H ι) :
    (x.bracket y).word.weight HEAddres.weight =
      x.word.weight HEAddres.weight +
        y.word.weight HEAddres.weight :=
  rfl

@[simp]
lemma coefficient_eval_bracket
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (x y : SPFactor H ι) :
    (x.bracket y).coefficient.eval e =
      x.coefficient.eval e * y.coefficient.eval e := by
  simp [bracket]

@[simp]
lemma wordValue_bracket
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x y : SPFactor H ι) :
    (x.bracket y).wordValue (n := n) =
      ⁅x.wordValue (n := n), y.wordValue (n := n)⁆ :=
  rfl

@[simp]
lemma eval_bracket
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (x y : SPFactor H ι) :
    (x.bracket y).eval (n := n) e =
      ⁅x.wordValue (n := n), y.wordValue (n := n)⁆ ^
        (x.coefficient.eval e * y.coefficient.eval e) := by
  rw [eval, wordValue_bracket, coefficient_eval_bracket]

/-- Every polynomial Hall factor has positive ordinary word weight. -/
lemma word_weight_pos
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x : SPFactor H ι) :
    0 < x.word.weight HEAddres.weight :=
  CWord.weight_pos
    HEAddres.weight HEAddres.weight_pos x.word

/-- A leading bracket correction has larger weight than its left input. -/
lemma word_bracket_left
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x y : SPFactor H ι) :
    x.word.weight HEAddres.weight <
      (x.bracket y).word.weight HEAddres.weight := by
  rw [word_weight_bracket]
  exact Nat.lt_add_of_pos_right y.word_weight_pos

/-- A leading bracket correction has larger weight than its right input. -/
lemma word_bracket_right
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x y : SPFactor H ι) :
    y.word.weight HEAddres.weight <
      (x.bracket y).word.weight HEAddres.weight := by
  rw [word_weight_bracket]
  exact Nat.lt_add_of_pos_left x.word_weight_pos

/-- The unpowered Hall word lies in its predicted lower-central term. -/
lemma value_lower_series
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x : SPFactor H ι) :
    x.wordValue (n := n) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (x.word.weight HEAddres.weight - 1) := by
  exact
    CWord.eval_lower_series
      HEAddres.freeLowerTruncation
      HEAddres.weight
      HEAddres.weight_pos
      HEAddres.free_truncation_series
      x.word

/-- Applying the signed polynomial coefficient does not lower commutator depth. -/
lemma eval_lower_series
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (x : SPFactor H ι) :
    x.eval (n := n) e ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (x.word.weight HEAddres.weight - 1) :=
  (Subgroup.lowerCentralSeries
    (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (x.word.weight HEAddres.weight - 1)).zpow_mem
      x.value_lower_series (x.coefficient.eval e)

/-- Evaluate a list of signed polynomial Hall factors in order. -/
def listEval
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (L : List (SPFactor H ι)) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  (L.map fun x => x.eval e).prod

@[simp]
lemma listEval_nil
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H) :
    listEval (n := n) e [] = 1 :=
  rfl

@[simp]
lemma listEval_cons
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (x : SPFactor H ι)
    (L : List (SPFactor H ι)) :
    listEval (n := n) e (x :: L) = x.eval e * listEval e L :=
  rfl

@[simp]
lemma listEval_append
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (L M : List (SPFactor H ι)) :
    listEval (n := n) e (L ++ M) = listEval e L * listEval e M := by
  simp [listEval]

/-- Embedding one-monomial factors into signed factors preserves list evaluation. -/
lemma list_eval_monomial
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (L : List (SCFactor H ι)) :
    listEval (n := n) e (L.map ofMonomial) =
      SCFactor.listEval e L := by
  induction L with
  | nil =>
      rfl
  | cons x L ih =>
      change (ofMonomial x).eval e * listEval e (L.map ofMonomial) =
        x.eval e * SCFactor.listEval e L
      rw [eval_ofMonomial, ih]

/-- A polynomial Hall factor at or above the cutoff evaluates trivially. -/
lemma eval_n_weight
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (x : SPFactor H ι)
    (hx : n ≤ x.word.weight HEAddres.weight) :
    x.eval (n := n) e = 1 := by
  apply eq_bot_iff.mp
    SCFactor.trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (Nat.sub_le_sub_right hx 1)
    (x.eval_lower_series e)

end SPFactor

end TCTex
end Towers
