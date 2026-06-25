import Submission.Group.Zassenhaus.CorrectionFormulas

/-!
# Attaching normalized power expansions to Hall words

The arithmetic normalizer returns a finite list of repeated-block recipe terms.
A symbolic Hall collector needs a finite list of symbolic factors instead.
This file attaches every normalized term to one commutator word and proves that
the resulting factor list evaluates to the expected power of that word.  It
then packages the result as a correction-packet constructor.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

/-- Products of signed powers of one group element add their exponents. -/
lemma list_zpow_power
    {G : Type*}
    [Group G]
    (g : G)
    (L : List ℤ) :
    (L.map fun z => g ^ z).prod = g ^ L.sum := by
  induction L with
  | nil =>
      simp
  | cons z L ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, ih]
      exact (zpow_add g z L.sum).symm

/-- Mapped form of `list_zpow_power`. -/
lemma list_prod_zpow
    {G α : Type*}
    [Group G]
    (g : G)
    (f : α → ℤ)
    (L : List α) :
    (L.map fun x => g ^ f x).prod = g ^ (L.map f).sum := by
  simpa only [List.map_map, Function.comp_apply] using
    (list_zpow_power g (L.map f))

/-- Evaluate a finite sum of functions pointwise. -/
lemma list_sum_power
    {α M : Type*}
    [AddMonoid M]
    (L : List (α → M))
    (x : α) :
    L.sum x = (L.map fun f => f x).sum := by
  induction L with
  | nil =>
      simp
  | cons f L ih =>
      simp [ih]

namespace BRTerm

/-- Attach one normalized repeated-block term to one symbolic Hall word. -/
def symbolicPowerFactor
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (word : CWord (HEAddres H))
    (term :
      BRTerm inputWeight
        (word.weight PEAddres.weight)) :
    SPFactora H inputWeight where
  word := word
  coefficient := term.1
  recipe := term.2

@[simp]
lemma exponent_symbolic_factor
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (word : CWord (HEAddres H))
    (term :
      BRTerm inputWeight
        (word.weight PEAddres.weight)) :
    (term.symbolicPowerFactor word).exponent = term.eval := by
  ext q
  simp [symbolicPowerFactor, SPFactora.exponent,
    BRTerm.eval]

@[simp]
lemma symbolic_power_factor
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (word : CWord (HEAddres H))
    (term :
      BRTerm inputWeight
        (word.weight PEAddres.weight))
    (q : ℕ) :
    (term.symbolicPowerFactor word).eval (n := n) q =
      word.eval PEAddres.freeLowerTruncation ^
        term.eval q := by
  change
    word.eval PEAddres.freeLowerTruncation ^
        (term.1 * term.2.eval q) =
      word.eval PEAddres.freeLowerTruncation ^
        term.eval q
  simp [BRTerm.eval]

end BRTerm

namespace BCExp

/-- Attach every term of one normalized expansion to the same Hall word. -/
def symbolicPowerFactors
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (word : CWord (HEAddres H))
    (expansion :
      BCExp inputWeight
        (word.weight PEAddres.weight)) :
    List (SPFactora H inputWeight) :=
  expansion.terms.map fun term => term.symbolicPowerFactor word

/--
The symbolic factors attached to one normalized expansion evaluate to one
power of the selected Hall word.
-/
lemma list_power_factors
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (word : CWord (HEAddres H))
    (expansion :
      BCExp inputWeight
        (word.weight PEAddres.weight))
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (expansion.symbolicPowerFactors word) =
      word.eval PEAddres.freeLowerTruncation ^
        expansion.eval q := by
  simpa [symbolicPowerFactors, SPFactora.listEval,
    BCExp.eval, Function.comp_def,
    list_sum_power] using
      (list_prod_zpow
        (word.eval
          (PEAddres.freeLowerTruncation (n := n)))
        (fun term :
          BRTerm inputWeight
            (word.weight PEAddres.weight) => term.eval q)
        expansion.terms)

/-- Every attached symbolic factor retains the selected Hall word. -/
lemma symbolic_power_factors
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (word : CWord (HEAddres H))
    (expansion :
      BCExp inputWeight
        (word.weight PEAddres.weight))
    {factor : SPFactora H inputWeight}
    (hfactor : factor ∈ expansion.symbolicPowerFactors word) :
    factor.word = word := by
  rcases List.mem_map.mp hfactor with ⟨term, _hterm, rfl⟩
  rfl

end BCExp

/--
A normalized repeated-power exponent attached to one symbolic Hall word.
-/
structure SWExp
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (inputWeight : ℕ) where
  word : CWord (HEAddres H)
  expansion :
    BCExp inputWeight
      (word.weight PEAddres.weight)

namespace SWExp

/-- Emit the symbolic Hall factors represented by one word expansion. -/
def factors
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : SWExp H inputWeight) :
    List (SPFactora H inputWeight) :=
  wordExpansion.expansion.symbolicPowerFactors wordExpansion.word

/-- The signed exponent represented by one word expansion. -/
def exponent
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : SWExp H inputWeight) :
    ℕ → ℤ :=
  wordExpansion.expansion.eval

/-- Emitted symbolic factors evaluate to the represented word power. -/
lemma listEval_factors
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : SWExp H inputWeight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q wordExpansion.factors =
      wordExpansion.word.eval
          PEAddres.freeLowerTruncation ^
        wordExpansion.exponent q :=
  BCExp.list_power_factors
    wordExpansion.word wordExpansion.expansion q

/-- Every emitted factor has the represented Hall word. -/
lemma of_mem_factors
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansion : SWExp H inputWeight)
    {factor : SPFactora H inputWeight}
    (hfactor : factor ∈ wordExpansion.factors) :
    factor.word = wordExpansion.word :=
  BCExp.symbolic_power_factors
    wordExpansion.word wordExpansion.expansion hfactor

/-- Flatten the symbolic factors emitted by a finite list of word expansions. -/
def listFactors
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (wordExpansions : List (SWExp H inputWeight)) :
    List (SPFactora H inputWeight) :=
  wordExpansions.flatMap fun wordExpansion => wordExpansion.factors

/-- Evaluate the represented powers of a finite list of Hall words in order. -/
def listValue
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (wordExpansions : List (SWExp H inputWeight)) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  (wordExpansions.map fun wordExpansion =>
    wordExpansion.word.eval
        PEAddres.freeLowerTruncation ^
      wordExpansion.exponent q).prod

/-- Flattening a finite list of word expansions preserves its represented value. -/
lemma list_factors
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (q : ℕ)
    (wordExpansions : List (SWExp H inputWeight)) :
    SPFactora.listEval (n := n) q
        (listFactors wordExpansions) =
      listValue (n := n) q wordExpansions := by
  induction wordExpansions with
  | nil =>
      simp [listFactors, listValue]
  | cons wordExpansion wordExpansions ih =>
      change
        SPFactora.listEval (n := n) q
              (wordExpansion.factors ++ listFactors wordExpansions) =
          wordExpansion.word.eval
                PEAddres.freeLowerTruncation ^
              wordExpansion.exponent q *
            listValue (n := n) q wordExpansions
      rw [SPFactora.listEval_append,
        wordExpansion.listEval_factors, ih]

end SWExp

namespace SCForm

/-- Attach a normalized correction formula to its output Hall word. -/
noncomputable def toWordExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (word : CWord (HEAddres H))
    (formula :
      SCForm H inputWeight
        (word.weight PEAddres.weight)) :
    SWExp H inputWeight where
  word := word
  expansion := formula.expansion hinputWeight

@[simp]
lemma exponent_word_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (word : CWord (HEAddres H))
    (formula :
      SCForm H inputWeight
        (word.weight PEAddres.weight)) :
    (formula.toWordExpansion hinputWeight word).exponent = formula.eval := by
  exact formula.expansion_eval hinputWeight

end SCForm

namespace SHPkt

/--
Build a sound correction packet from a finite list of normalized higher-word
expansions and their remaining group-theoretic collection identity.
-/
def ofWordExpansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (B A : SPFactora H inputWeight)
    (wordExpansions :
      List (SWExp H inputWeight))
    (hvalue :
      ∀ q : ℕ,
        SWExp.listValue (n := n) q wordExpansions =
          ⁅B.eval (n := n) q, A.eval (n := n) q⁆)
    (hleft :
      ∀ wordExpansion ∈ wordExpansions,
        B.word.weight PEAddres.weight <
          wordExpansion.word.weight PEAddres.weight)
    (hright :
      ∀ wordExpansion ∈ wordExpansions,
        A.word.weight PEAddres.weight <
          wordExpansion.word.weight PEAddres.weight) :
    SHPkt n B A where
  factors := SWExp.listFactors wordExpansions
  listEval_eq q := by
    rw [SWExp.list_factors]
    exact hvalue q
  word_weight_left factor hfactor := by
    rcases List.mem_flatMap.mp hfactor with
      ⟨wordExpansion, hwordExpansion, hfactor⟩
    rw [wordExpansion.of_mem_factors hfactor]
    exact hleft wordExpansion hwordExpansion
  word_weight_right factor hfactor := by
    rcases List.mem_flatMap.mp hfactor with
      ⟨wordExpansion, hwordExpansion, hfactor⟩
    rw [wordExpansion.of_mem_factors hfactor]
    exact hright wordExpansion hwordExpansion

/--
Build a sound correction packet from a normalized higher-correction formula
and the remaining group-theoretic collection identity for its output word.
-/
noncomputable def ofWordFormula
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (B A : SPFactora H inputWeight)
    (word : CWord (HEAddres H))
    (formula :
      SCForm H inputWeight
        (word.weight PEAddres.weight))
    (hformula :
      ∀ q : ℕ,
        word.eval PEAddres.freeLowerTruncation ^
            formula.eval q =
          ⁅B.eval (n := n) q, A.eval (n := n) q⁆)
    (hleft :
      B.word.weight PEAddres.weight <
        word.weight PEAddres.weight)
    (hright :
      A.word.weight PEAddres.weight <
        word.weight PEAddres.weight) :
    SHPkt n B A where
  factors := (formula.toWordExpansion hinputWeight word).factors
  listEval_eq q := by
    rw [SWExp.listEval_factors,
      SCForm.exponent_word_expansion]
    exact hformula q
  word_weight_left factor hfactor := by
    rw [(formula.toWordExpansion hinputWeight word).of_mem_factors hfactor]
    exact hleft
  word_weight_right factor hfactor := by
    rw [(formula.toWordExpansion hinputWeight word).of_mem_factors hfactor]
    exact hright

end SHPkt

end TCTex
end Submission
