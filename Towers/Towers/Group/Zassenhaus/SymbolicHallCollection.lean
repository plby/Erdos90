import Towers.Group.Zassenhaus.InversePolynomials

/-!
# Symbolic factors for parametrized Hall collection

A parametrized Hall collector repeatedly swaps out-of-order factors and emits
higher-weight commutator corrections.  This file packages the data carried by
one emitted factor:

* a commutator word in weighted Hall addresses;
* a weighted product of generalized binomial coefficients;
* the lower-central depth forced by the commutator word.

The file is intentionally isolated from the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

namespace HEAddres

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
    0 < a.weight :=
  ((H a.1).commutator a.2).weight_pos

/-- Address evaluation lies in the lower-central term selected by its weight. -/
lemma free_truncation_series
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (a : HEAddres H) :
    a.freeLowerTruncation (n := n) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (a.weight - 1) :=
  ((H a.1).commutator a.2).free_truncation_series

end HEAddres

/--
One factor emitted by a symbolic Hall collector.  The binomial recipe is
bounded by the output commutator weight, recording the invariant that a packet
cannot contribute below the total weight of the source labels it selected.
-/
structure SCFactor
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  word :
    CWord (HEAddres H)
  coefficient :
    WHMono H ι
      (word.weight HEAddres.weight)

namespace SCFactor

/-- A raw source Hall exponent before any collection swaps. -/
def source
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (j : ι)
    (a : HEAddres H) :
    SCFactor H ι where
  word := .atom a
  coefficient :=
    WHMono.single j a (by
      simp [HEAddres.weight])

/-- Relabel source blocks while preserving the emitted commutator word. -/
def mapInput
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    (f : ι → κ)
    (x : SCFactor H ι) :
    SCFactor H κ where
  word := x.word
  coefficient := x.coefficient.mapInput f

/--
Combine two packet recipes when a collection swap emits their commutator
correction.
-/
def bracket
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x y : SCFactor H ι) :
    SCFactor H ι where
  word := .commutator x.word y.word
  coefficient := x.coefficient.append y.coefficient le_rfl

/-- The group value of the emitted commutator word before applying its power. -/
def wordValue
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x : SCFactor H ι) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  x.word.eval HEAddres.freeLowerTruncation

/-- Evaluate one symbolic factor on its input Hall exponent families. -/
def eval
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (x : SCFactor H ι) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  x.wordValue ^ x.coefficient.eval e

/-- Every emitted commutator word has positive weight. -/
lemma word_weight_pos
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x : SCFactor H ι) :
    0 < x.word.weight HEAddres.weight :=
  CWord.weight_pos
    HEAddres.weight HEAddres.weight_pos x.word

/-- The unpowered commutator word lies in its predicted lower-central term. -/
lemma value_lower_series
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x : SCFactor H ι) :
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

/-- Applying the symbolic coefficient does not lower the commutator depth. -/
lemma eval_lower_series
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (x : SCFactor H ι) :
    x.eval (n := n) e ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (x.word.weight HEAddres.weight - 1) :=
  (Subgroup.lowerCentralSeries
    (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (x.word.weight HEAddres.weight - 1)).zpow_mem
      x.value_lower_series (x.coefficient.eval e)

@[simp]
lemma coefficient_eval_source
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (j : ι)
    (a : HEAddres H) :
    (source j a).coefficient.eval e = e j a.1 a.2 := by
  simp [source]

@[simp]
lemma wordValue_source
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (j : ι)
    (a : HEAddres H) :
    (source j a).wordValue (n := n) =
      ((H a.1).commutator a.2).freeLowerTruncation :=
  rfl

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
  simp [eval]

@[simp]
lemma coefficient_eval_input
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    (e : κ → HEFam H)
    (f : ι → κ)
    (x : SCFactor H ι) :
    (x.mapInput f).coefficient.eval e = x.coefficient.eval (e ∘ f) := by
  simp [mapInput]

@[simp]
lemma eval_mapInput
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι κ : Type}
    (e : κ → HEFam H)
    (f : ι → κ)
    (x : SCFactor H ι) :
    (x.mapInput f).eval (n := n) e = x.eval (e ∘ f) := by
  simp [eval, mapInput, wordValue]

@[simp]
lemma word_weight_bracket
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x y : SCFactor H ι) :
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
    (x y : SCFactor H ι) :
    (x.bracket y).coefficient.eval e =
      x.coefficient.eval e * y.coefficient.eval e := by
  simp [bracket]

@[simp]
lemma wordValue_bracket
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x y : SCFactor H ι) :
    (x.bracket y).wordValue (n := n) =
      ⁅x.wordValue (n := n), y.wordValue (n := n)⁆ :=
  rfl

@[simp]
lemma eval_bracket
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (x y : SCFactor H ι) :
    (x.bracket y).eval (n := n) e =
      ⁅x.wordValue (n := n), y.wordValue (n := n)⁆ ^
        (x.coefficient.eval e * y.coefficient.eval e) := by
  rw [eval, wordValue_bracket, coefficient_eval_bracket]

/-- A bracket correction has strictly larger weight than its left input. -/
lemma word_bracket_left
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x y : SCFactor H ι) :
    x.word.weight HEAddres.weight <
      (x.bracket y).word.weight HEAddres.weight := by
  rw [word_weight_bracket]
  exact Nat.lt_add_of_pos_right y.word_weight_pos

/-- A bracket correction has strictly larger weight than its right input. -/
lemma word_bracket_right
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x y : SCFactor H ι) :
    y.word.weight HEAddres.weight <
      (x.bracket y).word.weight HEAddres.weight := by
  rw [word_weight_bracket]
  exact Nat.lt_add_of_pos_left x.word_weight_pos

/-- Evaluate a list of symbolic Hall factors in order. -/
def listEval
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (L : List (SCFactor H ι)) :
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
    (x : SCFactor H ι)
    (L : List (SCFactor H ι)) :
    listEval (n := n) e (x :: L) = x.eval e * listEval e L :=
  rfl

@[simp]
lemma listEval_append
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (L M : List (SCFactor H ι)) :
    listEval (n := n) e (L ++ M) = listEval e L * listEval e M := by
  simp [listEval]

/--
A list of emitted factors whose word weights are all at least `r` evaluates in
the `r`th one-based lower-central layer.
-/
lemma list_series_weight
    {d n r : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (e : ι → HEFam H)
    (L : List (SCFactor H ι))
    (hL :
      ∀ x ∈ L,
        r ≤ x.word.weight HEAddres.weight) :
    listEval (n := n) e L ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (r - 1) := by
  apply Subgroup.list_prod_mem
  intro y hy
  rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
  exact Subgroup.lowerCentralSeries_antitone (Nat.sub_le_sub_right (hL x hx) 1)
    (x.eval_lower_series e)

/-- The final lower-central term vanishes in the defining truncation quotient. -/
lemma trunc_last_bot
    {d n : ℕ} :
    Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (n - 1) =
      ⊥ := by
  simpa [LowerCentralTruncation] using
    (lower_last_bot
      (G := FreeGroup (FreeGenerator.{u} d)) (c := n))

/-- A symbolic factor at or above the truncation weight evaluates trivially. -/
lemma eval_n_weight
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (x : SCFactor H ι)
    (hx : n ≤ x.word.weight HEAddres.weight) :
    x.eval (n := n) e = 1 := by
  apply eq_bot_iff.mp trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (Nat.sub_le_sub_right hx 1)
    (x.eval_lower_series e)

/--
A list consisting entirely of factors at or above the truncation weight
evaluates trivially.
-/
lemma list_n_weight
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (L : List (SCFactor H ι))
    (hL :
      ∀ x ∈ L,
        n ≤ x.word.weight HEAddres.weight) :
    listEval (n := n) e L = 1 := by
  apply eq_bot_iff.mp trunc_last_bot
  exact list_series_weight e L hL

end SCFactor

end TCTex
end Towers

/-!
# Symbolic steps for parametrized Hall collection

The product collector swaps adjacent out-of-order factors.  Moving `B` past `A`
inserts a list of higher-weight corrections whose product is `[B, A]`.

This file isolates the generic algebra of that move.  A later Hall-algorithm
constructor only needs to build `HCPkt`s.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

/--
The symbolic output required to move one evaluated factor `B` to the right of
one evaluated factor `A`.

Every emitted factor has strictly larger word weight than both inputs.  This is
the termination invariant behind the usual parametrized Hall algorithm.
-/
structure HCPkt
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (B A : SCFactor H ι) where
  factors :
    List (SCFactor H ι)
  listEval_eq :
    ∀ {n : ℕ} (e : ι → HEFam H),
      SCFactor.listEval (n := n) e factors =
        ⁅B.eval (n := n) e, A.eval (n := n) e⁆
  word_weight_left :
    ∀ x ∈ factors,
      B.word.weight HEAddres.weight <
        x.word.weight HEAddres.weight
  word_weight_right :
    ∀ x ∈ factors,
      A.word.weight HEAddres.weight <
        x.word.weight HEAddres.weight

namespace HCPkt

/-- Packet evaluation is exactly the correction needed for the adjacent swap. -/
lemma list_mul_swap
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : HCPkt B A)
    (e : ι → HEFam H) :
    SCFactor.listEval (n := n) e C.factors *
          A.eval (n := n) e * B.eval (n := n) e =
      B.eval (n := n) e * A.eval (n := n) e := by
  rw [C.listEval_eq]
  simp [commutatorElement_def, mul_assoc]

/-- Left-input weight growth in a form convenient for arithmetic bounds. -/
lemma succ_weight_left
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : HCPkt B A)
    {x : SCFactor H ι}
    (hx : x ∈ C.factors) :
    B.word.weight HEAddres.weight + 1 ≤
      x.word.weight HEAddres.weight :=
  C.word_weight_left x hx

/-- Right-input weight growth in a form convenient for arithmetic bounds. -/
lemma succ_weight_right
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : HCPkt B A)
    {x : SCFactor H ι}
    (hx : x ∈ C.factors) :
    A.word.weight HEAddres.weight + 1 ≤
      x.word.weight HEAddres.weight :=
  C.word_weight_right x hx

/--
A correction packet emitted one step below the truncation cutoff is already
trivial in the truncation quotient.
-/
lemma n_succ_left
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : HCPkt B A)
    (e : ι → HEFam H)
    (hB : n ≤ B.word.weight HEAddres.weight + 1) :
    SCFactor.listEval (n := n) e C.factors = 1 := by
  apply SCFactor.list_n_weight
  intro x hx
  exact hB.trans (C.succ_weight_left hx)

/--
The symmetric truncation criterion using the right input of a correction
packet.
-/
lemma n_succ_right
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : HCPkt B A)
    (e : ι → HEFam H)
    (hA : n ≤ A.word.weight HEAddres.weight + 1) :
    SCFactor.listEval (n := n) e C.factors = 1 := by
  apply SCFactor.list_n_weight
  intro x hx
  exact hA.trans (C.succ_weight_right hx)

end HCPkt

/-- One sound adjacent symbolic Hall-collection move. -/
inductive SHStep
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) :
    List (SCFactor H ι) →
      List (SCFactor H ι) → Prop where
  | obstruction
      (P S : List (SCFactor H ι))
      (B A : SCFactor H ι)
      (C : HCPkt B A) :
      SHStep H ι
        (P ++ [B, A] ++ S)
        (P ++ C.factors ++ [A, B] ++ S)

/-- Finite sequence of sound adjacent symbolic Hall-collection moves. -/
abbrev SHRw
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (L R : List (SCFactor H ι)) :
    Prop :=
  Relation.ReflTransGen (SHStep H ι) L R

/-- One symbolic Hall-collection move preserves the evaluated product. -/
lemma SHStep.listEval_eq
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SCFactor H ι)}
    (h : SHStep H ι L R)
    (e : ι → HEFam H) :
    SCFactor.listEval (n := n) e R =
      SCFactor.listEval (n := n) e L := by
  cases h with
  | obstruction P S B A C =>
      calc
        SCFactor.listEval (n := n) e
              (P ++ C.factors ++ [A, B] ++ S) =
            SCFactor.listEval e P *
                (SCFactor.listEval e C.factors *
                  A.eval e * B.eval e) *
              SCFactor.listEval e S := by
            simp [mul_assoc]
        _ =
            SCFactor.listEval e P *
                (B.eval e * A.eval e) *
              SCFactor.listEval e S := by
            rw [C.list_mul_swap]
        _ =
            SCFactor.listEval (n := n) e
              (P ++ [B, A] ++ S) := by
            simp [mul_assoc]

/-- Any finite symbolic Hall-collection run preserves the evaluated product. -/
lemma SHRw.listEval_eq
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SCFactor H ι)}
    (h : SHRw L R)
    (e : ι → HEFam H) :
    SCFactor.listEval (n := n) e R =
      SCFactor.listEval (n := n) e L := by
  induction h with
  | refl => rfl
  | tail hLR hstep ih =>
      exact (hstep.listEval_eq e).trans ih

end TCTex
end Towers

/-!
# Source lists for parametrized Hall collection

The generic symbolic rewrite engine starts from the Hall factors already
present in its input blocks.  This file builds those source lists and proves
that their evaluations are the existing collected Hall products.
-/

namespace Towers
namespace TCTex

universe u

/-- The ordered symbolic source factors in one fixed Hall-weight layer. -/
def symbolicWeightFactors
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    {ι : Type}
    (j : ι)
    (r : ℕ) :
    List (SCFactor H ι) :=
  (Finset.univ.sort fun i i' : (H r).index => i ≤ i').map fun i =>
    SCFactor.source j
      (⟨r, i⟩ : HEAddres H)

/-- Fixed-weight symbolic sources evaluate to the corresponding Hall segment. -/
lemma list_source_factors
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    {ι : Type}
    (e : ι → HEFam H)
    (j : ι)
    (r : ℕ) :
    SCFactor.listEval (n := n) e
        (symbolicWeightFactors H j r) =
      (H r).collectedWeightProduct (n := n) (e j r) := by
  simp only [symbolicWeightFactors,
    SCFactor.listEval, List.map_map, Function.comp_def,
    SCFactor.eval_source,
    BCWta.collectedWeightProduct,
    BCWta.collected_lower_centralterm,
    BCWt.evalin_freelower_centtrunterm]
  simp [Function.comp_def]

/-- Symbolic source factors through ordinary Hall weight `k`. -/
def symbolicPrefixFactors
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    {ι : Type}
    (j : ι)
    (k : ℕ) :
    List (SCFactor H ι) :=
  (List.range k).flatMap fun q =>
    symbolicWeightFactors H j (q + 1)

/-- Prefix source factors evaluate to the existing collected Hall prefix. -/
lemma list_prefix_factors
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    {ι : Type}
    (e : ι → HEFam H)
    (j : ι)
    (k : ℕ) :
    SCFactor.listEval (n := n) e
        (symbolicPrefixFactors H j k) =
      collectedPrefixProduct (n := n) H (e j) k := by
  induction k with
  | zero =>
      simp [symbolicPrefixFactors, collectedPrefixProduct]
  | succ k ih =>
      rw [symbolicPrefixFactors, List.range_succ, List.flatMap_append,
        List.flatMap_singleton, SCFactor.listEval_append,
        collected_prefix_succ]
      change
        SCFactor.listEval e
              (symbolicPrefixFactors H j k) *
            SCFactor.listEval e
              (symbolicWeightFactors H j (k + 1)) =
          collectedPrefixProduct H (e j) k *
            (H (k + 1)).collectedWeightProduct (e j (k + 1))
      rw [ih, list_source_factors]

/-- Symbolic source factors for one full collected Hall product. -/
def symbolicHallFactors
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    {ι : Type}
    (j : ι) :
    List (SCFactor H ι) :=
  symbolicPrefixFactors H j (n - 1)

/-- One full symbolic source block evaluates to its collected Hall product. -/
lemma eval_symbolic_factors
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    {ι : Type}
    (e : ι → HEFam H)
    (j : ι) :
    SCFactor.listEval (n := n) e
        (symbolicHallFactors (n := n) H j) =
      collectedHallProduct (n := n) H (e j) := by
  simp [symbolicHallFactors, collectedHallProduct,
    list_prefix_factors]

/-- Concatenate the symbolic source blocks selected by a list of input labels. -/
def symbolicSourceFactors
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    {ι : Type}
    (labels : List ι) :
    List (SCFactor H ι) :=
  labels.flatMap fun j => symbolicHallFactors (n := n) H j

/-- A concatenated source list evaluates to the product of its collected blocks. -/
lemma symbolic_source_factors
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    {ι : Type}
    (e : ι → HEFam H)
    (labels : List ι) :
    SCFactor.listEval (n := n) e
        (symbolicSourceFactors (n := n) H labels) =
      (labels.map fun j => collectedHallProduct (n := n) H (e j)).prod := by
  induction labels with
  | nil =>
      simp [symbolicSourceFactors]
  | cons j labels ih =>
      rw [symbolicSourceFactors, List.flatMap_cons,
        SCFactor.listEval_append]
      change
        SCFactor.listEval e (symbolicHallFactors H j) *
            SCFactor.listEval e
              (symbolicSourceFactors H labels) =
          collectedHallProduct H (e j) *
            (labels.map fun j => collectedHallProduct H (e j)).prod
      rw [eval_symbolic_factors, ih]

/-- The source list attached to an ordinary finite list of Hall exponent blocks. -/
def indexedSymbolicFactors
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H)) :
    List (SCFactor H (Fin e.length)) :=
  symbolicSourceFactors (n := n) H (List.finRange e.length)

/--
The indexed symbolic source list is exactly the raw finite product consumed by
TeX Claim 8.
-/
lemma indexed_symbolic_factors
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H)) :
    SCFactor.listEval (n := n) (fun j : Fin e.length => e.get j)
        (indexedSymbolicFactors (n := n) H e) =
      collectedHallProducts (n := n) H e := by
  rw [indexedSymbolicFactors,
    symbolic_source_factors]
  unfold collectedHallProducts
  simpa only [List.map_map, Function.comp_apply] using congrArg
    (fun L : List (HEFam H) =>
      (L.map fun f => collectedHallProduct (n := n) H f).prod)
    (List.map_get_finRange e)

/--
The raw symbolic source list for the inverse of one collected Hall product:
reverse the factor order and negate every source exponent.
-/
def symbolicInverseFactors
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    List (SCFactor H (Fin 1)) :=
  (symbolicHallFactors (n := n) H (0 : Fin 1)).reverse

/--
The raw inverse source list evaluates to the inverse collected Hall product
consumed by the inverse form of TeX Claim 8.
-/
lemma list_symbolic_factors
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H) :
    SCFactor.listEval (n := n)
        (fun _ : Fin 1 => negExponentFamily e)
        (symbolicInverseFactors (n := n) H) =
      (collectedHallProduct (n := n) H e)⁻¹ := by
  rw [← eval_symbolic_factors H (fun _ : Fin 1 => e) (0 : Fin 1)]
  simp [symbolicInverseFactors, symbolicHallFactors,
    symbolicPrefixFactors, symbolicWeightFactors,
    SCFactor.listEval, List.map_reverse, List.map_flatMap,
    List.map_map,
    Function.comp_def, negExponentFamily, zpow_neg, List.prod_inv_reverse]

end TCTex
end Towers

/-!
# Truncating symbolic Hall collection

In the free nilpotent quotient `F_d / gamma_n(F_d)`, every symbolic Hall factor
of ordinary word weight at least `n` evaluates to the identity.  The Hall
collector can therefore erase such factors as soon as they appear.

This file packages that finite-control operation for symbolic factor lists and
correction packets.  After truncation, every emitted correction lies strictly
between the parent weights and the fixed cutoff.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

namespace SCFactor

/-- Remaining room below the nilpotent truncation cutoff. -/
def cutoffDefect
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ)
    (x : SCFactor H ι) :
    ℕ :=
  n - x.word.weight HEAddres.weight

/-- Keep precisely the symbolic factors whose ordinary word weight is below `n`. -/
def truncate
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ)
    (L : List (SCFactor H ι)) :
    List (SCFactor H ι) :=
  L.filter fun x => x.word.weight HEAddres.weight < n

@[simp]
lemma truncate_nil
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ) :
    truncate n ([] : List (SCFactor H ι)) = [] :=
  rfl

@[simp]
lemma truncate_append
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ)
    (L M : List (SCFactor H ι)) :
    truncate n (L ++ M) = truncate n L ++ truncate n M := by
  simp [truncate]

/-- Every retained symbolic factor is genuinely below the fixed cutoff. -/
lemma word_weight_truncate
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L : List (SCFactor H ι)}
    {x : SCFactor H ι}
    (hx : x ∈ truncate n L) :
    x.word.weight HEAddres.weight < n := by
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hx).2

/-- Truncating twice at the same cutoff has no further effect. -/
@[simp]
lemma truncate_truncate
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (L : List (SCFactor H ι)) :
    truncate n (truncate n L) = truncate n L := by
  simp [truncate]

/-- Truncation never increases the number of symbolic factors. -/
lemma length_truncate_le
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (L : List (SCFactor H ι)) :
    (truncate n L).length ≤ L.length := by
  simpa [truncate] using
    (List.length_filter_le
      (fun x : SCFactor H ι =>
        decide (x.word.weight HEAddres.weight < n)) L)

/--
Discarding factors at or above the nilpotent truncation weight leaves the
evaluated list product unchanged.
-/
lemma listEval_truncate
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (L : List (SCFactor H ι)) :
    listEval (n := n) e (truncate n L) = listEval e L := by
  induction L with
  | nil =>
      rfl
  | cons x L ih =>
      by_cases hx : x.word.weight HEAddres.weight < n
      · rw [show truncate n (x :: L) = x :: truncate n L by
              simp [truncate, hx]]
        change
          x.eval (n := n) e * listEval (n := n) e (truncate n L) =
            x.eval (n := n) e * listEval (n := n) e L
        rw [ih]
      · have hnx : n ≤ x.word.weight HEAddres.weight :=
          Nat.le_of_not_gt hx
        rw [show truncate n (x :: L) = truncate n L by
              simp [truncate, hx]]
        change
          listEval (n := n) e (truncate n L) =
            x.eval (n := n) e * listEval (n := n) e L
        rw [ih, eval_n_weight e x hnx, one_mul]

/-- A list is physically truncated when all of its factors lie below `n`. -/
def IsTruncated
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ)
    (L : List (SCFactor H ι)) :
    Prop :=
  ∀ x ∈ L, x.word.weight HEAddres.weight < n

/-- Truncation always produces a physically truncated list. -/
lemma isTruncated_truncate
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (L : List (SCFactor H ι)) :
    IsTruncated n (truncate n L) :=
  fun _ hx => word_weight_truncate hx

/-- Physically truncated lists are fixed by truncation. -/
lemma truncate_self_truncated
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L : List (SCFactor H ι)}
    (hL : IsTruncated n L) :
    truncate n L = L := by
  apply List.filter_eq_self.2
  intro x hx
  simpa only [decide_eq_true_eq] using hL x hx

end SCFactor

/--
A correction packet after erasing semantically trivial factors of weight at
least `n`.  Unlike `HCPkt`, its evaluation law is
specific to the chosen nilpotent quotient.
-/
structure SCPkta
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ)
    (B A : SCFactor H ι) where
  factors :
    List (SCFactor H ι)
  listEval_eq :
    ∀ e : ι → HEFam H,
      SCFactor.listEval (n := n) e factors =
        ⁅B.eval (n := n) e, A.eval (n := n) e⁆
  word_weight_left :
    ∀ x ∈ factors,
      B.word.weight HEAddres.weight <
        x.word.weight HEAddres.weight
  word_weight_right :
    ∀ x ∈ factors,
      A.word.weight HEAddres.weight <
        x.word.weight HEAddres.weight
  word_weight_cutoff :
    ∀ x ∈ factors,
      x.word.weight HEAddres.weight < n

namespace HCPkt

/-- Erase the semantically trivial corrections at or above the fixed cutoff. -/
def truncate
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : HCPkt B A) :
    SCPkta n B A where
  factors := SCFactor.truncate n C.factors
  listEval_eq := by
    intro e
    rw [SCFactor.listEval_truncate]
    exact C.listEval_eq e
  word_weight_left := by
    intro x hx
    exact C.word_weight_left x (List.mem_filter.mp hx).1
  word_weight_right := by
    intro x hx
    exact C.word_weight_right x (List.mem_filter.mp hx).1
  word_weight_cutoff := by
    intro x hx
    exact SCFactor.word_weight_truncate hx

end HCPkt

namespace SCPkta

/-- A truncated correction packet is still exactly the correction needed for its swap. -/
lemma list_mul_swap
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : SCPkta n B A)
    (e : ι → HEFam H) :
    SCFactor.listEval (n := n) e C.factors *
          A.eval (n := n) e * B.eval (n := n) e =
      B.eval (n := n) e * A.eval (n := n) e := by
  rw [C.listEval_eq]
  simp [commutatorElement_def, mul_assoc]

/-- Every factor in a truncated correction packet lies below its cutoff. -/
lemma weight_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : SCPkta n B A)
    {x : SCFactor H ι}
    (hx : x ∈ C.factors) :
    x.word.weight HEAddres.weight < n :=
  C.word_weight_cutoff x hx

/-- Every retained correction has positive remaining cutoff defect. -/
lemma defect_pos_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : SCPkta n B A)
    {x : SCFactor H ι}
    (hx : x ∈ C.factors) :
    0 < SCFactor.cutoffDefect n x := by
  simp [SCFactor.cutoffDefect,
    C.weight_factors hx]

/--
After truncation, corrections lie in the finite weight interval strictly above
the left parent and strictly below the cutoff.
-/
lemma interval_truncate_left
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : SCPkta n B A)
    {x : SCFactor H ι}
    (hx : x ∈ C.factors) :
    B.word.weight HEAddres.weight <
        x.word.weight HEAddres.weight ∧
      x.word.weight HEAddres.weight < n :=
  ⟨C.word_weight_left x hx, C.weight_factors hx⟩

/--
After truncation, corrections lie in the finite weight interval strictly above
the right parent and strictly below the cutoff.
-/
lemma interval_truncate_right
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : SCPkta n B A)
    {x : SCFactor H ι}
    (hx : x ∈ C.factors) :
    A.word.weight HEAddres.weight <
        x.word.weight HEAddres.weight ∧
      x.word.weight HEAddres.weight < n :=
  ⟨C.word_weight_right x hx, C.weight_factors hx⟩

/--
Every retained correction strictly lowers the cutoff-minus-weight recursion
measure relative to the left parent.
-/
lemma defect_left_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : SCPkta n B A)
    {x : SCFactor H ι}
    (hx : x ∈ C.factors) :
    SCFactor.cutoffDefect n x <
      SCFactor.cutoffDefect n B := by
  have hxInterval := C.interval_truncate_left hx
  simp only [SCFactor.cutoffDefect]
  omega

/--
Every retained correction strictly lowers the cutoff-minus-weight recursion
measure relative to the right parent.
-/
lemma cutoff_defect_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : SCPkta n B A)
    {x : SCFactor H ι}
    (hx : x ∈ C.factors) :
    SCFactor.cutoffDefect n x <
      SCFactor.cutoffDefect n A := by
  have hxInterval := C.interval_truncate_right hx
  simp only [SCFactor.cutoffDefect]
  omega

end SCPkta

namespace HCPkt

/--
Once the left parent is one step below the cutoff, every correction is erased
by physical truncation.
-/
lemma truncate_nil_left
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : HCPkt B A)
    (hB : n ≤ B.word.weight HEAddres.weight + 1) :
    (C.truncate (n := n)).factors = [] := by
  apply List.filter_eq_nil_iff.2
  intro x hx hdecide
  exact (not_lt_of_ge (hB.trans (C.succ_weight_left hx)))
    (of_decide_eq_true hdecide)

/--
Once the right parent is one step below the cutoff, every correction is erased
by physical truncation.
-/
lemma truncate_nil_n
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : HCPkt B A)
    (hA : n ≤ A.word.weight HEAddres.weight + 1) :
    (C.truncate (n := n)).factors = [] := by
  apply List.filter_eq_nil_iff.2
  intro x hx hdecide
  exact (not_lt_of_ge (hA.trans (C.succ_weight_right hx)))
    (of_decide_eq_true hdecide)

end HCPkt

/--
One physically truncated Hall-collection move: interchange an adjacent pair
and immediately erase every correction of weight at least `n`.
-/
inductive TSColl
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) :
    List (SCFactor H ι) →
      List (SCFactor H ι) → Prop where
  | obstruction
      (P S : List (SCFactor H ι))
      (B A : SCFactor H ι)
      (C : SCPkta n B A) :
      TSColl H ι
        (P ++ [B, A] ++ S)
        (P ++ C.factors ++ [A, B] ++ S)

/-- A truncated local collection move still preserves the evaluated product. -/
lemma TSColl.listEval_eq
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SCFactor H ι)}
    (h : TSColl (n := n) H ι L R)
    (e : ι → HEFam H) :
    SCFactor.listEval (n := n) e R =
      SCFactor.listEval (n := n) e L := by
  cases h with
  | obstruction P S B A C =>
      calc
        SCFactor.listEval (n := n) e
              (P ++ C.factors ++ [A, B] ++ S) =
            SCFactor.listEval e P *
                (SCFactor.listEval e C.factors *
                  A.eval e * B.eval e) *
              SCFactor.listEval e S := by
            simp [mul_assoc]
        _ =
            SCFactor.listEval e P *
                (B.eval e * A.eval e) *
              SCFactor.listEval e S := by
            rw [C.list_mul_swap]
        _ =
            SCFactor.listEval (n := n) e
              (P ++ [B, A] ++ S) := by
            simp [mul_assoc]

/-- Physical truncation is preserved by one cutoff-specific collection move. -/
lemma TSColl.isTruncated
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SCFactor H ι)}
    (h : TSColl (n := n) H ι L R)
    (hL : SCFactor.IsTruncated n L) :
    SCFactor.IsTruncated n R := by
  cases h with
  | obstruction P S B A C =>
      intro x hx
      rcases List.mem_append.mp hx with hx | hxS
      · rcases List.mem_append.mp hx with hx | hxAB
        · rcases List.mem_append.mp hx with hxP | hxC
          · exact hL x (List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inl hxP))))
          · exact C.word_weight_cutoff x hxC
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxAB
          rcases hxAB with hxA | hxB
          · exact hL x (List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inr (by simp [hxA])))))
          · exact hL x (List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inr (by simp [hxB])))))
      · exact hL x (List.mem_append.mpr (.inr hxS))

/-- Finite sequence of physically truncated symbolic Hall-collection moves. -/
abbrev SCRwb
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (L R : List (SCFactor H ι)) :
    Prop :=
  Relation.ReflTransGen (TSColl (n := n) H ι) L R

/-- Any finite physically truncated collection run preserves evaluation. -/
lemma SCRwb.listEval_eq
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SCFactor H ι)}
    (h : SCRwb (n := n) L R)
    (e : ι → HEFam H) :
    SCFactor.listEval (n := n) e R =
      SCFactor.listEval (n := n) e L := by
  induction h with
  | refl => rfl
  | tail hLR hstep ih =>
      exact (hstep.listEval_eq e).trans ih

/-- Physical truncation is preserved by any finite cutoff-specific run. -/
lemma SCRwb.isTruncated
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SCFactor H ι)}
    (h : SCRwb (n := n) L R)
    (hL : SCFactor.IsTruncated n L) :
    SCFactor.IsTruncated n R := by
  induction h with
  | refl => exact hL
  | tail hLR hstep ih =>
      exact hstep.isTruncated ih

end TCTex
end Towers

/-!
# Well-founded recursion for truncated symbolic Hall collection

The Hall collector replaces an obstruction by correction factors of strictly
higher word weight.  Below a fixed nilpotent cutoff this is a well-founded
process: the remaining cutoff-minus-weight defect strictly decreases.

This file packages that termination argument independently of any particular
packet constructor.
-/

namespace Towers
namespace TCTex

universe u

namespace SCFactor

/-- A correction descends from a parent when it has smaller remaining cutoff defect. -/
def CorrectionDescends
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ)
    (child parent : SCFactor H ι) :
    Prop :=
  cutoffDefect n child < cutoffDefect n parent

/-- Correction descent is well-founded because it is measured in `ℕ`. -/
lemma correction_well_founded
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type} :
    WellFounded (@CorrectionDescends d H ι n) := by
  unfold CorrectionDescends
  exact InvImage.wf (cutoffDefect n) Nat.lt_wfRel.wf

/-- The recursion principle used by a cutoff-specific Hall collector. -/
theorem correctionDescends_induction
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {motive : SCFactor H ι → Prop}
    (step :
      ∀ parent,
        (∀ child, CorrectionDescends n child parent → motive child) →
          motive parent)
    (x : SCFactor H ι) :
    motive x :=
  correction_well_founded.induction x step

/-- Positive cutoff defect is equivalent to lying strictly below the cutoff. -/
lemma cutoff_defect_pos
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x : SCFactor H ι) :
    0 < cutoffDefect n x ↔
      x.word.weight HEAddres.weight < n := by
  simp [cutoffDefect]

/-- Zero cutoff defect is equivalent to having reached or crossed the cutoff. -/
lemma cutoff_defect_weight
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x : SCFactor H ι) :
    cutoffDefect n x = 0 ↔
      n ≤ x.word.weight HEAddres.weight := by
  exact Nat.sub_eq_zero_iff_le

end SCFactor

namespace SCPkta

/-- Every retained correction descends from the left parent. -/
lemma descends_left_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : SCPkta n B A)
    {x : SCFactor H ι}
    (hx : x ∈ C.factors) :
    SCFactor.CorrectionDescends n x B :=
  C.defect_left_factors hx

/-- Every retained correction descends from the right parent. -/
lemma correction_descends_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : SCPkta n B A)
    {x : SCFactor H ι}
    (hx : x ∈ C.factors) :
    SCFactor.CorrectionDescends n x A :=
  C.cutoff_defect_factors hx

/--
If the left parent has at most one unit of cutoff defect, there is no room for
a retained correction factor.
-/
lemma nil_defect_left
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : SCPkta n B A)
    (hB : SCFactor.cutoffDefect n B ≤ 1) :
    C.factors = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro x hx
  have hxPos := C.defect_pos_factors hx
  have hxLt := C.defect_left_factors hx
  omega

/--
If the right parent has at most one unit of cutoff defect, there is no room for
a retained correction factor.
-/
lemma factors_nil_defect
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SCFactor H ι}
    (C : SCPkta n B A)
    (hA : SCFactor.cutoffDefect n A ≤ 1) :
    C.factors = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro x hx
  have hxPos := C.defect_pos_factors hx
  have hxLt := C.cutoff_defect_factors hx
  omega

end SCPkta

end TCTex
end Towers

/-!
# Concrete correction packets near the truncation cutoff

At the top of the lower-central filtration, powered commutators have no room
for higher errors.  This gives the base cases for a recursive product and
inverse Hall collector: an obstruction either vanishes, or emits exactly its
leading bracket.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

/--
If `y` commutes with its commutator with `x`, integral powers in the right
input pull out of the commutator.
-/
lemma zpow_commute_collection
    {G : Type*} [Group G]
    {x y : G}
    (hcomm : Commute y ⁅x, y⁆) :
    ∀ m : ℤ, ⁅x, y ^ m⁆ = ⁅x, y⁆ ^ m
  | .ofNat m => by
      simpa only [Int.ofNat_eq_natCast, zpow_natCast] using
        commutator_element_commute hcomm m
  | .negSucc m => by
      have hinv :
          ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ := by
        calc
          ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y := by
            simp only [commutatorElement_def, inv_inv, mul_inv_rev]
            group
          _ = ⁅x, y⁆⁻¹ := by
            rw [(hcomm.inv_left.inv_right).eq]
            simp
      have hcommInv :
          Commute y⁻¹ ⁅x, y⁻¹⁆ := by
        rw [hinv]
        exact hcomm.inv_left.inv_right
      simpa only [zpow_negSucc, ← inv_pow, hinv] using
        commutator_element_commute hcommInv (m + 1)

namespace SCPkta

/-- A trivial evaluated commutator needs no retained correction factors. -/
def empty_commutator_one
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (B A : SCFactor H ι)
    (hcommutator :
      ∀ e : ι → HEFam H,
        ⁅B.eval (n := n) e, A.eval (n := n) e⁆ = 1) :
    SCPkta n B A where
  factors := []
  listEval_eq e := by
    simpa using (hcommutator e).symm
  word_weight_left x hx := by
    simp at hx
  word_weight_right x hx := by
    simp at hx
  word_weight_cutoff x hx := by
    simp at hx

/--
If the parent weights already sum to the cutoff, their commutator vanishes in
the truncation quotient.
-/
def empty_n_weight
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (B A : SCFactor H ι)
    (hsum :
      n ≤ B.word.weight HEAddres.weight +
        A.word.weight HEAddres.weight) :
    SCPkta n B A :=
  empty_commutator_one B A fun e => by
    apply eq_bot_iff.mp
      SCFactor.trunc_last_bot
    exact Subgroup.lowerCentralSeries_antitone (by
      have hB := B.word_weight_pos
      have hA := A.word_weight_pos
      omega)
      (element_lower_series
        (B.eval_lower_series e)
        (A.eval_lower_series e))

/--
If both inputs commute with their leading commutator, the singleton symbolic
bracket evaluates to the full commutator of the evaluated powered factors.
-/
lemma singleton_bracket_commute
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (B A : SCFactor H ι)
    (hB :
      Commute (B.wordValue (n := n))
        ⁅B.wordValue (n := n), A.wordValue (n := n)⁆)
    (hA :
      Commute (A.wordValue (n := n))
        ⁅B.wordValue (n := n), A.wordValue (n := n)⁆)
    (e : ι → HEFam H) :
    (B.bracket A).eval (n := n) e =
      ⁅B.eval (n := n) e, A.eval (n := n) e⁆ := by
  rw [SCFactor.eval_bracket e B A]
  change
    ⁅B.wordValue (n := n), A.wordValue (n := n)⁆ ^
        (B.coefficient.eval e * A.coefficient.eval e) =
      ⁅B.wordValue (n := n) ^ B.coefficient.eval e,
        A.wordValue (n := n) ^ A.coefficient.eval e⁆
  have hleft :
      ⁅B.wordValue (n := n) ^ B.coefficient.eval e, A.wordValue (n := n)⁆ =
        ⁅B.wordValue (n := n), A.wordValue (n := n)⁆ ^
          B.coefficient.eval e :=
    commutator_zpow_commute hB (B.coefficient.eval e)
  have hright :
      Commute (A.wordValue (n := n))
        ⁅B.wordValue (n := n) ^ B.coefficient.eval e,
          A.wordValue (n := n)⁆ := by
    rw [hleft]
    exact hA.zpow_right (B.coefficient.eval e)
  rw [zpow_commute_collection hright,
    hleft, zpow_mul]

/-- The class-two powered interchange is represented by one retained bracket factor. -/
def bracket_commute
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (B A : SCFactor H ι)
    (hB :
      Commute (B.wordValue (n := n))
        ⁅B.wordValue (n := n), A.wordValue (n := n)⁆)
    (hA :
      Commute (A.wordValue (n := n))
        ⁅B.wordValue (n := n), A.wordValue (n := n)⁆)
    (hcutoff :
      B.word.weight HEAddres.weight +
          A.word.weight HEAddres.weight < n) :
    SCPkta n B A where
  factors := [B.bracket A]
  listEval_eq e := by
    simpa using singleton_bracket_commute B A hB hA e
  word_weight_left x hx := by
    rcases List.mem_singleton.mp hx with rfl
    exact B.word_bracket_left A
  word_weight_right x hx := by
    rcases List.mem_singleton.mp hx with rfl
    exact B.word_bracket_right A
  word_weight_cutoff x hx := by
    rcases List.mem_singleton.mp hx with rfl
    simpa using hcutoff

/--
Near the lower-central cutoff the two nested commutators vanish, so the exact
powered interchange packet is the singleton bracket.
-/
def singleton_bracket_two
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (B A : SCFactor H ι)
    (hcutoff :
      B.word.weight HEAddres.weight +
          A.word.weight HEAddres.weight < n)
    (hleft :
      n ≤
        2 * B.word.weight HEAddres.weight +
          A.word.weight HEAddres.weight)
    (hright :
      n ≤
        B.word.weight HEAddres.weight +
          2 * A.word.weight HEAddres.weight) :
    SCPkta n B A := by
  let x := B.wordValue (n := n)
  let y := A.wordValue (n := n)
  let bWeight := B.word.weight HEAddres.weight
  let aWeight := A.word.weight HEAddres.weight
  have hbWeight : 0 < bWeight := by
    simpa [bWeight] using B.word_weight_pos
  have haWeight : 0 < aWeight := by
    simpa [aWeight] using A.word_weight_pos
  have hx :
      x ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (bWeight - 1) := by
    simpa [x, bWeight] using B.value_lower_series (n := n)
  have hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (aWeight - 1) := by
    simpa [y, aWeight] using A.value_lower_series (n := n)
  have hxy :
      ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        ((bWeight - 1) + (aWeight - 1) + 1) :=
    element_lower_series hx hy
  have hxx :
      ⁅x, ⁅x, y⁆⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        ((bWeight - 1) + ((bWeight - 1) + (aWeight - 1) + 1) + 1) :=
    element_lower_series hx hxy
  have hyy :
      ⁅y, ⁅x, y⁆⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        ((aWeight - 1) + ((bWeight - 1) + (aWeight - 1) + 1) + 1) :=
    element_lower_series hy hxy
  have hxxOne : ⁅x, ⁅x, y⁆⁆ = 1 := by
    apply eq_bot_iff.mp
      SCFactor.trunc_last_bot
    exact Subgroup.lowerCentralSeries_antitone (by omega) hxx
  have hyyOne : ⁅y, ⁅x, y⁆⁆ = 1 := by
    apply eq_bot_iff.mp
      SCFactor.trunc_last_bot
    exact Subgroup.lowerCentralSeries_antitone (by omega) hyy
  apply bracket_commute B A
  · rw [← commutatorElement_eq_one_iff_commute]
    simpa [x, y] using hxxOne
  · rw [← commutatorElement_eq_one_iff_commute]
    simpa [x, y] using hyyOne
  · exact hcutoff

/--
In the class-two zone, the exact packet is either empty or the singleton
leading bracket, depending on whether the leading bracket itself survives the
cutoff.
-/
def of_classTwo
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (B A : SCFactor H ι)
    (hleft :
      n ≤
        2 * B.word.weight HEAddres.weight +
          A.word.weight HEAddres.weight)
    (hright :
      n ≤
        B.word.weight HEAddres.weight +
          2 * A.word.weight HEAddres.weight) :
    SCPkta n B A :=
  if hcutoff :
      n ≤ B.word.weight HEAddres.weight +
        A.word.weight HEAddres.weight then
    empty_n_weight B A hcutoff
  else
    singleton_bracket_two B A (Nat.lt_of_not_ge hcutoff) hleft hright

/--
If three times the smaller parent weight reaches the cutoff, the obstruction
is already in the class-two terminal zone.
-/
def n_min_weight
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (B A : SCFactor H ι)
    (hterminal :
      n ≤ 3 * min
        (B.word.weight HEAddres.weight)
        (A.word.weight HEAddres.weight)) :
    SCPkta n B A :=
  of_classTwo B A
    (by
      have hminB :
          min
              (B.word.weight HEAddres.weight)
              (A.word.weight HEAddres.weight) ≤
            B.word.weight HEAddres.weight :=
        Nat.min_le_left _ _
      have hminA :
          min
              (B.word.weight HEAddres.weight)
              (A.word.weight HEAddres.weight) ≤
            A.word.weight HEAddres.weight :=
        Nat.min_le_right _ _
      omega)
    (by
      have hminB :
          min
              (B.word.weight HEAddres.weight)
              (A.word.weight HEAddres.weight) ≤
            B.word.weight HEAddres.weight :=
        Nat.min_le_left _ _
      have hminA :
          min
              (B.word.weight HEAddres.weight)
              (A.word.weight HEAddres.weight) ≤
            A.word.weight HEAddres.weight :=
        Nat.min_le_right _ _
      omega)

end SCPkta

/-- An obstruction at total weight at least the cutoff swaps without corrections. -/
def TSColl.obstrucempty_nle_addwordweight
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (P S : List (SCFactor H ι))
    (B A : SCFactor H ι)
    (hsum :
      n ≤ B.word.weight HEAddres.weight +
        A.word.weight HEAddres.weight) :
    TSColl (n := n) H ι
      (P ++ [B, A] ++ S)
      (P ++ [A, B] ++ S) := by
  simpa using
    TSColl.obstruction P S B A
      (SCPkta.empty_n_weight
        B A hsum)

/-- A class-two adjacent swap emits exactly one leading bracket correction. -/
def TSColl.obstruction_singletbracket_classtwo
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (P S : List (SCFactor H ι))
    (B A : SCFactor H ι)
    (hcutoff :
      B.word.weight HEAddres.weight +
          A.word.weight HEAddres.weight < n)
    (hleft :
      n ≤
        2 * B.word.weight HEAddres.weight +
          A.word.weight HEAddres.weight)
    (hright :
      n ≤
        B.word.weight HEAddres.weight +
          2 * A.word.weight HEAddres.weight) :
    TSColl (n := n) H ι
      (P ++ [B, A] ++ S)
      (P ++ [B.bracket A, A, B] ++ S) := by
  simpa using
    TSColl.obstruction P S B A
      (SCPkta.singleton_bracket_two
        B A hcutoff hleft hright)

/--
In the class-two zone, perform the adjacent swap with its automa chosen
empty-or-singleton terminal correction packet.
-/
def TSColl.obstruction_class_two
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (P S : List (SCFactor H ι))
    (B A : SCFactor H ι)
    (hleft :
      n ≤
        2 * B.word.weight HEAddres.weight +
          A.word.weight HEAddres.weight)
    (hright :
      n ≤
        B.word.weight HEAddres.weight +
          2 * A.word.weight HEAddres.weight) :
    TSColl (n := n) H ι
      (P ++ [B, A] ++ S)
      (P ++
        (SCPkta.of_classTwo
          B A hleft hright).factors ++ [A, B] ++ S) :=
  TSColl.obstruction P S B A
    (SCPkta.of_classTwo B A hleft hright)

end TCTex
end Towers
