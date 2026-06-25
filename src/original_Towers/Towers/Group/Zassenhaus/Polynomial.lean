import Towers.Group.Zassenhaus.CorrectionSemantics
import Towers.Group.Zassenhaus.SymbolicHallCollection
import Towers.Group.Zassenhaus.SymbolicHallFactors
import Towers.Group.Zassenhaus.PositiveDegreeRecipes
import Towers.Group.Zassenhaus.CompletePetrescoRecipe
import Towers.Group.Zassenhaus.ChooseNormalization
import Towers.Group.LowerCentralStrong
import Towers.Group.Zassenhaus.PacketCompression


-- Merged from PolynomialClassTwoPackets.lean

/-!
# Class-two packets for signed polynomial Hall factors

At the top of the lower-central filtration, signed-polynomial commutators have
no room for nested errors.  The physically truncated product and inverse
collector can therefore choose automa between an empty packet and the
singleton leading bracket.

Unlike the atomic class-two constructor, this file applies after recursive
collection has already produced signed polynomial factors.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

namespace TSPkt

/-- A trivial evaluated commutator needs no retained polynomial factors. -/
def empty_commutator_one
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (B A : SPFactor H ι)
    (hcommutator :
      ∀ e : ι → HEFam H,
        ⁅B.eval (n := n) e, A.eval (n := n) e⁆ = 1) :
    TSPkt n B A where
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
If the parent weights already sum to the cutoff, their evaluated commutator
vanishes in the truncation quotient.
-/
def empty_n_weight
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (B A : SPFactor H ι)
    (hsum :
      n ≤ B.word.weight HEAddres.weight +
        A.word.weight HEAddres.weight) :
    TSPkt n B A :=
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
If both word values commute with their leading commutator, the singleton
polynomial bracket evaluates to the full commutator of the evaluated factors.
-/
lemma singleton_bracket_commute
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (B A : SPFactor H ι)
    (hB :
      Commute (B.wordValue (n := n))
        ⁅B.wordValue (n := n), A.wordValue (n := n)⁆)
    (hA :
      Commute (A.wordValue (n := n))
        ⁅B.wordValue (n := n), A.wordValue (n := n)⁆)
    (e : ι → HEFam H) :
    (B.bracket A).eval (n := n) e =
      ⁅B.eval (n := n) e, A.eval (n := n) e⁆ := by
  rw [SPFactor.eval_bracket e B A]
  change
    ⁅B.wordValue (n := n), A.wordValue (n := n)⁆ ^
        (B.coefficient.eval e * A.coefficient.eval e) =
      ⁅B.wordValue (n := n) ^ B.coefficient.eval e,
        A.wordValue (n := n) ^ A.coefficient.eval e⁆
  have hleft :
      ⁅B.wordValue (n := n) ^ B.coefficient.eval e,
          A.wordValue (n := n)⁆ =
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

/-- The class-two powered interchange is represented by one retained bracket. -/
def bracket_commute
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (B A : SPFactor H ι)
    (hB :
      Commute (B.wordValue (n := n))
        ⁅B.wordValue (n := n), A.wordValue (n := n)⁆)
    (hA :
      Commute (A.wordValue (n := n))
        ⁅B.wordValue (n := n), A.wordValue (n := n)⁆)
    (hcutoff :
      B.word.weight HEAddres.weight +
          A.word.weight HEAddres.weight < n) :
    TSPkt n B A where
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
Near the cutoff the two nested commutators vanish, so the exact polynomial
interchange packet is the singleton leading bracket.
-/
def singleton_bracket_two
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (B A : SPFactor H ι)
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
    TSPkt n B A := by
  let x := B.wordValue (n := n)
  let y := A.wordValue (n := n)
  let bWeight := B.word.weight HEAddres.weight
  let aWeight := A.word.weight HEAddres.weight
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
In the class-two zone, choose automa between an empty packet and the
singleton leading bracket according to whether that bracket survives.
-/
def of_classTwo
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (B A : SPFactor H ι)
    (hleft :
      n ≤
        2 * B.word.weight HEAddres.weight +
          A.word.weight HEAddres.weight)
    (hright :
      n ≤
        B.word.weight HEAddres.weight +
          2 * A.word.weight HEAddres.weight) :
    TSPkt n B A :=
  if hcutoff :
      n ≤ B.word.weight HEAddres.weight +
        A.word.weight HEAddres.weight then
    empty_n_weight B A hcutoff
  else
    singleton_bracket_two B A (Nat.lt_of_not_ge hcutoff) hleft hright

/--
If three times the smaller parent weight reaches the cutoff, the polynomial
obstruction is already in the class-two terminal zone.
-/
def n_min_weight
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (B A : SPFactor H ι)
    (hterminal :
      n ≤ 3 * min
        (B.word.weight HEAddres.weight)
        (A.word.weight HEAddres.weight)) :
    TSPkt n B A :=
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

end TSPkt

/-- An obstruction at total weight at least the cutoff swaps without corrections. -/
def TCStepa.obstrucempty_nle_addwordweight
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (P S : List (SPFactor H ι))
    (B A : SPFactor H ι)
    (hsum :
      n ≤ B.word.weight HEAddres.weight +
        A.word.weight HEAddres.weight) :
    TCStepa (n := n) H ι
      (P ++ [B, A] ++ S)
      (P ++ [A, B] ++ S) := by
  simpa using
    TCStepa.obstruction P S B A
      (TSPkt.empty_n_weight
        B A hsum)

/-- A class-two adjacent swap emits exactly one surviving bracket correction. -/
def TCStepa.obstruction_singletbracket_classtwo
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (P S : List (SPFactor H ι))
    (B A : SPFactor H ι)
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
    TCStepa (n := n) H ι
      (P ++ [B, A] ++ S)
      (P ++ [B.bracket A, A, B] ++ S) := by
  simpa using
    TCStepa.obstruction P S B A
      (TSPkt.singleton_bracket_two
        B A hcutoff hleft hright)

end TCTex
end Towers

-- Merged from PolynomialSignedCoordinateEndpoints.lean

/-!
# Signed coordinate endpoints for product and inverse Hall collection

Nonterminal Hall-Petresco collection emits signed polynomial coefficients.
The earlier coordinate endpoint stores only unsigned monomial lists, so it is
not expressive enough to serve as the terminal object of that collector.

This file packages the signed endpoint: every Hall coordinate stores a finite
list of signed formulas.  Its canonical factor list is still ordered first by
weight and then by the finite Hall index.  Evaluation collapses each list to
the corresponding collected Hall exponent, and finite semantic rewrite runs
to this endpoint discharge the product and inverse forms of Claim 8 directly.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace WBForm

/-- Read one signed coordinate formula as one atomic symbolic Hall factor. -/
def symbolicPolynomialFactor
    {d s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (formula : WBForm H ι s)
    (i : (H s).index) :
    SPFactor H ι where
  word := .atom (⟨s, i⟩ : HEAddres H)
  coefficient := formula

@[simp]
lemma symbolic_polynomial_factor
    {d n s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (formula : WBForm H ι s)
    (i : (H s).index) :
    (formula.symbolicPolynomialFactor i).eval (n := n) e =
      ((H s).commutator i).freeLowerTruncation ^
        formula.eval e :=
  rfl

end WBForm

/--
Finite signed formulas for every collected Hall coordinate.

Keeping a list of formulas, rather than prematurely coalescing each coordinate
to one formula, lets the operational collector append normalized correction
packets without deciding formula equality.
-/
structure CCRecipe
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  formulas :
    ∀ s : ℕ, (H s).index → List (WBForm H ι s)

namespace CCRecipe

/-- Evaluate and add every signed formula assigned to one Hall coordinate. -/
def eval
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    (e : ι → HEFam H) :
    HEFam H :=
  fun s i => ((R.formulas s i).map fun formula => formula.eval e).sum

/-- Every evaluated signed coordinate recipe lies in the Claim 8 span. -/
lemma combination_weighted_monomials
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    (e : ι → HEFam H)
    (s : ℕ)
    (i : (H s).index) :
    ICMonomi
      H s e (R.eval e s i) := by
  change
    ICMonomi
      H s e ((R.formulas s i).map fun formula => formula.eval e).sum
  induction R.formulas s i with
  | nil =>
      exact ICMonomi.zero e
  | cons formula formulas ih =>
      simp only [List.map_cons, List.sum_cons]
      exact ICMonomi.add
        (formula.combination_weighted_monomials e)
        ih

/-- The canonical signed polynomial factors in one fixed Hall-weight layer. -/
def weightFactors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    (s : ℕ) :
    List (SPFactor H ι) :=
  (Finset.univ.sort fun i i' : (H s).index => i ≤ i').flatMap fun i =>
    (R.formulas s i).map fun formula =>
      formula.symbolicPolynomialFactor i

/-- Fixed-weight signed factors evaluate to their collected Hall segment. -/
lemma list_weight_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    (e : ι → HEFam H)
    (s : ℕ) :
    SPFactor.listEval (n := n) e (R.weightFactors s) =
      (H s).collectedWeightProduct (n := n) (R.eval e s) := by
  simp [weightFactors, SPFactor.listEval,
    CCRecipe.eval,
    WBForm.symbolicPolynomialFactor,
    SPFactor.eval,
    SPFactor.wordValue,
    HEAddres.freeLowerTruncation,
    BCWta.collectedWeightProduct,
    BCWta.collected_lower_centralterm,
    BCWt.evalin_freelower_centtrunterm,
    List.flatMap, Function.comp_def, list_zpow_sum]
  rfl

/-- Canonical signed factors through ordinary Hall weight `k`. -/
def prefixFactors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    (k : ℕ) :
    List (SPFactor H ι) :=
  (List.range k).flatMap fun q => R.weightFactors (q + 1)

/-- Prefix signed factors evaluate to the collected Hall prefix. -/
lemma eval_prefix_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    (e : ι → HEFam H)
    (k : ℕ) :
    SPFactor.listEval (n := n) e (R.prefixFactors k) =
      collectedPrefixProduct (n := n) H (R.eval e) k := by
  induction k with
  | zero =>
      simp [prefixFactors, collectedPrefixProduct]
  | succ k ih =>
      rw [prefixFactors, List.range_succ, List.flatMap_append,
        List.flatMap_singleton, SPFactor.listEval_append,
        collected_prefix_succ]
      change
        SPFactor.listEval e (R.prefixFactors k) *
            SPFactor.listEval e (R.weightFactors (k + 1)) =
          collectedPrefixProduct H (R.eval e) k *
            (H (k + 1)).collectedWeightProduct (R.eval e (k + 1))
      rw [ih, R.list_weight_factors]

/-- Full canonical signed factor list represented by the coordinate recipes. -/
def factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι) :
    List (SPFactor H ι) :=
  R.prefixFactors (n - 1)

/-- Full canonical signed factors evaluate to the collected Hall product. -/
lemma listEval_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e (R.factors (n := n)) =
      collectedHallProduct (n := n) H (R.eval e) := by
  simp [factors, collectedHallProduct, R.eval_prefix_factors]

/-- Every signed factor in one fixed layer has exactly that layer weight. -/
lemma word_weight_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    {s : ℕ}
    {x : SPFactor H ι}
    (hx : x ∈ R.weightFactors s) :
    x.word.weight HEAddres.weight = s := by
  rcases List.mem_flatMap.mp hx with ⟨i, _hi, hx⟩
  rcases List.mem_map.mp hx with ⟨formula, _hformula, rfl⟩
  rfl

/-- Prefix signed endpoints have weight bounded by the prefix length. -/
lemma word_prefix_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    {k : ℕ}
    {x : SPFactor H ι}
    (hx : x ∈ R.prefixFactors k) :
    x.word.weight HEAddres.weight ≤ k := by
  rcases List.mem_flatMap.mp hx with ⟨q, hq, hx⟩
  rw [R.word_weight_factors hx]
  exact List.mem_range.mp hq

/-- Canonical signed endpoints are physically below the quotient cutoff. -/
lemma isTruncated_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι) :
    SPFactor.IsTruncated n (R.factors (n := n)) := by
  intro x hx
  have hweight := R.word_prefix_factors hx
  have hpos := x.word_weight_pos
  omega

/-- A signed endpoint has no canonical factors below `lowerWeight`. -/
def NTBelow
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    (lowerWeight : ℕ) :
    Prop :=
  ∀ s : ℕ, s < lowerWeight → R.weightFactors s = []

/-- Endpoints with no lower terms are supported in their declared stratum. -/
lemma no_terms_below
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    (hR : R.NTBelow lowerWeight) :
    SPFactor.WordWeightLeast lowerWeight
      (R.factors (n := n)) := by
  intro x hx
  rcases List.mem_flatMap.mp hx with ⟨q, _hq, hx⟩
  by_contra hweight
  have hlt : q + 1 < lowerWeight := by
    rw [← R.word_weight_factors hx]
    omega
  rw [hR (q + 1) hlt] at hx
  simp at hx

end CCRecipe

/--
A finite normalized semantic rewrite run to a signed coordinate endpoint
constructs the product form of Claim 8.
-/
theorem data_formula_rewrites
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (R : CCRecipe H (Fin e.length))
    (hrewrites :
      SSRw
        (n := n) (lowerWeight := 1)
        ((indexedSymbolicFactors (n := n) H e).map
          SPFactor.ofMonomial)
        (R.factors (n := n))) :
    CollectedCoordinateData (n := n) H e := by
  let input : Fin e.length → HEFam H := fun j => e.get j
  refine ⟨R.eval input, ?_, ?_⟩
  · exact (R.listEval_factors input).symm.trans
      ((hrewrites.listEval_eq input).trans
        ((SPFactor.list_eval_monomial input
            (indexedSymbolicFactors (n := n) H e)).trans
          (indexed_symbolic_factors H e)))
  · intro s _hs _hsn i
    exact R.combination_weighted_monomials
      input s i

/--
A finite normalized semantic rewrite run to a signed coordinate endpoint
constructs the inverse form of Claim 8.
-/
theorem collected_formula_rewrites
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (R : CCRecipe H (Fin 1))
    (hrewrites :
      SSRw
        (n := n) (lowerWeight := 1)
        ((symbolicInverseFactors (n := n) H).map
          SPFactor.ofMonomial)
        (R.factors (n := n))) :
    CollectedInverseData (n := n) H e := by
  let input : Fin 1 → HEFam H :=
    fun _ => negExponentFamily e
  refine ⟨R.eval input, ?_, ?_⟩
  · exact (R.listEval_factors input).symm.trans
      ((hrewrites.listEval_eq input).trans
        ((SPFactor.list_eval_monomial input
            (symbolicInverseFactors (n := n) H)).trans
          (list_symbolic_factors H e)))
  · intro s _hs _hsn i
    exact R.combination_weighted_monomials
      input s i

end TCTex
end Towers

-- Merged from PolynomialSignedTruncation.lean

/-!
# Physical truncation for signed polynomial Hall factors

In the free nilpotent quotient `F_d / gamma_n(F_d)`, every signed polynomial
Hall factor of ordinary word weight at least `n` evaluates to the identity.
Thus a universal higher-word expansion can be cut down to its finite physical
support before it is handed to the signed semantic collector.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace SPFactor

/-- Keep precisely the signed polynomial factors whose word weight is below `n`. -/
def truncate
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ)
    (L : List (SPFactor H ι)) :
    List (SPFactor H ι) :=
  L.filter fun x => x.word.weight HEAddres.weight < n

@[simp]
lemma truncate_nil
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ) :
    truncate n ([] : List (SPFactor H ι)) = [] :=
  rfl

@[simp]
lemma truncate_append
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ)
    (L M : List (SPFactor H ι)) :
    truncate n (L ++ M) = truncate n L ++ truncate n M := by
  simp [truncate]

/-- Every retained signed polynomial factor lies genuinely below the cutoff. -/
lemma word_weight_truncate
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L : List (SPFactor H ι)}
    {x : SPFactor H ι}
    (hx : x ∈ truncate n L) :
    x.word.weight HEAddres.weight < n := by
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hx).2

/-- Truncating twice at the same cutoff has no further effect. -/
@[simp]
lemma truncate_truncate
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (L : List (SPFactor H ι)) :
    truncate n (truncate n L) = truncate n L := by
  simp [truncate]

/-- Truncation never increases the number of signed polynomial factors. -/
lemma length_truncate_le
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (L : List (SPFactor H ι)) :
    (truncate n L).length ≤ L.length := by
  simpa [truncate] using
    (List.length_filter_le
      (fun x : SPFactor H ι =>
        decide (x.word.weight HEAddres.weight < n)) L)

/--
Discarding signed factors at or above the nilpotent cutoff preserves the
evaluated list product.
-/
lemma listEval_truncate
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (L : List (SPFactor H ι)) :
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

end SPFactor

end TCTex
end Towers

-- Merged from PolynomialSemantic.lean

/-!
# Supported packet factories for product and inverse polynomial collection

The group-theoretic input to one signed-polynomial Hall stratum is a supply of
truncated correction packets for supported adjacent factors.  Once supplied,
the next-stratum semantic normalizer replaces each strictly higher correction
list by its canonical coordinate endpoint.

This file isolates that packet-supply obligation, constructs it in the
class-two terminal region, and packages the normalized adjacent rewrite made
available by any supported packet factory.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace SSRw

/-- A single normalized semantic obstruction is a finite rewrite run. -/
lemma single
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      SSColl
        (n := n) H ι lowerWeight L R) :
    SSRw
      (n := n) (lowerWeight := lowerWeight) L R :=
  Relation.ReflTransGen.single h

end SSRw

/--
A supply of physically truncated correction packets for pairs supported in
one ordinary Hall-weight stratum.
-/
structure TSFtry
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (lowerWeight : ℕ) where
  packet :
    ∀ (B A : SPFactor H ι),
      lowerWeight ≤ B.word.weight HEAddres.weight →
      lowerWeight ≤ A.word.weight HEAddres.weight →
        TSPkt n B A

namespace TSFtry

/-- Any explicit packet constructor for supported pairs supplies a factory. -/
def ofPacket
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      ∀ {ι : Type} (B A : SPFactor H ι),
        lowerWeight ≤ B.word.weight HEAddres.weight →
        lowerWeight ≤ A.word.weight HEAddres.weight →
          TSPkt n B A) :
    TSFtry
      (n := n) H lowerWeight where
  packet := packet

/--
If three times the active stratum reaches the cutoff, every supported pair has
the automatic class-two empty-or-singleton polynomial correction packet.
-/
def of_classTwo
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hterminal : n ≤ 3 * lowerWeight) :
    TSFtry
      (n := n) H lowerWeight where
  packet B A hB hA :=
    TSPkt.n_min_weight
      B A (by
        have hlowerMin :
            lowerWeight ≤
              min
                (B.word.weight HEAddres.weight)
                (A.word.weight HEAddres.weight) :=
          Nat.le_min.mpr ⟨hB, hA⟩
        omega)

/--
A supported packet factory and a next-stratum normalizer produce one
normalized adjacent semantic obstruction.
-/
lemma supported_semantic_step
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (normalizer :
      TSNormalc
        (n := n) (lowerWeight := lowerWeight + 1) H)
    (P S : List (SPFactor H ι))
    (B A : SPFactor H ι)
    (hB : lowerWeight ≤ B.word.weight HEAddres.weight)
    (hA : lowerWeight ≤ A.word.weight HEAddres.weight) :
    ∃ normalization :
        TSNorm
          lowerWeight (factory.packet B A hB hA),
      SSColl
        (n := n) H ι lowerWeight
        (P ++ [B, A] ++ S)
        (P ++ normalization.coordinates.polynomialFactors (n := n) ++
          [A, B] ++ S) :=
  (factory.packet B A hB hA).supported_semantic_left
    P S B A hB normalizer

/--
The normalized adjacent obstruction supplied by a packet factory is also a
finite semantic rewrite run.
-/
lemma supported_semantic_rewrites
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (normalizer :
      TSNormalc
        (n := n) (lowerWeight := lowerWeight + 1) H)
    (P S : List (SPFactor H ι))
    (B A : SPFactor H ι)
    (hB : lowerWeight ≤ B.word.weight HEAddres.weight)
    (hA : lowerWeight ≤ A.word.weight HEAddres.weight) :
    ∃ normalization :
        TSNorm
          lowerWeight (factory.packet B A hB hA),
      SSRw
        (n := n) (lowerWeight := lowerWeight)
        (P ++ [B, A] ++ S)
        (P ++ normalization.coordinates.polynomialFactors (n := n) ++
          [A, B] ++ S) := by
  rcases factory.supported_semantic_step normalizer P S B A hB hA with
    ⟨normalization, hstep⟩
  exact
    ⟨normalization,
      SSRw.single
        hstep⟩

end TSFtry

end TCTex
end Towers

/-!
# Weight strata of product and inverse polynomial coordinate endpoints

Canonical coordinate recipes are concatenated in increasing ordinary Hall
weight.  A filtration-recursive scheduler needs to separate the visible
prefix through one active stratum from its strictly higher tail.

This file packages that decomposition for both the underlying monomial
endpoint and its signed-polynomial embedding.  In particular, a supported
endpoint splits into its current layer followed by a physically truncated
tail supported one stratum higher.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace CHRecipe

/-- Canonical monomial endpoint factors in weights strictly above `lowerWeight`. -/
def tailFactors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (lowerWeight : ℕ) :
    List (SCFactor H ι) :=
  (List.range' lowerWeight (n - 1 - lowerWeight)).flatMap fun s =>
    R.weightFactors (s + 1)

/-- The monomial prefix and higher tail concatenate back to the full endpoint. -/
lemma factors_append_tail
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (hlowerWeight : lowerWeight ≤ n - 1) :
    R.factors (n := n) =
      R.prefixFactors lowerWeight ++ R.tailFactors (n := n) lowerWeight := by
  have hrange :
      List.range lowerWeight ++
          List.range' lowerWeight (n - 1 - lowerWeight) =
        List.range (n - 1) := by
    rw [List.range_eq_range', List.range_eq_range']
    simpa [Nat.add_sub_of_le hlowerWeight] using
      (List.range'_append
        (s := 0) (m := lowerWeight) (n := n - 1 - lowerWeight) (step := 1))
  unfold factors prefixFactors tailFactors
  rw [← List.flatMap_append, hrange]

/-- Signed-polynomial embedding of the canonical higher tail. -/
def polynomialTailFactors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (lowerWeight : ℕ) :
    List (SPFactor H ι) :=
  (R.tailFactors (n := n) lowerWeight).map
    SPFactor.ofMonomial

/-- The signed-polynomial endpoint is its embedded prefix followed by its tail. -/
lemma prefix_append_tail
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (hlowerWeight : lowerWeight ≤ n - 1) :
    R.polynomialFactors (n := n) =
      (R.prefixFactors lowerWeight).map
          SPFactor.ofMonomial ++
        R.polynomialTailFactors (n := n) lowerWeight := by
  rw [polynomialFactors, R.factors_append_tail
    hlowerWeight, List.map_append]
  rfl

/-- Every embedded higher-tail factor lies in the next support stratum. -/
lemma succ_tail_factors
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    {x : SPFactor H ι}
    (hx : x ∈ R.polynomialTailFactors (n := n) lowerWeight) :
    lowerWeight + 1 ≤ x.word.weight HEAddres.weight := by
  rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
  rcases List.mem_flatMap.mp hy with ⟨s, hs, hy⟩
  change lowerWeight + 1 ≤ y.word.weight HEAddres.weight
  rw [R.word_weight_factors hy]
  have hsLower : lowerWeight ≤ s :=
    List.left_le_of_mem_range' hs
  omega

/-- The embedded higher tail is supported one stratum above the prefix. -/
lemma least_tail_factors
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι) :
    SPFactor.WordWeightLeast (lowerWeight + 1)
      (R.polynomialTailFactors (n := n) lowerWeight) :=
  fun _ hx => R.succ_tail_factors hx

/-- The embedded higher tail remains physically below the quotient cutoff. -/
lemma truncated_tail_factors
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (hlowerWeight : lowerWeight ≤ n - 1) :
    SPFactor.IsTruncated n
      (R.polynomialTailFactors (n := n) lowerWeight) := by
  intro x hx
  apply R.truncated_polynomial_factors
  rw [R.prefix_append_tail
    hlowerWeight]
  exact List.mem_append_right _ hx

/-- If one layer is below the endpoint support, its normalized block is empty. -/
lemma nil_terms_below
    {d lowerWeight s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (hR : R.NTBelow lowerWeight)
    (hs : s < lowerWeight) :
    R.weightFactors s = [] :=
  hR s hs

/--
If no terms occur below a positive support stratum, the endpoint prefix
through that stratum consists exactly of its current-weight block.
-/
lemma prefix_no_below
    {d lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (hR : R.NTBelow lowerWeight)
    (hlowerWeight : 1 ≤ lowerWeight) :
    R.prefixFactors lowerWeight = R.weightFactors lowerWeight := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (by omega : lowerWeight ≠ 0)
  rw [prefixFactors, List.range_succ, List.flatMap_append,
    List.flatMap_singleton]
  have hprevious :
      (List.range k).flatMap (fun s => R.weightFactors (s + 1)) = [] := by
    apply List.flatMap_eq_nil_iff.2
    intro s hs
    apply R.nil_terms_below hR
    have hsRange := List.mem_range.mp hs
    omega
  rw [hprevious, List.nil_append]

/--
A supported signed-polynomial endpoint splits into its embedded current layer
followed by a tail supported one stratum higher.
-/
lemma poly_no_below
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (hR : R.NTBelow lowerWeight)
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightCutoff : lowerWeight ≤ n - 1) :
    R.polynomialFactors (n := n) =
      (R.weightFactors lowerWeight).map
          SPFactor.ofMonomial ++
        R.polynomialTailFactors (n := n) lowerWeight := by
  rw [R.prefix_append_tail
      hlowerWeightCutoff,
    R.prefix_no_below hR hlowerWeightPos]

end CHRecipe

end TCTex
end Towers

/-!
# Filtration recursion for product and inverse polynomial normalizers

Signed-polynomial correction packets rise strictly in ordinary Hall weight.
Consequently, a collector for stratum `lowerWeight` may recursively call a
normalizer for `lowerWeight + 1`.  Once `n ≤ lowerWeight`, physical truncation
forces every supported source list to be empty and closes the recursion.

This file isolates the remaining local scheduler obligation and proves the
well-founded filtration recursion around it.  Product and inverse Claim 8 are
reduced to constructing the one-stratum insertion step.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
The local scheduler obligation at one support stratum: assuming correction
packets can be normalized one stratum higher, insert one retained factor into
a canonical coordinate endpoint at the current stratum.
-/
structure TRInsert
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    Prop where
  insert :
    ∀ lowerWeight : ℕ,
      TSNormalc
          (n := n) (lowerWeight := lowerWeight + 1) H →
        TSInsertc
          (n := n) (lowerWeight := lowerWeight) H

namespace TSNormalc

/--
Successive-stratum insertion plus the empty cutoff terminal case constructs a
semantic normalizer at every support stratum.
-/
noncomputable def recInsertionStep
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (step :
      TRInsert
        (n := n) H)
    (lowerWeight : ℕ) :
    TSNormalc
      (n := n) (lowerWeight := lowerWeight) H :=
  if hterminal : n ≤ lowerWeight then
    of_cutoff H hterminal
  else
    ofInsertionKernel
      (step.insert lowerWeight
        (recInsertionStep H step (lowerWeight + 1)))
termination_by n - lowerWeight
decreasing_by omega

end TSNormalc

/--
A recursive one-stratum insertion constructor supplies the product form of
Claim 8.
-/
theorem collected_insertion_step
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (step :
      TRInsert
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  data_semantic_normalizer
    H e
      (TSNormalc.recInsertionStep
        H step 1)

/--
A recursive one-stratum insertion constructor supplies the inverse form of
Claim 8.
-/
theorem semantic_insertion_step
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (step :
      TRInsert
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  collected_semantic_normalizer
    H e
      (TSNormalc.recInsertionStep
        H step 1)

end TCTex
end Towers

/-!
# One-stratum scheduling interface for product and inverse polynomials

A recursive signed-polynomial Hall collector works one ordinary Hall-weight
stratum at a time.  At the current stratum, a normalized endpoint is its
visible fixed-weight block followed by a tail supported one stratum higher.

This file packages that endpoint view and exposes the operational scheduler
obligation: finite normalized obstruction rewrites must insert one factor into
the endpoint.  Such a schedule immediately supplies the semantic insertion
kernel consumed by filtration recursion.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
A supported signed-polynomial coordinate endpoint viewed at one active
ordinary Hall-weight stratum.
-/
structure CSViewa
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (lowerWeight : ℕ)
    (coordinates : CHRecipe H ι) :
    Prop where
  lowerWeight_pos : 1 ≤ lowerWeight
  lowerWeight_cutoff : lowerWeight ≤ n - 1
  coordinates_no_below : coordinates.NTBelow lowerWeight

namespace CSViewa

/-- The normalized signed-polynomial endpoint block at the active stratum. -/
def currentFactors
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CHRecipe H ι}
    (_view :
      CSViewa
        (n := n) lowerWeight coordinates) :
    List (SPFactor H ι) :=
  (coordinates.weightFactors lowerWeight).map
    SPFactor.ofMonomial

/-- The normalized endpoint tail strictly above the active stratum. -/
def higherFactors
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CHRecipe H ι}
    (_view :
      CSViewa
        (n := n) lowerWeight coordinates) :
    List (SPFactor H ι) :=
  coordinates.polynomialTailFactors (n := n) lowerWeight

/-- The complete normalized endpoint is its active block followed by its tail. -/
lemma current_append_higher
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CHRecipe H ι}
    (view :
      CSViewa
        (n := n) lowerWeight coordinates) :
    coordinates.polynomialFactors (n := n) =
      view.currentFactors ++ view.higherFactors := by
  exact
    coordinates.poly_no_below
      view.coordinates_no_below view.lowerWeight_pos
        view.lowerWeight_cutoff

/-- Every active-block factor has exactly the active ordinary Hall weight. -/
lemma word_current_factors
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CHRecipe H ι}
    (view :
      CSViewa
        (n := n) lowerWeight coordinates)
    {x : SPFactor H ι}
    (hx : x ∈ view.currentFactors) :
    x.word.weight HEAddres.weight = lowerWeight := by
  rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact coordinates.word_weight_factors hy

/-- The active block is supported at the active stratum. -/
lemma least_current_factors
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CHRecipe H ι}
    (view :
      CSViewa
        (n := n) lowerWeight coordinates) :
    SPFactor.WordWeightLeast lowerWeight
      view.currentFactors := by
  intro x hx
  rw [view.word_current_factors hx]

/-- The higher tail is supported one stratum above the active block. -/
lemma least_higher_factors
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CHRecipe H ι}
    (view :
      CSViewa
        (n := n) lowerWeight coordinates) :
    SPFactor.WordWeightLeast (lowerWeight + 1)
      view.higherFactors :=
  coordinates.least_tail_factors

/-- The higher tail remains physically below the quotient cutoff. -/
lemma truncated_higher_factors
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CHRecipe H ι}
    (view :
      CSViewa
        (n := n) lowerWeight coordinates) :
    SPFactor.IsTruncated n view.higherFactors :=
  coordinates.truncated_tail_factors view.lowerWeight_cutoff

end CSViewa

namespace SSRw

/-- Finite normalized semantic obstruction runs compose under concatenation. -/
lemma append
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L₁ R₁ L₂ R₂ : List (SPFactor H ι)}
    (hleft :
      SSRw
        (n := n) (lowerWeight := lowerWeight) L₁ R₁)
    (hright :
      SSRw
        (n := n) (lowerWeight := lowerWeight) L₂ R₂) :
    SSRw
      (n := n) (lowerWeight := lowerWeight)
      (L₁ ++ L₂) (R₁ ++ R₂) := by
  have hleft' :
      SSRw
        (n := n) (lowerWeight := lowerWeight)
        (L₁ ++ L₂) (R₁ ++ L₂) := by
    simpa using hleft.context [] L₂
  have hright' :
      SSRw
        (n := n) (lowerWeight := lowerWeight)
        (R₁ ++ L₂) (R₁ ++ R₂) := by
    simpa using hright.context R₁ []
  exact hleft'.trans hright'

end SSRw

/--
The operational one-stratum scheduler obligation.  Assuming correction
packets can already be normalized one stratum higher, inserting one factor
must be witnessed by a finite run of normalized obstruction swaps.
-/
structure RSInsert
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    Prop where
  insert :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      TSNormalc
          (n := n) (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CHRecipe H ι)
          (factor : SPFactor H ι),
          coordinates.NTBelow lowerWeight →
          lowerWeight ≤ factor.word.weight HEAddres.weight →
          factor.word.weight HEAddres.weight < n →
            ∃ next : CHRecipe H ι,
              next.NTBelow lowerWeight ∧
                SSRw
                  (n := n) (lowerWeight := lowerWeight)
                  (coordinates.polynomialFactors (n := n) ++ [factor])
                  (next.polynomialFactors (n := n))

namespace RSInsert

/--
An operational one-stratum schedule supplies the semantic insertion step used
by well-founded filtration recursion.
-/
def recSemanticInsertion
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (schedule :
      RSInsert
        (n := n) H) :
    TRInsert
      (n := n) H where
  insert lowerWeight normalizer := {
    insert := by
      intro ι coordinates factor hcoordinates hfactorSupported hfactorTruncated
      rcases schedule.insert lowerWeight normalizer coordinates factor
          hcoordinates hfactorSupported hfactorTruncated with
        ⟨next, hnextSupported, hrewrites⟩
      exact ⟨next, hnextSupported, hrewrites.listEval_eq⟩ }

end RSInsert

/--
An operational one-stratum schedule constructs product recollection
polynomials.
-/
theorem collected_insertion_schedule
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (schedule :
      RSInsert
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  collected_insertion_step
    H e schedule.recSemanticInsertion

/--
An operational one-stratum schedule constructs inverse recollection
polynomials.
-/
theorem semantic_insertion_schedule
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (schedule :
      RSInsert
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  semantic_insertion_step
    H e schedule.recSemanticInsertion

end TCTex
end Towers

/-!
# Canonical higher-tail splicing for product and inverse polynomial coordinates

At one active Hall-weight stratum, inserting a strictly heavier signed factor
does not change the current coordinate block.  The old higher tail and the new
factor can be normalized one stratum higher, then spliced back above the
untouched active block.

This file implements that splice and proves the automatic strictly-heavier
insertion branch.  The remaining polynomial recollection problem is therefore
the active-weight branch.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace CHRecipe

/--
Keep the base recipes through `lowerWeight` and use `higher` strictly above
that stratum.
-/
def spliceHigherTail
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (base higher : CHRecipe H ι)
    (lowerWeight : ℕ) :
    CHRecipe H ι where
  recipes s i :=
    if s ≤ lowerWeight then base.recipes s i else higher.recipes s i

@[simp]
lemma recipes_splice_higher
    {d lowerWeight s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (base higher : CHRecipe H ι)
    (hs : s ≤ lowerWeight)
    (i : (H s).index) :
    (base.spliceHigherTail higher lowerWeight).recipes s i =
      base.recipes s i := by
  simp [spliceHigherTail, hs]

@[simp]
lemma recipes_splice_tail
    {d lowerWeight s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (base higher : CHRecipe H ι)
    (hs : lowerWeight < s)
    (i : (H s).index) :
    (base.spliceHigherTail higher lowerWeight).recipes s i =
      higher.recipes s i := by
  simp [spliceHigherTail, Nat.not_le_of_lt hs]

/-- Through the splice stratum, fixed-weight factors come from the base. -/
lemma splice_higher_tail
    {d lowerWeight s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (base higher : CHRecipe H ι)
    (hs : s ≤ lowerWeight) :
    (base.spliceHigherTail higher lowerWeight).weightFactors s =
      base.weightFactors s := by
  unfold weightFactors
  apply List.flatMap_congr
  intro i _hi
  rw [base.recipes_splice_higher higher hs]

/-- Strictly above the splice stratum, fixed-weight factors come from `higher`. -/
lemma factors_splice_higher
    {d lowerWeight s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (base higher : CHRecipe H ι)
    (hs : lowerWeight < s) :
    (base.spliceHigherTail higher lowerWeight).weightFactors s =
      higher.weightFactors s := by
  unfold weightFactors
  apply List.flatMap_congr
  intro i _hi
  rw [base.recipes_splice_tail higher hs]

/-- Splicing preserves the lower support bound of the base endpoint. -/
lemma no_below_splice
    {d lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (base higher : CHRecipe H ι)
    (hbase : base.NTBelow lowerWeight) :
    (base.spliceHigherTail higher lowerWeight).NTBelow lowerWeight := by
  intro s hs
  rw [base.splice_higher_tail higher (by omega)]
  exact hbase s hs

/-- Any endpoint supported above a prefix has no factors in that prefix. -/
lemma nil_no_below
    {d lowerWeight k : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (hR : R.NTBelow lowerWeight)
    (hk : k < lowerWeight) :
    R.prefixFactors k = [] := by
  unfold prefixFactors
  apply List.flatMap_eq_nil_iff.2
  intro s hs
  apply R.nil_terms_below hR
  have hsRange := List.mem_range.mp hs
  omega

/-- The spliced higher monomial tail is exactly the tail supplied by `higher`. -/
lemma tail_splice_higher
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (base higher : CHRecipe H ι) :
    (base.spliceHigherTail higher lowerWeight).tailFactors
        (n := n) lowerWeight =
      higher.tailFactors (n := n) lowerWeight := by
  unfold tailFactors
  apply List.flatMap_congr
  intro s hs
  apply base.factors_splice_higher higher
  have hsLower := List.left_le_of_mem_range' hs
  omega

/--
If `higher` begins one stratum above the splice, its full signed endpoint is
exactly its signed tail above `lowerWeight`.
-/
lemma no_below_succ
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (higher : CHRecipe H ι)
    (hhigher : higher.NTBelow (lowerWeight + 1))
    (hlowerWeightCutoff : lowerWeight ≤ n - 1) :
    higher.polynomialFactors (n := n) =
      higher.polynomialTailFactors (n := n) lowerWeight := by
  rw [higher.prefix_append_tail
      hlowerWeightCutoff,
    higher.nil_no_below hhigher (by omega)]
  rfl

/--
The signed factors of a supported splice are the untouched active block
followed by the complete normalized higher endpoint.
-/
lemma factors_splice_tail
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (base higher : CHRecipe H ι)
    (hbase : base.NTBelow lowerWeight)
    (hhigher : higher.NTBelow (lowerWeight + 1))
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightCutoff : lowerWeight ≤ n - 1) :
    (base.spliceHigherTail higher lowerWeight).polynomialFactors (n := n) =
      (base.weightFactors lowerWeight).map
          SPFactor.ofMonomial ++
        higher.polynomialFactors (n := n) := by
  rw [poly_no_below
        (base.spliceHigherTail higher lowerWeight)
        (base.no_below_splice higher hbase)
          hlowerWeightPos hlowerWeightCutoff,
    base.splice_higher_tail higher (Nat.le_refl _)]
  rw [polynomialTailFactors, base.tail_splice_higher higher,
    ← polynomialTailFactors,
    ← higher.no_below_succ
      hhigher hlowerWeightCutoff]

end CHRecipe

namespace TSNormalc

/--
Insert a factor strictly above a positive active stratum by normalizing the old
higher tail together with the factor, then splicing that normalized tail back
above the untouched active coordinate block.
-/
lemma insertion_pos_weight
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer :
      TSNormalc
        (n := n) (lowerWeight := lowerWeight + 1) H)
    (coordinates : CHRecipe H ι)
    (factor : SPFactor H ι)
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hfactorWeight :
      lowerWeight < factor.word.weight HEAddres.weight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    ∃ next : CHRecipe H ι,
      next.NTBelow lowerWeight ∧
        ∀ e : ι → HEFam H,
          SPFactor.listEval (n := n) e
              (next.polynomialFactors (n := n)) =
            SPFactor.listEval (n := n) e
              (coordinates.polynomialFactors (n := n) ++ [factor]) := by
  have hlowerWeightCutoff : lowerWeight ≤ n - 1 := by
    omega
  have htailTruncated :
      SPFactor.IsTruncated n
        (coordinates.polynomialTailFactors (n := n) lowerWeight) :=
    coordinates.truncated_tail_factors hlowerWeightCutoff
  have htailSupported :
      SPFactor.WordWeightLeast (lowerWeight + 1)
        (coordinates.polynomialTailFactors (n := n) lowerWeight) :=
    coordinates.least_tail_factors
  have hsourceTruncated :
      SPFactor.IsTruncated n
        (coordinates.polynomialTailFactors (n := n) lowerWeight ++ [factor]) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact htailTruncated x hx
    · rcases List.mem_singleton.mp hx with rfl
      exact hfactorTruncated
  have hsourceSupported :
      SPFactor.WordWeightLeast (lowerWeight + 1)
        (coordinates.polynomialTailFactors (n := n) lowerWeight ++ [factor]) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact htailSupported x hx
    · rcases List.mem_singleton.mp hx with rfl
      omega
  rcases normalizer.normalize
      (coordinates.polynomialTailFactors (n := n) lowerWeight ++ [factor])
      hsourceTruncated hsourceSupported with
    ⟨higher, hhigher, hhigherEval⟩
  refine
    ⟨coordinates.spliceHigherTail higher lowerWeight,
      coordinates.no_below_splice higher hcoordinates, ?_⟩
  intro e
  rw [coordinates.factors_splice_tail higher hcoordinates
      hhigher hlowerWeightPos hlowerWeightCutoff,
    coordinates.poly_no_below
      hcoordinates hlowerWeightPos hlowerWeightCutoff,
    SPFactor.listEval_append,
    SPFactor.listEval_append,
    hhigherEval e,
    SPFactor.listEval_append,
    SPFactor.listEval_append]
  simp [mul_assoc]

/--
At stratum zero, delegate the complete endpoint plus the inserted factor to
the next-stratum normalizer.
-/
lemma insertion_zero
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer :
      TSNormalc
        (n := n) (lowerWeight := 1) H)
    (coordinates : CHRecipe H ι)
    (factor : SPFactor H ι)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    ∃ next : CHRecipe H ι,
      next.NTBelow 0 ∧
        ∀ e : ι → HEFam H,
          SPFactor.listEval (n := n) e
              (next.polynomialFactors (n := n)) =
            SPFactor.listEval (n := n) e
              (coordinates.polynomialFactors (n := n) ++ [factor]) := by
  have hsourceTruncated :
      SPFactor.IsTruncated n
        (coordinates.polynomialFactors (n := n) ++ [factor]) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact coordinates.truncated_polynomial_factors x hx
    · rcases List.mem_singleton.mp hx with rfl
      exact hfactorTruncated
  have hsourceSupported :
      SPFactor.WordWeightLeast 1
        (coordinates.polynomialFactors (n := n) ++ [factor]) := by
    intro x _hx
    exact x.word_weight_pos
  rcases normalizer.normalize
      (coordinates.polynomialFactors (n := n) ++ [factor])
      hsourceTruncated hsourceSupported with
    ⟨next, _hnextSupported, hnextEval⟩
  exact ⟨next, fun _s hs => False.elim (by omega), hnextEval⟩

/-- Delegate any insertion strictly above the active stratum. -/
lemma insertion_word_weight
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer :
      TSNormalc
        (n := n) (lowerWeight := lowerWeight + 1) H)
    (coordinates : CHRecipe H ι)
    (factor : SPFactor H ι)
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hfactorWeight :
      lowerWeight < factor.word.weight HEAddres.weight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    ∃ next : CHRecipe H ι,
      next.NTBelow lowerWeight ∧
        ∀ e : ι → HEFam H,
          SPFactor.listEval (n := n) e
              (next.polynomialFactors (n := n)) =
            SPFactor.listEval (n := n) e
              (coordinates.polynomialFactors (n := n) ++ [factor]) := by
  by_cases hlowerWeight : lowerWeight = 0
  · subst lowerWeight
    exact normalizer.insertion_zero coordinates factor
      hfactorTruncated
  · exact normalizer.insertion_pos_weight coordinates
      factor hcoordinates (by omega) hfactorWeight hfactorTruncated

end TSNormalc

/--
The genuinely nontrivial local branch: insert a factor whose word weight is
exactly the active coordinate stratum.
-/
structure SemanticInsertionBranch
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    Prop where
  insert :
    ∀ lowerWeight : ℕ,
      TSNormalc
          (n := n) (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CHRecipe H ι)
          (factor : SPFactor H ι),
          coordinates.NTBelow lowerWeight →
          factor.word.weight HEAddres.weight = lowerWeight →
          factor.word.weight HEAddres.weight < n →
            ∃ next : CHRecipe H ι,
              next.NTBelow lowerWeight ∧
                ∀ e : ι → HEFam H,
                  SPFactor.listEval (n := n) e
                      (next.polynomialFactors (n := n)) =
                    SPFactor.listEval (n := n) e
                      (coordinates.polynomialFactors (n := n) ++ [factor])

namespace TRInsert

/--
Strictly heavier insertions are automatic by tail delegation.  An active-weight
insertion branch therefore supplies the complete filtration-recursive step.
-/
def insertion_branch
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (active :
      SemanticInsertionBranch
        (n := n) H) :
    TRInsert
      (n := n) H where
  insert lowerWeight normalizer := {
    insert := by
      intro ι (coordinates : CHRecipe H ι)
        (factor : SPFactor H _)
        hcoordinates hfactorSupported hfactorTruncated
      by_cases hfactorStrict :
          lowerWeight < factor.word.weight HEAddres.weight
      · exact normalizer.insertion_word_weight coordinates factor
          hcoordinates hfactorStrict hfactorTruncated
      · exact active.insert lowerWeight normalizer coordinates factor
          hcoordinates (by omega) hfactorTruncated }

end TRInsert

/--
An active-weight insertion branch constructs product recollection
polynomials.
-/
theorem coordinate_insertion_branch
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (active :
      SemanticInsertionBranch
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  collected_insertion_step
    H e
      (TRInsert.insertion_branch
        active)

/--
An active-weight insertion branch constructs inverse recollection
polynomials.
-/
theorem data_insertion_branch
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (active :
      SemanticInsertionBranch
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  semantic_insertion_step
    H e
      (TRInsert.insertion_branch
        active)

end TCTex
end Towers

/-!
# List-valued semantic insertion derivations for product and inverse polynomials

The More3 collector recursively inserts one correction term before continuing
an obstructed insertion.  Signed-polynomial Hall collection has the same shape,
except that a delegated correction packet is normalized to a whole list of
higher-weight coordinate factors.

This file packages that list-valued recursion.  A single-factor insertion may
swap one adjacent obstruction, recursively fold its normalized correction
block into the preceding prefix, and then continue inserting the original
factor.  A block insertion folds a finite correction list by repeated
single-factor insertion.

Both certificates compile to finite normalized semantic obstruction rewrites.
The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

mutual

  /-- A list-valued More3 insertion derivation for one supported stratum. -/
  inductive SSInsertb
      {d n : ℕ}
      (H : ∀ r : ℕ, BCWta.{u} d r)
      (ι : Type)
      (lowerWeight : ℕ) :
      List (SPFactor H ι) →
        SPFactor H ι →
          List (SPFactor H ι) → Prop where
    | nil
        (A : SPFactor H ι) :
        SSInsertb
          (n := n) H ι lowerWeight [] A [A]
    | append
        (P : List (SPFactor H ι))
        (B A : SPFactor H ι) :
        SSInsertb
          (n := n) H ι lowerWeight (P ++ [B]) A (P ++ [B, A])
    | obstruction
        (P : List (SPFactor H ι))
        (B A : SPFactor H ι)
        (C : TSPkt n B A)
        (normalization :
          TSNorm
            lowerWeight C)
        {Q R : List (SPFactor H ι)}
        (hcorrections :
          TSInsertd
            (n := n) H ι lowerWeight P
              (normalization.coordinates.polynomialFactors (n := n)) Q)
        (hinsert :
          SSInsertb
            (n := n) H ι lowerWeight Q A R) :
        SSInsertb
          (n := n) H ι lowerWeight (P ++ [B]) A (R ++ [B])

  /--
  Fold a finite normalized correction block into a preceding prefix by
  repeated semantic insertion.
  -/
  inductive TSInsertd
      {d n : ℕ}
      (H : ∀ r : ℕ, BCWta.{u} d r)
      (ι : Type)
      (lowerWeight : ℕ) :
      List (SPFactor H ι) →
        List (SPFactor H ι) →
          List (SPFactor H ι) → Prop where
    | nil
        (P : List (SPFactor H ι)) :
        TSInsertd
          (n := n) H ι lowerWeight P [] P
    | snoc
        (P source : List (SPFactor H ι))
        (A : SPFactor H ι)
        {Q R : List (SPFactor H ι)}
        (hsource :
          TSInsertd
            (n := n) H ι lowerWeight P source Q)
        (hinsert :
          SSInsertb
            (n := n) H ι lowerWeight Q A R) :
        TSInsertd
          (n := n) H ι lowerWeight P (source ++ [A]) R

end

namespace SSInsertb

/-- A semantic insertion certificate compiles to a finite obstruction run. -/
lemma rewrites
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    {A : SPFactor H ι}
    (h :
      SSInsertb
        (n := n) H ι lowerWeight L A R) :
    SSRw
      (n := n) (lowerWeight := lowerWeight) (L ++ [A]) R := by
  refine
    SSInsertb.recOn
      (motive_1 := fun L A R _h =>
        SSRw
          (n := n) (lowerWeight := lowerWeight) (L ++ [A]) R)
      (motive_2 := fun P source R _h =>
        SSRw
          (n := n) (lowerWeight := lowerWeight) (P ++ source) R)
      h ?_ ?_ ?_ ?_ ?_
  · intro A
    simpa using
      (Relation.ReflTransGen.refl :
        SSRw
          (n := n) (lowerWeight := lowerWeight) [A] [A])
  · intro P B A
    simpa [List.append_assoc] using
      (Relation.ReflTransGen.refl :
        SSRw
          (n := n) (lowerWeight := lowerWeight)
          (P ++ [B, A]) (P ++ [B, A]))
  · intro P B A C normalization Q R hcorrections hinsert
      ihcorrections ihinsert
    have hswap :
        SSRw
          (n := n) (lowerWeight := lowerWeight)
          (P ++ [B, A])
          (P ++ normalization.coordinates.polynomialFactors (n := n) ++
            [A, B]) := by
      apply SSRw.single
      simpa using
        (SSColl.obstruction
          P [] B A C normalization)
    have hrouteCorrections :
        SSRw
          (n := n) (lowerWeight := lowerWeight)
          (P ++ normalization.coordinates.polynomialFactors (n := n) ++
            [A, B])
          (Q ++ [A, B]) := by
      simpa [List.append_assoc] using
        ihcorrections.context [] [A, B]
    have hrouteA :
        SSRw
          (n := n) (lowerWeight := lowerWeight)
          (Q ++ [A, B]) (R ++ [B]) := by
      simpa [List.append_assoc] using ihinsert.context [] [B]
    simpa [List.append_assoc] using
      hswap.trans (hrouteCorrections.trans hrouteA)
  · intro P
    simpa using
      (Relation.ReflTransGen.refl :
        SSRw
          (n := n) (lowerWeight := lowerWeight) P P)
  · intro P source A Q R hsource hinsert ihsource ihinsert
    have hroutePrefix :
        SSRw
          (n := n) (lowerWeight := lowerWeight)
          ((P ++ source) ++ [A]) (Q ++ [A]) := by
      simpa [List.append_assoc] using ihsource.context [] [A]
    simpa [List.append_assoc] using hroutePrefix.trans ihinsert

end SSInsertb

namespace TSInsertd

/-- A block-folding certificate compiles to a finite obstruction run. -/
lemma rewrites
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {P source R : List (SPFactor H ι)}
    (h :
      TSInsertd
        (n := n) H ι lowerWeight P source R) :
    SSRw
      (n := n) (lowerWeight := lowerWeight) (P ++ source) R := by
  refine
    TSInsertd.recOn
      (motive_1 := fun L A R _h =>
        SSRw
          (n := n) (lowerWeight := lowerWeight) (L ++ [A]) R)
      (motive_2 := fun P source R _h =>
        SSRw
          (n := n) (lowerWeight := lowerWeight) (P ++ source) R)
      h ?_ ?_ ?_ ?_ ?_
  · intro A
    simpa using
      (Relation.ReflTransGen.refl :
        SSRw
          (n := n) (lowerWeight := lowerWeight) [A] [A])
  · intro P B A
    simpa [List.append_assoc] using
      (Relation.ReflTransGen.refl :
        SSRw
          (n := n) (lowerWeight := lowerWeight)
          (P ++ [B, A]) (P ++ [B, A]))
  · intro P B A C normalization Q R hcorrections hinsert
      ihcorrections ihinsert
    have hswap :
        SSRw
          (n := n) (lowerWeight := lowerWeight)
          (P ++ [B, A])
          (P ++ normalization.coordinates.polynomialFactors (n := n) ++
            [A, B]) := by
      apply SSRw.single
      simpa using
        (SSColl.obstruction
          P [] B A C normalization)
    have hrouteCorrections :
        SSRw
          (n := n) (lowerWeight := lowerWeight)
          (P ++ normalization.coordinates.polynomialFactors (n := n) ++
            [A, B])
          (Q ++ [A, B]) := by
      simpa [List.append_assoc] using
        ihcorrections.context [] [A, B]
    have hrouteA :
        SSRw
          (n := n) (lowerWeight := lowerWeight)
          (Q ++ [A, B]) (R ++ [B]) := by
      simpa [List.append_assoc] using ihinsert.context [] [B]
    simpa [List.append_assoc] using
      hswap.trans (hrouteCorrections.trans hrouteA)
  · intro P
    simpa using
      (Relation.ReflTransGen.refl :
        SSRw
          (n := n) (lowerWeight := lowerWeight) P P)
  · intro P source A Q R hsource hinsert ihsource ihinsert
    have hroutePrefix :
        SSRw
          (n := n) (lowerWeight := lowerWeight)
          ((P ++ source) ++ [A]) (Q ++ [A]) := by
      simpa [List.append_assoc] using ihsource.context [] [A]
    simpa [List.append_assoc] using hroutePrefix.trans ihinsert

end TSInsertd

namespace SSInsertb

/-- A semantic insertion certificate preserves evaluation exactly. -/
lemma listEval_eq
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    {A : SPFactor H ι}
    (h :
      SSInsertb
        (n := n) H ι lowerWeight L A R)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e R =
      SPFactor.listEval (n := n) e (L ++ [A]) :=
  h.rewrites.listEval_eq e

/-- A semantic insertion certificate preserves physical truncation. -/
lemma isTruncated
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    {A : SPFactor H ι}
    (h :
      SSInsertb
        (n := n) H ι lowerWeight L A R)
    (hL : SPFactor.IsTruncated n L)
    (hA : A.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n R := by
  apply h.rewrites.isTruncated
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hL x hx
  · rcases List.mem_singleton.mp hx with rfl
    exact hA

/-- A semantic insertion certificate preserves its current-stratum bound. -/
lemma wordWeightLeast
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    {A : SPFactor H ι}
    (h :
      SSInsertb
        (n := n) H ι lowerWeight L A R)
    (hL : SPFactor.WordWeightLeast lowerWeight L)
    (hA : lowerWeight ≤ A.word.weight HEAddres.weight) :
    SPFactor.WordWeightLeast lowerWeight R := by
  apply h.rewrites.wordWeightLeast
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hL x hx
  · rcases List.mem_singleton.mp hx with rfl
    exact hA

end SSInsertb

namespace TSInsertd

/-- Folding a normalized correction block preserves evaluation exactly. -/
lemma listEval_eq
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {P source R : List (SPFactor H ι)}
    (h :
      TSInsertd
        (n := n) H ι lowerWeight P source R)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e R =
      SPFactor.listEval (n := n) e (P ++ source) :=
  h.rewrites.listEval_eq e

/-- Folding a normalized correction block preserves physical truncation. -/
lemma isTruncated
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {P source R : List (SPFactor H ι)}
    (h :
      TSInsertd
        (n := n) H ι lowerWeight P source R)
    (hP : SPFactor.IsTruncated n P)
    (hsource : SPFactor.IsTruncated n source) :
    SPFactor.IsTruncated n R := by
  apply h.rewrites.isTruncated
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hP x hx
  · exact hsource x hx

/-- Folding a normalized correction block preserves lower word-weight bounds. -/
lemma wordWeightLeast
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {P source R : List (SPFactor H ι)}
    (h :
      TSInsertd
        (n := n) H ι lowerWeight P source R)
    (hP : SPFactor.WordWeightLeast lowerWeight P)
    (hsource :
      SPFactor.WordWeightLeast lowerWeight source) :
    SPFactor.WordWeightLeast lowerWeight R := by
  apply h.rewrites.wordWeightLeast
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hP x hx
  · exact hsource x hx

end TSInsertd

namespace TSFtry

/--
A supported packet factory reduces one obstructed insertion to routing its
normalized higher correction block and then continuing the original
insertion.
-/
lemma semantic_inserts_obstruction
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (normalizer :
      TSNormalc
        (n := n) (lowerWeight := lowerWeight + 1) H)
    (P : List (SPFactor H ι))
    (B A : SPFactor H ι)
    (hB : lowerWeight ≤ B.word.weight HEAddres.weight)
    (hA : lowerWeight ≤ A.word.weight HEAddres.weight)
    (hcontinue :
      ∀ normalization :
          TSNorm
            lowerWeight (factory.packet B A hB hA),
        ∃ Q R : List (SPFactor H ι),
          TSInsertd
              (n := n) H ι lowerWeight P
                (normalization.coordinates.polynomialFactors (n := n)) Q ∧
            SSInsertb
              (n := n) H ι lowerWeight Q A R) :
    ∃ R : List (SPFactor H ι),
      SSInsertb
        (n := n) H ι lowerWeight (P ++ [B]) A R := by
  rcases (factory.packet B A hB hA).normalization_left
      hB normalizer with
    ⟨normalization⟩
  rcases hcontinue normalization with ⟨Q, R, hcorrections, hinsert⟩
  exact
    ⟨R ++ [B],
      SSInsertb.obstruction
        P B A (factory.packet B A hB hA) normalization
          hcorrections hinsert⟩

end TSFtry

/--
A structured one-stratum scheduler obligation: endpoint insertion is witnessed
by a list-valued semantic insertion derivation.
-/
structure IDSched
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    Prop where
  insert :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      TSNormalc
          (n := n) (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CHRecipe H ι)
          (factor : SPFactor H ι),
          coordinates.NTBelow lowerWeight →
          lowerWeight ≤ factor.word.weight HEAddres.weight →
          factor.word.weight HEAddres.weight < n →
            ∃ next : CHRecipe H ι,
              next.NTBelow lowerWeight ∧
                SSInsertb
                  (n := n) H ι lowerWeight
                    (coordinates.polynomialFactors (n := n)) factor
                      (next.polynomialFactors (n := n))

namespace IDSched

/-- Structured insertion derivations supply the finite-rewrite scheduler. -/
def recursiveCoordinateInsertion
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (schedule :
      IDSched
        (n := n) H) :
    RSInsert
      (n := n) H where
  insert lowerWeight normalizer coordinates factor hcoordinates
      hfactorSupported hfactorTruncated := by
    rcases schedule.insert lowerWeight normalizer coordinates factor
        hcoordinates hfactorSupported hfactorTruncated with
      ⟨next, hnextSupported, hinsert⟩
    exact ⟨next, hnextSupported, hinsert.rewrites⟩

end IDSched

/--
A structured list-valued insertion schedule constructs product recollection
polynomials.
-/
theorem insertion_derivation_schedule
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (schedule :
      IDSched
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  collected_insertion_schedule
    H e schedule.recursiveCoordinateInsertion

/--
A structured list-valued insertion schedule constructs inverse recollection
polynomials.
-/
theorem recursive_insertion_derivation
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (schedule :
      IDSched
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  semantic_insertion_schedule
    H e schedule.recursiveCoordinateInsertion

end TCTex
end Towers

/-!
# Active-layer resolutions for product and inverse polynomial coordinates

After strictly heavier insertions have been delegated automa, the
remaining local operation occurs at one active Hall-weight stratum.  It must
replace the old endpoint followed by one active-weight signed factor by:

* a new normalized coordinate block at the active weight; and
* a residual signed-polynomial source supported strictly above that weight.

The next-stratum normalizer recollects the residual source, and canonical
higher-tail splicing assembles the final endpoint.  This file packages that
reduction and a collector-facing finite-rewrite route interface.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
The semantic output of resolving one active-weight signed-polynomial
insertion.  The active coordinate block has already been updated; every
remaining factor belongs to the next support stratum.
-/
structure SAResolu
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (coordinates : CHRecipe H ι)
    (factor : SPFactor H ι) where
  activeCoordinates :
    CHRecipe H ι
  active_terms_below :
    activeCoordinates.NTBelow lowerWeight
  higherSource :
    List (SPFactor H ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_least_succ :
    SPFactor.WordWeightLeast (lowerWeight + 1)
      higherSource
  active_append_source :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e
          ((activeCoordinates.weightFactors lowerWeight).map
              SPFactor.ofMonomial ++
            higherSource) =
        SPFactor.listEval (n := n) e
          (coordinates.polynomialFactors (n := n) ++ [factor])

namespace SAResolu

/--
Normalize the strictly higher residual source and splice it above the updated
active coordinate block.
-/
lemma exists_insertion
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CHRecipe H ι}
    {factor : SPFactor H ι}
    (resolution :
      SAResolu
        (n := n) (lowerWeight := lowerWeight) H ι coordinates factor)
    (normalizer :
      TSNormalc
        (n := n) (lowerWeight := lowerWeight + 1) H)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    ∃ next : CHRecipe H ι,
      next.NTBelow lowerWeight ∧
        ∀ e : ι → HEFam H,
          SPFactor.listEval (n := n) e
              (next.polynomialFactors (n := n)) =
            SPFactor.listEval (n := n) e
              (coordinates.polynomialFactors (n := n) ++ [factor]) := by
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    have hfactorPos := factor.word_weight_pos
    omega
  have hlowerWeightCutoff : lowerWeight ≤ n - 1 := by
    omega
  rcases normalizer.normalize resolution.higherSource
      resolution.higher_source_truncated
      resolution.higher_least_succ with
    ⟨higher, hhigher, hhigherEval⟩
  refine
    ⟨resolution.activeCoordinates.spliceHigherTail higher lowerWeight,
      resolution.activeCoordinates.no_below_splice higher
        resolution.active_terms_below, ?_⟩
  intro e
  rw [resolution.activeCoordinates.factors_splice_tail higher
      resolution.active_terms_below hhigher hlowerWeightPos
        hlowerWeightCutoff,
    SPFactor.listEval_append,
    hhigherEval e,
    ← SPFactor.listEval_append]
  exact resolution.active_append_source e

end SAResolu

/--
A supply of semantic active-layer resolutions.  This is the exact remaining
local semantic obligation after higher-tail delegation.
-/
structure TRFtryb
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  resolve :
    ∀ {ι : Type}
      (lowerWeight : ℕ)
      (coordinates : CHRecipe H ι)
      (factor : SPFactor H ι),
      coordinates.NTBelow lowerWeight →
      factor.word.weight HEAddres.weight = lowerWeight →
      factor.word.weight HEAddres.weight < n →
        SAResolu
          (n := n) (lowerWeight := lowerWeight) H ι coordinates factor

namespace TRFtryb

/-- Active-layer resolutions supply the residual active insertion branch. -/
def insertionBranch
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      TRFtryb
        (n := n) H) :
    SemanticInsertionBranch
      (n := n) H where
  insert lowerWeight normalizer coordinates factor hcoordinates hfactorWeight
      hfactorTruncated :=
    (factory.resolve lowerWeight coordinates factor hcoordinates hfactorWeight
      hfactorTruncated).exists_insertion normalizer hfactorWeight
        hfactorTruncated

/--
An active-layer resolution factory supplies the complete filtration-recursive
semantic insertion step.
-/
def recSemanticInsertion
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      TRFtryb
        (n := n) H) :
    TRInsert
      (n := n) H :=
  TRInsert.insertion_branch
    factory.insertionBranch

end TRFtryb

/--
A collector-facing active-layer certificate.  A finite normalized obstruction
run routes one active-weight insertion to a new active coordinate block
followed by a strictly higher residual source.
-/
structure SSRoute
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (coordinates : CHRecipe H ι)
    (factor : SPFactor H ι) where
  activeCoordinates :
    CHRecipe H ι
  active_terms_below :
    activeCoordinates.NTBelow lowerWeight
  higherSource :
    List (SPFactor H ι)
  higher_least_succ :
    SPFactor.WordWeightLeast (lowerWeight + 1)
      higherSource
  rewrites :
    SSRw
      (n := n) (lowerWeight := lowerWeight)
        (coordinates.polynomialFactors (n := n) ++ [factor])
        ((activeCoordinates.weightFactors lowerWeight).map
            SPFactor.ofMonomial ++ higherSource)

namespace SSRoute

/-- A finite normalized route supplies the corresponding semantic resolution. -/
def activeLayerResolution
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CHRecipe H ι}
    {factor : SPFactor H ι}
    (route :
      SSRoute
        (n := n) (lowerWeight := lowerWeight) H ι coordinates factor)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    SAResolu
      (n := n) (lowerWeight := lowerWeight) H ι coordinates factor where
  activeCoordinates := route.activeCoordinates
  active_terms_below :=
    route.active_terms_below
  higherSource := route.higherSource
  higher_source_truncated := by
    have houtput :
        SPFactor.IsTruncated n
          ((route.activeCoordinates.weightFactors lowerWeight).map
              SPFactor.ofMonomial ++ route.higherSource) :=
      route.rewrites.isTruncated (by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact coordinates.truncated_polynomial_factors x hx
        · rcases List.mem_singleton.mp hx with rfl
          exact hfactorTruncated)
    intro x hx
    exact houtput x (List.mem_append_right _ hx)
  higher_least_succ :=
    route.higher_least_succ
  active_append_source := fun e =>
    route.rewrites.listEval_eq e

end SSRoute

/--
A structured finite-rewrite route schedule for the only nonautomatic branch:
inserting one factor whose weight is exactly the active stratum.
-/
structure TRSem
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  route :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      TSNormalc
          (n := n) (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CHRecipe H ι)
          (factor : SPFactor H ι),
          coordinates.NTBelow lowerWeight →
          factor.word.weight HEAddres.weight = lowerWeight →
          factor.word.weight HEAddres.weight < n →
            SSRoute
              (n := n) (lowerWeight := lowerWeight) H ι coordinates factor

namespace TRSem

/--
A structured active-layer finite-rewrite route schedule supplies the residual
active insertion branch.
-/
def insertionBranch
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (schedule :
      TRSem
        (n := n) H) :
    SemanticInsertionBranch
      (n := n) H where
  insert lowerWeight normalizer coordinates factor hcoordinates hfactorWeight
      hfactorTruncated :=
    ((schedule.route lowerWeight normalizer coordinates factor hcoordinates
      hfactorWeight hfactorTruncated).activeLayerResolution
        hfactorTruncated).exists_insertion normalizer hfactorWeight
          hfactorTruncated

/--
A structured active-layer finite-rewrite route schedule supplies the complete
filtration-recursive semantic insertion step.
-/
def recSemanticInsertion
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (schedule :
      TRSem
        (n := n) H) :
    TRInsert
      (n := n) H :=
  TRInsert.insertion_branch
    schedule.insertionBranch

end TRSem

/--
An active-layer resolution factory constructs product recollection
polynomials.
-/
theorem coordinate_resolution_factory
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (factory :
      TRFtryb
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  collected_insertion_step
    H e factory.recSemanticInsertion

/--
An active-layer resolution factory constructs inverse recollection
polynomials.
-/
theorem data_resolution_factory
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (factory :
      TRFtryb
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  semantic_insertion_step
    H e factory.recSemanticInsertion

/--
A structured active-layer route schedule constructs product recollection
polynomials.
-/
theorem collected_active_route
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (schedule :
      TRSem
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  collected_insertion_step
    H e schedule.recSemanticInsertion

/--
A structured active-layer route schedule constructs inverse recollection
polynomials.
-/
theorem collected_active_schedule
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (schedule :
      TRSem
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  semantic_insertion_step
    H e schedule.recSemanticInsertion

end TCTex
end Towers

/-!
# Universal product and inverse polynomial collection reduction

The standalone signed-polynomial theory has now separated the two inputs
required from a universal Hall collector:

* higher-word correction packets for each supported adjacent swap; and
* a canonical endpoint builder whose derivation recursively routes the
  normalized higher correction blocks emitted by those swaps.

This file packages those inputs together.  A universal one-stratum derivation
builder supplies the schedule used by filtration recursion, and therefore
constructs the global product and inverse coordinate polynomials required by
Claim 8.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
The exact remaining one-stratum operational constructor.  For each support
stratum it receives the recursively constructed next-stratum semantic
normalizer and a supported signed-polynomial correction-packet factory.  It
must recollect one supported truncated factor into a canonical coordinate
endpoint, witnessed by the list-valued semantic insertion derivation.
-/
structure SDBuild
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  correctionFactory :
    ∀ lowerWeight : ℕ,
      TSFtry
        (n := n) H lowerWeight
  insert :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      TSNormalc
          (n := n) (lowerWeight := lowerWeight + 1) H →
        TSFtry
            (n := n) H lowerWeight →
          ∀ (coordinates : CHRecipe H ι)
            (factor : SPFactor H ι),
            coordinates.NTBelow lowerWeight →
            lowerWeight ≤ factor.word.weight HEAddres.weight →
            factor.word.weight HEAddres.weight < n →
              ∃ next : CHRecipe H ι,
                next.NTBelow lowerWeight ∧
                  SSInsertb
                    (n := n) H ι lowerWeight
                      (coordinates.polynomialFactors (n := n)) factor
                        (next.polynomialFactors (n := n))

namespace SDBuild

/--
A universal derivation builder supplies the structured one-stratum insertion
schedule consumed by filtration recursion.
-/
def insertionDerivationSchedule
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (builder :
      SDBuild
        (n := n) H) :
    IDSched
      (n := n) H where
  insert lowerWeight normalizer :=
    builder.insert lowerWeight normalizer (builder.correctionFactory lowerWeight)

/--
A universal derivation builder also supplies the semantic normalizer at every
stratum by well-founded filtration recursion.
-/
noncomputable def semanticCoordinateNormalizer
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (builder :
      SDBuild
        (n := n) H)
    (lowerWeight : ℕ) :
    TSNormalc
      (n := n) (lowerWeight := lowerWeight) H :=
  TSNormalc.recInsertionStep
    H
      (builder.insertionDerivationSchedule
        |>.recursiveCoordinateInsertion
        |>.recSemanticInsertion)
      lowerWeight

end SDBuild

/--
A universal signed-polynomial semantic collection builder constructs product
recollection polynomials.
-/
theorem universal_derivation_builder
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (builder :
      SDBuild
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  insertion_derivation_schedule
    H e builder.insertionDerivationSchedule

/--
A universal signed-polynomial semantic collection builder constructs inverse
recollection polynomials.
-/
theorem collected_derivation_builder
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (builder :
      SDBuild
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  recursive_insertion_derivation
    H e builder.insertionDerivationSchedule

end TCTex
end Towers

/-!
# Splitting active-layer product and inverse polynomial routing

Resolving one active-weight signed-polynomial insertion has two independent
parts:

* update the normalized block in the active Hall-weight stratum; and
* move the inserted factor left across the old strictly higher tail, leaving a
  residual source supported in the next stratum.

This file proves that these witnesses compose to an active-layer resolution.
It also packages a finite normalized-rewrite certificate for the higher-tail
route and derives the complete filtration-recursive Claim 8 adapter.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
The same-stratum part of an active insertion: absorb one active-weight factor
into the normalized active coordinate block.
-/
structure TruncatedSemanticResolution
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (coordinates : CHRecipe H ι)
    (factor : SPFactor H ι) where
  activeCoordinates :
    CHRecipe H ι
  active_terms_below :
    activeCoordinates.NTBelow lowerWeight
  list_eval_active :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e
          ((activeCoordinates.weightFactors lowerWeight).map
            SPFactor.ofMonomial) =
        SPFactor.listEval (n := n) e
          ((coordinates.weightFactors lowerWeight).map
              SPFactor.ofMonomial ++ [factor])

/--
The higher-tail part of an active insertion: move the inserted active factor
left across the old higher tail and retain only a next-stratum residual source.
-/
structure SemanticHigherResolution
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (coordinates : CHRecipe H ι)
    (factor : SPFactor H ι) where
  higherSource :
    List (SPFactor H ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_least_succ :
    SPFactor.WordWeightLeast (lowerWeight + 1)
      higherSource
  factor_append_source :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e
          ([factor] ++ higherSource) =
        SPFactor.listEval (n := n) e
          (coordinates.polynomialTailFactors (n := n) lowerWeight ++ [factor])

namespace SAResolu

/--
An active block update and a higher-tail route compose to the active-layer
resolution required by canonical tail splicing.
-/
def activeHigherTail
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CHRecipe H ι}
    {factor : SPFactor H ι}
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (block :
      TruncatedSemanticResolution
        (n := n) (lowerWeight := lowerWeight) H ι coordinates factor)
    (tail :
      SemanticHigherResolution
        (n := n) (lowerWeight := lowerWeight) H ι coordinates factor) :
    SAResolu
      (n := n) (lowerWeight := lowerWeight) H ι coordinates factor where
  activeCoordinates := block.activeCoordinates
  active_terms_below :=
    block.active_terms_below
  higherSource := tail.higherSource
  higher_source_truncated := tail.higher_source_truncated
  higher_least_succ :=
    tail.higher_least_succ
  active_append_source := by
    have hlowerWeightPos : 1 ≤ lowerWeight := by
      have hfactorPos := factor.word_weight_pos
      omega
    have hlowerWeightCutoff : lowerWeight ≤ n - 1 := by
      omega
    intro e
    calc
      SPFactor.listEval (n := n) e
            ((block.activeCoordinates.weightFactors lowerWeight).map
                SPFactor.ofMonomial ++
              tail.higherSource) =
          SPFactor.listEval e
              ((block.activeCoordinates.weightFactors lowerWeight).map
                SPFactor.ofMonomial) *
            SPFactor.listEval e tail.higherSource := by
              rw [SPFactor.listEval_append]
      _ =
          SPFactor.listEval e
              ((coordinates.weightFactors lowerWeight).map
                  SPFactor.ofMonomial ++ [factor]) *
            SPFactor.listEval e tail.higherSource := by
              rw [block.list_eval_active e]
      _ =
          SPFactor.listEval e
              ((coordinates.weightFactors lowerWeight).map
                SPFactor.ofMonomial) *
            SPFactor.listEval e
              ([factor] ++ tail.higherSource) := by
              simp [SPFactor.listEval_append, mul_assoc]
      _ =
          SPFactor.listEval e
              ((coordinates.weightFactors lowerWeight).map
                SPFactor.ofMonomial) *
            SPFactor.listEval e
              (coordinates.polynomialTailFactors (n := n) lowerWeight ++
                [factor]) := by
              rw [tail.factor_append_source e]
      _ =
          SPFactor.listEval e
            ((coordinates.weightFactors lowerWeight).map
                SPFactor.ofMonomial ++
              coordinates.polynomialTailFactors (n := n) lowerWeight ++
                [factor]) := by
              simp [SPFactor.listEval_append]
      _ =
          SPFactor.listEval e
            (coordinates.polynomialFactors (n := n) ++ [factor]) := by
              rw [coordinates.poly_no_below
                hcoordinates hlowerWeightPos hlowerWeightCutoff]

end SAResolu

/--
A finite normalized-rewrite certificate for routing one active factor across
the old higher tail.
-/
structure HTRoute
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (coordinates : CHRecipe H ι)
    (factor : SPFactor H ι) where
  higherSource :
    List (SPFactor H ι)
  higher_least_succ :
    SPFactor.WordWeightLeast (lowerWeight + 1)
      higherSource
  rewrites :
    SSRw
      (n := n) (lowerWeight := lowerWeight)
        (coordinates.polynomialTailFactors (n := n) lowerWeight ++ [factor])
        ([factor] ++ higherSource)

namespace HTRoute

/-- A finite higher-tail route supplies its semantic routing resolution. -/
def higherTailResolution
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CHRecipe H ι}
    {factor : SPFactor H ι}
    (route :
      HTRoute
        (n := n) (lowerWeight := lowerWeight) H ι coordinates factor)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    SemanticHigherResolution
      (n := n) (lowerWeight := lowerWeight) H ι coordinates factor where
  higherSource := route.higherSource
  higher_source_truncated := by
    have hlowerWeightCutoff : lowerWeight ≤ n - 1 := by
      omega
    have houtput :
        SPFactor.IsTruncated n
          ([factor] ++ route.higherSource) :=
      route.rewrites.isTruncated (by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact coordinates.truncated_tail_factors
            hlowerWeightCutoff x hx
        · rcases List.mem_singleton.mp hx with rfl
          exact hfactorTruncated)
    intro x hx
    exact houtput x (List.mem_append_right _ hx)
  higher_least_succ :=
    route.higher_least_succ
  factor_append_source := fun e =>
    route.rewrites.listEval_eq e

/-- If the old higher tail is empty, its route emits no residuals. -/
def tail_factors_nil
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (coordinates : CHRecipe H ι)
    (factor : SPFactor H ι)
    (htail :
      coordinates.polynomialTailFactors (n := n) lowerWeight = []) :
    HTRoute
      (n := n) (lowerWeight := lowerWeight) H ι coordinates factor where
  higherSource := []
  higher_least_succ := by
    intro x hx
    simp at hx
  rewrites := by
    simpa [htail] using
      (Relation.ReflTransGen.refl :
        SSRw
          (n := n) (lowerWeight := lowerWeight) [factor] [factor])

end HTRoute

/-- A supply of same-stratum active-block updates. -/
structure SemanticResolutionFactory
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  resolve :
    ∀ {ι : Type}
      (lowerWeight : ℕ)
      (coordinates : CHRecipe H ι)
      (factor : SPFactor H ι),
      coordinates.NTBelow lowerWeight →
      factor.word.weight HEAddres.weight = lowerWeight →
      factor.word.weight HEAddres.weight < n →
        TruncatedSemanticResolution
          (n := n) (lowerWeight := lowerWeight) H ι coordinates factor

/--
A recursive finite-rewrite schedule for routing an active factor across the old
strictly higher endpoint tail.
-/
structure RSHigher
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  route :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      TSNormalc
          (n := n) (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CHRecipe H ι)
          (factor : SPFactor H ι),
          coordinates.NTBelow lowerWeight →
          factor.word.weight HEAddres.weight = lowerWeight →
          factor.word.weight HEAddres.weight < n →
            HTRoute
              (n := n) (lowerWeight := lowerWeight) H ι coordinates factor

namespace RSHigher

open SAResolu

/--
Same-stratum active-block updates and higher-tail routes supply the residual
active insertion branch.
-/
def insertionBranch
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (schedule :
      RSHigher
        (n := n) H)
    (blockFactory :
      SemanticResolutionFactory
        (n := n) H) :
    SemanticInsertionBranch
      (n := n) H where
  insert lowerWeight normalizer coordinates factor hcoordinates hfactorWeight
      hfactorTruncated :=
    (activeHigherTail hcoordinates hfactorWeight hfactorTruncated
      (blockFactory.resolve lowerWeight coordinates factor hcoordinates
        hfactorWeight hfactorTruncated)
      ((schedule.route lowerWeight normalizer coordinates factor hcoordinates
        hfactorWeight hfactorTruncated).higherTailResolution
          hfactorWeight hfactorTruncated)).exists_insertion normalizer
            hfactorWeight hfactorTruncated

/--
Same-stratum active-block updates and higher-tail routes supply the complete
filtration-recursive semantic insertion step.
-/
def recSemanticInsertion
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (schedule :
      RSHigher
        (n := n) H)
    (blockFactory :
      SemanticResolutionFactory
        (n := n) H) :
    TRInsert
      (n := n) H :=
  TRInsert.insertion_branch
    (schedule.insertionBranch blockFactory)

end RSHigher

/--
Same-stratum active-block updates and higher-tail routes construct product
recollection polynomials.
-/
theorem active_higher_tail
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (schedule :
      RSHigher
        (n := n) H)
    (blockFactory :
      SemanticResolutionFactory
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  collected_insertion_step
    H e (schedule.recSemanticInsertion blockFactory)

/--
Same-stratum active-block updates and higher-tail routes construct inverse
recollection polynomials.
-/
theorem collected_higher_tail
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (schedule :
      RSHigher
        (n := n) H)
    (blockFactory :
      SemanticResolutionFactory
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  semantic_insertion_step
    H e (schedule.recSemanticInsertion blockFactory)

end TCTex
end Towers

/-!
# Residual routing inside an active product and inverse polynomial layer

Absorbing one active-weight signed-polynomial factor into a normalized
coordinate block may itself emit strictly higher corrections.  Thus the honest
active-layer split has two residual sources:

* an active-block residual produced while normalizing the current stratum; and
* a higher-tail residual produced while moving the inserted factor left across
  the old tail.

Both residuals start in the next support stratum.  Their concatenation can be
delegated to the next-stratum normalizer and spliced above the updated active
block.  This file proves that composition and packages finite normalized
rewrite certificates for the active-block part.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
Normalize one active-weight signed-polynomial factor against the current
coordinate block, retaining a strictly higher residual source.
-/
structure TSResolu
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (coordinates : CHRecipe H ι)
    (factor : SPFactor H ι) where
  activeCoordinates :
    CHRecipe H ι
  active_terms_below :
    activeCoordinates.NTBelow lowerWeight
  higherSource :
    List (SPFactor H ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_least_succ :
    SPFactor.WordWeightLeast (lowerWeight + 1)
      higherSource
  active_append_source :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e
          ((activeCoordinates.weightFactors lowerWeight).map
              SPFactor.ofMonomial ++
            higherSource) =
        SPFactor.listEval (n := n) e
          ((coordinates.weightFactors lowerWeight).map
              SPFactor.ofMonomial ++ [factor])

namespace TSResolu

/-- A pure active-block update is the special case with no higher residual. -/
def activeResolution
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CHRecipe H ι}
    {factor : SPFactor H ι}
    (block :
      TruncatedSemanticResolution
        (n := n) (lowerWeight := lowerWeight) H ι coordinates factor) :
    TSResolu
      (n := n) (lowerWeight := lowerWeight) H ι coordinates factor where
  activeCoordinates := block.activeCoordinates
  active_terms_below :=
    block.active_terms_below
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_least_succ := by
    intro x hx
    simp at hx
  active_append_source := by
    intro e
    simpa using block.list_eval_active e

end TSResolu

namespace SAResolu

/--
An active-block residual and a higher-tail residual compose to the complete
active-layer resolution consumed by canonical tail splicing.
-/
def active_block_tail
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CHRecipe H ι}
    {factor : SPFactor H ι}
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (block :
      TSResolu
        (n := n) (lowerWeight := lowerWeight) H ι coordinates factor)
    (tail :
      SemanticHigherResolution
        (n := n) (lowerWeight := lowerWeight) H ι coordinates factor) :
    SAResolu
      (n := n) (lowerWeight := lowerWeight) H ι coordinates factor where
  activeCoordinates := block.activeCoordinates
  active_terms_below :=
    block.active_terms_below
  higherSource := block.higherSource ++ tail.higherSource
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact block.higher_source_truncated x hx
    · exact tail.higher_source_truncated x hx
  higher_least_succ := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact block.higher_least_succ x hx
    · exact tail.higher_least_succ x hx
  active_append_source := by
    have hlowerWeightPos : 1 ≤ lowerWeight := by
      have hfactorPos := factor.word_weight_pos
      omega
    have hlowerWeightCutoff : lowerWeight ≤ n - 1 := by
      omega
    intro e
    calc
      SPFactor.listEval (n := n) e
            ((block.activeCoordinates.weightFactors lowerWeight).map
                SPFactor.ofMonomial ++
              (block.higherSource ++ tail.higherSource)) =
          SPFactor.listEval e
              ((block.activeCoordinates.weightFactors lowerWeight).map
                  SPFactor.ofMonomial ++
                block.higherSource) *
            SPFactor.listEval e tail.higherSource := by
              simp [SPFactor.listEval_append, mul_assoc]
      _ =
          SPFactor.listEval e
              ((coordinates.weightFactors lowerWeight).map
                  SPFactor.ofMonomial ++ [factor]) *
            SPFactor.listEval e tail.higherSource := by
              rw [block.active_append_source e]
      _ =
          SPFactor.listEval e
              ((coordinates.weightFactors lowerWeight).map
                SPFactor.ofMonomial) *
            SPFactor.listEval e
              ([factor] ++ tail.higherSource) := by
              simp [SPFactor.listEval_append, mul_assoc]
      _ =
          SPFactor.listEval e
              ((coordinates.weightFactors lowerWeight).map
                SPFactor.ofMonomial) *
            SPFactor.listEval e
              (coordinates.polynomialTailFactors (n := n) lowerWeight ++
                [factor]) := by
              rw [tail.factor_append_source e]
      _ =
          SPFactor.listEval e
            ((coordinates.weightFactors lowerWeight).map
                SPFactor.ofMonomial ++
              coordinates.polynomialTailFactors (n := n) lowerWeight ++
                [factor]) := by
              simp [SPFactor.listEval_append]
      _ =
          SPFactor.listEval e
            (coordinates.polynomialFactors (n := n) ++ [factor]) := by
              rw [coordinates.poly_no_below
                hcoordinates hlowerWeightPos hlowerWeightCutoff]

end SAResolu

/--
A finite normalized-rewrite certificate for normalizing one active-weight
factor against the current coordinate block.
-/
structure TARoute
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (coordinates : CHRecipe H ι)
    (factor : SPFactor H ι) where
  activeCoordinates :
    CHRecipe H ι
  active_terms_below :
    activeCoordinates.NTBelow lowerWeight
  higherSource :
    List (SPFactor H ι)
  higher_least_succ :
    SPFactor.WordWeightLeast (lowerWeight + 1)
      higherSource
  rewrites :
    SSRw
      (n := n) (lowerWeight := lowerWeight)
        ((coordinates.weightFactors lowerWeight).map
            SPFactor.ofMonomial ++ [factor])
        ((activeCoordinates.weightFactors lowerWeight).map
            SPFactor.ofMonomial ++ higherSource)

namespace TARoute

/-- An active-block rewrite route supplies its semantic residual resolution. -/
def activeBlockResolution
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CHRecipe H ι}
    {factor : SPFactor H ι}
    (route :
      TARoute
        (n := n) (lowerWeight := lowerWeight) H ι coordinates factor)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TSResolu
      (n := n) (lowerWeight := lowerWeight) H ι coordinates factor where
  activeCoordinates := route.activeCoordinates
  active_terms_below :=
    route.active_terms_below
  higherSource := route.higherSource
  higher_source_truncated := by
    have hblock :
        SPFactor.IsTruncated n
          ((coordinates.weightFactors lowerWeight).map
            SPFactor.ofMonomial) := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
      change y.word.weight HEAddres.weight < n
      rw [coordinates.word_weight_factors hy]
      omega
    have houtput :
        SPFactor.IsTruncated n
          ((route.activeCoordinates.weightFactors lowerWeight).map
              SPFactor.ofMonomial ++
            route.higherSource) :=
      route.rewrites.isTruncated (by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hblock x hx
        · rcases List.mem_singleton.mp hx with rfl
          exact hfactorTruncated)
    intro x hx
    exact houtput x (List.mem_append_right _ hx)
  higher_least_succ :=
    route.higher_least_succ
  active_append_source := fun e =>
    route.rewrites.listEval_eq e

end TARoute

/--
A recursive finite-rewrite schedule for normalizing one active factor against
the current coordinate block.
-/
structure RSSched
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  route :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      TSNormalc
          (n := n) (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CHRecipe H ι)
          (factor : SPFactor H ι),
          coordinates.NTBelow lowerWeight →
          factor.word.weight HEAddres.weight = lowerWeight →
          factor.word.weight HEAddres.weight < n →
            TARoute
              (n := n) (lowerWeight := lowerWeight) H ι coordinates factor

namespace RSSched

open SAResolu

/--
Active-block residual routes and higher-tail routes supply the residual active
insertion branch.
-/
def insertionBranch
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (blockSchedule :
      RSSched
        (n := n) H)
    (tailSchedule :
      RSHigher
        (n := n) H) :
    SemanticInsertionBranch
      (n := n) H where
  insert lowerWeight normalizer coordinates factor hcoordinates hfactorWeight
      hfactorTruncated := by
    let blockRoute :=
      blockSchedule.route lowerWeight normalizer coordinates factor
        hcoordinates hfactorWeight hfactorTruncated
    let tailRoute :=
      tailSchedule.route lowerWeight normalizer coordinates factor
        hcoordinates hfactorWeight hfactorTruncated
    exact
      (active_block_tail hcoordinates hfactorWeight
        hfactorTruncated
          (blockRoute.activeBlockResolution hfactorWeight
            hfactorTruncated)
          (tailRoute.higherTailResolution hfactorWeight
            hfactorTruncated)).exists_insertion normalizer hfactorWeight
              hfactorTruncated

/--
Active-block residual routes and higher-tail routes supply the complete
filtration-recursive semantic insertion step.
-/
def recSemanticInsertion
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (blockSchedule :
      RSSched
        (n := n) H)
    (tailSchedule :
      RSHigher
        (n := n) H) :
    TRInsert
      (n := n) H :=
  TRInsert.insertion_branch
    (blockSchedule.insertionBranch tailSchedule)

end RSSched

/--
The two residual route schedules construct product recollection polynomials.
-/
theorem residual_route_schedules
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (blockSchedule :
      RSSched
        (n := n) H)
    (tailSchedule :
      RSHigher
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  collected_insertion_step
    H e (blockSchedule.recSemanticInsertion tailSchedule)

/--
The two residual route schedules construct inverse recollection polynomials.
-/
theorem collected_active_schedules
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (blockSchedule :
      RSSched
        (n := n) H)
    (tailSchedule :
      RSHigher
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  semantic_insertion_step
    H e (blockSchedule.recSemanticInsertion tailSchedule)

end TCTex
end Towers

-- Merged from PolynomialSignedUniversalCorrectionFactories.lean

/-!
# Universal higher-word factories for signed polynomial corrections

The nonterminal signed collector needs a physically truncated correction
packet for every supported adjacent pair.  The mathematically natural input is
slightly more general: a finite ordered higher-word expansion whose evaluation
is the required commutator correction before semantically trivial factors are
erased.

This file packages that all-integral expansion interface and compiles it to the
cutoff-specific packet factory consumed by signed semantic routing.  It
isolates the remaining interpolation theorem without mixing it with cutoff
bookkeeping.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

/--
A finite signed-polynomial expansion of one adjacent commutator correction.
The expansion may still contain factors reaching the quotient cutoff.
-/
structure SCExp
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (B A : SPFactor H ι) where
  factors :
    List (SPFactor H ι)
  listEval_eq :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e factors =
        ⁅B.eval (n := n) e, A.eval (n := n) e⁆
  word_weight_left :
    ∀ x ∈ factors,
      B.word.weight HEAddres.weight <
        x.word.weight HEAddres.weight
  word_weight_right :
    ∀ x ∈ factors,
      A.word.weight HEAddres.weight <
        x.word.weight HEAddres.weight

namespace SCExp

/--
Erase semantically trivial factors from a finite all-integral expansion.  The
result is the exact cutoff-specific correction packet used by collection.
-/
def truncate
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    (expansion : SCExp (n := n) B A) :
    TSPkt n B A where
  factors := SPFactor.truncate n expansion.factors
  listEval_eq e := by
    rw [SPFactor.listEval_truncate]
    exact expansion.listEval_eq e
  word_weight_left x hx :=
    expansion.word_weight_left x (List.mem_filter.mp hx).1
  word_weight_right x hx :=
    expansion.word_weight_right x (List.mem_filter.mp hx).1
  word_weight_cutoff x hx :=
    SPFactor.word_weight_truncate hx

end SCExp

/--
Universal all-integral correction expansions for pairs supported in one
ordinary Hall-weight stratum.
-/
structure SSFtrya
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (lowerWeight : ℕ) where
  expansion :
    ∀ {ι : Type}
      (B A : SPFactor H ι),
      lowerWeight ≤ B.word.weight HEAddres.weight →
      lowerWeight ≤ A.word.weight HEAddres.weight →
        SCExp (n := n) B A

namespace SSFtrya

/--
Truncate every universal expansion to obtain the packet supply expected by
one-stratum signed semantic collection.
-/
def correctionPacketFactory
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      SSFtrya
        (n := n) H lowerWeight) :
    TSFtry
      (n := n) H lowerWeight where
  packet B A hB hA :=
    (factory.expansion B A hB hA).truncate

end SSFtrya

end TCTex
end Towers

-- Merged from PolynomialFormula.lean

/-!
# Constant-one obstruction for signed Hall polynomial formulas

Every admissible weighted Hall-binomial monomial contains at least one
positive-index generalized binomial coefficient.  Consequently, every signed
formula vanishes when all source Hall exponents vanish.  In particular, the
polynomial factor language has no analogue of the powered collector's
constant-one `wordUnit` factor.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace WHMono

/-- Every admissible weighted Hall-binomial monomial vanishes at zero input. -/
@[simp]
lemma eval_zeroInput
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (monomial : WHMono H ι targetWeight) :
    monomial.eval (fun _ : ι => (0 : HEFam H)) = 0 := by
  rw [WHMono.eval]
  apply Finset.prod_eq_zero (Finset.mem_univ ⟨0, monomial.length_pos⟩)
  exact Ring.choose_zero_pos ℤ (monomial.binomialIndex_pos _)

end WHMono

namespace WBTerm

/-- Every signed recipe term vanishes at zero input. -/
@[simp]
lemma eval_zeroInput
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (term : WBTerm H ι targetWeight) :
    term.eval (fun _ : ι => (0 : HEFam H)) = 0 := by
  simp [eval]

end WBTerm

namespace WBForm

/-- Every finite signed Hall polynomial formula vanishes at zero input. -/
@[simp]
lemma eval_zeroInput
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (formula : WBForm H ι targetWeight) :
    formula.eval (fun _ : ι => (0 : HEFam H)) = 0 := by
  simp [eval]

/-- No weighted signed Hall polynomial formula is the constant function one. -/
lemma not_forall_one
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (formula : WBForm H ι targetWeight) :
    ¬ ∀ e : ι → HEFam H, formula.eval e = 1 := by
  intro hconstant
  simpa using hconstant (fun _ : ι => (0 : HEFam H))

end WBForm

namespace SPFactor

/--
No signed Hall polynomial factor has coefficient identically one.  This is the
precise obstruction to copying the powered collector's `wordUnit` bridge.
-/
lemma not_forall_coefficient
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι) :
    ¬ ∀ e : ι → HEFam H, factor.coefficient.eval e = 1 :=
  factor.coefficient.not_forall_one

end SPFactor

end TCTex
end Towers

/-!
# Substituting signed formulas into Hall-Petresco block recipes

Complete Hall-Petresco block recipes are naturally expressed in terms of
generalized binomial coefficients of their two parent exponents.  At a
nonterminal signed collection step those parent exponents are no longer raw
input coordinates: they are finite weighted Hall-binomial formulas.

This file isolates the one arithmetic input needed to cross that boundary and
proves all remaining substitution bookkeeping.  A positive-choose normalizer
turns `choose (formula.eval e) k` back into a finite weighted formula whenever
`0 < k`.  Degree-zero blocks are erased exactly as in the raw specialization.
The resulting generic binder substitutes arbitrary signed polynomial factors
into complete block recipes, proves the expected evaluation and strict weight
bounds, and compiles any universal all-integral Hall-Petresco packet into the
word-expansion interface consumed by the recursive collector.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u v

open scoped commutatorElement
open HACoeff

namespace WBForm

/--
Arithmetic normalization of positive generalized binomial coefficients of
signed formulas.  The target weight scales by the binomial index.
-/
structure RCNormal
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  ringChoose :
    ∀ {targetWeight : ℕ},
      WBForm H ι targetWeight →
        ∀ k : ℕ,
          0 < k →
            WBForm H ι (k * targetWeight)
  eval_ringChoose :
    ∀ {targetWeight : ℕ}
      (formula : WBForm H ι targetWeight)
      (k : ℕ)
      (hk : 0 < k)
      (e : ι → HEFam H),
        (ringChoose formula k hk).eval e =
          Ring.choose (formula.eval e) k

/--
A positive-choose normalizer available uniformly for every source-label type.
-/
structure PositiveChooseNormalizer
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  normalizer :
    ∀ ι : Type, RCNormal H ι

namespace RCNormal

/--
Normalize the product of the positive generalized binomial coefficients
listed by one nonempty block history.
-/
def ringChooseProduct
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : RCNormal H ι)
    (formula : WBForm H ι targetWeight) :
    ∀ (degrees : List ℕ),
      degrees ≠ [] →
        (∀ degree ∈ degrees, 0 < degree) →
          WBForm H ι (degrees.sum * targetWeight)
  | [], hdegrees, _ => False.elim (hdegrees rfl)
  | [degree], _, hpositive => by
      simpa using
        normalizer.ringChoose formula degree
          (hpositive degree (by simp))
  | degree :: nextDegree :: degrees, _, hpositive =>
      (normalizer.ringChoose formula degree
        (hpositive degree (by simp))).mul
          (normalizer.ringChooseProduct formula (nextDegree :: degrees)
            (by simp)
            (fun next hnext => hpositive next (by simp [hnext])))
          (by simp [Nat.add_mul])

@[simp]
lemma ring_choose_product
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : RCNormal H ι)
    (formula : WBForm H ι targetWeight) :
    ∀ (degrees : List ℕ)
      (hdegrees : degrees ≠ [])
      (hpositive : ∀ degree ∈ degrees, 0 < degree)
      (e : ι → HEFam H),
        (normalizer.ringChooseProduct formula degrees hdegrees hpositive).eval e =
          (degrees.map fun degree => Ring.choose (formula.eval e) degree).prod
  | [], hdegrees, _, _ => False.elim (hdegrees rfl)
  | [degree], _, hpositive, e => by
      simp only [ringChooseProduct]
      simpa using
        normalizer.eval_ringChoose formula degree
          (hpositive degree (by simp)) e
  | degree :: nextDegree :: degrees, _, hpositive, e => by
      simp only [ringChooseProduct, WBForm.eval_mul,
        List.map_cons, List.prod_cons]
      rw [normalizer.eval_ringChoose formula degree
        (hpositive degree (by simp)) e]
      rw [normalizer.ring_choose_product formula
        (nextDegree :: degrees) (by simp)
        (fun next hnext => hpositive next (by simp [hnext])) e]
      rfl

end RCNormal
end WBForm

namespace PFSubsti

/--
Substitute arbitrary signed Hall words for the two abstract Hall-pair atoms of
one complete block recipe.
-/
def boundWord
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : BRecipe)
    (B A : SPFactor H ι) :
    CWord (HEAddres H) :=
  CWord.hallPairBind B.word A.word R.erasedShape

@[simp]
lemma weight_boundWord
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : BRecipe)
    (B A : SPFactor H ι) :
    (boundWord R B A).weight HEAddres.weight =
      R.leftDegree * B.word.weight HEAddres.weight +
        R.rightDegree * A.word.weight HEAddres.weight := by
  rw [boundWord, CWord.weight_pair_bind,
    CWord.pair_atom_degree,
    R.erased_left_degree, R.erased_shape_degree]

/--
The signed coefficient obtained by substituting two arbitrary parent formulas
into one complete block recipe.
-/
def coefficientFormula
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B A : SPFactor H ι) :
    WBForm H ι
      (R.leftDegree * B.word.weight HEAddres.weight +
        R.rightDegree * A.word.weight HEAddres.weight) :=
  let left :=
    normalizer.ringChooseProduct B.coefficient
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
    normalizer.ringChooseProduct A.coefficient
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
  left.mul right (by
    simp only [      BRSpec.sum_positiveDegrees]
    rfl)

@[simp]
lemma eval_coefficientFormula
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (R : BRecipe)
    (B A : SPFactor H ι) :
    (coefficientFormula normalizer R B A).eval e =
      BRSpec.coefficientValue R
        (B.coefficient.eval e) (A.coefficient.eval e) := by
  simp only [coefficientFormula, WBForm.eval_mul,
    WBForm.RCNormal.ring_choose_product,
    BRSpec.coefficientValue,
    BRSpec.choose_positive_degrees]

/--
Attach one complete Hall-Petresco block history to arbitrary signed parent
factors.
-/
def symbolicFactor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B A : SPFactor H ι) :
    SPFactor H ι where
  word := boundWord R B A
  coefficient :=
    (coefficientFormula normalizer R B A).weaken (by
      rw [weight_boundWord])

@[simp]
lemma word_symbolicFactor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B A : SPFactor H ι) :
    (symbolicFactor normalizer R B A).word = boundWord R B A :=
  rfl

@[simp]
lemma word_symbolic_factor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B A : SPFactor H ι) :
    (symbolicFactor normalizer R B A).word.weight HEAddres.weight =
      R.leftDegree * B.word.weight HEAddres.weight +
        R.rightDegree * A.word.weight HEAddres.weight :=
  weight_boundWord R B A

@[simp]
lemma coefficient_symbolic_factor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (R : BRecipe)
    (B A : SPFactor H ι) :
    (symbolicFactor normalizer R B A).coefficient.eval e =
      BRSpec.coefficientValue R
        (B.coefficient.eval e) (A.coefficient.eval e) := by
  simp [symbolicFactor]

@[simp]
lemma value_symbolic_factor
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B A : SPFactor H ι) :
    (symbolicFactor normalizer R B A).wordValue (n := n) =
      R.erasedShape.eval
        (HPAtom.eval (B.wordValue (n := n)) (A.wordValue (n := n))) := by
  simp [symbolicFactor, SPFactor.wordValue, boundWord,
    CWord.eval_pair_bind]

@[simp]
lemma eval_symbolicFactor
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (R : BRecipe)
    (B A : SPFactor H ι) :
    (symbolicFactor normalizer R B A).eval (n := n) e =
      R.erasedShape.eval
          (HPAtom.eval (B.wordValue (n := n)) (A.wordValue (n := n))) ^
        BRSpec.coefficientValue R
          (B.coefficient.eval e) (A.coefficient.eval e) := by
  rw [SPFactor.eval, value_symbolic_factor,
    coefficient_symbolic_factor]

/-- Generic substituted recipe factors are strictly above their left parent. -/
lemma left_symbolic_factor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B A : SPFactor H ι) :
    B.word.weight HEAddres.weight <
      (symbolicFactor normalizer R B A).word.weight HEAddres.weight := by
  rw [word_symbolic_factor]
  refine lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _
      (BRSpec.leftDegree_pos R)) ?_
  exact Nat.lt_add_of_pos_right
    (Nat.mul_pos
      (BRSpec.rightDegree_pos R)
      A.word_weight_pos)

/-- Generic substituted recipe factors are strictly above their right parent. -/
lemma right_symbolic_factor
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (R : BRecipe)
    (B A : SPFactor H ι) :
    A.word.weight HEAddres.weight <
      (symbolicFactor normalizer R B A).word.weight HEAddres.weight := by
  rw [word_symbolic_factor]
  refine lt_of_le_of_lt
    (Nat.le_mul_of_pos_left _
      (BRSpec.rightDegree_pos R)) ?_
  rw [Nat.add_comm]
  exact Nat.lt_add_of_pos_right
    (Nat.mul_pos
      (BRSpec.leftDegree_pos R)
      B.word_weight_pos)

/-- Attach a finite ordered endpoint recipe list to arbitrary signed parents. -/
def symbolicFactors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (recipes : List BRecipe)
    (B A : SPFactor H ι) :
    List (SPFactor H ι) :=
  recipes.map fun R => symbolicFactor normalizer R B A

lemma listSymbolicFactors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : WBForm.RCNormal H ι)
    (e : ι → HEFam H)
    (recipes : List BRecipe)
    (B A : SPFactor H ι) :
    SPFactor.listEval (n := n) e
        (symbolicFactors normalizer recipes B A) =
      (recipes.map fun R =>
        R.erasedShape.eval
            (HPAtom.eval (B.wordValue (n := n)) (A.wordValue (n := n))) ^
          BRSpec.coefficientValue R
            (B.coefficient.eval e) (A.coefficient.eval e)).prod := by
  induction recipes with
  | nil =>
      rfl
  | cons R recipes ih =>
      change
        (symbolicFactor normalizer R B A).eval e *
            SPFactor.listEval e
              (symbolicFactors normalizer recipes B A) =
          _ * _
      rw [eval_symbolicFactor, ih]
      rfl

lemma recipe_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {normalizer : WBForm.RCNormal H ι}
    {recipes : List BRecipe}
    {B A x : SPFactor H ι}
    (hx : x ∈ symbolicFactors normalizer recipes B A) :
    ∃ R ∈ recipes, x = symbolicFactor normalizer R B A := by
  rcases List.mem_map.mp hx with ⟨R, hR, rfl⟩
  exact ⟨R, hR, rfl⟩

/--
A multiplicity-independent Hall-Petresco recipe packet valid in every group
and for arbitrary integral parent exponents.
-/
structure UAInt where
  recipes :
    List BRecipe
  listEval_eq :
    ∀ {G : Type v} [Group G]
      (left right : G)
      (leftExponent rightExponent : ℤ),
        (recipes.map fun R =>
          R.erasedShape.eval (HPAtom.eval left right) ^
            BRSpec.coefficientValue R
              leftExponent rightExponent).prod =
          ⁅left ^ leftExponent, right ^ rightExponent⁆

/--
A finite all-integral Hall-Petresco packet in one free lower-central
truncation.  Unlike `UAInt`, this is the cutoff-specific
object needed by the nilpotent collector: omitted sufficiently deep words are
already trivial in the quotient.
-/
structure TAPkt
    (d n : ℕ) where
  recipes :
    List BRecipe
  listEval_eq :
    ∀ (left right :
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightExponent : ℤ),
        (recipes.map fun R =>
          R.erasedShape.eval (HPAtom.eval left right) ^
            BRSpec.coefficientValue R
              leftExponent rightExponent).prod =
          ⁅left ^ leftExponent, right ^ rightExponent⁆

namespace TAPkt

/--
Formula normalization compiles a cutoff-specific all-integral Hall-Petresco
packet into one arbitrary-parent signed correction expansion.
-/
def toCorrectionExpansion
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet : TAPkt d n)
    (normalizer : WBForm.RCNormal H ι)
    (B A : SPFactor H ι) :
    SCExp (n := n) B A where
  factors := symbolicFactors normalizer packet.recipes B A
  listEval_eq e := by
    rw [listSymbolicFactors]
    simpa [SPFactor.eval] using
      packet.listEval_eq (B.wordValue (n := n)) (A.wordValue (n := n))
        (B.coefficient.eval e) (A.coefficient.eval e)
  word_weight_left := by
    intro x hx
    rcases recipe_factors hx with ⟨R, _hR, rfl⟩
    exact left_symbolic_factor normalizer R B A
  word_weight_right := by
    intro x hx
    rcases recipe_factors hx with ⟨R, _hR, rfl⟩
    exact right_symbolic_factor normalizer R B A

/--
A cutoff packet and uniform formula arithmetic supply the correction factory
needed in every signed support stratum.
-/
def supportedWordFactory
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet : TAPkt d n)
    (normalizers :
      WBForm.PositiveChooseNormalizer H)
    (lowerWeight : ℕ) :
    SSFtrya
      (n := n) H lowerWeight where
  expansion B A _hB _hA :=
    packet.toCorrectionExpansion (normalizers.normalizer _) B A

end TAPkt

namespace UAInt

/-- Every genuinely universal packet specializes to any lower-central cutoff. -/
def truncatedAll
    {d n : ℕ}
    (packet : UAInt.{u}) :
    TAPkt d n where
  recipes := packet.recipes
  listEval_eq left right leftExponent rightExponent :=
    packet.listEval_eq left right leftExponent rightExponent

/--
Substitution normalization compiles a universal all-integral Hall-Petresco
packet into the all-integral word expansion expected by signed collection.
-/
def toCorrectionExpansion
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (packet : UAInt)
    (normalizer : WBForm.RCNormal H ι)
    (B A : SPFactor H ι) :
    SCExp (n := n) B A :=
  (packet.truncatedAll (d := d) (n := n))
    |>.toCorrectionExpansion normalizer B A

end UAInt
end PFSubsti

end TCTex
end Towers

/-!
# Additive normalization of generalized binomial formulas

The remaining positive-choose arithmetic can be reduced before tackling the
hard multiplicative case.  By Chu-Vandermonde, normalizing
`choose (left + right) k` is a finite sum of products
`choose left i * choose right j` over `i + j = k`.

This file makes that reduction constructive for weighted Hall-binomial
formulas.  It proves that a normalizer for one signed recipe term extends to a
normalizer for an arbitrary finite signed formula.  The only hard arithmetic
left after this file is positive-choose normalization of one integer-scaled
product of raw generalized binomial coefficients.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace WBForm

/-- Sum a finite list of formulas sharing one target weight. -/
def listSum
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type} :
    List (WBForm H ι targetWeight) →
      WBForm H ι targetWeight
  | [] => zero H ι targetWeight
  | formula :: formulas => formula.append (listSum formulas)

@[simp]
lemma eval_listSum
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (formulas : List (WBForm H ι targetWeight))
    (e : ι → HEFam H) :
    (listSum formulas).eval e =
      (formulas.map fun formula => formula.eval e).sum := by
  induction formulas with
  | nil =>
      simp [listSum]
  | cons formula formulas ih =>
      simp [listSum, ih]

/--
Positive generalized-binomial normalization for one signed recipe term.
-/
structure PRNormal
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  ringChoose :
    ∀ {targetWeight : ℕ},
      WBTerm H ι targetWeight →
        ∀ k : ℕ,
          0 < k →
            WBForm H ι (k * targetWeight)
  eval_ringChoose :
    ∀ {targetWeight : ℕ}
      (term : WBTerm H ι targetWeight)
      (k : ℕ)
      (hk : 0 < k)
      (e : ι → HEFam H),
        (ringChoose term k hk).eval e =
          Ring.choose (term.eval e) k

namespace PRNormal

/--
One Chu-Vandermonde summand.  Since the outer index is positive, at least one
of the two antidiagonal indices is positive; the zero-index branch is erased
rather than represented as a constant-one formula.
-/
def addChooseSummand
    {d targetWeight k : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : PRNormal H ι)
    (recurse :
      ∀ j : ℕ,
        0 < j →
          WBForm H ι (j * targetWeight))
    (term : WBTerm H ι targetWeight)
    (ij : ℕ × ℕ)
    (hij : ij ∈ Finset.antidiagonal k)
    (hk : 0 < k) :
    WBForm H ι (k * targetWeight) := by
  have hsum : ij.1 + ij.2 = k := Finset.mem_antidiagonal.mp hij
  by_cases hleft : ij.1 = 0
  · have hright : ij.2 = k := by omega
    have hrightPos : 0 < ij.2 := by omega
    exact (recurse ij.2 hrightPos).weaken (by rw [hright])
  · by_cases hright : ij.2 = 0
    · have hleftEq : ij.1 = k := by omega
      exact
        (normalizer.ringChoose term ij.1 (Nat.pos_of_ne_zero hleft)).weaken
          (by rw [hleftEq])
    · exact
        (normalizer.ringChoose term ij.1 (Nat.pos_of_ne_zero hleft)).mul
          (recurse ij.2 (Nat.pos_of_ne_zero hright))
          (by rw [← Nat.add_mul, hsum])

@[simp]
lemma add_choose_summand
    {d targetWeight k : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : PRNormal H ι)
    (recurse :
      ∀ j : ℕ,
        0 < j →
          WBForm H ι (j * targetWeight))
    (term : WBTerm H ι targetWeight)
    (ij : ℕ × ℕ)
    (hij : ij ∈ Finset.antidiagonal k)
    (hk : 0 < k)
    (tail : WBForm H ι targetWeight)
    (e : ι → HEFam H)
    (hrecurse :
      ∀ (j : ℕ) (hj : 0 < j),
        (recurse j hj).eval e =
          Ring.choose (tail.eval e) j) :
    (normalizer.addChooseSummand recurse term ij hij hk).eval e =
      Ring.choose (term.eval e) ij.1 *
        Ring.choose (tail.eval e) ij.2 := by
  have hsum : ij.1 + ij.2 = k := Finset.mem_antidiagonal.mp hij
  rw [addChooseSummand]
  split
  next hleft =>
    have hright : ij.2 = k := by omega
    simp [hleft, hrecurse]
  next hleft =>
    split
    next hright =>
      simp [hright, normalizer.eval_ringChoose]
    next hright =>
      simp [WBForm.eval_mul,
        normalizer.eval_ringChoose, hrecurse]

/--
Sum all Chu-Vandermonde summands for one head term and an already-normalized
tail formula.
-/
noncomputable def addChoose
    {d targetWeight k : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : PRNormal H ι)
    (recurse :
      ∀ j : ℕ,
        0 < j →
          WBForm H ι (j * targetWeight))
    (term : WBTerm H ι targetWeight)
    (hk : 0 < k) :
    WBForm H ι (k * targetWeight) :=
  WBForm.listSum
    ((Finset.antidiagonal k).attach.toList.map fun ij =>
      normalizer.addChooseSummand recurse term ij.1 ij.2 hk)

@[simp]
lemma eval_addChoose
    {d targetWeight k : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : PRNormal H ι)
    (recurse :
      ∀ j : ℕ,
        0 < j →
          WBForm H ι (j * targetWeight))
    (term : WBTerm H ι targetWeight)
    (hk : 0 < k)
    (tail : WBForm H ι targetWeight)
    (e : ι → HEFam H)
    (hrecurse :
      ∀ (j : ℕ) (hj : 0 < j),
        (recurse j hj).eval e =
          Ring.choose (tail.eval e) j) :
    (normalizer.addChoose (k := k) recurse term hk).eval e =
      Ring.choose (term.eval e + tail.eval e) k := by
  rw [addChoose, WBForm.eval_listSum]
  simp only [List.map_map]
  rw [← List.sum_toFinset _ (Finset.nodup_toList _)]
  rw [show
      (Finset.antidiagonal k).attach.toList.toFinset =
        (Finset.antidiagonal k).attach by
      ext ij
      simp]
  rw [Ring.add_choose_eq k (Commute.all _ _)]
  conv_rhs => rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro ij hij
  exact normalizer.add_choose_summand recurse term ij ij.2 hk tail e hrecurse

/--
Recursively normalize positive generalized binomial coefficients of a finite
list of signed recipe terms.
-/
noncomputable def ringChooseTerms
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : PRNormal H ι) :
    (terms : List (WBTerm H ι targetWeight)) →
      ∀ k : ℕ,
        0 < k →
          WBForm H ι (k * targetWeight)
  | [], k, _hk => WBForm.zero H ι (k * targetWeight)
  | term :: terms, k, hk =>
      normalizer.addChoose
        (fun j hj => normalizer.ringChooseTerms terms j hj)
        term hk
termination_by terms => terms.length

@[simp]
lemma ring_choose_terms
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : PRNormal H ι)
    (terms : List (WBTerm H ι targetWeight))
    (k : ℕ)
    (hk : 0 < k)
    (e : ι → HEFam H) :
    (normalizer.ringChooseTerms terms k hk).eval e =
      Ring.choose
        (({ terms := terms } :
          WBForm H ι targetWeight).eval e)
        k := by
  induction terms generalizing k with
  | nil =>
      simp [ringChooseTerms, WBForm.eval,
        WBForm.zero, Ring.choose_zero_pos ℤ hk]
  | cons term terms ih =>
      simpa [ringChooseTerms, WBForm.eval] using
        normalizer.eval_addChoose
          (fun j hj => normalizer.ringChooseTerms terms j hj)
          term hk
          ({ terms := terms } :
            WBForm H ι targetWeight)
          e
          (fun j hj => ih j hj)

/--
Chu-Vandermonde lifts positive-choose normalization from one signed recipe
term to every finite signed formula.
-/
noncomputable def ringChooseNormalizer
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : PRNormal H ι) :
    RCNormal H ι where
  ringChoose formula k hk :=
    normalizer.ringChooseTerms formula.terms k hk
  eval_ringChoose formula k hk e :=
    normalizer.ring_choose_terms formula.terms k hk e

end PRNormal
end WBForm

end TCTex
end Towers

/-!
# Class-two all-integral Hall-Petresco packets

In a lower-central truncation with cutoff at most three, every triple
commutator vanishes.  The powered commutator of two arbitrary elements is
therefore represented by the singleton basic Hall-Petresco recipe, for
arbitrary integral source exponents.

This is the terminal constructor for the cutoff-specific all-integral packet
required by signed product and inverse collection.  The file is intentionally
not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace PFSubsti
namespace TAPkt

universe u

open scoped commutatorElement
open BRSpec

/--
At cutoff at most three, arbitrary elements commute with their leading
commutator in the defining lower-central truncation quotient.
-/
lemma commute_n_three
    {d n : ℕ}
    (hn : n ≤ 3)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) :
    Commute left ⁅left, right⁆ ∧
      Commute right ⁅left, right⁆ := by
  have hleft :
      left ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hright :
      right ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hbracket :
      ⁅left, right⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
    simpa using
      element_lower_series hleft hright
  have hleftNested :
      ⁅left, ⁅left, right⁆⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
    simpa using
      element_lower_series hleft hbracket
  have hrightNested :
      ⁅right, ⁅left, right⁆⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
    simpa using
      element_lower_series hright hbracket
  have hleftNestedOne : ⁅left, ⁅left, right⁆⁆ = 1 := by
    apply eq_bot_iff.mp
      SCFactor.trunc_last_bot
    exact Subgroup.lowerCentralSeries_antitone (by omega) hleftNested
  have hrightNestedOne : ⁅right, ⁅left, right⁆⁆ = 1 := by
    apply eq_bot_iff.mp
      SCFactor.trunc_last_bot
    exact Subgroup.lowerCentralSeries_antitone (by omega) hrightNested
  constructor
  · rw [← commutatorElement_eq_one_iff_commute]
    exact hleftNestedOne
  · rw [← commutatorElement_eq_one_iff_commute]
    exact hrightNestedOne

/--
At cutoff at most three, the singleton basic recipe is the complete
all-integral Hall-Petresco packet.
-/
def n_three
    {d n : ℕ}
    (hn : n ≤ 3) :
    TAPkt.{u} d n where
  recipes := [hallPair]
  listEval_eq left right leftExponent rightExponent := by
    have hcommutes :=
      commute_n_three hn left right
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, erased_shape_pair, coefficient_value_pair,
      CWord.eval_pair_base]
    have hpullLeft :
        ⁅left ^ leftExponent, right⁆ =
          ⁅left, right⁆ ^ leftExponent :=
      commutator_zpow_commute
        hcommutes.1 leftExponent
    have hcommuteRight :
        Commute right ⁅left ^ leftExponent, right⁆ := by
      rw [hpullLeft]
      exact hcommutes.2.zpow_right leftExponent
    rw [zpow_commute_collection
      hcommuteRight, hpullLeft, zpow_mul]

end TAPkt
end PFSubsti
end TCTex
end Towers

/-!
# Scalar normalization of generalized-binomial formulas

After additive Chu-Vandermonde normalization, one positive generalized
binomial coefficient still has the form `choose (c * monomial) k`, where `c`
is a fixed signed integer and `monomial` is a product of raw generalized
binomial coefficients.  Newton interpolation removes that fixed scalar:

`choose (c * z) k = sum_j a(c,k,j) * choose z j`.

This file proves the identity for every signed integer `z`, then packages it
as a compiler from raw-monomial choose normalization to signed-term choose
normalization.  It is intentionally not imported by the existing collection
proof.
-/

namespace Towers
namespace TCTex

universe u

/-- The natural-input function used to interpolate `z ↦ choose (c * z) k`. -/
def chooseScaleFunction
    (coefficient : ℤ)
    (k : ℕ) :
    ℕ → ℤ :=
  fun q => Ring.choose (coefficient * (q : ℤ)) k

/-- The Newton coefficient of `z ↦ choose (c * z) k`. -/
def chooseScaleCoefficient
    (coefficient : ℤ)
    (k j : ℕ) :
    ℤ :=
  natBinomialCoefficient (chooseScaleFunction coefficient k) j

/-- The rational polynomial `z ↦ choose (c * z) k`. -/
noncomputable def chooseScalePolynomial
    (coefficient : ℤ)
    (k : ℕ) :
    Polynomial ℚ :=
  (natChoosePolynomial k).comp
    (Polynomial.C (coefficient : ℚ) * Polynomial.X)

lemma choose_scale_polynomial
    (coefficient : ℤ)
    (k : ℕ) :
    (chooseScalePolynomial coefficient k).natDegree ≤ k := by
  have hlinear :
      (Polynomial.C (coefficient : ℚ) * Polynomial.X).natDegree ≤ 1 := by
    calc
      (Polynomial.C (coefficient : ℚ) * Polynomial.X).natDegree ≤
          (Polynomial.C (coefficient : ℚ)).natDegree +
            Polynomial.X.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 0 + 1 := by
        gcongr <;> simp
      _ = 1 := by simp
  exact Polynomial.natDegree_comp_le.trans
    (by
      calc
        (natChoosePolynomial k).natDegree *
              (Polynomial.C (coefficient : ℚ) * Polynomial.X).natDegree ≤
            k * 1 :=
          Nat.mul_le_mul (degree_choose_polynomial k) hlinear
        _ = k := by simp)

@[simp]
lemma ring_scale_int
    (coefficient z : ℤ)
    (k : ℕ) :
    (chooseScalePolynomial coefficient k).eval (z : ℚ) =
      ((Ring.choose (coefficient * z) k : ℤ) : ℚ) := by
  rw [chooseScalePolynomial, Polynomial.eval_comp]
  simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Int.cast_mul] using nat_choose_int (coefficient * z) k

lemma scale_function_most
    (coefficient : ℤ)
    (k : ℕ) :
    IVMost
      (chooseScaleFunction coefficient k) k := by
  refine ⟨chooseScalePolynomial coefficient k,
    choose_scale_polynomial coefficient k, ?_⟩
  intro q
  simpa [chooseScaleFunction] using
    ring_scale_int coefficient (q : ℤ) k

lemma binomial_expansion_int
    (f : ℕ → ℤ)
    (m : ℕ)
    (z : ℤ) :
    (natBinomialExpansion f m).eval (z : ℚ) =
      ((∑ j ∈ Finset.range (m + 1),
        natBinomialCoefficient f j * Ring.choose z j : ℤ) : ℚ) := by
  rw [natBinomialExpansion, Polynomial.eval_finsetSum]
  simp_rw [Polynomial.eval_C_mul, nat_choose_int]
  norm_cast

/--
Newton interpolation for a fixed signed scalar, valid on every signed integer
input rather than only on natural inputs.
-/
lemma ring_choose_mul
    (coefficient z : ℤ)
    (k : ℕ) :
    Ring.choose (coefficient * z) k =
      ∑ j ∈ Finset.range (k + 1),
        chooseScaleCoefficient coefficient k j * Ring.choose z j := by
  have hpolynomial :
      chooseScalePolynomial coefficient k =
        natBinomialExpansion
          (chooseScaleFunction coefficient k) k := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.infinite_of_injective_forall_mem
      (Nat.cast_injective :
        Function.Injective (fun q : ℕ => (q : ℚ)))
    intro q
    calc
      (chooseScalePolynomial coefficient k).eval (q : ℚ) =
          ((Ring.choose (coefficient * (q : ℤ)) k : ℤ) : ℚ) := by
            simpa using
              ring_scale_int coefficient (q : ℤ) k
      _ =
          (natBinomialExpansion
            (chooseScaleFunction coefficient k) k).eval (q : ℚ) := by
            rw [binomial_expansion_polynomial]
            norm_cast
            exact
              (scale_function_most
                coefficient k).nat_binomial_basisexpansion q
  have heval :=
    congrArg
      (fun P : Polynomial ℚ => P.eval (z : ℚ))
      hpolynomial
  change
    (chooseScalePolynomial coefficient k).eval (z : ℚ) =
      (natBinomialExpansion
        (chooseScaleFunction coefficient k) k).eval (z : ℚ) at heval
  rw [ring_scale_int,
    binomial_expansion_int] at heval
  exact_mod_cast heval

@[simp]
lemma choose_scale_coefficient
    (coefficient : ℤ)
    (k : ℕ)
    (hk : 0 < k) :
    chooseScaleCoefficient coefficient k 0 = 0 := by
  simp [chooseScaleCoefficient, natBinomialCoefficient,
    chooseScaleFunction, Ring.choose_zero_pos ℤ hk]

namespace WBTerm

/-- Scale one signed term without changing its raw monomial. -/
def scaleForChoose
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (coefficient : ℤ)
    (term : WBTerm H ι targetWeight) :
    WBTerm H ι targetWeight :=
  (coefficient * term.1, term.2)

@[simp]
lemma eval_scale_choose
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (coefficient : ℤ)
    (term : WBTerm H ι targetWeight)
    (e : ι → HEFam H) :
    (term.scaleForChoose coefficient).eval e =
      coefficient * term.eval e := by
  simp [scaleForChoose, eval]
  ring

end WBTerm

namespace WBForm

/-- Scale every signed coefficient in one formula. -/
def scaleForChoose
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (coefficient : ℤ)
    (formula : WBForm H ι targetWeight) :
    WBForm H ι targetWeight where
  terms := formula.terms.map fun term => term.scaleForChoose coefficient

@[simp]
lemma eval_scale_choose
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (coefficient : ℤ)
    (formula : WBForm H ι targetWeight)
    (e : ι → HEFam H) :
    (formula.scaleForChoose coefficient).eval e =
      coefficient * formula.eval e := by
  cases formula with
  | mk terms =>
      induction terms with
      | nil =>
          simp [scaleForChoose, eval]
      | cons head tail ih =>
          change
            (head.scaleForChoose coefficient).eval e +
                (scaleForChoose coefficient
                  ({ terms := tail } :
                    WBForm H ι targetWeight)).eval e =
              coefficient *
                (head.eval e +
                  ({ terms := tail } :
                    WBForm H ι targetWeight).eval e)
          rw [WBTerm.eval_scale_choose, ih, mul_add]

/--
Positive generalized-binomial normalization for one raw Hall-binomial
monomial.  This is the remaining multiplicative arithmetic interface.
-/
structure PMNormal
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  ringChoose :
    ∀ {targetWeight : ℕ},
      WHMono H ι targetWeight →
        ∀ k : ℕ,
          0 < k →
            WBForm H ι (k * targetWeight)
  eval_ringChoose :
    ∀ {targetWeight : ℕ}
      (monomial : WHMono H ι targetWeight)
      (k : ℕ)
      (hk : 0 < k)
      (e : ι → HEFam H),
        (ringChoose monomial k hk).eval e =
          Ring.choose (monomial.eval e) k

namespace PMNormal

/--
Normalize `choose (c * monomial) k` by Newton expansion in `choose monomial j`.
The constant Newton summand vanishes because `k` is positive.
-/
noncomputable def ringChooseTerm
    {d targetWeight k : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : PMNormal H ι)
    (term : WBTerm H ι targetWeight)
    (_hk : 0 < k) :
    WBForm H ι (k * targetWeight) :=
  WBForm.listSum
    (List.ofFn fun j : Fin k =>
      ((normalizer.ringChoose term.2 (j + 1) (by omega)).weaken
          (Nat.mul_le_mul_right targetWeight (by omega))).scaleForChoose
        (chooseScaleCoefficient term.1 k (j + 1)))

@[simp]
lemma ring_choose_term
    {d targetWeight k : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : PMNormal H ι)
    (term : WBTerm H ι targetWeight)
    (hk : 0 < k)
    (e : ι → HEFam H) :
    (normalizer.ringChooseTerm term hk).eval e =
      Ring.choose (term.eval e) k := by
  rw [ringChooseTerm, WBForm.eval_listSum]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply,
    WBForm.eval_scale_choose,
    WBForm.eval_weaken,
    normalizer.eval_ringChoose]
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ =>
      chooseScaleCoefficient term.1 k (j + 1) *
        Ring.choose (term.2.eval e) (j + 1))]
  change
    (∑ j ∈ Finset.range k,
      chooseScaleCoefficient term.1 k (j + 1) *
        Ring.choose (term.2.eval e) (j + 1)) =
      Ring.choose (term.1 * term.2.eval e) k
  rw [ring_choose_mul]
  rw [Finset.sum_range_succ']
  simp [choose_scale_coefficient term.1 k hk]

/--
Scalar Newton expansion lifts raw-monomial normalization to normalization of
one signed recipe term.
-/
noncomputable def positiveRingNormalizer
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer : PMNormal H ι) :
    PRNormal H ι where
  ringChoose term _k hk :=
    normalizer.ringChooseTerm term hk
  eval_ringChoose term _k hk e :=
    normalizer.ring_choose_term term hk e

end PMNormal

/-- Uniform raw-monomial choose normalization over every input type. -/
structure CMNormal
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  normalizer :
    ∀ ι : Type, PMNormal H ι

namespace CMNormal

/--
Scalar Newton expansion followed by Chu-Vandermonde supplies the uniform
formula normalizer used by Hall-Petresco packet substitution.
-/
noncomputable def positiveChooseNormalizer
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (normalizers : CMNormal H) :
    PositiveChooseNormalizer H where
  normalizer ι :=
    (normalizers.normalizer ι).positiveRingNormalizer
      |>.ringChooseNormalizer

end CMNormal
end WBForm

end TCTex
end Towers

/-!
# Class-three all-integral Hall-Petresco packets

In a lower-central truncation with cutoff at most four, quadruple
commutators vanish.  The powered commutator of two arbitrary elements is
therefore represented by the basic bracket and its two triple-commutator
corrections.  This file proves the signed commutator formulas directly and
packages the resulting three-term cutoff packet.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

open scoped commutatorElement

namespace HCThree

universe u

/-- Pascal's identity for the degree-two generalized binomial coefficient. -/
lemma ring_choose_add
    (z : ℤ) :
    Ring.choose (z + 1) 2 = z + Ring.choose z 2 := by
  simpa only [Ring.choose_one_right] using
    (Ring.choose_succ_succ z 1)

/--
Signed class-three collection for an integral power in the left commutator
input.  The hypotheses state exactly that the first triple correction
commutes with the two lower-weight factors.
-/
lemma commutator_element_zpow
    {G : Type*} [Group G]
    (x y : G)
    (hXD : Commute x ⁅x, ⁅x, y⁆⁆)
    (hCD : Commute ⁅x, y⁆ ⁅x, ⁅x, y⁆⁆) :
    ∀ z : ℤ,
      ⁅x ^ z, y⁆ =
        ⁅x, ⁅x, y⁆⁆ ^ Ring.choose z 2 *
          ⁅x, y⁆ ^ z := by
  let C : G := ⁅x, y⁆
  let D : G := ⁅x, ⁅x, y⁆⁆
  have hCD' : Commute C D := by
    simpa [C, D] using hCD
  have hXD' : Commute x D := by
    simpa [D] using hXD
  have hconj :
      ∀ z : ℤ, x ^ z * C * (x ^ z)⁻¹ = D ^ z * C := by
    intro z
    calc
      x ^ z * C * (x ^ z)⁻¹ =
          ⁅x ^ z, C⁆ * C := by
            simp only [commutatorElement_def]
            group
      _ = D ^ z * C := by
            rw [commutator_zpow_commute hXD' z]
  have hstep :
      ∀ z : ℤ, ⁅x ^ (z + 1), y⁆ = D ^ z * C * ⁅x ^ z, y⁆ := by
    intro z
    rw [zpow_add_one, element_mul_left, hconj]
  intro z
  induction z using Int.induction_on with
  | zero =>
      simp 
  | succ z ih =>
      change ⁅x ^ ((z : ℤ) + 1), y⁆ =
        D ^ Ring.choose ((z : ℤ) + 1) 2 * C ^ ((z : ℤ) + 1)
      change ⁅x ^ (z : ℤ), y⁆ =
        D ^ Ring.choose (z : ℤ) 2 * C ^ (z : ℤ) at ih
      rw [hstep, ih, ring_choose_add, zpow_add, zpow_add]
      simp only [zpow_one]
      calc
        D ^ (z : ℤ) * C *
              (D ^ Ring.choose (z : ℤ) 2 * C ^ (z : ℤ)) =
            D ^ (z : ℤ) *
              (C * D ^ Ring.choose (z : ℤ) 2) * C ^ (z : ℤ) := by
                group
        _ =
            D ^ (z : ℤ) *
              (D ^ Ring.choose (z : ℤ) 2 * C) * C ^ (z : ℤ) := by
                rw [(hCD'.zpow_right (Ring.choose (z : ℤ) 2)).eq]
        _ = D ^ (z : ℤ) * D ^ Ring.choose (z : ℤ) 2 *
              (C ^ (z : ℤ) * C) := by
                group
  | pred z ih =>
      let w : ℤ := -(z : ℤ) - 1
      have hw : w + 1 = -(z : ℤ) := by
        simp [w]
      change ⁅x ^ w, y⁆ = D ^ Ring.choose w 2 * C ^ w
      calc
        ⁅x ^ w, y⁆ =
            (D ^ w * C)⁻¹ * ⁅x ^ (w + 1), y⁆ := by
              rw [hstep]
              group
        _ =
            (D ^ w * C)⁻¹ *
              (D ^ Ring.choose (w + 1) 2 * C ^ (w + 1)) := by
              rw [hw, ih]
        _ =
            D ^ (-w) * C⁻¹ *
              (D ^ Ring.choose (w + 1) 2 * C ^ (w + 1)) := by
              rw [mul_inv_rev, ← zpow_neg]
              rw [(hCD'.inv_left.zpow_right (-w)).eq]
        _ =
            D ^ (-w) * D ^ Ring.choose (w + 1) 2 *
              (C⁻¹ * C ^ (w + 1)) := by
              calc
                D ^ (-w) * C⁻¹ *
                      (D ^ Ring.choose (w + 1) 2 * C ^ (w + 1)) =
                    D ^ (-w) *
                      (C⁻¹ * D ^ Ring.choose (w + 1) 2) *
                        C ^ (w + 1) := by group
                _ =
                    D ^ (-w) *
                      (D ^ Ring.choose (w + 1) 2 * C⁻¹) *
                        C ^ (w + 1) := by
                          rw [(hCD'.inv_left.zpow_right
                            (Ring.choose (w + 1) 2)).eq]
                _ = _ := by group
        _ =
            D ^ (-w + Ring.choose (w + 1) 2) *
              C ^ (-1 + (w + 1)) := by
              rw [← zpow_neg_one, ← zpow_add, ← zpow_add]
        _ = D ^ Ring.choose w 2 * C ^ w := by
              have hD :
                  -w + Ring.choose (w + 1) 2 =
                    Ring.choose w 2 := by
                rw [ring_choose_add]
                ring
              have hC : -1 + (w + 1) = w := by
                ring
              rw [hD, hC]

/--
Signed class-three collection for an integral power in the right commutator
input.
-/
lemma element_zpow_nested
    {G : Type*} [Group G]
    (x y : G)
    (hYD : Commute y ⁅y, ⁅x, y⁆⁆)
    (hCD : Commute ⁅x, y⁆ ⁅y, ⁅x, y⁆⁆) :
    ∀ z : ℤ,
      ⁅x, y ^ z⁆ =
        ⁅x, y⁆ ^ z *
          ⁅y, ⁅x, y⁆⁆ ^ Ring.choose z 2 := by
  let C : G := ⁅x, y⁆
  let D : G := ⁅y, ⁅x, y⁆⁆
  have hCD' : Commute C D := by
    simpa [C, D] using hCD
  have hYD' : Commute y D := by
    simpa [D] using hYD
  have hconj :
      ∀ z : ℤ, y ^ z * C * (y ^ z)⁻¹ = D ^ z * C := by
    intro z
    calc
      y ^ z * C * (y ^ z)⁻¹ =
          ⁅y ^ z, C⁆ * C := by
            simp only [commutatorElement_def]
            group
      _ = D ^ z * C := by
            rw [commutator_zpow_commute hYD' z]
  have hstep :
      ∀ z : ℤ, ⁅x, y ^ (z + 1)⁆ = ⁅x, y ^ z⁆ * (D ^ z * C) := by
    intro z
    rw [zpow_add_one, element_mul_right]
    calc
      ⁅x, y ^ z⁆ * y ^ z * ⁅x, y⁆ * (y ^ z)⁻¹ =
          ⁅x, y ^ z⁆ * (y ^ z * C * (y ^ z)⁻¹) := by
            simp only [C, mul_assoc]
      _ = ⁅x, y ^ z⁆ * (D ^ z * C) := by
            rw [hconj]
  intro z
  induction z using Int.induction_on with
  | zero =>
      simp 
  | succ z ih =>
      change ⁅x, y ^ ((z : ℤ) + 1)⁆ =
        C ^ ((z : ℤ) + 1) * D ^ Ring.choose ((z : ℤ) + 1) 2
      change ⁅x, y ^ (z : ℤ)⁆ =
        C ^ (z : ℤ) * D ^ Ring.choose (z : ℤ) 2 at ih
      rw [hstep, ih, ring_choose_add, zpow_add, zpow_add]
      simp only [zpow_one]
      calc
        C ^ (z : ℤ) * D ^ Ring.choose (z : ℤ) 2 *
              (D ^ (z : ℤ) * C) =
            C ^ (z : ℤ) *
              (D ^ (Ring.choose (z : ℤ) 2 + (z : ℤ)) * C) := by
                rw [zpow_add]
                group
        _ =
            C ^ (z : ℤ) *
              (C * D ^ (Ring.choose (z : ℤ) 2 + (z : ℤ))) := by
                rw [← (hCD'.zpow_right
                  (Ring.choose (z : ℤ) 2 + (z : ℤ))).eq]
        _ = C ^ (z : ℤ) * C *
              (D ^ (z : ℤ) * D ^ Ring.choose (z : ℤ) 2) := by
                rw [add_comm (Ring.choose (z : ℤ) 2) (z : ℤ), zpow_add]
                group
  | pred z ih =>
      let w : ℤ := -(z : ℤ) - 1
      have hw : w + 1 = -(z : ℤ) := by
        simp [w]
      change ⁅x, y ^ w⁆ = C ^ w * D ^ Ring.choose w 2
      calc
        ⁅x, y ^ w⁆ =
            ⁅x, y ^ (w + 1)⁆ * (D ^ w * C)⁻¹ := by
              rw [hstep]
              group
        _ =
            (C ^ (w + 1) * D ^ Ring.choose (w + 1) 2) *
              (D ^ w * C)⁻¹ := by
              rw [hw, ih]
        _ =
            (C ^ (w + 1) * D ^ Ring.choose (w + 1) 2) *
              (C⁻¹ * D ^ (-w)) := by
              rw [mul_inv_rev, ← zpow_neg]
        _ =
            C ^ (w + 1) * C⁻¹ *
              (D ^ Ring.choose (w + 1) 2 * D ^ (-w)) := by
              calc
                C ^ (w + 1) * D ^ Ring.choose (w + 1) 2 *
                      (C⁻¹ * D ^ (-w)) =
                    C ^ (w + 1) *
                      (D ^ Ring.choose (w + 1) 2 * C⁻¹) *
                        D ^ (-w) := by group
                _ =
                    C ^ (w + 1) *
                      (C⁻¹ * D ^ Ring.choose (w + 1) 2) *
                        D ^ (-w) := by
                          rw [← (hCD'.inv_left.zpow_right
                            (Ring.choose (w + 1) 2)).eq]
                _ = _ := by group
        _ =
            C ^ (w + 1 + -1) *
              D ^ (Ring.choose (w + 1) 2 + -w) := by
              rw [← zpow_neg_one, ← zpow_add, ← zpow_add]
        _ = C ^ w * D ^ Ring.choose w 2 := by
              have hC : w + 1 + -1 = w := by
                ring
              have hD :
                  Ring.choose (w + 1) 2 + -w =
                    Ring.choose w 2 := by
                rw [ring_choose_add]
                ring
              rw [hC, hD]

/--
Every element of the third one-based lower-central layer is central in a
free lower-central truncation with cutoff at most four.
-/
lemma commute_series_four
    {d n : ℕ}
    (hn : n ≤ 4)
    (x :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    {z :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n}
    (hz :
      z ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 2) :
    Commute x z := by
  have hx :
      x ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hcommutator :
      ⁅x, z⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 3 := by
    simpa using
      element_lower_series hx hz
  rw [← commutatorElement_eq_one_iff_commute]
  apply eq_bot_iff.mp
    SCFactor.trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (by omega) hcommutator

/--
Complete signed class-three Hall-Petresco formula in a free lower-central
truncation with cutoff at most four.
-/
lemma element_zpow_class
    {d n : ℕ}
    (hn : n ≤ 4)
    (left right :
      LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ) :
    ⁅left ^ leftExponent, right ^ rightExponent⁆ =
      ⁅left, ⁅left, right⁆⁆ ^
          (Ring.choose leftExponent 2 * rightExponent) *
        ⁅left, right⁆ ^ (leftExponent * rightExponent) *
          ⁅right, ⁅left, right⁆⁆ ^
            (leftExponent * Ring.choose rightExponent 2) := by
  let C := ⁅left, right⁆
  let D := ⁅left, ⁅left, right⁆⁆
  let E := ⁅right, ⁅left, right⁆⁆
  have hleft :
      left ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hright :
      right ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hC :
      C ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
    simpa [C] using
      element_lower_series hleft hright
  have hD :
      D ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
    simpa [D] using
      element_lower_series hleft hC
  have hE :
      E ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
    simpa [E] using
      element_lower_series hright hC
  have hcentralD :
      ∀ x :
          LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
        Commute x D :=
    fun x => commute_series_four hn x hD
  have hcentralE :
      ∀ x :
          LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n,
        Commute x E :=
    fun x => commute_series_four hn x hE
  have hleftExpansion :
      ⁅left ^ leftExponent, right⁆ =
        D ^ Ring.choose leftExponent 2 * C ^ leftExponent := by
    simpa [C, D] using
      commutator_element_zpow
        left right (hcentralD left) (hcentralD C) leftExponent
  have hleftPower :
      left ^ leftExponent ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 0 := by
    simp
  have hpoweredC :
      ⁅left ^ leftExponent, right⁆ ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 1 := by
    simpa using
      element_lower_series hleftPower hright
  have hpoweredE :
      ⁅right, ⁅left ^ leftExponent, right⁆⁆ ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) 2 := by
    simpa using
      element_lower_series hright hpoweredC
  have hrightPoweredE :
      Commute right ⁅right, ⁅left ^ leftExponent, right⁆⁆ :=
    commute_series_four
      hn right hpoweredE
  have hpoweredCPoweredE :
      Commute ⁅left ^ leftExponent, right⁆
        ⁅right, ⁅left ^ leftExponent, right⁆⁆ :=
    commute_series_four
      hn ⁅left ^ leftExponent, right⁆ hpoweredE
  have hrightExpansion :
      ⁅left ^ leftExponent, right ^ rightExponent⁆ =
        ⁅left ^ leftExponent, right⁆ ^ rightExponent *
          ⁅right, ⁅left ^ leftExponent, right⁆⁆ ^
            Ring.choose rightExponent 2 := by
    exact
      element_zpow_nested
        (left ^ leftExponent) right
        hrightPoweredE hpoweredCPoweredE
        rightExponent
  have hscaledE :
      ⁅right, ⁅left ^ leftExponent, right⁆⁆ =
        E ^ leftExponent := by
    rw [hleftExpansion, element_mul_right]
    rw [commutatorElement_eq_one_iff_commute.mpr
      ((hcentralD right).zpow_right (Ring.choose leftExponent 2))]
    rw [one_mul]
    rw [zpow_commute_collection
      (hcentralE C)]
    change
      D ^ Ring.choose leftExponent 2 * E ^ leftExponent *
          (D ^ Ring.choose leftExponent 2)⁻¹ =
        E ^ leftExponent
    rw [((hcentralE D).zpow_zpow
      (Ring.choose leftExponent 2) leftExponent).eq]
    group
  rw [hrightExpansion, hscaledE, hleftExpansion]
  rw [((hcentralD C).symm.zpow_zpow
    (Ring.choose leftExponent 2) leftExponent).mul_zpow]
  rw [zpow_mul, zpow_mul, zpow_mul]

end HCThree

open HACoeff

namespace BRSpec

/-- The first label in a singleton source block of degree two. -/
def singletonLabelZero :
    BlockLabel [2] :=
  ⟨0, ⟨0, by simp⟩⟩

/-- The second label in a singleton source block of degree two. -/
def singletonBlockLabel :
    BlockLabel [2] :=
  ⟨0, ⟨1, by simp⟩⟩

/-- The left triple correction `[x,[x,y]]`. -/
def leftTriple :
    BRecipe where
  leftBlocks := [2]
  rightBlocks := [1]
  word :=
    .commutator
      (.atom (.inl singletonLabelZero))
      (.commutator
        (.atom (.inl singletonBlockLabel))
        (.atom (.inr singletonOneLabel)))
  positive := by
    simp [collapseBlockRecipe, collapseRecipeLabel,
      CWord.PBPos]
  left_degree_eq := by
    simp [collapseBlockRecipe, collapseRecipeLabel]
  right_degree_eq := by
    simp [collapseBlockRecipe, collapseRecipeLabel]

/-- The right triple correction `[y,[x,y]]`. -/
def rightTriple :
    BRecipe where
  leftBlocks := [1]
  rightBlocks := [2]
  word :=
    .commutator
      (.atom (.inr singletonLabelZero))
      (.commutator
        (.atom (.inl singletonOneLabel))
        (.atom (.inr singletonBlockLabel)))
  positive := by
    simp [collapseBlockRecipe, collapseRecipeLabel,
      CWord.PBPos]
  left_degree_eq := by
    simp [collapseBlockRecipe, collapseRecipeLabel]
  right_degree_eq := by
    simp [collapseBlockRecipe, collapseRecipeLabel]

/-- Erasing the left triple recipe gives `[x,[x,y]]`. -/
@[simp]
lemma erased_left_triple :
    leftTriple.erasedShape =
      .commutator (.atom .left) CWord.hallPairBase := by
  rfl

/-- Erasing the right triple recipe gives `[y,[x,y]]`. -/
@[simp]
lemma erased_right_triple :
    rightTriple.erasedShape =
      .commutator (.atom .right) CWord.hallPairBase := by
  rfl

/-- The left triple recipe contributes `choose a 2 * b`. -/
@[simp]
lemma coefficient_left_triple
    (leftExponent rightExponent : ℤ) :
    coefficientValue leftTriple leftExponent rightExponent =
      Ring.choose leftExponent 2 * rightExponent := by
  simp [coefficientValue, leftTriple]

/-- The right triple recipe contributes `a * choose b 2`. -/
@[simp]
lemma coefficient_value_triple
    (leftExponent rightExponent : ℤ) :
    coefficientValue rightTriple leftExponent rightExponent =
      leftExponent * Ring.choose rightExponent 2 := by
  simp [coefficientValue, rightTriple]

/-- Evaluating the left triple recipe gives `[x,[x,y]]`. -/
@[simp]
lemma eval_erased_triple
    {G : Type*} [Group G]
    (left right : G) :
    leftTriple.erasedShape.eval (HPAtom.eval left right) =
      ⁅left, ⁅left, right⁆⁆ := by
  rfl

/-- Evaluating the right triple recipe gives `[y,[x,y]]`. -/
@[simp]
lemma erased_shape_triple
    {G : Type*} [Group G]
    (left right : G) :
    rightTriple.erasedShape.eval (HPAtom.eval left right) =
      ⁅right, ⁅left, right⁆⁆ := by
  rfl

end BRSpec

namespace PFSubsti
namespace TAPkt

open BRSpec

/--
At cutoff at most four, the basic bracket and its two triple corrections form
the complete all-integral Hall-Petresco packet.
-/
def n_four
    {d n : ℕ}
    (hn : n ≤ 4) :
    TAPkt.{u} d n where
  recipes := [leftTriple, hallPair, rightTriple]
  listEval_eq left right leftExponent rightExponent := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, eval_erased_triple, erased_shape_triple,
      coefficient_left_triple, coefficient_value_pair,
      coefficient_value_triple, erased_shape_pair,
      CWord.eval_pair_base]
    simpa only [mul_assoc] using
      (HCThree.element_zpow_class
        hn left right leftExponent rightExponent).symm

end TAPkt
end PFSubsti

end TCTex
end Towers

/-!
# Finite-grid reduction for generalized binomial formula normalization

The scalar Newton and additive Chu-Vandermonde layers reduce positive-choose
normalization of an arbitrary signed formula to normalization of one raw
finite product of generalized binomial coefficients in Hall coordinates.

This file removes the remaining inessential source-label bookkeeping.  It
isolates the arithmetic theorem on a canonical finite slot grid `Fin length`,
then proves that any such theorem relabels back to arbitrary source families
and supplies the full positive-choose normalizer consumed by Hall-Petresco
formula substitution.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace WBForm

/--
The canonical finite-grid arithmetic kernel.  Its inputs are exactly one
nonempty finite product of positive generalized binomial coefficients in
independent Hall-coordinate slots.
-/
structure PGNormal
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  ringChoose :
    ∀ {length targetWeight : ℕ}
      (_length_pos : 0 < length)
      (address : Fin length → HEAddres H)
      (binomialIndex : Fin length → ℕ)
      (_binomialIndex_pos : ∀ ν, 0 < binomialIndex ν)
      (_weightedWeight_le :
        ∑ ν, binomialIndex ν * (address ν).1 ≤ targetWeight)
      (k : ℕ),
        0 < k →
          WBForm H (Fin length) (k * targetWeight)
  eval_ringChoose :
    ∀ {length targetWeight : ℕ}
      (length_pos : 0 < length)
      (address : Fin length → HEAddres H)
      (binomialIndex : Fin length → ℕ)
      (binomialIndex_pos : ∀ ν, 0 < binomialIndex ν)
      (weightedWeight_le :
        ∑ ν, binomialIndex ν * (address ν).1 ≤ targetWeight)
      (k : ℕ)
      (hk : 0 < k)
      (e : Fin length → HEFam H),
        (ringChoose length_pos address binomialIndex binomialIndex_pos
            weightedWeight_le k hk).eval e =
          Ring.choose
            (∏ ν,
              Ring.choose
                (e ν (address ν).1 (address ν).2)
                (binomialIndex ν))
            k

namespace PGNormal

/--
Relabel a canonical finite-grid normalizer along the source slots of one raw
Hall-binomial monomial.
-/
def positiveMonomialNormalizer
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (normalizer : PGNormal H)
    (ι : Type) :
    PMNormal H ι where
  ringChoose monomial k hk :=
    (normalizer.ringChoose monomial.length_pos monomial.address
      monomial.binomialIndex monomial.binomialIndex_pos
      monomial.weightedWeight_le k hk).mapInput monomial.input
  eval_ringChoose monomial k hk e := by
    rw [WBForm.eval_mapInput]
    rw [normalizer.eval_ringChoose]
    rfl

/--
Relabel finite-grid arithmetic uniformly over every source-label type.
-/
def chooseMonomialNormalizer
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (normalizer : PGNormal H) :
    CMNormal H where
  normalizer ι :=
    normalizer.positiveMonomialNormalizer ι

/--
Finite-grid arithmetic, scalar Newton interpolation, and Chu-Vandermonde
together supply formula normalization uniformly for every source-label type.
-/
noncomputable def positiveChooseNormalizer
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (normalizer : PGNormal H) :
    PositiveChooseNormalizer H where
  normalizer :=
    normalizer.chooseMonomialNormalizer
      |>.positiveChooseNormalizer
      |>.normalizer

end PGNormal
end WBForm

end TCTex
end Towers

/-!
# Newton normalization of scalar interpolation coefficients

The scalar identity

`choose (c * z) k = sum_j a(c,k,j) * choose z j`

is useful recursively only after the coefficient `a(c,k,j)` is normalized as
a polynomial in `c`.  This file proves that each coefficient has degree at
most `k` and expands it in the signed Newton basis:

`a(c,k,j) = sum_h b(k,j,h) * choose c h`.

The resulting two-variable expansion is the arithmetic step needed to split a
raw Hall-binomial product into a head slot and a shorter tail product.  This
file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

/--
A rational polynomial of bounded degree whose values on every signed integer
are integral has the expected signed Newton-binomial expansion.
-/
lemma int_binomial_expansion
    (g : ℤ → ℤ)
    (P : Polynomial ℚ)
    (degreeBound : ℕ)
    (hdegree : P.natDegree ≤ degreeBound)
    (heval : ∀ z : ℤ, P.eval (z : ℚ) = (g z : ℚ))
    (z : ℤ) :
    g z =
      ∑ j ∈ Finset.range (degreeBound + 1),
        natBinomialCoefficient (fun q : ℕ => g q) j *
          Ring.choose z j := by
  let f : ℕ → ℤ := fun q => g q
  have hf : IVMost f degreeBound := by
    refine ⟨P, hdegree, ?_⟩
    intro q
    simpa [f] using heval (q : ℤ)
  have hpolynomial :
      P = natBinomialExpansion f degreeBound := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.infinite_of_injective_forall_mem
      (Nat.cast_injective :
        Function.Injective (fun q : ℕ => (q : ℚ)))
    intro q
    change
      P.eval (q : ℚ) =
        (natBinomialExpansion f degreeBound).eval (q : ℚ)
    conv_lhs =>
      rw [show (q : ℚ) = ((q : ℤ) : ℚ) by norm_cast, heval]
    rw [binomial_expansion_polynomial]
    norm_cast
    exact hf.nat_binomial_basisexpansion q
  have hsigned :=
    congrArg
      (fun Q : Polynomial ℚ => Q.eval (z : ℚ))
      hpolynomial
  change
    P.eval (z : ℚ) =
      (natBinomialExpansion f degreeBound).eval (z : ℚ) at hsigned
  rw [heval, binomial_expansion_int] at hsigned
  norm_cast at hsigned

/--
The polynomial in `coefficient` represented by the scalar Newton coefficient
`chooseScaleCoefficient coefficient k j`.
-/
noncomputable def ringChooseScale
    (k : ℕ) :
    ℕ → Polynomial ℚ
  | 0 => chooseScalePolynomial 0 k
  | j + 1 =>
      chooseScalePolynomial (j + 1 : ℕ) k -
        ∑ i : Fin (j + 1),
          Polynomial.C (Nat.choose (j + 1) i : ℚ) *
            ringChooseScale k i
termination_by j => j
decreasing_by
  omega

@[simp]
lemma choose_scale_int
    (coefficient : ℤ)
    (k j : ℕ) :
      (ringChooseScale k j).eval (coefficient : ℚ) =
        (chooseScaleCoefficient coefficient k j : ℚ) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
      cases j with
      | zero =>
          simp [ringChooseScale,
            chooseScaleCoefficient, natBinomialCoefficient,
            chooseScaleFunction, ring_scale_int]
      | succ j =>
          rw [ringChooseScale, Polynomial.eval_sub,
            Polynomial.eval_finsetSum]
          simp_rw [Polynomial.eval_mul, Polynomial.eval_C]
          have hrecursive :
              ∀ i : Fin (j + 1),
                (ringChooseScale k i).eval
                    (coefficient : ℚ) =
                  (chooseScaleCoefficient coefficient k i : ℚ) :=
            fun i => ih i i.isLt
          simp_rw [hrecursive]
          rw [ring_scale_int]
          simp [chooseScaleCoefficient, natBinomialCoefficient,
            chooseScaleFunction, mul_comm]

lemma nat_choose_scale
    (k j : ℕ) :
    (ringChooseScale k j).natDegree ≤ k := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
      cases j with
      | zero =>
          simpa [ringChooseScale] using
            choose_scale_polynomial 0 k
      | succ j =>
          rw [ringChooseScale]
          have hsum :
              (∑ i : Fin (j + 1),
                Polynomial.C (Nat.choose (j + 1) i : ℚ) *
                  ringChooseScale k i).natDegree ≤ k := by
            apply Polynomial.natDegree_sum_le_of_forall_le
              (s := Finset.univ)
              (fun i : Fin (j + 1) =>
                Polynomial.C (Nat.choose (j + 1) i : ℚ) *
                  ringChooseScale k i)
            intro i _hi
            exact Polynomial.natDegree_mul_le.trans
              (by
                calc
                  (Polynomial.C (Nat.choose (j + 1) i : ℚ)).natDegree +
                        (ringChooseScale k i).natDegree ≤
                      0 + k := by
                    gcongr
                    · simp
                    · exact ih i i.isLt
                  _ = k := by simp)
          simpa using
            Polynomial.natDegree_sub_le_of_le
              (choose_scale_polynomial (j + 1 : ℕ) k)
              hsum

/-- The second-stage Newton coefficient for `a(c,k,j)` as a function of `c`. -/
def chooseScaleExpansion
    (k j h : ℕ) :
    ℤ :=
  natBinomialCoefficient
    (fun coefficient : ℕ =>
      chooseScaleCoefficient coefficient k j)
    h

/--
Every scalar interpolation coefficient is itself a signed Newton polynomial
of degree at most the outer choose index.
-/
lemma choose_scale_sum
    (coefficient : ℤ)
    (k j : ℕ) :
    chooseScaleCoefficient coefficient k j =
      ∑ h ∈ Finset.range (k + 1),
        chooseScaleExpansion k j h *
          Ring.choose coefficient h := by
  simpa [chooseScaleExpansion] using
    int_binomial_expansion
      (fun nextCoefficient : ℤ =>
        chooseScaleCoefficient nextCoefficient k j)
      (ringChooseScale k j)
      k
      (nat_choose_scale k j)
      (fun nextCoefficient =>
        choose_scale_int nextCoefficient k j)
      coefficient

lemma choose_scale_left
    (k : ℕ)
    (hk : 0 < k) :
    ∀ j : ℕ,
      chooseScaleCoefficient 0 k j = 0
  | 0 => choose_scale_coefficient 0 k hk
  | j + 1 => by
      simp only [chooseScaleCoefficient, natBinomialCoefficient,
        chooseScaleFunction, zero_mul, Ring.choose_zero_pos ℤ hk,
        zero_sub, neg_eq_zero]
      apply Finset.sum_eq_zero
      intro i _hi
      change chooseScaleCoefficient 0 k i * (Nat.choose (j + 1) i : ℤ) = 0
      rw [choose_scale_left k hk i]
      simp

@[simp]
lemma choose_scale_expansion
    (k j : ℕ)
    (hk : 0 < k) :
    chooseScaleExpansion k j 0 = 0 := by
  simp [chooseScaleExpansion,
    natBinomialCoefficient, choose_scale_left k hk]

lemma nat_binomial_function
    (r : ℕ) :
    natBinomialCoefficient (fun _q : ℕ => 0) r = 0 := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      cases r with
      | zero =>
          simp [natBinomialCoefficient]
      | succ r =>
          simp only [natBinomialCoefficient, zero_sub, neg_eq_zero]
          apply Finset.sum_eq_zero
          intro i _hi
          rw [ih i i.isLt]
          simp

@[simp]
lemma ring_choose_scale
    (k h : ℕ)
    (hk : 0 < k) :
    chooseScaleExpansion k 0 h = 0 := by
  change
    natBinomialCoefficient
      (fun coefficient : ℕ =>
        chooseScaleCoefficient coefficient k 0)
      h = 0
  simp only [choose_scale_coefficient _ k hk]
  exact nat_binomial_function h

/--
Two-variable Newton decomposition of `choose (left * right) k`.  Both
zero-index rows vanish for positive `k`, so the displayed finite ranges can be
shifted to positive indices by downstream formula constructors.
-/
lemma ring_choose_sum
    (left right : ℤ)
    (k : ℕ) :
    Ring.choose (left * right) k =
      ∑ j ∈ Finset.range (k + 1),
        ∑ h ∈ Finset.range (k + 1),
          chooseScaleExpansion k j h *
            Ring.choose left h *
              Ring.choose right j := by
  rw [ring_choose_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [choose_scale_sum]
  rw [Finset.sum_mul]

/--
Positive-index form of the two-variable decomposition.  This is the form used
by weighted formula constructors, whose monomials contain only positive
generalized-binomial indices.
-/
lemma ring_choose_pos
    (left right : ℤ)
    (k : ℕ)
    (hk : 0 < k) :
    Ring.choose (left * right) k =
      ∑ j ∈ Finset.range k,
        ∑ h ∈ Finset.range k,
          chooseScaleExpansion k (j + 1) (h + 1) *
            Ring.choose left (h + 1) *
              Ring.choose right (j + 1) := by
  rw [ring_choose_sum]
  rw [Finset.sum_range_succ']
  simp only [ring_choose_scale k _ hk,
    zero_mul, Finset.sum_const_zero]
  rw [add_zero]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.sum_range_succ']
  simp [choose_scale_expansion k (j + 1) hk]

end TCTex
end Towers

/-!
# Unary normalization of nested generalized binomial coefficients

The finite-grid raw-product recursion needs a one-slot base case.  This file
normalizes

`choose (choose z a) k`

into the signed Newton basis `choose z b`, with `b ≤ k * a`, and packages that
expansion as an explicit weighted Hall-binomial formula for one coordinate.
It is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/-- The signed one-variable function `z ↦ choose (choose z a) k`. -/
def nestedChooseFunction
    (a k : ℕ) :
    ℤ → ℤ :=
  fun z => Ring.choose (Ring.choose z a) k

/-- The rational polynomial representing `z ↦ choose (choose z a) k`. -/
noncomputable def nestedRingChoose
    (a k : ℕ) :
    Polynomial ℚ :=
  (natChoosePolynomial k).comp (natChoosePolynomial a)

lemma nat_nested_choose
    (a k : ℕ) :
    (nestedRingChoose a k).natDegree ≤ k * a := by
  exact Polynomial.natDegree_comp_le.trans
    (Nat.mul_le_mul
      (degree_choose_polynomial k)
      (degree_choose_polynomial a))

@[simp]
lemma nested_choose_int
    (a k : ℕ)
    (z : ℤ) :
    (nestedRingChoose a k).eval (z : ℚ) =
      (nestedChooseFunction a k z : ℚ) := by
  simp [nestedRingChoose, nestedChooseFunction,
    Polynomial.eval_comp, nat_choose_int]

/-- Newton coefficient for `z ↦ choose (choose z a) k`. -/
def nestedChooseCoefficient
    (a k b : ℕ) :
    ℤ :=
  natBinomialCoefficient
    (fun q : ℕ => nestedChooseFunction a k q)
    b

/-- Signed Newton expansion of one nested generalized binomial coefficient. -/
lemma nested_choose_sum
    (a k : ℕ)
    (z : ℤ) :
    nestedChooseFunction a k z =
      ∑ b ∈ Finset.range (k * a + 1),
        nestedChooseCoefficient a k b * Ring.choose z b := by
  simpa [nestedChooseCoefficient] using
    int_binomial_expansion
      (nestedChooseFunction a k)
      (nestedRingChoose a k)
      (k * a)
      (nat_nested_choose a k)
      (nested_choose_int a k)
      z

@[simp]
lemma nested_ring_choose
    (a k : ℕ)
    (ha : 0 < a)
    (hk : 0 < k) :
    nestedChooseCoefficient a k 0 = 0 := by
  simp [nestedChooseCoefficient, natBinomialCoefficient,
    nestedChooseFunction, Ring.choose_zero_pos ℤ ha,
    Ring.choose_zero_pos ℤ hk]

namespace WHMono

/-- One raw generalized-binomial coordinate factor `choose(e input address) b`. -/
def singleChoose
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {targetWeight : ℕ}
    (input : ι)
    (address : HEAddres H)
    (binomialIndex : ℕ)
    (binomialIndex_pos : 0 < binomialIndex)
    (weightedWeight_le : binomialIndex * address.1 ≤ targetWeight) :
    WHMono H ι targetWeight where
  length := 1
  length_pos := by simp
  input := fun _ => input
  address := fun _ => address
  binomialIndex := fun _ => binomialIndex
  binomialIndex_pos := by simp [binomialIndex_pos]
  weightedWeight_le := by simpa using weightedWeight_le

@[simp]
lemma eval_singleChoose
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {targetWeight : ℕ}
    (e : ι → HEFam H)
    (input : ι)
    (address : HEAddres H)
    (binomialIndex : ℕ)
    (binomialIndex_pos : 0 < binomialIndex)
    (weightedWeight_le : binomialIndex * address.1 ≤ targetWeight) :
    (singleChoose input address binomialIndex binomialIndex_pos
      weightedWeight_le).eval e =
        Ring.choose (e input address.1 address.2) binomialIndex := by
  simp [singleChoose, WHMono.eval]

end WHMono

namespace WBForm

/--
Explicit one-slot formula normalizing
`choose (choose (e input address) a) k`.
-/
noncomputable def ringChooseSingle
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (input : ι)
    (address : HEAddres H)
    (a : ℕ)
    (_ha : 0 < a)
    (hweight : a * address.1 ≤ targetWeight)
    (k : ℕ)
    (_hk : 0 < k) :
    WBForm H ι (k * targetWeight) :=
  WBForm.listSum
    (List.ofFn fun b : Fin (k * a) =>
      WBForm.singleton
        (nestedChooseCoefficient a k (b + 1),
          WHMono.singleChoose input address (b + 1)
            (by omega)
            (by
              calc
                (b + 1) * address.1 ≤
                    (k * a) * address.1 :=
                  Nat.mul_le_mul_right address.1 (by omega)
                _ = k * (a * address.1) := Nat.mul_assoc k a address.1
                _ ≤ k * targetWeight :=
                  Nat.mul_le_mul_left k hweight)))

@[simp]
lemma choose_single_factor
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (input : ι)
    (address : HEAddres H)
    (a : ℕ)
    (ha : 0 < a)
    (hweight : a * address.1 ≤ targetWeight)
    (k : ℕ)
    (hk : 0 < k)
    (e : ι → HEFam H) :
    (ringChooseSingle input address a ha hweight k hk).eval e =
      Ring.choose (Ring.choose (e input address.1 address.2) a) k := by
  rw [ringChooseSingle, WBForm.eval_listSum]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply,
    WBForm.eval_singleton,
    WBTerm.eval,
    WHMono.eval_singleChoose]
  rw [Fin.sum_univ_eq_sum_range
    (fun b : ℕ =>
      nestedChooseCoefficient a k (b + 1) *
        Ring.choose (e input address.1 address.2) (b + 1))]
  change
    (∑ b ∈ Finset.range (k * a),
      nestedChooseCoefficient a k (b + 1) *
        Ring.choose (e input address.1 address.2) (b + 1)) =
      nestedChooseFunction a k (e input address.1 address.2)
  rw [nested_choose_sum]
  rw [Finset.sum_range_succ']
  simp [nested_ring_choose a k ha hk]

end WBForm

end TCTex
end Towers

/-!
# Constructing finite-grid generalized-binomial normalization

This file discharges the finite-grid arithmetic kernel isolated by
`ProductInverseCollectionPolynomialFormulaChooseFiniteGridReduction`.
A nonempty raw product is normalized recursively:

* one coordinate uses unary nested-choose normalization;
* a longer product splits into its head and tail;
* the positive-positive two-variable Newton decomposition normalizes the
  split product and preserves the weighted target bound.

The resulting concrete finite-grid family supplies the full positive-choose
normalizer consumed by Hall-Petresco substitution.  This file is intentionally
not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/-- One raw generalized-binomial factor in a finite Hall-coordinate product. -/
structure WBFactor
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  input : ι
  address : HEAddres H
  binomialIndex : ℕ
  binomialIndex_pos : 0 < binomialIndex

namespace WBFactor

/-- Weighted Hall cost of one raw generalized-binomial factor. -/
def weight
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : WBFactor H ι) :
    ℕ :=
  factor.binomialIndex * factor.address.1

/-- Signed evaluation of one raw generalized-binomial factor. -/
def eval
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : WBFactor H ι)
    (e : ι → HEFam H) :
    ℤ :=
  Ring.choose
    (e factor.input factor.address.1 factor.address.2)
    factor.binomialIndex

/-- Total weighted Hall cost of a list of raw factors. -/
def listWeight
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type} :
    List (WBFactor H ι) →
      ℕ
  | factors => (factors.map weight).sum

/-- Product evaluation of a list of raw factors. -/
def listEval
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type} :
    List (WBFactor H ι) →
      (ι → HEFam H) →
        ℤ
  | factors, e => (factors.map fun factor => factor.eval e).prod

end WBFactor

namespace WBForm

@[simp]
lemma eval_sum_fn
    {d targetWeight length : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (formulas : Fin length → WBForm H ι targetWeight)
    (e : ι → HEFam H) :
    (WBForm.listSum (List.ofFn formulas)).eval e =
      ∑ i, (formulas i).eval e := by
  rw [WBForm.eval_listSum]
  simp [List.map_ofFn, List.sum_ofFn]

/--
Normalize a positive generalized binomial coefficient of one nonempty list of
raw factors.  The output target is the exact scaled total input weight.
-/
noncomputable def ringChooseFactors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type} :
    (factors : List (WBFactor H ι)) →
      factors ≠ [] →
        ∀ k : ℕ,
          0 < k →
            WBForm H ι
              (k * WBFactor.listWeight factors)
  | [], hnonempty, _k, _hk => False.elim (hnonempty rfl)
  | [factor], _hnonempty, k, hk =>
      ringChooseSingle factor.input factor.address
        factor.binomialIndex factor.binomialIndex_pos le_rfl k hk
  | factor :: nextFactor :: factors, _hnonempty, k, hk =>
      WBForm.listSum
        (List.ofFn fun j : Fin k =>
          WBForm.listSum
            (List.ofFn fun h : Fin k =>
              (((ringChooseSingle factor.input factor.address
                    factor.binomialIndex factor.binomialIndex_pos le_rfl
                    (h + 1) (by omega)).mul
                  (ringChooseFactors (nextFactor :: factors) (by simp)
                    (j + 1) (by omega))
                  (by
                    change
                      (h + 1) * factor.weight +
                          (j + 1) *
                            WBFactor.listWeight
                              (nextFactor :: factors) ≤
                        k *
                          (factor.weight +
                            WBFactor.listWeight
                              (nextFactor :: factors))
                    rw [Nat.mul_add]
                    exact Nat.add_le_add
                      (Nat.mul_le_mul_right factor.weight
                        (Nat.succ_le_iff.mpr h.isLt))
                      (Nat.mul_le_mul_right
                        (WBFactor.listWeight
                          (nextFactor :: factors))
                        (Nat.succ_le_iff.mpr j.isLt)))).scaleForChoose
                (chooseScaleExpansion
                  k (j + 1) (h + 1)))))
termination_by factors => factors.length

@[simp]
lemma choose_raw_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type} :
    ∀ (factors : List (WBFactor H ι))
      (hnonempty : factors ≠ [])
      (k : ℕ)
      (hk : 0 < k)
      (e : ι → HEFam H),
        (ringChooseFactors factors hnonempty k hk).eval e =
          Ring.choose (WBFactor.listEval factors e) k
  | [], hnonempty, _k, _hk, _e => False.elim (hnonempty rfl)
  | [factor], _hnonempty, k, hk, e => by
      simpa only [ringChooseFactors, WBFactor.listEval,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        WBFactor.eval] using
        choose_single_factor factor.input factor.address
          factor.binomialIndex factor.binomialIndex_pos le_rfl k hk e
  | factor :: nextFactor :: factors, _hnonempty, k, hk, e => by
      rw [ringChooseFactors, eval_sum_fn]
      simp_rw [eval_sum_fn,
        WBForm.eval_scale_choose,
        WBForm.eval_mul,
        choose_single_factor,
        choose_raw_factors (nextFactor :: factors) (by simp)]
      simpa only [WBFactor.listEval,
        WBFactor.eval, List.map_cons, List.prod_cons,
        ← Fin.sum_univ_eq_sum_range, mul_assoc] using
        (ring_choose_pos
          (factor.eval e)
          (WBFactor.listEval (nextFactor :: factors) e)
          k hk).symm
termination_by factors => factors.length

end WBForm

namespace WBFactor

/-- Canonical raw-factor list attached to an independent finite slot grid. -/
def finiteGridFactors
    {d length : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (address : Fin length → HEAddres H)
    (binomialIndex : Fin length → ℕ)
    (binomialIndex_pos : ∀ ν, 0 < binomialIndex ν) :
    List (WBFactor H (Fin length)) :=
  List.ofFn fun ν =>
    { input := ν
      address := address ν
      binomialIndex := binomialIndex ν
      binomialIndex_pos := binomialIndex_pos ν }

@[simp]
lemma list_grid_factors
    {d length : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (address : Fin length → HEAddres H)
    (binomialIndex : Fin length → ℕ)
    (binomialIndex_pos : ∀ ν, 0 < binomialIndex ν) :
    listWeight (finiteGridFactors address binomialIndex binomialIndex_pos) =
      ∑ ν, binomialIndex ν * (address ν).1 := by
  simp [finiteGridFactors, listWeight, weight, List.sum_ofFn]

@[simp]
lemma eval_grid_factors
    {d length : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (address : Fin length → HEAddres H)
    (binomialIndex : Fin length → ℕ)
    (binomialIndex_pos : ∀ ν, 0 < binomialIndex ν)
    (e : Fin length → HEFam H) :
    listEval (finiteGridFactors address binomialIndex binomialIndex_pos) e =
      ∏ ν,
        Ring.choose
          (e ν (address ν).1 (address ν).2)
          (binomialIndex ν) := by
  simp [finiteGridFactors, listEval, eval, List.prod_ofFn]

end WBFactor

namespace WBForm

/-- Concrete finite-grid arithmetic kernel for every canonical Hall family. -/
noncomputable def positiveGridNormalizer
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    PGNormal H where
  ringChoose length_pos address binomialIndex binomialIndex_pos
      weightedWeight_le k hk :=
    (ringChooseFactors
      (WBFactor.finiteGridFactors
        address binomialIndex binomialIndex_pos)
      (by
        apply List.ne_nil_of_length_pos
        simp [WBFactor.finiteGridFactors, length_pos])
      k hk).weaken
        (Nat.mul_le_mul_left k (by
          simpa using weightedWeight_le))
  eval_ringChoose length_pos address binomialIndex binomialIndex_pos
      weightedWeight_le k hk e := by
    rw [WBForm.eval_weaken,
      choose_raw_factors]
    simp

/--
The constructed finite-grid kernel, scalar Newton interpolation, and
Chu-Vandermonde give the positive-choose formula normalizer required by
Hall-Petresco substitution.
-/
noncomputable def chooseNormalizerFamily
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    PositiveChooseNormalizer H :=
  PGNormal.positiveChooseNormalizer
    (positiveGridNormalizer H)

end WBForm

end TCTex
end Towers

/-!
# Natural and signed Hall-Petresco packet interface

The concrete inverse-trace collector naturally proves identities first at
natural source multiplicities.  Claim 8 needs one cutoff-specific ordered
recipe list whose generalized-binomial formula remains valid at arbitrary
integral source exponents.

This file separates those two obligations.  It proves the natural compression
adapter for any independently constructed counted-family expansion, packages
the uniform natural packet law, and compiles an explicit signed lift into the
existing all-integral packet consumed by polynomial collection.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

open HACoeff
open BFTrunc
open BRSpec
open ITEvalua
open PPColl.RCColl.RPAggreg

namespace RNCompre
namespace BFam.Expansion

/--
Every independently constructed counted-family expansion compresses to the
expected generalized-binomial recipe identity at its generating natural
multiplicities.
-/
lemma recipe_cast_pow
    {M N : ℕ}
    (expansion : BFam.Expansion M N)
    {G : Type*}
    [Group G]
    (x y : G) :
    (((expansion.families.map BFam.recipe).map fun R =>
      R.erasedShape.eval (HPAtom.eval x y) ^
        coefficientValue R (M : ℤ) (N : ℤ)).prod) =
      ⁅x ^ M, y ^ N⁆ := by
  rw [← collapsed_realization_cast x y]
  calc
    collapsedList x y
          (BFam.realizationList expansion.families) =
        hallPairSpecialize x y
          (collapsedListEval
            (BFam.realizationList expansion.families)) := by
      symm
      exact pair_specialize_collapsed x y _
    _ =
        hallPairSpecialize x y
          ⁅universalLeft ^ M, universalRight ^ N⁆ := by
      rw [expansion.collapsed_eval_eq]
    _ = ⁅x ^ M, y ^ N⁆ := by
      simp only [map_commutatorElement, map_pow,
        specialize_universal_left, specialize_universal_right]

end BFam.Expansion
end RNCompre

namespace FNPkt

/--
One ordered cutoff-specific recipe packet whose Hall-Petresco identity is
known uniformly at natural source multiplicities.
-/
structure TNPkt
    (d n : ℕ) where
  recipes :
    List BRecipe
  list_nat_cast :
    ∀ (left right :
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightExponent : ℕ),
        (recipes.map fun R =>
          R.erasedShape.eval (HPAtom.eval left right) ^
            coefficientValue R
              (leftExponent : ℤ) (rightExponent : ℤ)).prod =
          ⁅left ^ leftExponent, right ^ rightExponent⁆

namespace TNPkt

/--
The remaining signed-extension theorem for one uniform natural packet.
This is the exact symbolic Hall-collection obligation beyond natural
multiplicity counting.
-/
structure AILift
    {d n : ℕ}
    (packet : TNPkt.{u} d n) :
    Prop where
  listEval_eq :
    ∀ (left right :
        LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (leftExponent rightExponent : ℤ),
        (packet.recipes.map fun R =>
          R.erasedShape.eval (HPAtom.eval left right) ^
            coefficientValue R leftExponent rightExponent).prod =
          ⁅left ^ leftExponent, right ^ rightExponent⁆

namespace AILift

/--
An explicit signed lift is exactly the all-integral packet consumed by
formula substitution.
-/
def truncatedAll
    {d n : ℕ}
    {packet : TNPkt.{u} d n}
    (lift : packet.AILift) :
    PFSubsti.TAPkt.{u}
      d n where
  recipes := packet.recipes
  listEval_eq := lift.listEval_eq

end AILift
end TNPkt
end FNPkt

namespace PFSubsti
namespace TAPkt

/--
Every signed packet forgets to its uniform natural specialization.
-/
def truncatedNaturalPacket
    {d n : ℕ}
    (packet : TAPkt.{u} d n) :
    FNPkt.TNPkt.{u}
      d n where
  recipes := packet.recipes
  list_nat_cast left right leftExponent rightExponent := by
    simpa only [zpow_natCast] using
      packet.listEval_eq left right
        (leftExponent : ℤ) (rightExponent : ℤ)

end TAPkt
end PFSubsti

end TCTex
end Towers
