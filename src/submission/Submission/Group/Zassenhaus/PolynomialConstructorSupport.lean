import Submission.Group.Zassenhaus.InversePolynomials
import Submission.Group.Zassenhaus.SymbolicHallCollection

universe u

-- Merged from PolynomialBaseCases.lean

/-!
# Base cases for Hall product and inverse collection polynomials

These are the initial cases for a symbolic Hall collector: the zero Hall
family, the empty product, a singleton product, and the inverse of the zero
family.  They inhabit the Claim 8 interfaces from
`FinitePGroupCollection.lean` without changing the existing import graph.
-/

namespace Submission
namespace TCTex

/-- Every finite collected prefix of the zero Hall family is the identity. -/
lemma collected_prefix_zero
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (k : ℕ) :
    collectedPrefixProduct (n := n) H (0 : HEFam H) k = 1 := by
  simp [collectedPrefixProduct,
    BCWta.collected_weight_productzero]

/-- The full collected product of the zero Hall family is the identity. -/
lemma collected_product_zero
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    collectedHallProduct (n := n) H (0 : HEFam H) = 1 := by
  simp [collectedHallProduct, collected_prefix_zero]

/-- The empty list of collected Hall products has Claim 8 polynomial data. -/
theorem collected_data_nil
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    CollectedCoordinateData (n := n) H [] := by
  refine ⟨0, ?_, ?_⟩
  · simp [collectedHallProducts, collected_product_zero]
  · intro s _hs _hsn i
    exact
      ICMonomi.zero
        (fun j : Fin [].length => [].get j)

/--
A singleton input list already is collected.  Its coordinates are singleton
recipes `choose E 1`, so it has Claim 8 polynomial data without any swaps.
-/
theorem collected_data_singleton
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H) :
    CollectedCoordinateData (n := n) H [e] := by
  refine ⟨e, ?_, ?_⟩
  · simp [collectedHallProducts]
  · intro s _hs _hsn i
    simpa using
      (ICMonomi.inputExponent
        (fun j : Fin 1 => [e].get j) (0 : Fin 1)
        (⟨s, i⟩ : HEAddres H) le_rfl)

/-- The inverse of the zero Hall family has Claim 8 polynomial data. -/
theorem collected_data_zero
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    CollectedInverseData
      (n := n) H (0 : HEFam H) := by
  refine ⟨0, ?_, ?_⟩
  · simp [collected_product_zero]
  · intro s _hs _hsn i
    exact
      ICMonomi.zero
        (fun _ : Fin 1 => negExponentFamily (0 : HEFam H))

end TCTex
end Submission

-- Merged from PolynomialConstructors.lean

/-!
# Constructor bridge for Hall product and inverse collection polynomials

A concrete parametrized Hall algorithm ends with one finite list of admissible
binomial recipes for every collected Hall coordinate.  This file packages that
output and turns a sound symbolic rewrite run into the Claim 8 interfaces
already consumed by `FinitePGroupCollection.lean`.
-/

namespace Submission
namespace TCTex

/-- Products of powers of one group element add their integer exponents. -/
lemma prod_zpow_sum
    {G : Type*} [Group G]
    (g : G)
    (L : List ℤ) :
    (L.map fun z => g ^ z).prod = g ^ L.sum := by
  induction L with
  | nil =>
      simp
  | cons z L ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, ih]
      exact (zpow_add g z L.sum).symm

/-- Mapped form of `prod_zpow_sum`. -/
lemma list_zpow_sum
    {G α : Type*} [Group G]
    (g : G)
    (f : α → ℤ)
    (L : List α) :
    (L.map fun x => g ^ f x).prod = g ^ (L.map f).sum := by
  simpa only [List.map_map, Function.comp_apply] using
    (prod_zpow_sum g (L.map f))

namespace WHMono

/-- Read one admissible coordinate recipe as one atomic symbolic Hall factor. -/
def symbolicCollectionFactor
    {d s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (m : WHMono H ι s)
    (i : (H s).index) :
    SCFactor H ι where
  word := .atom (⟨s, i⟩ : HEAddres H)
  coefficient := m

@[simp]
lemma symbolic_collection_factor
    {d n s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (m : WHMono H ι s)
    (i : (H s).index) :
    (m.symbolicCollectionFactor i).eval (n := n) e =
      ((H s).commutator i).freeLowerTruncation ^ m.eval e :=
  rfl

end WHMono

/-- Finite admissible binomial recipes for every collected Hall coordinate. -/
structure CHRecipe
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  recipes :
    ∀ s : ℕ, (H s).index → List (WHMono H ι s)

namespace CHRecipe

/-- Evaluate every finite coordinate recipe list and sum its contributions. -/
def eval
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (e : ι → HEFam H) :
    HEFam H :=
  fun s i => ((R.recipes s i).map fun m => m.eval e).sum

/-- Every evaluated coordinate recipe list lies in the required integer span. -/
lemma combination_weighted_monomials
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (e : ι → HEFam H)
    (s : ℕ)
    (i : (H s).index) :
    ICMonomi
      H s e (R.eval e s i) := by
  change
    ICMonomi
      H s e ((R.recipes s i).map fun m => m.eval e).sum
  induction R.recipes s i with
  | nil =>
      exact ICMonomi.zero e
  | cons m L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact ICMonomi.add
        (Submodule.subset_span ⟨m, rfl⟩) ih

/-- The normalized symbolic factors in one fixed Hall-weight layer. -/
def weightFactors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (s : ℕ) :
    List (SCFactor H ι) :=
  (Finset.univ.sort fun i i' : (H s).index => i ≤ i').flatMap fun i =>
    (R.recipes s i).map fun m => m.symbolicCollectionFactor i

/-- Fixed-weight normalized recipe factors evaluate to their Hall segment. -/
lemma list_weight_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (e : ι → HEFam H)
    (s : ℕ) :
    SCFactor.listEval (n := n) e (R.weightFactors s) =
      (H s).collectedWeightProduct (n := n) (R.eval e s) := by
  simp [weightFactors, SCFactor.listEval,
    CHRecipe.eval,
    BCWta.collectedWeightProduct,
    BCWta.collected_lower_centralterm,
    BCWt.evalin_freelower_centtrunterm,
    List.flatMap, Function.comp_def, list_zpow_sum]

/-- Normalized symbolic recipe factors through ordinary Hall weight `k`. -/
def prefixFactors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (k : ℕ) :
    List (SCFactor H ι) :=
  (List.range k).flatMap fun q => R.weightFactors (q + 1)

/-- Prefix normalized recipe factors evaluate to the collected Hall prefix. -/
lemma eval_prefix_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (e : ι → HEFam H)
    (k : ℕ) :
    SCFactor.listEval (n := n) e (R.prefixFactors k) =
      collectedPrefixProduct (n := n) H (R.eval e) k := by
  induction k with
  | zero =>
      simp [prefixFactors, collectedPrefixProduct]
  | succ k ih =>
      rw [prefixFactors, List.range_succ, List.flatMap_append,
        List.flatMap_singleton, SCFactor.listEval_append,
        collected_prefix_succ]
      change
        SCFactor.listEval e (R.prefixFactors k) *
            SCFactor.listEval e (R.weightFactors (k + 1)) =
          collectedPrefixProduct H (R.eval e) k *
            (H (k + 1)).collectedWeightProduct (R.eval e (k + 1))
      rw [ih, R.list_weight_factors]

/-- Full normalized symbolic factor list represented by the coordinate recipes. -/
def factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι) :
    List (SCFactor H ι) :=
  R.prefixFactors (n - 1)

/-- Full normalized recipe factors evaluate to the collected Hall product. -/
lemma listEval_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (e : ι → HEFam H) :
    SCFactor.listEval (n := n) e (R.factors (n := n)) =
      collectedHallProduct (n := n) H (R.eval e) := by
  simp [factors, collectedHallProduct, R.eval_prefix_factors]

end CHRecipe

/--
A normalized symbolic collection output.  The concrete collector supplies its
final factor list together with the coordinate recipes read from that list.
-/
structure CollectedSymbolicForm
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) where
  coordinates :
    CHRecipe H ι
  factors :
    List (SCFactor H ι)
  listEval_eq :
    ∀ e : ι → HEFam H,
      SCFactor.listEval (n := n) e factors =
        collectedHallProduct (n := n) H (coordinates.eval e)

namespace CHRecipe

/-- The canonical normalized symbolic form represented by coordinate recipes. -/
def normalForm
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι) :
    CollectedSymbolicForm (n := n) H ι where
  coordinates := R
  factors := R.factors (n := n)
  listEval_eq := R.listEval_factors

end CHRecipe

/--
A sound symbolic collection run from the indexed finite-product source list
constructs the product form of TeX Claim 8.
-/
theorem data_symbolic_rewrites
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (normal :
      CollectedSymbolicForm (n := n) H (Fin e.length))
    (hrewrites :
      SHRw
        (indexedSymbolicFactors (n := n) H e)
        normal.factors) :
    CollectedCoordinateData (n := n) H e := by
  let input : Fin e.length → HEFam H := fun j => e.get j
  refine ⟨normal.coordinates.eval input, ?_, ?_⟩
  · exact (normal.listEval_eq input).symm.trans
      ((hrewrites.listEval_eq input).trans
        (indexed_symbolic_factors H e))
  · intro s _hs _hsn i
    exact
      CHRecipe.combination_weighted_monomials
        normal.coordinates input s i

/--
A sound symbolic collection run from the reversed negated source list
constructs the inverse form of TeX Claim 8.
-/
theorem collected_symbolic_rewrites
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (normal : CollectedSymbolicForm (n := n) H (Fin 1))
    (hrewrites :
      SHRw
        (symbolicInverseFactors (n := n) H)
        normal.factors) :
    CollectedInverseData (n := n) H e := by
  let input : Fin 1 → HEFam H :=
    fun _ => negExponentFamily e
  refine ⟨normal.coordinates.eval input, ?_, ?_⟩
  · exact (normal.listEval_eq input).symm.trans
      ((hrewrites.listEval_eq input).trans
        (list_symbolic_factors H e))
  · intro s _hs _hsn i
    exact
      CHRecipe.combination_weighted_monomials
        normal.coordinates input s i

/--
Convenient product constructor: a rewrite run to the canonical recipe endpoint
is sufficient to build TeX Claim 8 product data.
-/
theorem data_recipe_rewrites
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (R : CHRecipe H (Fin e.length))
    (hrewrites :
      SHRw
        (indexedSymbolicFactors (n := n) H e)
        (R.factors (n := n))) :
    CollectedCoordinateData (n := n) H e :=
  data_symbolic_rewrites
    H e (R.normalForm (n := n)) hrewrites

/--
Convenient inverse constructor: a rewrite run from the reversed negated source
list to the canonical recipe endpoint is sufficient to build inverse data.
-/
theorem collected_inverse_rewrites
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (R : CHRecipe H (Fin 1))
    (hrewrites :
      SHRw
        (symbolicInverseFactors (n := n) H)
        (R.factors (n := n))) :
    CollectedInverseData (n := n) H e :=
  collected_symbolic_rewrites
    H e (R.normalForm (n := n)) hrewrites

end TCTex
end Submission

-- Merged from PolynomialTruncatedConstructors.lean

/-!
# Truncated constructor bridge for Hall product and inverse collection

The terminating Hall scheduler runs inside one fixed free nilpotent quotient.
This file proves that its source and target lists are physically truncated and
turns a finite cutoff-specific rewrite run into the Claim 8 data interfaces.
-/

namespace Submission
namespace TCTex

namespace SCFactor

/-- Every factor in one fixed-weight source layer has exactly that weight. -/
lemma word_symbolic_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {j : ι}
    {r : ℕ}
    {x : SCFactor H ι}
    (hx : x ∈ symbolicWeightFactors H j r) :
    x.word.weight HEAddres.weight = r := by
  rcases List.mem_map.mp hx with ⟨i, _hi, rfl⟩
  rfl

/-- Prefix source factors have weight bounded by the prefix length. -/
lemma symbolic_prefix_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {j : ι}
    {k : ℕ}
    {x : SCFactor H ι}
    (hx : x ∈ symbolicPrefixFactors H j k) :
    x.word.weight HEAddres.weight ≤ k := by
  rcases List.mem_flatMap.mp hx with ⟨q, hq, hx⟩
  rw [word_symbolic_factors hx]
  exact List.mem_range.mp hq

/-- One collected Hall source block is physically below the quotient cutoff. -/
lemma truncated_hall_factors
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    {ι : Type}
    (j : ι) :
    IsTruncated n (symbolicHallFactors (n := n) H j) := by
  intro x hx
  have hweight :=
    symbolic_prefix_factors
      (H := H) (j := j) hx
  have hpos := x.word_weight_pos
  omega

/-- Any concatenation of collected source blocks is physically truncated. -/
lemma truncated_product_factors
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    {ι : Type}
    (labels : List ι) :
    IsTruncated n (symbolicSourceFactors (n := n) H labels) := by
  intro x hx
  rcases List.mem_flatMap.mp hx with ⟨j, _hj, hx⟩
  exact truncated_hall_factors H j x hx

/-- The indexed product source list consumed by Claim 8 is physically truncated. -/
lemma truncated_indexed_factors
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H)) :
    IsTruncated n (indexedSymbolicFactors (n := n) H e) :=
  truncated_product_factors H (List.finRange e.length)

/-- The reversed source list consumed by inverse Claim 8 is physically truncated. -/
lemma truncated_symbolic_factors
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    IsTruncated n (symbolicInverseFactors (n := n) H) := by
  intro x hx
  exact truncated_hall_factors H (0 : Fin 1) x
    (by simpa [symbolicInverseFactors] using hx)

end SCFactor

namespace CHRecipe

/-- Every normalized recipe factor in one fixed layer has exactly that layer weight. -/
lemma word_weight_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    {s : ℕ}
    {x : SCFactor H ι}
    (hx : x ∈ R.weightFactors s) :
    x.word.weight HEAddres.weight = s := by
  rcases List.mem_flatMap.mp hx with ⟨i, _hi, hx⟩
  rcases List.mem_map.mp hx with ⟨m, _hm, rfl⟩
  rfl

/-- Prefix recipe endpoints have weight bounded by the prefix length. -/
lemma word_prefix_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    {k : ℕ}
    {x : SCFactor H ι}
    (hx : x ∈ R.prefixFactors k) :
    x.word.weight HEAddres.weight ≤ k := by
  rcases List.mem_flatMap.mp hx with ⟨q, hq, hx⟩
  rw [R.word_weight_factors hx]
  exact List.mem_range.mp hq

/-- Canonical recipe endpoints are physically below the quotient cutoff. -/
lemma isTruncated_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι) :
    SCFactor.IsTruncated n (R.factors (n := n)) := by
  intro x hx
  have hweight := R.word_prefix_factors hx
  have hpos := x.word_weight_pos
  omega

end CHRecipe

/--
A cutoff-specific symbolic collection run from the indexed finite-product
source list constructs the product form of TeX Claim 8.
-/
theorem collected_truncated_rewrites
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (R : CHRecipe H (Fin e.length))
    (hrewrites :
      SCRwb (n := n)
        (indexedSymbolicFactors (n := n) H e)
        (R.factors (n := n))) :
    CollectedCoordinateData (n := n) H e := by
  let input : Fin e.length → HEFam H := fun j => e.get j
  refine ⟨R.eval input, ?_, ?_⟩
  · exact (R.listEval_factors input).symm.trans
      ((hrewrites.listEval_eq input).trans
        (indexed_symbolic_factors H e))
  · intro s _hs _hsn i
    exact R.combination_weighted_monomials input s i

/--
A cutoff-specific symbolic collection run from the reversed negated source list
constructs the inverse form of TeX Claim 8.
-/
theorem collected_recipe_rewrites
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (R : CHRecipe H (Fin 1))
    (hrewrites :
      SCRwb (n := n)
        (symbolicInverseFactors (n := n) H)
        (R.factors (n := n))) :
    CollectedInverseData (n := n) H e := by
  let input : Fin 1 → HEFam H :=
    fun _ => negExponentFamily e
  refine ⟨R.eval input, ?_, ?_⟩
  · exact (R.listEval_factors input).symm.trans
      ((hrewrites.listEval_eq input).trans
        (list_symbolic_factors H e))
  · intro s _hs _hsn i
    exact R.combination_weighted_monomials input s i

end TCTex
end Submission
