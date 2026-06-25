import Submission.Group.Zassenhaus.PolynomialConstructorSupport
import Submission.Group.Zassenhaus.SymbolicHallSteps

/-!
# Semantic delegation of product and inverse Hall corrections

A nonterminal product or inverse collector works with signed polynomial Hall
factors.  Every retained correction emitted by one truncated swap is physically
below the nilpotent cutoff and has strictly higher word weight than either
parent.  Thus a collector working in stratum `lowerWeight` may delegate the
correction packet to a semantic normalizer for stratum `lowerWeight + 1`.

Canonical Claim 8 coordinate recipes still form the endpoint: their ordinary
one-monomial factors embed into the richer signed-polynomial state.  This file
packages that endpoint, the higher-stratum handoff, and direct adapters from a
stratum-one semantic normalizer to the product and inverse Claim 8 interfaces.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

namespace SPFactor

/-- A signed polynomial factor list is physically below the quotient cutoff. -/
def IsTruncated
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ)
    (L : List (SPFactor H ι)) :
    Prop :=
  ∀ x ∈ L, x.word.weight HEAddres.weight < n

/-- Every signed polynomial factor in a list has weight at least one stratum. -/
def WordWeightLeast
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (lowerWeight : ℕ)
    (L : List (SPFactor H ι)) :
    Prop :=
  ∀ x ∈ L, lowerWeight ≤ x.word.weight HEAddres.weight

/-- Every signed polynomial factor list is supported from stratum one upward. -/
lemma word_least_one
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (L : List (SPFactor H ι)) :
    WordWeightLeast 1 L := by
  intro x _hx
  exact x.word_weight_pos

/-- Embedding physically truncated monomial factors preserves truncation. -/
lemma truncated_monomial
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L : List (SCFactor H ι)}
    (hL : SCFactor.IsTruncated n L) :
    IsTruncated n (L.map SPFactor.ofMonomial) := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
  exact hL y hy

end SPFactor

namespace CHRecipe

/-- Canonical Claim 8 recipes embedded into the signed-polynomial factor state. -/
def polynomialFactors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι) :
    List (SPFactor H ι) :=
  (R.factors (n := n)).map SPFactor.ofMonomial

/-- Embedded canonical recipe factors evaluate to the collected Hall product. -/
lemma list_polynomial_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e
        (R.polynomialFactors (n := n)) =
      collectedHallProduct (n := n) H (R.eval e) := by
  rw [polynomialFactors,
    SPFactor.list_eval_monomial,
    R.listEval_factors]

/-- Canonical recipe endpoints are physically truncated after embedding. -/
lemma truncated_polynomial_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι) :
    SPFactor.IsTruncated n
      (R.polynomialFactors (n := n)) :=
  SPFactor.truncated_monomial R.isTruncated_factors

/-- A coordinate endpoint has no canonical factors below `lowerWeight`. -/
def NTBelow
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (lowerWeight : ℕ) :
    Prop :=
  ∀ s : ℕ, s < lowerWeight → R.weightFactors s = []

/-- Endpoints with no lower terms are supported in the corresponding stratum. -/
lemma least_no_below
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CHRecipe H ι)
    (hR : R.NTBelow lowerWeight) :
    SPFactor.WordWeightLeast lowerWeight
      (R.polynomialFactors (n := n)) := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
  rcases List.mem_flatMap.mp hy with ⟨q, _hq, hy⟩
  by_contra hweight
  have hweight' :
      ¬ lowerWeight ≤ y.word.weight HEAddres.weight := by
    simpa [SPFactor.ofMonomial] using hweight
  have hlt : q + 1 < lowerWeight := by
    rw [← R.word_weight_factors hy]
    omega
  rw [hR (q + 1) hlt] at hy
  simp at hy

end CHRecipe

/--
A semantic normalizer for all physically truncated signed-polynomial factor
lists supported in one lower-weight stratum.
-/
structure TSNormalc
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    Prop where
  normalize :
    ∀ {ι : Type} (source : List (SPFactor H ι)),
      SPFactor.IsTruncated n source →
      SPFactor.WordWeightLeast lowerWeight source →
        ∃ coordinates : CHRecipe H ι,
          coordinates.NTBelow lowerWeight ∧
            ∀ e : ι → HEFam H,
              SPFactor.listEval (n := n) e
                  (coordinates.polynomialFactors (n := n)) =
                SPFactor.listEval (n := n) e source

namespace TSPkt

/-- A truncated polynomial correction packet is physically truncated as a list. -/
lemma isTruncated_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A) :
    SPFactor.IsTruncated n C.factors :=
  fun x hx => C.word_weight_cutoff x hx

/-- Corrections emitted from a supported left parent lie in the next stratum. -/
lemma least_succ_left
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (hB : lowerWeight ≤ B.word.weight HEAddres.weight) :
    SPFactor.WordWeightLeast
      (lowerWeight + 1) C.factors := by
  intro x hx
  have hxrise := C.word_weight_left x hx
  omega

/-- Corrections emitted from a supported right parent lie in the next stratum. -/
lemma least_succ_right
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (hA : lowerWeight ≤ A.word.weight HEAddres.weight) :
    SPFactor.WordWeightLeast
      (lowerWeight + 1) C.factors := by
  intro x hx
  have hxrise := C.word_weight_right x hx
  omega

end TSPkt

/--
A semantically normalized polynomial correction packet.  Its canonical recipe
endpoint remains in the next support stratum and evaluates to the commutator
required by the parent swap.
-/
structure TSNorm
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    (lowerWeight : ℕ)
    (C : TSPkt n B A) where
  coordinates :
    CHRecipe H ι
  coordinates_no_below :
    coordinates.NTBelow (lowerWeight + 1)
  list_eval_coordinates :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e
          (coordinates.polynomialFactors (n := n)) =
        ⁅B.eval (n := n) e, A.eval (n := n) e⁆

namespace TSPkt

/--
Delegate a polynomial correction packet to the next-stratum normalizer using
the support of its left parent.
-/
lemma normalization_left
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (hB : lowerWeight ≤ B.word.weight HEAddres.weight)
    (normalizer :
      TSNormalc
        (n := n) (lowerWeight := lowerWeight + 1) H) :
    Nonempty
      (TSNorm
        lowerWeight C) := by
  rcases normalizer.normalize C.factors C.isTruncated_factors
      (C.least_succ_left hB) with
    ⟨coordinates, hcoordinatesSupported, hcoordinates⟩
  exact ⟨{
    coordinates := coordinates
    coordinates_no_below := hcoordinatesSupported
    list_eval_coordinates := fun e =>
      (hcoordinates e).trans (C.listEval_eq e) }⟩

/--
Delegate a polynomial correction packet to the next-stratum normalizer using
the support of its right parent.
-/
lemma semantic_normalization
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (hA : lowerWeight ≤ A.word.weight HEAddres.weight)
    (normalizer :
      TSNormalc
        (n := n) (lowerWeight := lowerWeight + 1) H) :
    Nonempty
      (TSNorm
        lowerWeight C) := by
  rcases normalizer.normalize C.factors C.isTruncated_factors
      (C.least_succ_right hA) with
    ⟨coordinates, hcoordinatesSupported, hcoordinates⟩
  exact ⟨{
    coordinates := coordinates
    coordinates_no_below := hcoordinatesSupported
    list_eval_coordinates := fun e =>
      (hcoordinates e).trans (C.listEval_eq e) }⟩

end TSPkt

/--
A supported polynomial semantic normalizer constructs the product form of
Claim 8 directly from the indexed source list.
-/
theorem data_semantic_normalizer
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (normalizer :
      TSNormalc
        (n := n) (lowerWeight := 1) H) :
    CollectedCoordinateData (n := n) H e := by
  let source :=
    (indexedSymbolicFactors (n := n) H e).map
      SPFactor.ofMonomial
  rcases normalizer.normalize source
      (SPFactor.truncated_monomial
        (SCFactor.truncated_indexed_factors
          H e))
      (SPFactor.word_least_one source) with
    ⟨coordinates, _hcoordinatesSupported, hcoordinates⟩
  let input : Fin e.length → HEFam H := fun j => e.get j
  refine ⟨coordinates.eval input, ?_, ?_⟩
  · exact (coordinates.list_polynomial_factors input).symm.trans
      ((hcoordinates input).trans
        ((SPFactor.list_eval_monomial input
            (indexedSymbolicFactors (n := n) H e)).trans
          (indexed_symbolic_factors H e)))
  · intro s _hs _hsn i
    exact coordinates.combination_weighted_monomials
      input s i

/--
A supported polynomial semantic normalizer constructs the inverse form of
Claim 8 directly from the reversed negated source list.
-/
theorem collected_semantic_normalizer
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (normalizer :
      TSNormalc
        (n := n) (lowerWeight := 1) H) :
    CollectedInverseData (n := n) H e := by
  let source :=
    (symbolicInverseFactors (n := n) H).map
      SPFactor.ofMonomial
  rcases normalizer.normalize source
      (SPFactor.truncated_monomial
        (SCFactor.truncated_symbolic_factors H))
      (SPFactor.word_least_one source) with
    ⟨coordinates, _hcoordinatesSupported, hcoordinates⟩
  let input : Fin 1 → HEFam H :=
    fun _ => negExponentFamily e
  refine ⟨coordinates.eval input, ?_, ?_⟩
  · exact (coordinates.list_polynomial_factors input).symm.trans
      ((hcoordinates input).trans
        ((SPFactor.list_eval_monomial input
            (symbolicInverseFactors (n := n) H)).trans
          (list_symbolic_factors H e)))
  · intro s _hs _hsn i
    exact coordinates.combination_weighted_monomials
      input s i

end TCTex
end Submission

/-!
# Normalized semantic obstruction steps for product and inverse collection

A lower-stratum signed-polynomial Hall collector swaps two obstructing factors
by emitting a strictly higher-weight correction packet.  Once a semantic
normalizer for the next stratum is available, that raw packet can immediately
be replaced by its canonical coordinate-recipe endpoint.

This file packages the resulting obstruction step.  It proves exact evaluation
preservation, physical truncation, lower-support preservation, and closure
under finite contexts and rewrite runs.  These are the operational invariants
needed by a one-stratum product and inverse scheduler.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

namespace TSNorm

/--
The normalized correction endpoint performs the same adjacent swap as its raw
truncated polynomial packet.
-/
lemma list_mul_swap
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    (normalization :
      TSNorm
        lowerWeight C)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e
          (normalization.coordinates.polynomialFactors (n := n)) *
        A.eval (n := n) e * B.eval (n := n) e =
      B.eval (n := n) e * A.eval (n := n) e := by
  rw [normalization.list_eval_coordinates]
  simp [commutatorElement_def, mul_assoc]

/-- Normalized correction factors remain in the next support stratum. -/
lemma factors_least_succ
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    (normalization :
      TSNorm
        lowerWeight C) :
    SPFactor.WordWeightLeast (lowerWeight + 1)
      (normalization.coordinates.polynomialFactors (n := n)) :=
  normalization.coordinates.least_no_below
    normalization.coordinates_no_below

/-- Canonical normalized correction endpoints are physically truncated. -/
lemma polynomial_factors_truncated
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    (normalization :
      TSNorm
        lowerWeight C) :
    SPFactor.IsTruncated n
      (normalization.coordinates.polynomialFactors (n := n)) :=
  normalization.coordinates.truncated_polynomial_factors

end TSNorm

/--
One lower-stratum semantic obstruction step.  The emitted raw packet has
already been normalized one stratum higher.
-/
inductive SSColl
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (lowerWeight : ℕ) :
    List (SPFactor H ι) →
      List (SPFactor H ι) → Prop where
  | obstruction
      (P S : List (SPFactor H ι))
      (B A : SPFactor H ι)
      (C : TSPkt n B A)
      (normalization :
        TSNorm
          lowerWeight C) :
      SSColl H ι
        lowerWeight
        (P ++ [B, A] ++ S)
        (P ++ normalization.coordinates.polynomialFactors (n := n) ++
          [A, B] ++ S)

/-- One normalized semantic obstruction preserves evaluation exactly. -/
lemma SSColl.listEval_eq
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      SSColl
        (n := n) H ι lowerWeight L R)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e R =
      SPFactor.listEval (n := n) e L := by
  cases h with
  | obstruction P S B A C normalization =>
      calc
        SPFactor.listEval (n := n) e
              (P ++ normalization.coordinates.polynomialFactors (n := n) ++
                [A, B] ++ S) =
            SPFactor.listEval e P *
                (SPFactor.listEval e
                    (normalization.coordinates.polynomialFactors (n := n)) *
                  A.eval e * B.eval e) *
              SPFactor.listEval e S := by
            simp [mul_assoc]
        _ =
            SPFactor.listEval e P *
                (B.eval e * A.eval e) *
              SPFactor.listEval e S := by
            rw [normalization.list_mul_swap]
        _ =
            SPFactor.listEval (n := n) e
              (P ++ [B, A] ++ S) := by
            simp [mul_assoc]

/-- One normalized semantic obstruction preserves physical truncation. -/
lemma SSColl.isTruncated
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      SSColl
        (n := n) H ι lowerWeight L R)
    (hL : SPFactor.IsTruncated n L) :
    SPFactor.IsTruncated n R := by
  cases h with
  | obstruction P S B A C normalization =>
      intro x hx
      rcases List.mem_append.mp hx with hx | hxS
      · rcases List.mem_append.mp hx with hx | hxAB
        · rcases List.mem_append.mp hx with hxP | hxCorrection
          · exact hL x (by simp [hxP])
          · exact normalization.polynomial_factors_truncated x hxCorrection
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxAB
          rcases hxAB with hxA | hxB
          · exact hL x (by simp [hxA])
          · exact hL x (by simp [hxB])
      · exact hL x (by simp [hxS])

/-- One normalized semantic obstruction preserves the current support stratum. -/
lemma SSColl.wordWeightLeast
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      SSColl
        (n := n) H ι lowerWeight L R)
    (hL : SPFactor.WordWeightLeast lowerWeight L) :
    SPFactor.WordWeightLeast lowerWeight R := by
  cases h with
  | obstruction P S B A C normalization =>
      intro x hx
      rcases List.mem_append.mp hx with hx | hxS
      · rcases List.mem_append.mp hx with hx | hxAB
        · rcases List.mem_append.mp hx with hxP | hxCorrection
          · exact hL x (by simp [hxP])
          · exact
              (Nat.le_succ lowerWeight).trans
                (normalization.factors_least_succ
                  x hxCorrection)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxAB
          rcases hxAB with hxA | hxB
          · exact hL x (by simp [hxA])
          · exact hL x (by simp [hxB])
      · exact hL x (by simp [hxS])

/-- Normalized semantic obstruction steps remain valid inside list contexts. -/
lemma SSColl.context
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      SSColl
        (n := n) H ι lowerWeight L R)
    (P S : List (SPFactor H ι)) :
    SSColl
      (n := n) H ι lowerWeight
      (P ++ L ++ S) (P ++ R ++ S) := by
  cases h with
  | obstruction P0 S0 B A C normalization =>
      simpa [List.append_assoc] using
        (SSColl.obstruction
          (P ++ P0) (S0 ++ S) B A C normalization)

/-- Finite runs of normalized semantic obstruction steps. -/
abbrev SSRw
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (L R : List (SPFactor H ι)) :
    Prop :=
  Relation.ReflTransGen
    (SSColl
      (n := n) H ι lowerWeight) L R

namespace SSRw

/-- Any finite normalized semantic obstruction run preserves evaluation. -/
lemma listEval_eq
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      SSRw
        (n := n) (lowerWeight := lowerWeight) L R)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e R =
      SPFactor.listEval (n := n) e L := by
  induction h with
  | refl => rfl
  | tail hLR hstep ih =>
      exact (hstep.listEval_eq e).trans ih

/-- Finite normalized semantic obstruction runs preserve physical truncation. -/
lemma isTruncated
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      SSRw
        (n := n) (lowerWeight := lowerWeight) L R)
    (hL : SPFactor.IsTruncated n L) :
    SPFactor.IsTruncated n R := by
  induction h with
  | refl => exact hL
  | tail hLR hstep ih =>
      exact hstep.isTruncated ih

/-- Finite normalized semantic obstruction runs preserve lower support. -/
lemma wordWeightLeast
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      SSRw
        (n := n) (lowerWeight := lowerWeight) L R)
    (hL : SPFactor.WordWeightLeast lowerWeight L) :
    SPFactor.WordWeightLeast lowerWeight R := by
  induction h with
  | refl => exact hL
  | tail hLR hstep ih =>
      exact hstep.wordWeightLeast ih

/-- Finite normalized semantic obstruction runs remain valid inside contexts. -/
lemma context
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      SSRw
        (n := n) (lowerWeight := lowerWeight) L R)
    (P S : List (SPFactor H ι)) :
    SSRw
      (n := n) (lowerWeight := lowerWeight)
      (P ++ L ++ S) (P ++ R ++ S) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hLR hstep ih =>
      exact Relation.ReflTransGen.tail ih (hstep.context P S)

end SSRw

namespace TSPkt

/--
Using the support of the left parent, delegate a raw correction packet upward
and obtain one normalized semantic obstruction step.
-/
lemma supported_semantic_left
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (P S : List (SPFactor H ι))
    (B A : SPFactor H ι)
    (C : TSPkt n B A)
    (hB : lowerWeight ≤ B.word.weight HEAddres.weight)
    (normalizer :
      TSNormalc
        (n := n) (lowerWeight := lowerWeight + 1) H) :
    ∃ normalization :
        TSNorm
          lowerWeight C,
      SSColl
        (n := n) H ι lowerWeight
        (P ++ [B, A] ++ S)
        (P ++ normalization.coordinates.polynomialFactors (n := n) ++
          [A, B] ++ S) := by
  rcases C.normalization_left hB normalizer with
    ⟨normalization⟩
  exact ⟨normalization,
    SSColl.obstruction
      P S B A C normalization⟩

/--
Using the support of the right parent, delegate a raw correction packet upward
and obtain one normalized semantic obstruction step.
-/
lemma supported_semantic_right
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (P S : List (SPFactor H ι))
    (B A : SPFactor H ι)
    (C : TSPkt n B A)
    (hA : lowerWeight ≤ A.word.weight HEAddres.weight)
    (normalizer :
      TSNormalc
        (n := n) (lowerWeight := lowerWeight + 1) H) :
    ∃ normalization :
        TSNorm
          lowerWeight C,
      SSColl
        (n := n) H ι lowerWeight
        (P ++ [B, A] ++ S)
        (P ++ normalization.coordinates.polynomialFactors (n := n) ++
          [A, B] ++ S) := by
  rcases C.semantic_normalization hA normalizer with
    ⟨normalization⟩
  exact ⟨normalization,
    SSColl.obstruction
      P S B A C normalization⟩

end TSPkt

end TCTex
end Submission

/-!
# Semantic coordinate-endpoint insertion for product and inverse collection

A universal signed-polynomial Hall collector may be assembled incrementally.
Once a prefix has been normalized into canonical coordinate recipes, the
remaining local obligation is to insert one additional physically truncated
factor into that endpoint.

This file packages a support-bounded semantic insertion kernel and folds it
across finite source lists.  It also supplies the terminal normalizer at the
nilpotent cutoff: a physically truncated list supported in stratum
`lowerWeight` is empty once `n ≤ lowerWeight`.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace CHRecipe

/-- The canonical coordinate endpoint with no factors. -/
def empty
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) :
    CHRecipe H ι where
  recipes _ _ := []

@[simp]
lemma weightFactors_empty
    {d s : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) :
    (empty H ι).weightFactors s = [] := by
  simp [weightFactors, empty]

@[simp]
lemma prefixFactors_empty
    {d k : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) :
    (empty H ι).prefixFactors k = [] := by
  simp [prefixFactors]

@[simp]
lemma factors_empty
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) :
    (empty H ι).factors (n := n) = [] := by
  simp [factors]

@[simp]
lemma polynomialFactors_empty
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) :
    (empty H ι).polynomialFactors (n := n) = [] := by
  simp [polynomialFactors]

/-- The empty endpoint has no terms below every support bound. -/
lemma no_below_empty
    {d lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) :
    (empty H ι).NTBelow lowerWeight := by
  intro s _hs
  exact weightFactors_empty H ι

end CHRecipe

/--
A support-bounded semantic endpoint insertion kernel.  It inserts one retained
signed-polynomial factor into a canonical coordinate endpoint while preserving
evaluation for every input exponent family.
-/
structure TSInsertc
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    Prop where
  insert :
    ∀ {ι : Type}
      (coordinates : CHRecipe H ι)
      (factor : SPFactor H ι),
      coordinates.NTBelow lowerWeight →
      lowerWeight ≤ factor.word.weight HEAddres.weight →
      factor.word.weight HEAddres.weight < n →
        ∃ next : CHRecipe H ι,
          next.NTBelow lowerWeight ∧
            ∀ e : ι → HEFam H,
              SPFactor.listEval (n := n) e
                  (next.polynomialFactors (n := n)) =
                SPFactor.listEval (n := n) e
                  (coordinates.polynomialFactors (n := n) ++ [factor])

namespace TSInsertc

/--
Repeated semantic endpoint insertion normalizes every finite physically
truncated source list in the supported stratum.
-/
lemma exists_normalization
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (kernel :
      TSInsertc
        (n := n) (lowerWeight := lowerWeight) H) :
    ∀ source : List (SPFactor H ι),
      SPFactor.IsTruncated n source →
      SPFactor.WordWeightLeast lowerWeight source →
        ∃ coordinates : CHRecipe H ι,
          coordinates.NTBelow lowerWeight ∧
            ∀ e : ι → HEFam H,
              SPFactor.listEval (n := n) e
                  (coordinates.polynomialFactors (n := n)) =
                SPFactor.listEval (n := n) e source := by
  intro source hsourceTruncated hsourceSupported
  induction source using List.reverseRecOn with
  | nil =>
      refine ⟨CHRecipe.empty H ι, ?_, ?_⟩
      · exact CHRecipe.no_below_empty H ι
      · intro e
        simp
  | append_singleton initial factor ih =>
      have hinitialTruncated :
          SPFactor.IsTruncated n initial := by
        intro x hx
        exact hsourceTruncated x (by simp [hx])
      have hinitialSupported :
          SPFactor.WordWeightLeast lowerWeight
            initial := by
        intro x hx
        exact hsourceSupported x (by simp [hx])
      have hfactorSupported :
          lowerWeight ≤ factor.word.weight HEAddres.weight :=
        hsourceSupported factor (by simp)
      have hfactorTruncated :
          factor.word.weight HEAddres.weight < n :=
        hsourceTruncated factor (by simp)
      rcases ih hinitialTruncated hinitialSupported with
        ⟨coordinates, hcoordinatesSupported, hcoordinates⟩
      rcases kernel.insert coordinates factor hcoordinatesSupported
          hfactorSupported hfactorTruncated with
        ⟨next, hnextSupported, hnext⟩
      refine ⟨next, hnextSupported, ?_⟩
      intro e
      calc
        SPFactor.listEval (n := n) e
              (next.polynomialFactors (n := n)) =
            SPFactor.listEval (n := n) e
              (coordinates.polynomialFactors (n := n) ++ [factor]) :=
          hnext e
        _ = SPFactor.listEval (n := n) e
              (coordinates.polynomialFactors (n := n)) *
            factor.eval (n := n) e := by
          rw [SPFactor.listEval_append]
          simp
        _ = SPFactor.listEval (n := n) e initial *
            factor.eval (n := n) e := by
          rw [hcoordinates e]
        _ = SPFactor.listEval (n := n) e
              (initial ++ [factor]) := by
          rw [SPFactor.listEval_append]
          simp

end TSInsertc

namespace TSNormalc

/-- Endpoint insertion folds to a semantic normalizer for the same stratum. -/
def ofInsertionKernel
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (kernel :
      TSInsertc
        (n := n) (lowerWeight := lowerWeight) H) :
    TSNormalc
      (n := n) (lowerWeight := lowerWeight) H where
  normalize := kernel.exists_normalization

/--
At or above the nilpotent cutoff, every physically truncated supported source
list is empty, so the empty coordinate endpoint is the terminal normal form.
-/
def of_cutoff
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hcutoff : n ≤ lowerWeight) :
    TSNormalc
      (n := n) (lowerWeight := lowerWeight) H where
  normalize source hsourceTruncated hsourceSupported := by
    have hsource : source = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro x hx
      have hlt := hsourceTruncated x hx
      have hge := hsourceSupported x hx
      omega
    subst source
    exact
      ⟨CHRecipe.empty H _,
        CHRecipe.no_below_empty H _,
        by intro e; simp⟩

end TSNormalc

end TCTex
end Submission
