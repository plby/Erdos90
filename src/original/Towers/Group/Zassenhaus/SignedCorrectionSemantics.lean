import Towers.Group.Zassenhaus.Polynomial
import Mathlib.Data.Multiset.DershowitzManna
import Towers.Group.Zassenhaus.IntegerScaling
import Towers.Group.Zassenhaus.Active

open scoped IsMulCommutative


/-!
# Signed semantic delegation of product and inverse Hall corrections

Signed Hall-Petresco collection must terminate in signed coordinate recipes:
the correction formulas produced by nonterminal swaps carry arbitrary integer
coefficients.  This file gives that endpoint its semantic normalizer, the
nilpotent-cutoff base case, and the higher-stratum delegation interface for
raw correction packets.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

namespace CCRecipe

/-- The canonical signed coordinate endpoint with no factors. -/
def empty
    {d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) :
    CCRecipe H ι where
  formulas _ _ := []

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

/-- The empty signed endpoint has no terms below every support bound. -/
lemma no_below_empty
    {d lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type) :
    (empty H ι).NTBelow lowerWeight := by
  intro s _hs
  exact weightFactors_empty H ι

end CCRecipe

/--
A signed semantic normalizer for all physically truncated polynomial-factor
lists supported in one ordinary Hall-weight stratum.
-/
structure TSNormal
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    Prop where
  normalize :
    ∀ source : List (SPFactor H ι),
      SPFactor.IsTruncated n source →
      SPFactor.WordWeightLeast lowerWeight source →
        ∃ coordinates : CCRecipe H ι,
          coordinates.NTBelow lowerWeight ∧
            ∀ e : ι → HEFam H,
              SPFactor.listEval (n := n) e
                  (coordinates.factors (n := n)) =
                SPFactor.listEval (n := n) e source

namespace TSNormal

/--
At or above the nilpotent cutoff, physical truncation and support force the
source list to be empty.
-/
def of_cutoff
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hcutoff : n ≤ lowerWeight) :
    TSNormal
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
      ⟨CCRecipe.empty H _,
        CCRecipe.no_below_empty H _,
        by intro e; simp⟩

end TSNormal

/--
A semantically normalized polynomial correction packet whose endpoint stores
signed formulas directly.
-/
structure TPSem
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    (lowerWeight : ℕ)
    (C : TSPkt n B A) where
  coordinates :
    CCRecipe H ι
  coordinates_no_below :
    coordinates.NTBelow (lowerWeight + 1)
  list_eval_coordinates :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e
          (coordinates.factors (n := n)) =
        ⁅B.eval (n := n) e, A.eval (n := n) e⁆

namespace TSPkt

/--
Delegate a raw correction packet to a signed next-stratum normalizer using
the support of its left parent.
-/
lemma semantic_normalization_left
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (hB : lowerWeight ≤ B.word.weight HEAddres.weight)
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1) H) :
    Nonempty
      (TPSem
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
Delegate a raw correction packet to a signed next-stratum normalizer using
the support of its right parent.
-/
lemma semantic_normalization_right
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (hA : lowerWeight ≤ A.word.weight HEAddres.weight)
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1) H) :
    Nonempty
      (TPSem
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
A signed semantic normalizer constructs the product form of Claim 8 directly
from the indexed source list.
-/
theorem signed_semantic_normalizer
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (normalizer :
      TSNormal
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
  · exact (coordinates.listEval_factors input).symm.trans
      ((hcoordinates input).trans
        ((SPFactor.list_eval_monomial input
            (indexedSymbolicFactors (n := n) H e)).trans
          (indexed_symbolic_factors H e)))
  · intro s _hs _hsn i
    exact coordinates.combination_weighted_monomials
      input s i

/--
A signed semantic normalizer constructs the inverse form of Claim 8 directly
from the reversed negated source list.
-/
theorem collected_data_normalizer
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (normalizer :
      TSNormal
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
  · exact (coordinates.listEval_factors input).symm.trans
      ((hcoordinates input).trans
        ((SPFactor.list_eval_monomial input
            (symbolicInverseFactors (n := n) H)).trans
          (list_symbolic_factors H e)))
  · intro s _hs _hsn i
    exact coordinates.combination_weighted_monomials
      input s i

end TCTex
end Towers

/-!
# Signed semantic obstruction steps for product and inverse collection

A lower-stratum Hall collector swaps an obstructing adjacent pair and emits a
strictly higher correction packet.  Once that packet has been normalized into
signed coordinate recipes, it can be inserted immediately before the swapped
pair.  This file packages that step and its finite rewrite closure.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

namespace TPSem

/-- A signed normalized correction endpoint performs its required swap. -/
lemma list_mul_swap
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    (normalization :
      TPSem
        lowerWeight C)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e
          (normalization.coordinates.factors (n := n)) *
        A.eval (n := n) e * B.eval (n := n) e =
      B.eval (n := n) e * A.eval (n := n) e := by
  rw [normalization.list_eval_coordinates]
  simp [commutatorElement_def, mul_assoc]

/-- Signed normalized corrections remain in the next support stratum. -/
lemma weight_least_succ
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    (normalization :
      TPSem
        lowerWeight C) :
    SPFactor.WordWeightLeast (lowerWeight + 1)
      (normalization.coordinates.factors (n := n)) :=
  normalization.coordinates.no_terms_below
    normalization.coordinates_no_below

/-- Signed normalized correction endpoints are physically truncated. -/
lemma factors_isTruncated
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    (normalization :
      TPSem
        lowerWeight C) :
    SPFactor.IsTruncated n
      (normalization.coordinates.factors (n := n)) :=
  normalization.coordinates.isTruncated_factors

end TPSem

/-- One adjacent obstruction step with a signed normalized correction block. -/
inductive TSSem
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
        TPSem
          lowerWeight C) :
      TSSem
        H ι lowerWeight
        (P ++ [B, A] ++ S)
        (P ++ normalization.coordinates.factors (n := n) ++ [A, B] ++ S)

/-- One signed normalized obstruction preserves evaluation exactly. -/
lemma TSSem.listEval_eq
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      TSSem
        (n := n) H ι lowerWeight L R)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e R =
      SPFactor.listEval (n := n) e L := by
  cases h with
  | obstruction P S B A C normalization =>
      calc
        SPFactor.listEval (n := n) e
              (P ++ normalization.coordinates.factors (n := n) ++
                [A, B] ++ S) =
            SPFactor.listEval e P *
                (SPFactor.listEval e
                    (normalization.coordinates.factors (n := n)) *
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

/-- One signed normalized obstruction preserves physical truncation. -/
lemma TSSem.isTruncated
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      TSSem
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
          · exact normalization.factors_isTruncated x hxCorrection
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxAB
          rcases hxAB with hxA | hxB
          · exact hL x (by simp [hxA])
          · exact hL x (by simp [hxB])
      · exact hL x (by simp [hxS])

/-- One signed normalized obstruction preserves its support stratum. -/
lemma TSSem.wordWeightLeast
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      TSSem
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
                (normalization.weight_least_succ
                  x hxCorrection)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxAB
          rcases hxAB with hxA | hxB
          · exact hL x (by simp [hxA])
          · exact hL x (by simp [hxB])
      · exact hL x (by simp [hxS])

/-- Signed semantic obstruction steps remain valid inside list contexts. -/
lemma TSSem.context
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      TSSem
        (n := n) H ι lowerWeight L R)
    (P S : List (SPFactor H ι)) :
    TSSem
      (n := n) H ι lowerWeight
      (P ++ L ++ S) (P ++ R ++ S) := by
  cases h with
  | obstruction P0 S0 B A C normalization =>
      simpa [List.append_assoc] using
        (TSSem.obstruction
          (P ++ P0) (S0 ++ S) B A C normalization)

/-- Finite runs of signed normalized semantic obstruction steps. -/
abbrev TSRw
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (L R : List (SPFactor H ι)) :
    Prop :=
  Relation.ReflTransGen
    (TSSem
      (n := n) H ι lowerWeight) L R

namespace TSRw

/-- A single signed normalized obstruction is a finite rewrite run. -/
lemma single
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      TSSem
        (n := n) H ι lowerWeight L R) :
    TSRw
      (n := n) (lowerWeight := lowerWeight) L R :=
  Relation.ReflTransGen.single h

/-- Any finite signed normalized obstruction run preserves evaluation. -/
lemma listEval_eq
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      TSRw
        (n := n) (lowerWeight := lowerWeight) L R)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e R =
      SPFactor.listEval (n := n) e L := by
  induction h with
  | refl => rfl
  | tail hLR hstep ih =>
      exact (hstep.listEval_eq e).trans ih

/-- Finite signed obstruction runs preserve physical truncation. -/
lemma isTruncated
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      TSRw
        (n := n) (lowerWeight := lowerWeight) L R)
    (hL : SPFactor.IsTruncated n L) :
    SPFactor.IsTruncated n R := by
  induction h with
  | refl => exact hL
  | tail hLR hstep ih =>
      exact hstep.isTruncated ih

/-- Finite signed obstruction runs preserve lower support. -/
lemma wordWeightLeast
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      TSRw
        (n := n) (lowerWeight := lowerWeight) L R)
    (hL : SPFactor.WordWeightLeast lowerWeight L) :
    SPFactor.WordWeightLeast lowerWeight R := by
  induction h with
  | refl => exact hL
  | tail hLR hstep ih =>
      exact hstep.wordWeightLeast ih

/-- Finite signed obstruction runs remain valid inside contexts. -/
lemma context
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      TSRw
        (n := n) (lowerWeight := lowerWeight) L R)
    (P S : List (SPFactor H ι)) :
    TSRw
      (n := n) (lowerWeight := lowerWeight)
      (P ++ L ++ S) (P ++ R ++ S) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hLR hstep ih =>
      exact Relation.ReflTransGen.tail ih (hstep.context P S)

end TSRw

namespace TSPkt

/-- Delegate one raw correction packet upward and obtain a signed swap step. -/
lemma supported_semantic_collection
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (P S : List (SPFactor H ι))
    (B A : SPFactor H ι)
    (C : TSPkt n B A)
    (hB : lowerWeight ≤ B.word.weight HEAddres.weight)
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1) H) :
    ∃ normalization :
        TPSem
          lowerWeight C,
      TSSem
        (n := n) H ι lowerWeight
        (P ++ [B, A] ++ S)
        (P ++ normalization.coordinates.factors (n := n) ++ [A, B] ++ S) := by
  rcases C.semantic_normalization_left hB normalizer with
    ⟨normalization⟩
  exact
    ⟨normalization,
      TSSem.obstruction
        P S B A C normalization⟩

end TSPkt

end TCTex
end Towers

/-!
# Sharp signed semantic normalization of polynomial Hall corrections

The ambient signed collector normalizes a correction packet one stratum above
its current support bound.  Recursive routing through a higher tail needs a
stronger invariant: after crossing a parent of actual weight `parentWeight`,
normalize the emitted correction packet at support `parentWeight + 1`.

This file packages exact-parent normalization, weakening back to a coarser
ambient stratum, and families of normalizers available at every support bound.
It is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace CCRecipe

/-- A stronger lower-support bound may be exposed at any weaker stratum. -/
lemma NTBelow.mono
    {d lowerWeight strongerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {R : CCRecipe H ι}
    (hR : R.NTBelow strongerWeight)
    (hbound : lowerWeight ≤ strongerWeight) :
    R.NTBelow lowerWeight := by
  intro s hs
  exact hR s (hs.trans_le hbound)

end CCRecipe

namespace TPSem

/--
A sharply normalized signed correction endpoint may be exposed through an
interface requesting any weaker parent support bound.
-/
def weaken
    {d n lowerWeight strongerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    (normalization :
      TPSem
        strongerWeight C)
    (hbound : lowerWeight ≤ strongerWeight) :
    TPSem
      lowerWeight C where
  coordinates := normalization.coordinates
  coordinates_no_below :=
    normalization.coordinates_no_below.mono
      (Nat.add_le_add_right hbound 1)
  list_eval_coordinates := normalization.list_eval_coordinates

end TPSem

namespace TSPkt

/-- Normalize a correction packet at the exact weight of its left parent. -/
lemma nonempty_signed_normalization
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (normalizer :
      TSNormal
        (n := n)
        (lowerWeight := B.word.weight HEAddres.weight + 1) H) :
    Nonempty
      (TPSem
        (B.word.weight HEAddres.weight) C) :=
  C.semantic_normalization_left (Nat.le_refl _) normalizer

/-- Normalize a correction packet at the exact weight of its right parent. -/
lemma nonempty_normalization_weight
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (normalizer :
      TSNormal
        (n := n)
        (lowerWeight := A.word.weight HEAddres.weight + 1) H) :
    Nonempty
      (TPSem
        (A.word.weight HEAddres.weight) C) :=
  C.semantic_normalization_right (Nat.le_refl _) normalizer

/-- Choose the sharply normalized endpoint supported above the left parent. -/
noncomputable def semantic_normalization_weight
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (normalizer :
      TSNormal
        (n := n)
        (lowerWeight := B.word.weight HEAddres.weight + 1) H) :
    TPSem
      (B.word.weight HEAddres.weight) C :=
  Classical.choice
    (C.nonempty_signed_normalization normalizer)

/-- Choose the sharply normalized endpoint supported above the right parent. -/
noncomputable def signed_semantic_normalization
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (normalizer :
      TSNormal
        (n := n)
        (lowerWeight := A.word.weight HEAddres.weight + 1) H) :
    TPSem
      (A.word.weight HEAddres.weight) C :=
  Classical.choice
    (C.nonempty_normalization_weight normalizer)

end TSPkt

/-- A signed semantic coordinate normalizer available at every support bound. -/
structure SNFam
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  normalizer :
    ∀ lowerWeight : ℕ,
      TSNormal
        (n := n) (lowerWeight := lowerWeight) H

namespace SNFam

/-- Choose the correction endpoint normalized sharply above its left parent. -/
noncomputable def semantic_normalization_weight
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (family :
      SNFam
        (n := n) H)
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A) :
    TPSem
      (B.word.weight HEAddres.weight) C :=
  C.semantic_normalization_weight
    (family.normalizer (B.word.weight HEAddres.weight + 1))

/-- Choose the correction endpoint normalized sharply above its right parent. -/
noncomputable def signed_semantic_normalization
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (family :
      SNFam
        (n := n) H)
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A) :
    TPSem
      (A.word.weight HEAddres.weight) C :=
  C.signed_semantic_normalization
    (family.normalizer (A.word.weight HEAddres.weight + 1))

/-- Choose a left-parent-sharp endpoint at a weaker ambient support stratum. -/
noncomputable def normalization_left_sharp
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (family :
      SNFam
        (n := n) H)
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (hB : lowerWeight ≤ B.word.weight HEAddres.weight) :
    TPSem
      lowerWeight C :=
  (family.semantic_normalization_weight C).weaken hB

/-- Choose a right-parent-sharp endpoint at a weaker ambient support stratum. -/
noncomputable def signed_normalization_sharp
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (family :
      SNFam
        (n := n) H)
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (hA : lowerWeight ≤ A.word.weight HEAddres.weight) :
    TPSem
      lowerWeight C :=
  (family.signed_semantic_normalization C).weaken hA

end SNFam

end TCTex
end Towers

/-!
# Signed semantic coordinate insertion for product and inverse collection

A universal signed-polynomial Hall collector may be assembled incrementally.
Once a finite prefix has been normalized into signed coordinate recipes, the
remaining local obligation is to insert one retained polynomial factor into
that endpoint.  This file packages the local insertion kernel and folds it
across arbitrary finite supported source lists.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
A support-bounded signed semantic endpoint insertion kernel.  It inserts one
retained polynomial factor while preserving evaluation for every exponent
family.
-/
structure SSInsert
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    Prop where
  insert :
    ∀ (coordinates : CCRecipe H ι)
      (factor : SPFactor H ι),
      coordinates.NTBelow lowerWeight →
      lowerWeight ≤ factor.word.weight HEAddres.weight →
      factor.word.weight HEAddres.weight < n →
        ∃ next : CCRecipe H ι,
          next.NTBelow lowerWeight ∧
            ∀ e : ι → HEFam H,
              SPFactor.listEval (n := n) e
                  (next.factors (n := n)) =
                SPFactor.listEval (n := n) e
                  (coordinates.factors (n := n) ++ [factor])

namespace SSInsert

/--
Repeated signed endpoint insertion normalizes every finite physically
truncated source list in the supported stratum.
-/
lemma exists_normalization
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (kernel :
      SSInsert
        (n := n) (lowerWeight := lowerWeight) H) :
    ∀ source : List (SPFactor H ι),
      SPFactor.IsTruncated n source →
      SPFactor.WordWeightLeast lowerWeight source →
        ∃ coordinates : CCRecipe H ι,
          coordinates.NTBelow lowerWeight ∧
            ∀ e : ι → HEFam H,
              SPFactor.listEval (n := n) e
                  (coordinates.factors (n := n)) =
                SPFactor.listEval (n := n) e source := by
  intro source hsourceTruncated hsourceSupported
  induction source using List.reverseRecOn with
  | nil =>
      refine ⟨CCRecipe.empty H ι, ?_, ?_⟩
      · exact CCRecipe.no_below_empty H ι
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
              (next.factors (n := n)) =
            SPFactor.listEval (n := n) e
              (coordinates.factors (n := n) ++ [factor]) :=
          hnext e
        _ = SPFactor.listEval (n := n) e
              (coordinates.factors (n := n)) *
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

end SSInsert

namespace TSNormal

/-- Signed endpoint insertion folds to a semantic normalizer for one stratum. -/
def ofInsertionKernel
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (kernel :
      SSInsert
        (n := n) (lowerWeight := lowerWeight) H) :
    TSNormal
      (n := n) (lowerWeight := lowerWeight) H where
  normalize := kernel.exists_normalization

end TSNormal

end TCTex
end Towers

/-!
# Multiset descent for sharp signed polynomial Hall corrections

When an active signed polynomial factor crosses a higher-tail parent, normalize
the emitted correction packet sharply above the crossed parent's actual
weight.  Every retained correction factor then has strictly smaller cutoff
defect than that parent.  Replacing one parent by the finite correction block
decreases the Dershowitz-Manna order on multisets of cutoff defects.

This file is intentionally not imported by the existing collection proof.
-/

namespace Multiset

/-- Replacing one multiset element by finitely many smaller elements descends. -/
lemma dershowitz_manna_forall
    {α : Type*}
    [Preorder α]
    {X Y : Multiset α}
    {a : α}
    (hY : ∀ y ∈ Y, y < a) :
    IsDershowitzMannaLT (X + Y) (X + {a}) :=
  ⟨X, Y, {a}, by simp, rfl, rfl, fun y hy => ⟨a, by simp, hY y hy⟩⟩

end Multiset

namespace Towers
namespace TCTex

universe u

namespace SPFactor

/-- The cutoff-minus-weight defect of one signed polynomial Hall factor. -/
def cutoffDefect
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ)
    (x : SPFactor H ι) :
    ℕ :=
  n - x.word.weight HEAddres.weight

/-- The unordered multiset of cutoff defects carried by a signed factor list. -/
def cutoffDefectMultiset
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ)
    (L : List (SPFactor H ι)) :
    Multiset ℕ :=
  (L.map (cutoffDefect n) : Multiset ℕ)

@[simp]
lemma defect_multiset_nil
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type} :
    cutoffDefectMultiset (H := H) (ι := ι) n [] = ∅ := by
  simp [cutoffDefectMultiset]

@[simp]
lemma defect_multiset_append
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (L R : List (SPFactor H ι)) :
    cutoffDefectMultiset n (L ++ R) =
      cutoffDefectMultiset n L + cutoffDefectMultiset n R := by
  simp [cutoffDefectMultiset]

@[simp]
lemma cutoff_multiset_singleton
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (x : SPFactor H ι) :
    cutoffDefectMultiset n [x] = {cutoffDefect n x} := by
  simp [cutoffDefectMultiset]

/-- List descent induced by Dershowitz-Manna descent on cutoff defects. -/
def CutoffDefectMultiset
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ)
    (L R : List (SPFactor H ι)) :
    Prop :=
  Multiset.IsDershowitzMannaLT
    (cutoffDefectMultiset n L) (cutoffDefectMultiset n R)

/-- Cutoff-defect multiset descent is well founded on signed factor lists. -/
lemma well_founded_defect
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type} :
    WellFounded (CutoffDefectMultiset (H := H) (ι := ι) n) := by
  exact
    InvImage.wf (cutoffDefectMultiset (H := H) (ι := ι) n)
      Multiset.wellFounded_isDershowitzMannaLT

end SPFactor

namespace TPSem

/-- Sharp left-parent normalization strictly lowers every retained defect. -/
lemma factors_defect_left
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    (normalization :
      TPSem
        (B.word.weight HEAddres.weight) C)
    {x : SPFactor H ι}
    (hx : x ∈ normalization.coordinates.factors (n := n)) :
    SPFactor.cutoffDefect n x <
      SPFactor.cutoffDefect n B := by
  have hxSupported := normalization.weight_least_succ x hx
  have hxTruncated := normalization.factors_isTruncated x hx
  simp only [SPFactor.cutoffDefect]
  omega

/-- Sharp right-parent normalization strictly lowers every retained defect. -/
lemma factors_defect_right
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    (normalization :
      TPSem
        (A.word.weight HEAddres.weight) C)
    {x : SPFactor H ι}
    (hx : x ∈ normalization.coordinates.factors (n := n)) :
    SPFactor.cutoffDefect n x <
      SPFactor.cutoffDefect n A := by
  have hxSupported := normalization.weight_least_succ x hx
  have hxTruncated := normalization.factors_isTruncated x hx
  simp only [SPFactor.cutoffDefect]
  omega

/-- Replacing a left parent by its sharp correction endpoint descends. -/
lemma multisetAppendSingleton
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    (normalization :
      TPSem
        (B.word.weight HEAddres.weight) C)
    (P : List (SPFactor H ι)) :
    SPFactor.CutoffDefectMultiset n
      (P ++ normalization.coordinates.factors (n := n)) (P ++ [B]) := by
  unfold SPFactor.CutoffDefectMultiset
  rw [SPFactor.defect_multiset_append,
    SPFactor.defect_multiset_append,
    SPFactor.cutoff_multiset_singleton]
  apply Multiset.dershowitz_manna_forall
  intro y hy
  rw [SPFactor.cutoffDefectMultiset] at hy
  rcases List.mem_map.mp (Multiset.mem_coe.mp hy) with ⟨x, hx, rfl⟩
  exact normalization.factors_defect_left hx

/-- Replacing a right parent by its sharp correction endpoint descends. -/
lemma defectMultisetSingleton
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {B A : SPFactor H ι}
    {C : TSPkt n B A}
    (normalization :
      TPSem
        (A.word.weight HEAddres.weight) C)
    (P : List (SPFactor H ι)) :
    SPFactor.CutoffDefectMultiset n
      (P ++ normalization.coordinates.factors (n := n)) (P ++ [A]) := by
  unfold SPFactor.CutoffDefectMultiset
  rw [SPFactor.defect_multiset_append,
    SPFactor.defect_multiset_append,
    SPFactor.cutoff_multiset_singleton]
  apply Multiset.dershowitz_manna_forall
  intro y hy
  rw [SPFactor.cutoffDefectMultiset] at hy
  rcases List.mem_map.mp (Multiset.mem_coe.mp hy) with ⟨x, hx, rfl⟩
  exact normalization.factors_defect_right hx

end TPSem

namespace SNFam

/-- The selected sharp left-parent endpoint decreases cutoff-defect multisets. -/
lemma semantic_normalization_multiset
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (family :
      SNFam
        (n := n) H)
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (P : List (SPFactor H ι)) :
    SPFactor.CutoffDefectMultiset n
      (P ++
        (family.semantic_normalization_weight C).coordinates.factors
          (n := n))
      (P ++ [B]) :=
  TPSem.multisetAppendSingleton
    (family.semantic_normalization_weight C) P

/-- Weak exposure of a sharp left endpoint preserves its descent witness. -/
lemma sharp_defect_multiset
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (family :
      SNFam
        (n := n) H)
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (hB : lowerWeight ≤ B.word.weight HEAddres.weight)
    (P : List (SPFactor H ι)) :
    SPFactor.CutoffDefectMultiset n
      (P ++
        (family.normalization_left_sharp C hB).coordinates.factors
          (n := n))
      (P ++ [B]) := by
  simpa [normalization_left_sharp] using
    family.semantic_normalization_multiset
      C P

/-- The selected sharp right-parent endpoint decreases cutoff-defect multisets. -/
lemma normalization_defect_multiset
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (family :
      SNFam
        (n := n) H)
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (P : List (SPFactor H ι)) :
    SPFactor.CutoffDefectMultiset n
      (P ++
        (family.signed_semantic_normalization C).coordinates.factors
          (n := n))
      (P ++ [A]) :=
  let normalization := family.signed_semantic_normalization C
  normalization.defectMultisetSingleton P

/-- Weak exposure of a sharp right endpoint preserves its descent witness. -/
lemma normalization_sharp_multiset
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (family :
      SNFam
        (n := n) H)
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (hA : lowerWeight ≤ A.word.weight HEAddres.weight)
    (P : List (SPFactor H ι)) :
    SPFactor.CutoffDefectMultiset n
      (P ++
        (family.signed_normalization_sharp C hA).coordinates.factors
          (n := n))
      (P ++ [A]) := by
  simpa [signed_normalization_sharp] using
    family.normalization_defect_multiset
      C P

end SNFam

end TCTex
end Towers

/-!
# Filtration recursion for signed product and inverse polynomial normalizers

Signed polynomial correction packets rise strictly in ordinary Hall weight.
Consequently, a collector at `lowerWeight` may recursively call the normalizer
at `lowerWeight + 1`.  At or above the nilpotent cutoff every supported,
physically truncated source list is empty.

This file isolates the local signed insertion obligation and packages the
well-founded filtration recursion around it.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
The local signed scheduler obligation at one support stratum: assuming the
next-stratum normalizer, insert one retained factor into a signed coordinate
endpoint at the current stratum.
-/
structure TSInsert
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    Prop where
  insert :
    ∀ lowerWeight : ℕ,
      TSNormal
          (n := n) (lowerWeight := lowerWeight + 1) H →
        SSInsert
          (n := n) (lowerWeight := lowerWeight) H

namespace TSNormal

/--
Successive-stratum signed insertion plus the cutoff terminal case constructs
a signed semantic normalizer at every support stratum.
-/
noncomputable def recInsertionStep
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (step :
      TSInsert
        (n := n) H)
    (lowerWeight : ℕ) :
    TSNormal
      (n := n) (lowerWeight := lowerWeight) H :=
  if hterminal : n ≤ lowerWeight then
    of_cutoff H hterminal
  else
    ofInsertionKernel
      (step.insert lowerWeight
        (recInsertionStep H step (lowerWeight + 1)))
termination_by n - lowerWeight
decreasing_by omega

end TSNormal

/--
A recursive signed one-stratum insertion constructor supplies product
recollection polynomials.
-/
theorem collected_semantic_insertion
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (step :
      TSInsert
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  open TSNormal in
    signed_semantic_normalizer
      H e (recInsertionStep H step 1)

/--
A recursive signed one-stratum insertion constructor supplies inverse
recollection polynomials.
-/
theorem recursive_insertion_step
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (step :
      TSInsert
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  open TSNormal in
    collected_data_normalizer
      H e (recInsertionStep H step 1)

end TCTex
end Towers

/-!
# Weight strata of signed product and inverse polynomial endpoints

Signed coordinate recipes are concatenated in increasing ordinary Hall
weight.  A filtration-recursive scheduler needs to separate the visible
prefix through one active stratum from its strictly higher tail.  This file
packages that decomposition directly in the signed polynomial state.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace CCRecipe

/-- Signed endpoint factors in weights strictly above `lowerWeight`. -/
def tailFactors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    (lowerWeight : ℕ) :
    List (SPFactor H ι) :=
  (List.range' lowerWeight (n - 1 - lowerWeight)).flatMap fun s =>
    R.weightFactors (s + 1)

/-- The signed prefix and higher tail concatenate back to the full endpoint. -/
lemma factors_append_tail
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
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

/-- Every signed higher-tail factor lies in the next support stratum. -/
lemma word_tail_factors
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    {x : SPFactor H ι}
    (hx : x ∈ R.tailFactors (n := n) lowerWeight) :
    lowerWeight + 1 ≤ x.word.weight HEAddres.weight := by
  rcases List.mem_flatMap.mp hx with ⟨s, hs, hx⟩
  rw [R.word_weight_factors hx]
  have hsLower : lowerWeight ≤ s :=
    List.left_le_of_mem_range' hs
  omega

/-- The signed higher tail is supported one stratum above its prefix. -/
lemma word_least_factors
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι) :
    SPFactor.WordWeightLeast (lowerWeight + 1)
      (R.tailFactors (n := n) lowerWeight) :=
  fun _ hx => R.word_tail_factors hx

/-- The signed higher tail remains physically below the quotient cutoff. -/
lemma truncated_factors
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    (hlowerWeight : lowerWeight ≤ n - 1) :
    SPFactor.IsTruncated n
      (R.tailFactors (n := n) lowerWeight) := by
  intro x hx
  apply R.isTruncated_factors
  rw [R.factors_append_tail hlowerWeight]
  exact List.mem_append_right _ hx

/-- If one layer lies below endpoint support, its signed block is empty. -/
lemma nil_terms_below
    {d lowerWeight s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    (hR : R.NTBelow lowerWeight)
    (hs : s < lowerWeight) :
    R.weightFactors s = [] :=
  hR s hs

/--
If no terms occur below a positive support stratum, the endpoint prefix
through that stratum is exactly its current-weight block.
-/
lemma prefix_no_below
    {d lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
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
A supported signed endpoint splits into its active layer followed by a tail
supported one stratum higher.
-/
lemma append_no_below
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    (hR : R.NTBelow lowerWeight)
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightCutoff : lowerWeight ≤ n - 1) :
    R.factors (n := n) =
      R.weightFactors lowerWeight ++ R.tailFactors (n := n) lowerWeight := by
  rw [R.factors_append_tail hlowerWeightCutoff,
    R.prefix_no_below hR hlowerWeightPos]

end CCRecipe

end TCTex
end Towers

/-!
# Canonical higher-tail splicing for signed polynomial coordinates

At one active Hall-weight stratum, inserting a strictly heavier signed factor
does not change the current coordinate block.  The old higher tail together
with the new factor can be normalized one stratum higher, then spliced back
above the untouched active block.

This file implements that splice and proves the automatic strictly-heavier
insertion branch.  The remaining local recollection problem is therefore the
active-weight branch.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace CCRecipe

/-- Keep the base signed recipes through one stratum and use `higher` above it. -/
def spliceHigherTail
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (base higher : CCRecipe H ι)
    (lowerWeight : ℕ) :
    CCRecipe H ι where
  formulas s i :=
    if s ≤ lowerWeight then base.formulas s i else higher.formulas s i

@[simp]
lemma formulas_splice_higher
    {d lowerWeight s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (base higher : CCRecipe H ι)
    (hs : s ≤ lowerWeight)
    (i : (H s).index) :
    (base.spliceHigherTail higher lowerWeight).formulas s i =
      base.formulas s i := by
  simp [spliceHigherTail, hs]

@[simp]
lemma formulas_splice_tail
    {d lowerWeight s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (base higher : CCRecipe H ι)
    (hs : lowerWeight < s)
    (i : (H s).index) :
    (base.spliceHigherTail higher lowerWeight).formulas s i =
      higher.formulas s i := by
  simp [spliceHigherTail, Nat.not_le_of_lt hs]

/-- Through the splice stratum, fixed-weight factors come from the base. -/
lemma splice_higher_tail
    {d lowerWeight s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (base higher : CCRecipe H ι)
    (hs : s ≤ lowerWeight) :
    (base.spliceHigherTail higher lowerWeight).weightFactors s =
      base.weightFactors s := by
  unfold weightFactors
  apply List.flatMap_congr
  intro i _hi
  rw [base.formulas_splice_higher higher hs]

/-- Strictly above the splice stratum, fixed-weight factors come from `higher`. -/
lemma factors_splice_higher
    {d lowerWeight s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (base higher : CCRecipe H ι)
    (hs : lowerWeight < s) :
    (base.spliceHigherTail higher lowerWeight).weightFactors s =
      higher.weightFactors s := by
  unfold weightFactors
  apply List.flatMap_congr
  intro i _hi
  rw [base.formulas_splice_tail higher hs]

/-- Splicing preserves the lower support bound of the base endpoint. -/
lemma no_below_splice
    {d lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (base higher : CCRecipe H ι)
    (hbase : base.NTBelow lowerWeight) :
    (base.spliceHigherTail higher lowerWeight).NTBelow lowerWeight := by
  intro s hs
  rw [base.splice_higher_tail higher (by omega)]
  exact hbase s hs

/-- Any signed endpoint supported above a prefix has no factors in that prefix. -/
lemma nil_no_below
    {d lowerWeight k : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    (hR : R.NTBelow lowerWeight)
    (hk : k < lowerWeight) :
    R.prefixFactors k = [] := by
  unfold prefixFactors
  apply List.flatMap_eq_nil_iff.2
  intro s hs
  apply R.nil_terms_below hR
  have hsRange := List.mem_range.mp hs
  omega

/-- The spliced signed higher tail is exactly the tail supplied by `higher`. -/
lemma tail_splice_higher
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (base higher : CCRecipe H ι) :
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
exactly its tail above `lowerWeight`.
-/
lemma factors_no_below
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (higher : CCRecipe H ι)
    (hhigher : higher.NTBelow (lowerWeight + 1))
    (hlowerWeightCutoff : lowerWeight ≤ n - 1) :
    higher.factors (n := n) =
      higher.tailFactors (n := n) lowerWeight := by
  rw [higher.factors_append_tail hlowerWeightCutoff,
    higher.nil_no_below hhigher (by omega)]
  rfl

/--
The signed factors of a supported splice are the untouched active block
followed by the complete normalized higher endpoint.
-/
lemma factors_higher_tail
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (base higher : CCRecipe H ι)
    (hbase : base.NTBelow lowerWeight)
    (hhigher : higher.NTBelow (lowerWeight + 1))
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightCutoff : lowerWeight ≤ n - 1) :
    (base.spliceHigherTail higher lowerWeight).factors (n := n) =
      base.weightFactors lowerWeight ++ higher.factors (n := n) := by
  rw [append_no_below
        (base.spliceHigherTail higher lowerWeight)
        (base.no_below_splice higher hbase)
          hlowerWeightPos hlowerWeightCutoff,
    base.splice_higher_tail higher (Nat.le_refl _),
    base.tail_splice_higher higher,
    ← higher.factors_no_below
      hhigher hlowerWeightCutoff]

end CCRecipe

namespace TSNormal

/--
Insert a factor strictly above a positive active stratum by normalizing the
old higher tail together with the factor and splicing it back above the
untouched active block.
-/
lemma insertion_pos_weight
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1) H)
    (coordinates : CCRecipe H ι)
    (factor : SPFactor H ι)
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hfactorWeight :
      lowerWeight < factor.word.weight HEAddres.weight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    ∃ next : CCRecipe H ι,
      next.NTBelow lowerWeight ∧
        ∀ e : ι → HEFam H,
          SPFactor.listEval (n := n) e
              (next.factors (n := n)) =
            SPFactor.listEval (n := n) e
              (coordinates.factors (n := n) ++ [factor]) := by
  have hlowerWeightCutoff : lowerWeight ≤ n - 1 := by
    omega
  have htailTruncated :
      SPFactor.IsTruncated n
        (coordinates.tailFactors (n := n) lowerWeight) :=
    coordinates.truncated_factors hlowerWeightCutoff
  have htailSupported :
      SPFactor.WordWeightLeast (lowerWeight + 1)
        (coordinates.tailFactors (n := n) lowerWeight) :=
    coordinates.word_least_factors
  have hsourceTruncated :
      SPFactor.IsTruncated n
        (coordinates.tailFactors (n := n) lowerWeight ++ [factor]) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact htailTruncated x hx
    · rcases List.mem_singleton.mp hx with rfl
      exact hfactorTruncated
  have hsourceSupported :
      SPFactor.WordWeightLeast (lowerWeight + 1)
        (coordinates.tailFactors (n := n) lowerWeight ++ [factor]) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact htailSupported x hx
    · rcases List.mem_singleton.mp hx with rfl
      omega
  rcases normalizer.normalize
      (coordinates.tailFactors (n := n) lowerWeight ++ [factor])
      hsourceTruncated hsourceSupported with
    ⟨higher, hhigher, hhigherEval⟩
  refine
    ⟨coordinates.spliceHigherTail higher lowerWeight,
      coordinates.no_below_splice higher hcoordinates, ?_⟩
  intro e
  rw [coordinates.factors_higher_tail higher hcoordinates hhigher
      hlowerWeightPos hlowerWeightCutoff,
    coordinates.append_no_below
      hcoordinates hlowerWeightPos hlowerWeightCutoff,
    SPFactor.listEval_append,
    SPFactor.listEval_append,
    hhigherEval e,
    SPFactor.listEval_append,
    SPFactor.listEval_append]
  simp [mul_assoc]

/--
At stratum zero, delegate the complete signed endpoint plus the inserted
factor to the next-stratum normalizer.
-/
lemma insertion_zero
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := 1) H)
    (coordinates : CCRecipe H ι)
    (factor : SPFactor H ι)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    ∃ next : CCRecipe H ι,
      next.NTBelow 0 ∧
        ∀ e : ι → HEFam H,
          SPFactor.listEval (n := n) e
              (next.factors (n := n)) =
            SPFactor.listEval (n := n) e
              (coordinates.factors (n := n) ++ [factor]) := by
  have hsourceTruncated :
      SPFactor.IsTruncated n
        (coordinates.factors (n := n) ++ [factor]) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact coordinates.isTruncated_factors x hx
    · rcases List.mem_singleton.mp hx with rfl
      exact hfactorTruncated
  have hsourceSupported :
      SPFactor.WordWeightLeast 1
        (coordinates.factors (n := n) ++ [factor]) := by
    intro x _hx
    exact x.word_weight_pos
  rcases normalizer.normalize
      (coordinates.factors (n := n) ++ [factor])
      hsourceTruncated hsourceSupported with
    ⟨next, _hnextSupported, hnextEval⟩
  exact ⟨next, fun _s hs => False.elim (by omega), hnextEval⟩

/-- Delegate any signed insertion strictly above the active stratum. -/
lemma insertion_word_weight
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1) H)
    (coordinates : CCRecipe H ι)
    (factor : SPFactor H ι)
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hfactorWeight :
      lowerWeight < factor.word.weight HEAddres.weight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    ∃ next : CCRecipe H ι,
      next.NTBelow lowerWeight ∧
        ∀ e : ι → HEFam H,
          SPFactor.listEval (n := n) e
              (next.factors (n := n)) =
            SPFactor.listEval (n := n) e
              (coordinates.factors (n := n) ++ [factor]) := by
  by_cases hlowerWeight : lowerWeight = 0
  · subst lowerWeight
    exact normalizer.insertion_zero coordinates factor
      hfactorTruncated
  · exact normalizer.insertion_pos_weight coordinates
      factor hcoordinates (by omega) hfactorWeight hfactorTruncated

end TSNormal

/-- The genuinely nontrivial signed local branch is active-weight insertion. -/
structure SupportedInsertionBranch
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    Prop where
  insert :
    ∀ lowerWeight : ℕ,
      TSNormal
          (n := n) (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CCRecipe H ι)
          (factor : SPFactor H ι),
          coordinates.NTBelow lowerWeight →
          factor.word.weight HEAddres.weight = lowerWeight →
          factor.word.weight HEAddres.weight < n →
            ∃ next : CCRecipe H ι,
              next.NTBelow lowerWeight ∧
                ∀ e : ι → HEFam H,
                  SPFactor.listEval (n := n) e
                      (next.factors (n := n)) =
                    SPFactor.listEval (n := n) e
                      (coordinates.factors (n := n) ++ [factor])

namespace TSInsert

/--
Strictly heavier insertions are automatic by signed tail delegation.  An
active-weight insertion branch supplies the complete recursive signed step.
-/
def insertion_branch
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (active :
      SupportedInsertionBranch
        (n := n) H) :
    TSInsert
      (n := n) H where
  insert lowerWeight normalizer := {
    insert := by
      intro ι (coordinates : CCRecipe H ι)
        (factor : SPFactor H _)
        hcoordinates hfactorSupported hfactorTruncated
      by_cases hfactorStrict :
          lowerWeight < factor.word.weight HEAddres.weight
      · exact normalizer.insertion_word_weight coordinates factor
          hcoordinates hfactorStrict hfactorTruncated
      · exact active.insert lowerWeight normalizer coordinates factor
          hcoordinates (by omega) hfactorTruncated }

end TSInsert

/-- An active signed insertion branch constructs product recollection data. -/
theorem active_insertion_branch
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (active :
      SupportedInsertionBranch
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  open TSInsert in
    collected_semantic_insertion
      H e (insertion_branch active)

/-- An active signed insertion branch constructs inverse recollection data. -/
theorem collected_insertion_branch
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (active :
      SupportedInsertionBranch
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  open TSInsert in
    recursive_insertion_step
      H e (insertion_branch active)

end TCTex
end Towers

/-!
# One-stratum scheduling for signed product and inverse polynomials

A recursive signed Hall collector works one ordinary weight stratum at a time.
At the current stratum, a normalized endpoint is its visible fixed-weight
block followed by a tail supported one stratum higher.

This file packages that endpoint view and exposes the operational scheduler
obligation: finite signed normalized obstruction rewrites must insert one
factor into the endpoint.  Such a schedule supplies the semantic insertion
step consumed by filtration recursion.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/-- A signed coordinate endpoint viewed at one active ordinary weight stratum. -/
structure CSView
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (lowerWeight : ℕ)
    (coordinates : CCRecipe H ι) :
    Prop where
  lowerWeight_pos : 1 ≤ lowerWeight
  lowerWeight_cutoff : lowerWeight ≤ n - 1
  coordinates_no_below : coordinates.NTBelow lowerWeight

namespace CSView

/-- The normalized signed endpoint block at the active stratum. -/
def currentFactors
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CCRecipe H ι}
    (_view :
      CSView
        (n := n) lowerWeight coordinates) :
    List (SPFactor H ι) :=
  coordinates.weightFactors lowerWeight

/-- The normalized signed endpoint tail strictly above the active stratum. -/
def higherFactors
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CCRecipe H ι}
    (_view :
      CSView
        (n := n) lowerWeight coordinates) :
    List (SPFactor H ι) :=
  coordinates.tailFactors (n := n) lowerWeight

/-- The signed endpoint is its active block followed by its higher tail. -/
lemma factors_current_higher
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CCRecipe H ι}
    (view :
      CSView
        (n := n) lowerWeight coordinates) :
    coordinates.factors (n := n) =
      view.currentFactors ++ view.higherFactors :=
  coordinates.append_no_below
    view.coordinates_no_below view.lowerWeight_pos
      view.lowerWeight_cutoff

/-- Every active-block factor has exactly the active ordinary weight. -/
lemma word_current_factors
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CCRecipe H ι}
    (view :
      CSView
        (n := n) lowerWeight coordinates)
    {x : SPFactor H ι}
    (hx : x ∈ view.currentFactors) :
    x.word.weight HEAddres.weight = lowerWeight :=
  coordinates.word_weight_factors hx

/-- The signed active block is supported at the active stratum. -/
lemma least_current_factors
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CCRecipe H ι}
    (view :
      CSView
        (n := n) lowerWeight coordinates) :
    SPFactor.WordWeightLeast lowerWeight
      view.currentFactors := by
  intro x hx
  rw [view.word_current_factors hx]

/-- The signed higher tail is supported one stratum above the active block. -/
lemma least_higher_factors
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CCRecipe H ι}
    (view :
      CSView
        (n := n) lowerWeight coordinates) :
    SPFactor.WordWeightLeast (lowerWeight + 1)
      view.higherFactors :=
  coordinates.word_least_factors

/-- The signed higher tail remains below the quotient cutoff. -/
lemma truncated_higher_factors
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CCRecipe H ι}
    (view :
      CSView
        (n := n) lowerWeight coordinates) :
    SPFactor.IsTruncated n view.higherFactors :=
  coordinates.truncated_factors view.lowerWeight_cutoff

end CSView

namespace TSRw

/-- Finite signed normalized obstruction runs compose under concatenation. -/
lemma append
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L₁ R₁ L₂ R₂ : List (SPFactor H ι)}
    (hleft :
      TSRw
        (n := n) (lowerWeight := lowerWeight) L₁ R₁)
    (hright :
      TSRw
        (n := n) (lowerWeight := lowerWeight) L₂ R₂) :
    TSRw
      (n := n) (lowerWeight := lowerWeight)
      (L₁ ++ L₂) (R₁ ++ R₂) := by
  have hleft' :
      TSRw
        (n := n) (lowerWeight := lowerWeight)
        (L₁ ++ L₂) (R₁ ++ L₂) := by
    simpa using hleft.context [] L₂
  have hright' :
      TSRw
        (n := n) (lowerWeight := lowerWeight)
        (R₁ ++ L₂) (R₁ ++ R₂) := by
    simpa using hright.context R₁ []
  exact hleft'.trans hright'

end TSRw

/--
The operational signed one-stratum scheduler obligation.  Assuming correction
packets can already be normalized one stratum higher, inserting one factor is
witnessed by finite signed normalized obstruction rewrites.
-/
structure RISched
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    Prop where
  insert :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      TSNormal
          (n := n) (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CCRecipe H ι)
          (factor : SPFactor H ι),
          coordinates.NTBelow lowerWeight →
          lowerWeight ≤ factor.word.weight HEAddres.weight →
          factor.word.weight HEAddres.weight < n →
            ∃ next : CCRecipe H ι,
              next.NTBelow lowerWeight ∧
                TSRw
                  (n := n) (lowerWeight := lowerWeight)
                  (coordinates.factors (n := n) ++ [factor])
                  (next.factors (n := n))

namespace RISched

/-- An operational signed schedule supplies the recursive semantic step. -/
def recursiveInsertionStep
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (schedule :
      RISched
        (n := n) H) :
    TSInsert
      (n := n) H where
  insert lowerWeight normalizer := {
    insert := by
      intro ι coordinates factor hcoordinates hfactorSupported hfactorTruncated
      rcases schedule.insert lowerWeight normalizer coordinates factor
          hcoordinates hfactorSupported hfactorTruncated with
        ⟨next, hnextSupported, hrewrites⟩
      exact ⟨next, hnextSupported, hrewrites.listEval_eq⟩ }

end RISched

/-- An operational signed schedule constructs product recollection data. -/
theorem collected_recursive_insertion
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (schedule :
      RISched
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  collected_semantic_insertion
    H e schedule.recursiveInsertionStep

/-- An operational signed schedule constructs inverse recollection data. -/
theorem recursive_insertion_schedule
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (schedule :
      RISched
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  recursive_insertion_step
    H e schedule.recursiveInsertionStep

end TCTex
end Towers

/-!
# Active-layer resolutions for signed polynomial coordinates

After strictly heavier insertions have been delegated automa, the
remaining local operation occurs at one active Hall-weight stratum.  It must
replace the old signed endpoint followed by one active factor by:

* a new normalized signed coordinate block at the active weight; and
* a residual polynomial source supported strictly above that weight.

The next-stratum normalizer recollects the residual source, and canonical tail
splicing assembles the final endpoint.  This file packages that reduction and
a collector-facing finite-rewrite route interface.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/-- The semantic output of resolving one active-weight signed insertion. -/
structure TPResolu
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (coordinates : CCRecipe H ι)
    (factor : SPFactor H ι) where
  activeCoordinates :
    CCRecipe H ι
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
          (activeCoordinates.weightFactors lowerWeight ++ higherSource) =
        SPFactor.listEval (n := n) e
          (coordinates.factors (n := n) ++ [factor])

namespace TPResolu

/--
Normalize the strictly higher residual source and splice it above the updated
signed active coordinate block.
-/
lemma exists_insertion
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CCRecipe H ι}
    {factor : SPFactor H ι}
    (resolution :
      TPResolu
        (n := n) (lowerWeight := lowerWeight) H ι coordinates factor)
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1) H)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    ∃ next : CCRecipe H ι,
      next.NTBelow lowerWeight ∧
        ∀ e : ι → HEFam H,
          SPFactor.listEval (n := n) e
              (next.factors (n := n)) =
            SPFactor.listEval (n := n) e
              (coordinates.factors (n := n) ++ [factor]) := by
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
  rw [resolution.activeCoordinates.factors_higher_tail higher
      resolution.active_terms_below hhigher hlowerWeightPos
        hlowerWeightCutoff,
    SPFactor.listEval_append,
    hhigherEval e,
    ← SPFactor.listEval_append]
  exact resolution.active_append_source e

end TPResolu

/-- A supply of signed semantic active-layer resolutions. -/
structure
  SRFtry
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  resolve :
    ∀ {ι : Type}
      (lowerWeight : ℕ)
      (coordinates : CCRecipe H ι)
      (factor : SPFactor H ι),
      coordinates.NTBelow lowerWeight →
      factor.word.weight HEAddres.weight = lowerWeight →
      factor.word.weight HEAddres.weight < n →
        TPResolu
          (n := n) (lowerWeight := lowerWeight) H ι coordinates factor

namespace
  SRFtry

/-- Signed active-layer resolutions supply the active insertion branch. -/
def insertionBranch
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      SRFtry
        (n := n) H) :
    SupportedInsertionBranch
      (n := n) H where
  insert lowerWeight normalizer coordinates factor hcoordinates hfactorWeight
      hfactorTruncated :=
    (factory.resolve lowerWeight coordinates factor hcoordinates hfactorWeight
      hfactorTruncated).exists_insertion normalizer hfactorWeight
        hfactorTruncated

/-- Signed resolutions supply the complete recursive insertion step. -/
def recursiveInsertionStep
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (factory :
      SRFtry
        (n := n) H) :
    TSInsert
      (n := n) H :=
  TSInsert.insertion_branch
    factory.insertionBranch

end SRFtry

/-- A finite signed-rewrite certificate for one active-layer insertion. -/
structure SSRoutea
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (coordinates : CCRecipe H ι)
    (factor : SPFactor H ι) where
  activeCoordinates :
    CCRecipe H ι
  active_terms_below :
    activeCoordinates.NTBelow lowerWeight
  higherSource :
    List (SPFactor H ι)
  higher_least_succ :
    SPFactor.WordWeightLeast (lowerWeight + 1)
      higherSource
  rewrites :
    TSRw
      (n := n) (lowerWeight := lowerWeight)
        (coordinates.factors (n := n) ++ [factor])
        (activeCoordinates.weightFactors lowerWeight ++ higherSource)

namespace SSRoutea

/-- A finite signed route supplies the corresponding semantic resolution. -/
def activeLayerResolution
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CCRecipe H ι}
    {factor : SPFactor H ι}
    (route :
      SSRoutea
        (n := n) (lowerWeight := lowerWeight) H ι coordinates factor)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TPResolu
      (n := n) (lowerWeight := lowerWeight) H ι coordinates factor where
  activeCoordinates := route.activeCoordinates
  active_terms_below :=
    route.active_terms_below
  higherSource := route.higherSource
  higher_source_truncated := by
    have houtput :
        SPFactor.IsTruncated n
          (route.activeCoordinates.weightFactors lowerWeight ++
            route.higherSource) :=
      route.rewrites.isTruncated (by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact coordinates.isTruncated_factors x hx
        · rcases List.mem_singleton.mp hx with rfl
          exact hfactorTruncated)
    intro x hx
    exact houtput x (List.mem_append_right _ hx)
  higher_least_succ :=
    route.higher_least_succ
  active_append_source := fun e =>
    route.rewrites.listEval_eq e

end SSRoutea

/-- A recursive finite signed-rewrite schedule for active-weight insertions. -/
structure RSRoutea
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  route :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      TSNormal
          (n := n) (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CCRecipe H ι)
          (factor : SPFactor H ι),
          coordinates.NTBelow lowerWeight →
          factor.word.weight HEAddres.weight = lowerWeight →
          factor.word.weight HEAddres.weight < n →
            SSRoutea
              (n := n) (lowerWeight := lowerWeight) H ι coordinates factor

namespace RSRoutea

/-- A signed active-layer route schedule supplies the active branch. -/
def insertionBranch
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (schedule :
      RSRoutea
        (n := n) H) :
    SupportedInsertionBranch
      (n := n) H where
  insert lowerWeight normalizer coordinates factor hcoordinates hfactorWeight
      hfactorTruncated :=
    ((schedule.route lowerWeight normalizer coordinates factor hcoordinates
      hfactorWeight hfactorTruncated).activeLayerResolution
        hfactorTruncated).exists_insertion normalizer hfactorWeight
          hfactorTruncated

/-- A signed active-layer route schedule supplies the recursive step. -/
def recursiveInsertionStep
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (schedule :
      RSRoutea
        (n := n) H) :
    TSInsert
      (n := n) H :=
  TSInsert.insertion_branch
    schedule.insertionBranch

end RSRoutea

/-- A signed active-layer resolution factory constructs product data. -/
theorem active_resolution_factory
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (factory :
      SRFtry
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  collected_semantic_insertion
    H e factory.recursiveInsertionStep

/-- A signed active-layer resolution factory constructs inverse data. -/
theorem collected_resolution_factory
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (factory :
      SRFtry
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  recursive_insertion_step
    H e factory.recursiveInsertionStep

/-- A signed active-layer route schedule constructs product data. -/
theorem active_route_schedule
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (schedule :
      RSRoutea
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  collected_semantic_insertion
    H e schedule.recursiveInsertionStep

/-- A signed active-layer route schedule constructs inverse data. -/
theorem collected_route_schedule
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (schedule :
      RSRoutea
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  recursive_insertion_step
    H e schedule.recursiveInsertionStep

end TCTex
end Towers

/-!
# List-valued signed semantic insertion derivations

The More3 collector recursively inserts one correction term before continuing
an obstructed insertion.  In the signed polynomial state, one delegated
correction packet normalizes to a whole list of higher-weight coordinate
factors.  This file packages that list-valued recursion and compiles its
certificates to finite signed normalized obstruction rewrites.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

mutual

  /-- A list-valued signed More3 insertion derivation for one stratum. -/
  inductive TSInsertb
      {d n : ℕ}
      (H : ∀ r : ℕ, BCWta.{u} d r)
      (ι : Type)
      (lowerWeight : ℕ) :
      List (SPFactor H ι) →
        SPFactor H ι →
          List (SPFactor H ι) → Prop where
    | nil
        (A : SPFactor H ι) :
        TSInsertb
          (n := n) H ι lowerWeight [] A [A]
    | append
        (P : List (SPFactor H ι))
        (B A : SPFactor H ι) :
        TSInsertb
          (n := n) H ι lowerWeight (P ++ [B]) A (P ++ [B, A])
    | obstruction
        (P : List (SPFactor H ι))
        (B A : SPFactor H ι)
        (C : TSPkt n B A)
        (normalization :
          TPSem
            lowerWeight C)
        {Q R : List (SPFactor H ι)}
        (hcorrections :
          SSInserta
            (n := n) H ι lowerWeight P
              (normalization.coordinates.factors (n := n)) Q)
        (hinsert :
          TSInsertb
            (n := n) H ι lowerWeight Q A R) :
        TSInsertb
          (n := n) H ι lowerWeight (P ++ [B]) A (R ++ [B])

  /-- Fold a normalized signed correction block into a preceding prefix. -/
  inductive SSInserta
      {d n : ℕ}
      (H : ∀ r : ℕ, BCWta.{u} d r)
      (ι : Type)
      (lowerWeight : ℕ) :
      List (SPFactor H ι) →
        List (SPFactor H ι) →
          List (SPFactor H ι) → Prop where
    | nil
        (P : List (SPFactor H ι)) :
        SSInserta
          (n := n) H ι lowerWeight P [] P
    | snoc
        (P source : List (SPFactor H ι))
        (A : SPFactor H ι)
        {Q R : List (SPFactor H ι)}
        (hsource :
          SSInserta
            (n := n) H ι lowerWeight P source Q)
        (hinsert :
          TSInsertb
            (n := n) H ι lowerWeight Q A R) :
        SSInserta
          (n := n) H ι lowerWeight P (source ++ [A]) R

end

namespace TSInsertb

/-- A signed insertion certificate compiles to finite obstruction rewrites. -/
lemma rewrites
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    {A : SPFactor H ι}
    (h :
      TSInsertb
        (n := n) H ι lowerWeight L A R) :
    TSRw
      (n := n) (lowerWeight := lowerWeight) (L ++ [A]) R := by
  refine
    TSInsertb.recOn
      (motive_1 := fun L A R _h =>
        TSRw
          (n := n) (lowerWeight := lowerWeight) (L ++ [A]) R)
      (motive_2 := fun P source R _h =>
        TSRw
          (n := n) (lowerWeight := lowerWeight) (P ++ source) R)
      h ?_ ?_ ?_ ?_ ?_
  · intro A
    simpa using
      (Relation.ReflTransGen.refl :
        TSRw
          (n := n) (lowerWeight := lowerWeight) [A] [A])
  · intro P B A
    simpa [List.append_assoc] using
      (Relation.ReflTransGen.refl :
        TSRw
          (n := n) (lowerWeight := lowerWeight)
          (P ++ [B, A]) (P ++ [B, A]))
  · intro P B A C normalization Q R hcorrections hinsert
      ihcorrections ihinsert
    have hswap :
        TSRw
          (n := n) (lowerWeight := lowerWeight)
          (P ++ [B, A])
          (P ++ normalization.coordinates.factors (n := n) ++ [A, B]) := by
      apply
        TSRw.single
      simpa using
        (TSSem.obstruction
          P [] B A C normalization)
    have hrouteCorrections :
        TSRw
          (n := n) (lowerWeight := lowerWeight)
          (P ++ normalization.coordinates.factors (n := n) ++ [A, B])
          (Q ++ [A, B]) := by
      simpa [List.append_assoc] using
        ihcorrections.context [] [A, B]
    have hrouteA :
        TSRw
          (n := n) (lowerWeight := lowerWeight)
          (Q ++ [A, B]) (R ++ [B]) := by
      simpa [List.append_assoc] using ihinsert.context [] [B]
    simpa [List.append_assoc] using
      hswap.trans (hrouteCorrections.trans hrouteA)
  · intro P
    simpa using
      (Relation.ReflTransGen.refl :
        TSRw
          (n := n) (lowerWeight := lowerWeight) P P)
  · intro P source A Q R hsource hinsert ihsource ihinsert
    have hroutePrefix :
        TSRw
          (n := n) (lowerWeight := lowerWeight)
          ((P ++ source) ++ [A]) (Q ++ [A]) := by
      simpa [List.append_assoc] using ihsource.context [] [A]
    simpa [List.append_assoc] using hroutePrefix.trans ihinsert

/-- A signed insertion certificate preserves evaluation exactly. -/
lemma listEval_eq
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    {A : SPFactor H ι}
    (h :
      TSInsertb
        (n := n) H ι lowerWeight L A R)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e R =
      SPFactor.listEval (n := n) e (L ++ [A]) :=
  h.rewrites.listEval_eq e

/-- A signed insertion certificate preserves physical truncation. -/
lemma isTruncated
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    {A : SPFactor H ι}
    (h :
      TSInsertb
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

/-- A signed insertion certificate preserves its support stratum. -/
lemma wordWeightLeast
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    {A : SPFactor H ι}
    (h :
      TSInsertb
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

end TSInsertb

namespace SSInserta

/-- A signed correction-block certificate compiles to finite rewrites. -/
lemma rewrites
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {P source R : List (SPFactor H ι)}
    (h :
      SSInserta
        (n := n) H ι lowerWeight P source R) :
    TSRw
      (n := n) (lowerWeight := lowerWeight) (P ++ source) R := by
  refine
    SSInserta.recOn
      (motive_1 := fun L A R _h =>
        TSRw
          (n := n) (lowerWeight := lowerWeight) (L ++ [A]) R)
      (motive_2 := fun P source R _h =>
        TSRw
          (n := n) (lowerWeight := lowerWeight) (P ++ source) R)
      h ?_ ?_ ?_ ?_ ?_
  · intro A
    simpa using
      (Relation.ReflTransGen.refl :
        TSRw
          (n := n) (lowerWeight := lowerWeight) [A] [A])
  · intro P B A
    simpa [List.append_assoc] using
      (Relation.ReflTransGen.refl :
        TSRw
          (n := n) (lowerWeight := lowerWeight)
          (P ++ [B, A]) (P ++ [B, A]))
  · intro P B A C normalization Q R hcorrections hinsert
      ihcorrections ihinsert
    have hswap :
        TSRw
          (n := n) (lowerWeight := lowerWeight)
          (P ++ [B, A])
          (P ++ normalization.coordinates.factors (n := n) ++ [A, B]) := by
      apply
        TSRw.single
      simpa using
        (TSSem.obstruction
          P [] B A C normalization)
    have hrouteCorrections :
        TSRw
          (n := n) (lowerWeight := lowerWeight)
          (P ++ normalization.coordinates.factors (n := n) ++ [A, B])
          (Q ++ [A, B]) := by
      simpa [List.append_assoc] using
        ihcorrections.context [] [A, B]
    have hrouteA :
        TSRw
          (n := n) (lowerWeight := lowerWeight)
          (Q ++ [A, B]) (R ++ [B]) := by
      simpa [List.append_assoc] using ihinsert.context [] [B]
    simpa [List.append_assoc] using
      hswap.trans (hrouteCorrections.trans hrouteA)
  · intro P
    simpa using
      (Relation.ReflTransGen.refl :
        TSRw
          (n := n) (lowerWeight := lowerWeight) P P)
  · intro P source A Q R hsource hinsert ihsource ihinsert
    have hroutePrefix :
        TSRw
          (n := n) (lowerWeight := lowerWeight)
          ((P ++ source) ++ [A]) (Q ++ [A]) := by
      simpa [List.append_assoc] using ihsource.context [] [A]
    simpa [List.append_assoc] using hroutePrefix.trans ihinsert

/-- Folding a signed correction block preserves evaluation exactly. -/
lemma listEval_eq
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {P source R : List (SPFactor H ι)}
    (h :
      SSInserta
        (n := n) H ι lowerWeight P source R)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e R =
      SPFactor.listEval (n := n) e (P ++ source) :=
  h.rewrites.listEval_eq e

/-- Folding a signed correction block preserves physical truncation. -/
lemma isTruncated
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {P source R : List (SPFactor H ι)}
    (h :
      SSInserta
        (n := n) H ι lowerWeight P source R)
    (hP : SPFactor.IsTruncated n P)
    (hsource : SPFactor.IsTruncated n source) :
    SPFactor.IsTruncated n R := by
  apply h.rewrites.isTruncated
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hP x hx
  · exact hsource x hx

/-- Folding a signed correction block preserves lower support. -/
lemma wordWeightLeast
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {P source R : List (SPFactor H ι)}
    (h :
      SSInserta
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

end SSInserta

namespace TSFtry

/--
A packet factory reduces one obstructed signed insertion to routing its
normalized higher correction block and continuing the original insertion.
-/
lemma supported_inserts_obstruction
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1) H)
    (P : List (SPFactor H ι))
    (B A : SPFactor H ι)
    (hB : lowerWeight ≤ B.word.weight HEAddres.weight)
    (hA : lowerWeight ≤ A.word.weight HEAddres.weight)
    (hcontinue :
      ∀ normalization :
          TPSem
            lowerWeight (factory.packet B A hB hA),
        ∃ Q R : List (SPFactor H ι),
          SSInserta
              (n := n) H ι lowerWeight P
                (normalization.coordinates.factors (n := n)) Q ∧
            TSInsertb
              (n := n) H ι lowerWeight Q A R) :
    ∃ R : List (SPFactor H ι),
      TSInsertb
        (n := n) H ι lowerWeight (P ++ [B]) A R := by
  rcases (factory.packet B A hB hA).semantic_normalization_left
      hB normalizer with
    ⟨normalization⟩
  rcases hcontinue normalization with ⟨Q, R, hcorrections, hinsert⟩
  exact
    ⟨R ++ [B],
      TSInsertb.obstruction
        P B A (factory.packet B A hB hA) normalization
          hcorrections hinsert⟩

end TSFtry

/-- Structured signed insertion derivations at every active stratum. -/
structure
  RIDerivaa
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    Prop where
  insert :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      TSNormal
          (n := n) (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CCRecipe H ι)
          (factor : SPFactor H ι),
          coordinates.NTBelow lowerWeight →
          lowerWeight ≤ factor.word.weight HEAddres.weight →
          factor.word.weight HEAddres.weight < n →
            ∃ next : CCRecipe H ι,
              next.NTBelow lowerWeight ∧
                TSInsertb
                  (n := n) H ι lowerWeight
                    (coordinates.factors (n := n)) factor
                      (next.factors (n := n))

namespace
  RIDerivaa

/-- Structured signed insertion derivations supply the finite-rewrite schedule. -/
def semanticInsertionSchedule
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (schedule :
      RIDerivaa
        (n := n) H) :
    RISched
      (n := n) H where
  insert lowerWeight normalizer coordinates factor hcoordinates
      hfactorSupported hfactorTruncated := by
    rcases schedule.insert lowerWeight normalizer coordinates factor
        hcoordinates hfactorSupported hfactorTruncated with
      ⟨next, hnextSupported, hinsert⟩
    exact ⟨next, hnextSupported, hinsert.rewrites⟩

end RIDerivaa

/-- Structured signed insertion derivations construct product recollection data. -/
theorem collected_insertion_derivation
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (schedule :
      RIDerivaa
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  collected_recursive_insertion
    H e schedule.semanticInsertionSchedule

/-- Structured signed insertion derivations construct inverse recollection data. -/
theorem semantic_insertion_derivation
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (schedule :
      RIDerivaa
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  recursive_insertion_schedule
    H e schedule.semanticInsertionSchedule

end TCTex
end Towers

/-!
# Residual routing inside a signed active polynomial layer

Absorbing one active-weight factor into a signed coordinate block may itself
emit strictly higher corrections.  Moving that factor left across the old
higher tail may emit further corrections.  Both residual sources begin in the
next support stratum, so they concatenate and delegate upward together.

This file packages that honest split and finite signed-rewrite routes for both
parts of the active insertion.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/-- Recollect one active factor against the current block, retaining residuals. -/
structure
  SupportedSemanticResolution
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (coordinates : CCRecipe H ι)
    (factor : SPFactor H ι) where
  activeCoordinates :
    CCRecipe H ι
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
          (activeCoordinates.weightFactors lowerWeight ++ higherSource) =
        SPFactor.listEval (n := n) e
          (coordinates.weightFactors lowerWeight ++ [factor])

/-- Move one active factor across the old signed higher tail, retaining residuals. -/
structure SupportedHigherResolution
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (coordinates : CCRecipe H ι)
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
          (coordinates.tailFactors (n := n) lowerWeight ++ [factor])

namespace TPResolu

/-- Active-block and higher-tail residuals compose to a full active resolution. -/
def active_block_tail
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CCRecipe H ι}
    {factor : SPFactor H ι}
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (block :
      SupportedSemanticResolution
        (n := n) (lowerWeight := lowerWeight) H ι coordinates factor)
    (tail :
      SupportedHigherResolution
        (n := n) (lowerWeight := lowerWeight) H ι coordinates factor) :
    TPResolu
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
            (block.activeCoordinates.weightFactors lowerWeight ++
              (block.higherSource ++ tail.higherSource)) =
          SPFactor.listEval e
              (block.activeCoordinates.weightFactors lowerWeight ++
                block.higherSource) *
            SPFactor.listEval e tail.higherSource := by
              simp [SPFactor.listEval_append, mul_assoc]
      _ =
          SPFactor.listEval e
              (coordinates.weightFactors lowerWeight ++ [factor]) *
            SPFactor.listEval e tail.higherSource := by
              rw [block.active_append_source e]
      _ =
          SPFactor.listEval e
              (coordinates.weightFactors lowerWeight) *
            SPFactor.listEval e
              ([factor] ++ tail.higherSource) := by
              simp [SPFactor.listEval_append, mul_assoc]
      _ =
          SPFactor.listEval e
              (coordinates.weightFactors lowerWeight) *
            SPFactor.listEval e
              (coordinates.tailFactors (n := n) lowerWeight ++ [factor]) := by
              rw [tail.factor_append_source e]
      _ =
          SPFactor.listEval e
            (coordinates.weightFactors lowerWeight ++
              coordinates.tailFactors (n := n) lowerWeight ++ [factor]) := by
              simp [SPFactor.listEval_append]
      _ =
          SPFactor.listEval e
            (coordinates.factors (n := n) ++ [factor]) := by
              rw [coordinates.append_no_below
                hcoordinates hlowerWeightPos hlowerWeightCutoff]

end TPResolu

/-- A finite signed-rewrite route through the current active coordinate block. -/
structure TSRoutea
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (coordinates : CCRecipe H ι)
    (factor : SPFactor H ι) where
  activeCoordinates :
    CCRecipe H ι
  active_terms_below :
    activeCoordinates.NTBelow lowerWeight
  higherSource :
    List (SPFactor H ι)
  higher_least_succ :
    SPFactor.WordWeightLeast (lowerWeight + 1)
      higherSource
  rewrites :
    TSRw
      (n := n) (lowerWeight := lowerWeight)
        (coordinates.weightFactors lowerWeight ++ [factor])
        (activeCoordinates.weightFactors lowerWeight ++ higherSource)

namespace TSRoutea

/-- A signed active-block route supplies its residual resolution. -/
def activeBlockResolution
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CCRecipe H ι}
    {factor : SPFactor H ι}
    (route :
      TSRoutea
        (n := n) (lowerWeight := lowerWeight) H ι coordinates factor)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    SupportedSemanticResolution
      (n := n) (lowerWeight := lowerWeight) H ι coordinates factor where
  activeCoordinates := route.activeCoordinates
  active_terms_below :=
    route.active_terms_below
  higherSource := route.higherSource
  higher_source_truncated := by
    have hblock :
        SPFactor.IsTruncated n
          (coordinates.weightFactors lowerWeight) := by
      intro x hx
      rw [coordinates.word_weight_factors hx]
      omega
    have houtput :
        SPFactor.IsTruncated n
          (route.activeCoordinates.weightFactors lowerWeight ++
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

end TSRoutea

/-- A finite signed-rewrite route across the old strictly higher endpoint tail. -/
structure SHRoute
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (coordinates : CCRecipe H ι)
    (factor : SPFactor H ι) where
  higherSource :
    List (SPFactor H ι)
  higher_least_succ :
    SPFactor.WordWeightLeast (lowerWeight + 1)
      higherSource
  rewrites :
    TSRw
      (n := n) (lowerWeight := lowerWeight)
        (coordinates.tailFactors (n := n) lowerWeight ++ [factor])
        ([factor] ++ higherSource)

namespace SHRoute

/-- A signed higher-tail route supplies its residual resolution. -/
def higherTailResolution
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {coordinates : CCRecipe H ι}
    {factor : SPFactor H ι}
    (route :
      SHRoute
        (n := n) (lowerWeight := lowerWeight) H ι coordinates factor)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    SupportedHigherResolution
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
        · exact coordinates.truncated_factors
            hlowerWeightCutoff x hx
        · rcases List.mem_singleton.mp hx with rfl
          exact hfactorTruncated)
    intro x hx
    exact houtput x (List.mem_append_right _ hx)
  higher_least_succ :=
    route.higher_least_succ
  factor_append_source := fun e =>
    route.rewrites.listEval_eq e

end SHRoute

/-- A recursive signed-rewrite schedule for active-block residual routing. -/
structure TPRoute
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  route :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      TSNormal
          (n := n) (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CCRecipe H ι)
          (factor : SPFactor H ι),
          coordinates.NTBelow lowerWeight →
          factor.word.weight HEAddres.weight = lowerWeight →
          factor.word.weight HEAddres.weight < n →
            TSRoutea
              (n := n) (lowerWeight := lowerWeight) H ι coordinates factor

/-- A recursive signed-rewrite schedule for higher-tail routing. -/
structure RecursiveHigherSchedule
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  route :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      TSNormal
          (n := n) (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CCRecipe H ι)
          (factor : SPFactor H ι),
          coordinates.NTBelow lowerWeight →
          factor.word.weight HEAddres.weight = lowerWeight →
          factor.word.weight HEAddres.weight < n →
            SHRoute
              (n := n) (lowerWeight := lowerWeight) H ι coordinates factor

namespace TPRoute

open TPResolu

/-- The two signed residual route schedules supply the active insertion branch. -/
def insertionBranch
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (blockSchedule :
      TPRoute
        (n := n) H)
    (tailSchedule :
      RecursiveHigherSchedule
        (n := n) H) :
    SupportedInsertionBranch
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

/-- The two signed residual route schedules supply the recursive step. -/
def recursiveInsertionStep
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (blockSchedule :
      TPRoute
        (n := n) H)
    (tailSchedule :
      RecursiveHigherSchedule
        (n := n) H) :
    TSInsert
      (n := n) H :=
  TSInsert.insertion_branch
    (blockSchedule.insertionBranch tailSchedule)

end TPRoute

/-- Signed residual route schedules construct product recollection data. -/
theorem active_route_schedules
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (blockSchedule :
      TPRoute
        (n := n) H)
    (tailSchedule :
      RecursiveHigherSchedule
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  collected_semantic_insertion
    H e (blockSchedule.recursiveInsertionStep tailSchedule)

/-- Signed residual route schedules construct inverse recollection data. -/
theorem collected_route_schedules
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (blockSchedule :
      TPRoute
        (n := n) H)
    (tailSchedule :
      RecursiveHigherSchedule
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  recursive_insertion_step
    H e (blockSchedule.recursiveInsertionStep tailSchedule)

end TCTex
end Towers

/-!
# Universal signed product and inverse polynomial collection reduction

The standalone signed-polynomial theory has separated the two inputs required
from a universal Hall collector:

* higher-word correction packets for each supported adjacent swap; and
* a signed coordinate-endpoint builder whose derivation recursively routes the
  normalized correction blocks emitted by those swaps.

This file packages those inputs together.  A universal one-stratum derivation
builder supplies the signed schedule used by filtration recursion, and hence
constructs the global product and inverse coordinate polynomials required by
Claim 8.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
The exact remaining one-stratum operational constructor for signed global
recollection.  For each support stratum it receives the recursively
constructed next-stratum normalizer and a correction-packet factory.  It must
recollect one supported truncated factor into a signed coordinate endpoint,
witnessed by a list-valued More3 derivation.
-/
structure UDBuild
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  correctionFactory :
    ∀ lowerWeight : ℕ,
      TSFtry
        (n := n) H lowerWeight
  insert :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      TSNormal
          (n := n) (lowerWeight := lowerWeight + 1) H →
        TSFtry
            (n := n) H lowerWeight →
          ∀ (coordinates : CCRecipe H ι)
            (factor : SPFactor H ι),
            coordinates.NTBelow lowerWeight →
            lowerWeight ≤ factor.word.weight HEAddres.weight →
            factor.word.weight HEAddres.weight < n →
              ∃ next : CCRecipe H ι,
                next.NTBelow lowerWeight ∧
                  TSInsertb
                    (n := n) H ι lowerWeight
                      (coordinates.factors (n := n)) factor
                        (next.factors (n := n))

namespace UDBuild

/-- A universal signed builder supplies the structured insertion schedule. -/
def recursiveDerivationSchedule
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (builder :
      UDBuild
        (n := n) H) :
    RIDerivaa
      (n := n) H where
  insert lowerWeight normalizer :=
    builder.insert lowerWeight normalizer (builder.correctionFactory lowerWeight)

/-- A universal signed builder supplies the semantic normalizer at every stratum. -/
noncomputable def supportedCoordinateNormalizer
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (builder :
      UDBuild
        (n := n) H)
    (lowerWeight : ℕ) :
    TSNormal
      (n := n) (lowerWeight := lowerWeight) H :=
  TSNormal.recInsertionStep
    H
      (builder.recursiveDerivationSchedule
        |>.semanticInsertionSchedule
        |>.recursiveInsertionStep)
      lowerWeight

end UDBuild

/-- A universal signed builder constructs product recollection data. -/
theorem collect_derivation_builder
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : List (HEFam H))
    (builder :
      UDBuild
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  collected_insertion_derivation
    H e builder.recursiveDerivationSchedule

/-- A universal signed builder constructs inverse recollection data. -/
theorem semantic_derivation_builder
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (e : HEFam H)
    (builder :
      UDBuild
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  semantic_insertion_derivation
    H e builder.recursiveDerivationSchedule

end TCTex
end Towers

/-!
# High-weight semantic normalization for signed Hall polynomials

In the commutative region `n ≤ 2 * lowerWeight`, every retained signed
polynomial Hall factor can be replaced by its semantic Hall normal form.
The constant Hall coordinates of its unpowered word multiply the factor's
signed symbolic formula.  Coordinatewise append then merges finite normalized
endpoints without losing support or evaluation.

This supplies the terminal semantic normalizer needed by the recursive signed
collector.  The file is intentionally not imported by the existing collection
proof.
-/

namespace Towers
namespace TCTex

universe u

namespace WBTerm

/-- Scale the integer coefficient of one signed Hall-binomial recipe term. -/
def scale
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (coefficient : ℤ)
    (term : WBTerm H ι targetWeight) :
    WBTerm H ι targetWeight :=
  (coefficient * term.1, term.2)

@[simp]
lemma eval_scale
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (coefficient : ℤ)
    (term : WBTerm H ι targetWeight)
    (e : ι → HEFam H) :
    (term.scale coefficient).eval e = coefficient * term.eval e := by
  simp [scale, eval]
  ring

end WBTerm

namespace WBForm

/-- Scale every signed coefficient in one Hall-binomial formula. -/
def scale
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (coefficient : ℤ)
    (formula : WBForm H ι targetWeight) :
    WBForm H ι targetWeight where
  terms := formula.terms.map fun term => term.scale coefficient

@[simp]
lemma eval_scale
    {d targetWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (coefficient : ℤ)
    (formula : WBForm H ι targetWeight)
    (e : ι → HEFam H) :
    (formula.scale coefficient).eval e = coefficient * formula.eval e := by
  cases formula with
  | mk terms =>
      induction terms with
      | nil =>
          simp [scale, eval]
      | cons head tail ih =>
          change
            (head.scale coefficient).eval e +
                (scale coefficient
                  ({ terms := tail } :
                    WBForm H ι targetWeight)).eval e =
              coefficient *
                (head.eval e +
                  ({ terms := tail } :
                    WBForm H ι targetWeight).eval e)
          rw [WBTerm.eval_scale, ih, mul_add]

end WBForm

/--
In a commutative group, coordinatewise addition of exponents multiplies the
two corresponding ordered products.
-/
lemma list_zpow_add
    {G α : Type*}
    [Group G]
    [IsMulCommutative G]
    (g : α → G)
    (e f : α → ℤ)
    (L : List α) :
    (L.map fun i => g i ^ (e i + f i)).prod =
      (L.map fun i => g i ^ e i).prod *
        (L.map fun i => g i ^ f i).prod := by
  induction L with
  | nil =>
      simp
  | cons i L ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [zpow_add, ih]
      ac_rfl

/--
In a high lower-central region, adding two Hall-coordinate rows multiplies
their fixed-weight Hall segments.
-/
lemma BCWta.collectedweight_productadd_highweight
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hcutoff : n ≤ 2 * lowerWeight)
    (e f : HEFam H)
    (heBelow : ∀ s, s < lowerWeight → e s = 0)
    (hfBelow : ∀ s, s < lowerWeight → f s = 0)
    (s : ℕ) :
    (H s).collectedWeightProduct (n := n) ((e + f) s) =
      (H s).collectedWeightProduct (n := n) (e s) *
        (H s).collectedWeightProduct (n := n) (f s) := by
  by_cases hs : lowerWeight ≤ s
  · letI :
        IsMulCommutative
          (Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            (s - 1)) :=
      truncation_commutative_n
        (by omega)
    simp only [BCWta.collectedWeightProduct,
      BCWta.collected_lower_centralterm,
      BCWt.evalin_freelower_centtrunterm,
      Pi.add_apply]
    exact congrArg Subtype.val
      (list_zpow_add
        (fun i =>
          ((H s).commutator i).evalin_freelower_centtrunterm (n := n))
        (e s) (f s) (Finset.univ.sort fun i i' : (H s).index => i ≤ i'))
  · have he : e s = 0 := heBelow s (Nat.lt_of_not_ge hs)
    have hf : f s = 0 := hfBelow s (Nat.lt_of_not_ge hs)
    simp [he, hf, BCWta.collected_weight_productzero]

/--
In a high lower-central region, coordinatewise addition multiplies collected
Hall prefixes.
-/
lemma collected_prefix_high
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hcutoff : n ≤ 2 * lowerWeight)
    (e f : HEFam H)
    (heBelow : ∀ s, s < lowerWeight → e s = 0)
    (hfBelow : ∀ s, s < lowerWeight → f s = 0)
    (k : ℕ) :
    collectedPrefixProduct (n := n) H (e + f) k =
      collectedPrefixProduct (n := n) H e k *
        collectedPrefixProduct (n := n) H f k := by
  let S :=
    Subgroup.lowerCentralSeries
      (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (lowerWeight - 1)
  letI : IsMulCommutative S :=
    truncation_commutative_n
      hcutoff
  induction k with
  | zero =>
      simp [collectedPrefixProduct]
  | succ k ih =>
      rw [collected_prefix_succ, collected_prefix_succ,
        collected_prefix_succ, ih,
        BCWta.collectedweight_productadd_highweight
          hcutoff e f heBelow hfBelow]
      have hprefixF :
          collectedPrefixProduct (n := n) H f k ∈ S :=
        collected_initial_series f hfBelow k
      have hsegmentE :
          (H (k + 1)).collectedWeightProduct (n := n) (e (k + 1)) ∈ S :=
        BCWta.collec_produ_lowec
          e heBelow (k + 1)
      have hcommute :
          Commute
            (collectedPrefixProduct (n := n) H f k)
            ((H (k + 1)).collectedWeightProduct (n := n) (e (k + 1))) := by
        exact congrArg Subtype.val
          (mul_comm
            (⟨collectedPrefixProduct (n := n) H f k, hprefixF⟩ : S)
            (⟨(H (k + 1)).collectedWeightProduct (n := n) (e (k + 1)),
              hsegmentE⟩ : S))
      calc
        collectedPrefixProduct (n := n) H e k *
              collectedPrefixProduct (n := n) H f k *
            ((H (k + 1)).collectedWeightProduct (n := n) (e (k + 1)) *
              (H (k + 1)).collectedWeightProduct (n := n) (f (k + 1))) =
            collectedPrefixProduct (n := n) H e k *
                (collectedPrefixProduct (n := n) H f k *
                  (H (k + 1)).collectedWeightProduct (n := n) (e (k + 1))) *
              (H (k + 1)).collectedWeightProduct (n := n) (f (k + 1)) := by
                simp only [mul_assoc]
        _ =
            collectedPrefixProduct (n := n) H e k *
                ((H (k + 1)).collectedWeightProduct (n := n) (e (k + 1)) *
                  collectedPrefixProduct (n := n) H f k) *
              (H (k + 1)).collectedWeightProduct (n := n) (f (k + 1)) := by
                rw [hcommute.eq]
        _ =
            collectedPrefixProduct (n := n) H e k *
                (H (k + 1)).collectedWeightProduct (n := n) (e (k + 1)) *
              (collectedPrefixProduct (n := n) H f k *
                (H (k + 1)).collectedWeightProduct (n := n) (f (k + 1))) := by
                simp only [mul_assoc]

/--
In a high lower-central region, coordinatewise addition multiplies full
collected Hall products.
-/
lemma collected_add_high
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hcutoff : n ≤ 2 * lowerWeight)
    (e f : HEFam H)
    (heBelow : ∀ s, s < lowerWeight → e s = 0)
    (hfBelow : ∀ s, s < lowerWeight → f s = 0) :
    collectedHallProduct (n := n) H (e + f) =
      collectedHallProduct (n := n) H e *
        collectedHallProduct (n := n) H f := by
  exact collected_prefix_high
    hcutoff e f heBelow hfBelow (n - 1)

namespace CCRecipe

/-- Append signed formulas coordinatewise. -/
def add
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (left right : CCRecipe H ι) :
    CCRecipe H ι where
  formulas s i := left.formulas s i ++ right.formulas s i

/-- Coordinatewise formula append adds the evaluated Hall exponents. -/
@[simp]
lemma eval_add
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (left right : CCRecipe H ι)
    (e : ι → HEFam H) :
    (left.add right).eval e = left.eval e + right.eval e := by
  funext s i
  simp [add, eval]

/-- If one layer has no factors, each formula list in that layer is empty. -/
lemma formulas_nil_factors
    {d s : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    (hR : R.weightFactors s = [])
    (i : (H s).index) :
    R.formulas s i = [] := by
  have hflat :
      (Finset.univ.sort fun i i' : (H s).index => i ≤ i').flatMap
          (fun j =>
            (R.formulas s j).map fun formula =>
              formula.symbolicPolynomialFactor j) = [] := by
    simpa [weightFactors] using hR
  have hmap :=
    (List.flatMap_eq_nil_iff.mp hflat) i (by simp)
  simpa using hmap

/-- Coordinatewise formula append preserves a common lower support bound. -/
lemma NTBelow.add
    {d lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {left right : CCRecipe H ι}
    (hleft : left.NTBelow lowerWeight)
    (hright : right.NTBelow lowerWeight) :
    (left.add right).NTBelow lowerWeight := by
  intro s hs
  unfold CCRecipe.weightFactors
    CCRecipe.add
  apply List.flatMap_eq_nil_iff.2
  intro i _hi
  simp [left.formulas_nil_factors (hleft s hs) i,
    right.formulas_nil_factors (hright s hs) i]

/-- Evaluated coordinates vanish below a signed endpoint's support bound. -/
lemma eval_zero_below
    {d lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (R : CCRecipe H ι)
    (hR : R.NTBelow lowerWeight)
    (e : ι → HEFam H)
    (s : ℕ)
    (hs : s < lowerWeight) :
    R.eval e s = 0 := by
  funext i
  simp [eval, R.formulas_nil_factors (hR s hs) i]

/-- In the high-weight region, appended signed endpoints multiply semantically. -/
lemma list_high_weight
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hcutoff : n ≤ 2 * lowerWeight)
    (left right : CCRecipe H ι)
    (hleft : left.NTBelow lowerWeight)
    (hright : right.NTBelow lowerWeight)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e
        ((left.add right).factors (n := n)) =
      SPFactor.listEval (n := n) e
          (left.factors (n := n)) *
        SPFactor.listEval (n := n) e
          (right.factors (n := n)) := by
  rw [listEval_factors, listEval_factors, listEval_factors, eval_add]
  exact collected_add_high hcutoff
    (left.eval e) (right.eval e)
    (left.eval_zero_below hleft e) (right.eval_zero_below hright e)

end CCRecipe

namespace SPFactor

/--
Replace one signed polynomial factor by the Hall-normal coordinates of its
unpowered word, scaling its symbolic coefficient formula in each coordinate.
-/
noncomputable def signedCoordinateRecipes
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (x : SPFactor H ι) :
    CCRecipe H ι where
  formulas s i :=
    if hweight : x.word.weight HEAddres.weight ≤ s then
      [(x.coefficient.weaken hweight).scale
        (hallCoordinate hn H hH (x.wordValue (n := n)) i)]
    else
      []

/-- Evaluating the semantic formulas scales the word's Hall-normal coordinates. -/
lemma signed_coordinate_recipes
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (x : SPFactor H ι)
    (e : ι → HEFam H)
    (s : ℕ)
    (hs : 1 ≤ s)
    (hsn : s < n) :
    (x.signedCoordinateRecipes hn H hH).eval e s =
      zscaledExponentFamily
        (normalFormCoordinates hn H hH (x.wordValue (n := n)))
        (x.coefficient.eval e) s := by
  funext i
  by_cases hweight : x.word.weight HEAddres.weight ≤ s
  · simp [signedCoordinateRecipes,
      CCRecipe.eval, hweight, hallCoordinate,
      zscaledExponentFamily]
  · have hzero :
        hallCoordinate hn H hH (x.wordValue (n := n)) i = 0 := by
      exact lower_central_series
        hn H hH (x.wordValue (n := n)) x.value_lower_series
          hs (Nat.lt_of_not_ge hweight) hsn i
    change
      normalFormCoordinates hn H hH (x.wordValue (n := n)) s i = 0 at hzero
    simp [signedCoordinateRecipes,
      CCRecipe.eval, hweight, hzero,
      zscaledExponentFamily]

/-- Hall-normal coordinates of a retained polynomial factor vanish below its weight. -/
lemma coordinates_value_below
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (x : SPFactor H ι)
    (hx : x.word.weight HEAddres.weight < n) :
    ∀ s, s < x.word.weight HEAddres.weight →
      normalFormCoordinates hn H hH (x.wordValue (n := n)) s = 0 := by
  intro s hs
  funext i
  by_cases hspos : 1 ≤ s
  · change hallCoordinate hn H hH (x.wordValue (n := n)) i = 0
    exact lower_central_series
      hn H hH (x.wordValue (n := n)) x.value_lower_series
        hspos hs (hs.trans hx) i
  · have hs0 : s = 0 := by omega
    subst s
    exact False.elim ((H 0).commutator i).weight_pos.false

/--
In the commutative high-weight region, one factor's Hall-normal signed
endpoint evaluates exactly to that factor.
-/
lemma list_factors_recipes
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (x : SPFactor H ι)
    (hx : x.word.weight HEAddres.weight < n)
    (hcutoff : n ≤ 2 * x.word.weight HEAddres.weight)
    (e : ι → HEFam H) :
    SPFactor.listEval (n := n) e
        ((x.signedCoordinateRecipes hn H hH).factors (n := n)) =
      x.eval (n := n) e := by
  rw [CCRecipe.listEval_factors]
  calc
    collectedHallProduct (n := n) H
          ((x.signedCoordinateRecipes hn H hH).eval e) =
        collectedHallProduct (n := n) H
          (zscaledExponentFamily
            (normalFormCoordinates hn H hH (x.wordValue (n := n)))
            (x.coefficient.eval e)) := by
      unfold collectedHallProduct
      apply collected_product_coordinates
      intro s hs hsle
      exact x.signed_coordinate_recipes hn H hH e s hs (by omega)
    _ = collectedHallProduct (n := n) H
          (normalFormCoordinates hn H hH (x.wordValue (n := n))) ^
            x.coefficient.eval e := by
      exact zscaled_exponent_high
        hcutoff
        (normalFormCoordinates hn H hH (x.wordValue (n := n)))
        (x.coordinates_value_below hn H hH hx)
        (x.coefficient.eval e)
    _ = x.eval (n := n) e := by
      rw [collected_form_coordinates hn H hH]
      rfl

/-- Hall-normal signed recipes introduce no formulas below the factor weight. -/
lemma no_below_recipes
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (x : SPFactor H ι)
    (hx : lowerWeight ≤ x.word.weight HEAddres.weight) :
    (x.signedCoordinateRecipes hn H hH).NTBelow
      lowerWeight := by
  intro s hs
  unfold CCRecipe.weightFactors
  apply List.flatMap_eq_nil_iff.2
  intro i _hi
  have hweight : ¬x.word.weight HEAddres.weight ≤ s := by
    omega
  simp [signedCoordinateRecipes, hweight]

end SPFactor

namespace SSInsert

/--
The commutative region `n ≤ 2 * lowerWeight` has a canonical signed endpoint
insertion kernel.
-/
noncomputable def of_highWeight
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hcutoff : n ≤ 2 * lowerWeight) :
    SSInsert
      (n := n) (lowerWeight := lowerWeight) H where
  insert coordinates factor hcoordinates hfactorWeight hfactorTruncated := by
    let X := factor.signedCoordinateRecipes hn H hH
    refine ⟨coordinates.add X, ?_, ?_⟩
    · exact hcoordinates.add
        (factor.no_below_recipes
          hn H hH hfactorWeight)
    · intro e
      calc
        SPFactor.listEval (n := n) e
              ((coordinates.add X).factors (n := n)) =
            SPFactor.listEval (n := n) e
                (coordinates.factors (n := n)) *
              SPFactor.listEval (n := n) e
                (X.factors (n := n)) := by
          exact coordinates.list_high_weight hcutoff X
            hcoordinates
            (factor.no_below_recipes
              hn H hH hfactorWeight)
            e
        _ =
            SPFactor.listEval (n := n) e
                (coordinates.factors (n := n)) *
              factor.eval (n := n) e := by
          rw [factor.list_factors_recipes
            hn H hH hfactorTruncated (by omega) e]
        _ =
            SPFactor.listEval (n := n) e
              (coordinates.factors (n := n) ++ [factor]) := by
          rw [SPFactor.listEval_append]
          simp

end SSInsert

namespace TSNormal

/--
The commutative region `n ≤ 2 * lowerWeight` has a canonical signed semantic
normalizer.
-/
noncomputable def of_highWeight
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hcutoff : n ≤ 2 * lowerWeight) :
    TSNormal
      (n := n) (lowerWeight := lowerWeight) H :=
  ofInsertionKernel
    (SSInsert.of_highWeight
      hn H hH hcutoff)

end TSNormal

end TCTex
end Towers

/-!
# Sharp recursive routing through signed polynomial Hall higher tails

To move one active signed factor left across a strictly higher tail, cross the
final tail parent, normalize the emitted correction packet sharply above that
parent's actual weight, append the normalized correction block to the pending
prefix, and recurse.  The pending prefix changes from `P ++ [B]` to
`P ++ correctionFactors`, which strictly decreases the cutoff-defect multiset.

This file implements that More3 recursion and adapts it to the signed
higher-tail route schedule consumed by active-layer resolution.  It is
intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace TSInsertb

/-- Appending one factor verbatim is always a valid signed insertion. -/
lemma append_self
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (L : List (SPFactor H ι))
    (A : SPFactor H ι) :
    TSInsertb
      (n := n) H ι lowerWeight L A (L ++ [A]) := by
  rcases L.eq_nil_or_concat with rfl | ⟨P, B, rfl⟩
  · simpa using
      (TSInsertb.nil
        (n := n) (lowerWeight := lowerWeight) A)
  · exact
      (by
        simpa [List.concat_eq_append] using
          (TSInsertb.append
            (n := n) (lowerWeight := lowerWeight) P B A))

end TSInsertb

namespace SSInserta

/-- Appending a finite signed correction block verbatim is a valid insertion. -/
lemma append_self
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (P source : List (SPFactor H ι)) :
    SSInserta
      (n := n) H ι lowerWeight P source (P ++ source) := by
  induction source using List.reverseRecOn with
  | nil =>
      simpa using
        (SSInserta.nil
          (n := n) (lowerWeight := lowerWeight) P)
  | append_singleton source A ih =>
      simpa [List.append_assoc] using
        (SSInserta.snoc
          (n := n) (lowerWeight := lowerWeight) P source A ih
            (TSInsertb.append_self
              (n := n) (lowerWeight := lowerWeight) (P ++ source) A))

end SSInserta

/-- A More3 route moving one active signed factor before a strictly higher list. -/
structure THRoute
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (pending : List (SPFactor H ι))
    (factor : SPFactor H ι) where
  higherSource :
    List (SPFactor H ι)
  higher_least_succ :
    SPFactor.WordWeightLeast
      (lowerWeight + 1) higherSource
  inserts :
    TSInsertb
      (n := n) H ι lowerWeight pending factor ([factor] ++ higherSource)

namespace TSFtry

/--
Sharp parent-relative correction normalization constructs a terminating More3
route moving one active signed factor left across any strictly higher list.
-/
lemma nonempty_supported_route
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (family :
      SNFam
        (n := n) H)
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (pending : List (SPFactor H ι))
    (hpending :
      SPFactor.WordWeightLeast
        (lowerWeight + 1) pending) :
    Nonempty
      (THRoute
        (n := n) (lowerWeight := lowerWeight) H ι pending factor) := by
  refine
    (SPFactor.well_founded_defect
      (n := n) (H := H) (ι := ι)).induction
      (C := fun pending =>
        SPFactor.WordWeightLeast
            (lowerWeight + 1) pending →
          Nonempty
            (THRoute
              (n := n) (lowerWeight := lowerWeight) H ι pending factor))
      pending ?_ hpending
  intro pending ih hpending
  rcases pending.eq_nil_or_concat with rfl | ⟨P, B, rfl⟩
  · exact ⟨{
      higherSource := []
      higher_least_succ := by
        intro x hx
        simp at hx
      inserts := by
        simpa using
          (TSInsertb.nil
            (n := n) (lowerWeight := lowerWeight) factor)
    }⟩
  · have hP :
        SPFactor.WordWeightLeast (lowerWeight + 1) P :=
      fun x hx => hpending x (by simp [List.concat_eq_append, hx])
    have hBsucc :
        lowerWeight + 1 ≤ B.word.weight HEAddres.weight :=
      hpending B (by simp)
    have hB :
        lowerWeight ≤ B.word.weight HEAddres.weight :=
      (Nat.le_succ lowerWeight).trans hBsucc
    have hfactor :
        lowerWeight ≤ factor.word.weight HEAddres.weight := by
      omega
    let C := factory.packet B factor hB hfactor
    let normalization := family.normalization_left_sharp C hB
    have hnormalization :
        SPFactor.WordWeightLeast (lowerWeight + 1)
          (normalization.coordinates.factors (n := n)) :=
      normalization.weight_least_succ
    have hnextPending :
        SPFactor.WordWeightLeast (lowerWeight + 1)
          (P ++ normalization.coordinates.factors (n := n)) := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hP x hx
      · exact hnormalization x hx
    have hdescends :
        SPFactor.CutoffDefectMultiset n
          (P ++ normalization.coordinates.factors (n := n)) (P ++ [B]) := by
      dsimp [normalization]
      exact
        family.sharp_defect_multiset
          C hB P
    rcases ih _ (by simpa [List.concat_eq_append] using hdescends)
        hnextPending with
      ⟨route⟩
    exact ⟨{
      higherSource := route.higherSource ++ [B]
      higher_least_succ := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact route.higher_least_succ x hx
        · rcases List.mem_singleton.mp hx with rfl
          exact hBsucc
      inserts := by
        simpa [List.append_assoc] using
          (TSInsertb.obstruction
            (n := n) (lowerWeight := lowerWeight)
            P B factor C normalization
              (SSInserta.append_self
                (n := n) (lowerWeight := lowerWeight) P
                  (normalization.coordinates.factors (n := n)))
              route.inserts)
    }⟩

/-- Choose the sharp signed route through a strictly higher pending list. -/
noncomputable def supportedSemanticHigher
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (family :
      SNFam
        (n := n) H)
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (pending : List (SPFactor H ι))
    (hpending :
      SPFactor.WordWeightLeast
        (lowerWeight + 1) pending) :
    THRoute
      (n := n) (lowerWeight := lowerWeight) H ι pending factor :=
  Classical.choice
    (factory.nonempty_supported_route family factor
      hfactorWeight pending hpending)

/-- Move an active signed factor through a normalized endpoint's higher tail. -/
noncomputable def supportedTailRoute
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (family :
      SNFam
        (n := n) H)
    (coordinates : CCRecipe H ι)
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight) :
    SHRoute
      (n := n) (lowerWeight := lowerWeight) H ι coordinates factor := by
  let route :=
    factory.supportedSemanticHigher family factor
      hfactorWeight (coordinates.tailFactors (n := n) lowerWeight)
        coordinates.word_least_factors
  exact
    { higherSource := route.higherSource
      higher_least_succ :=
        route.higher_least_succ
      rewrites := route.inserts.rewrites }

end TSFtry

/-- A signed correction-packet factory available at every support stratum. -/
structure SFSched
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  factory :
    ∀ lowerWeight : ℕ,
      TSFtry
        (n := n) H lowerWeight

namespace SFSched

/--
A stratum-indexed packet supply and sharp normalizer family construct the
recursive signed higher-tail route schedule used by active-layer resolution.
-/
noncomputable def recursiveRouteSchedule
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (schedule :
      SFSched
        (n := n) H)
    (family :
      SNFam
        (n := n) H) :
    RecursiveHigherSchedule
      (n := n) H where
  route lowerWeight _normalizer coordinates factor _hcoordinates hfactorWeight
      _hfactorTruncated :=
    (schedule.factory lowerWeight).supportedTailRoute
      family coordinates factor hfactorWeight

end SFSched

end TCTex
end Towers

/-!
# High-weight terminal recursion for signed Hall recollection

The first signed-polynomial recursion used only the vacuous terminal case
`n ≤ lowerWeight`.  Semantic Hall-normalization closes the recursion earlier:
as soon as `n ≤ 2 * lowerWeight`, every supported residual list lies in a
commutative lower-central region and has a canonical signed endpoint.

This file packages that sharper well-founded recursion and its Claim 8
adapters.  The file is intentionally not imported by the existing collection
proof.
-/

namespace Towers
namespace TCTex

universe u

namespace TSNormal

/--
Successive-stratum signed insertion plus the commutative high-weight terminal
case constructs a signed semantic normalizer at every support stratum.
-/
noncomputable def rec_insertion_high
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (step :
      TSInsert
        (n := n) H)
    (lowerWeight : ℕ) :
    TSNormal
      (n := n) (lowerWeight := lowerWeight) H :=
  if hterminal : n ≤ 2 * lowerWeight then
    of_highWeight hn H hH hterminal
  else
    ofInsertionKernel
      (step.insert lowerWeight
        (rec_insertion_high hn H hH step (lowerWeight + 1)))
termination_by n - lowerWeight
decreasing_by omega

end TSNormal

/--
A recursive signed insertion constructor and graded Hall bases supply product
recollection polynomials using the high-weight terminal normalizer.
-/
theorem
  recursive_semantic_insertion
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (e : List (HEFam H))
    (step :
      TSInsert
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  open TSNormal in
    signed_semantic_normalizer
      H e (rec_insertion_high hn H hH step 1)

/--
A recursive signed insertion constructor and graded Hall bases supply inverse
recollection polynomials using the high-weight terminal normalizer.
-/
theorem
  recursive_insertion_high
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (e : HEFam H)
    (step :
      TSInsert
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  open TSNormal in
    collected_data_normalizer
      H e (rec_insertion_high hn H hH step 1)

end TCTex
end Towers

/-!
# Higher-tail routing from strictly deeper signed normalizers

The first sharp signed router consumed a semantic normalizer family indexed by
all support bounds.  That interface is stronger than the recursion needs.
While collecting at `lowerWeight`, every crossed higher-tail parent has weight
strictly above `lowerWeight`, so its sharply normalized correction packet only
uses a normalizer at a strictly deeper support bound.

This file records that narrower local interface and reconstructs the
terminating higher-tail route from it.  The restricted interface is suitable
for a well-founded recursive global collector.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
A local parent-sharp signed correction normalizer at one ambient stratum.
Its output is exposed at the ambient support bound, but its descent witness
records that it was normalized sharply above the crossed parent's true weight.
-/
structure TSNormala
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  normalize :
    ∀ {ι : Type}
      {B A : SPFactor H ι}
      (C : TSPkt n B A),
      lowerWeight ≤ B.word.weight HEAddres.weight →
        TPSem
          lowerWeight C
  normalize_defect_multiset :
    ∀ {ι : Type}
      {B A : SPFactor H ι}
      (C : TSPkt n B A)
      (hB : lowerWeight ≤ B.word.weight HEAddres.weight)
      (P : List (SPFactor H ι)),
      SPFactor.CutoffDefectMultiset n
        (P ++ (normalize C hB).coordinates.factors (n := n))
        (P ++ [B])

namespace TSNormala

/--
Strictly deeper signed normalizers construct the local parent-sharp
normalizer required at one ambient stratum.
-/
noncomputable def ofNormalizerAbove
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight) H) :
    TSNormala
      (n := n) (lowerWeight := lowerWeight) H where
  normalize := by
    intro ι B A C hB
    exact
      (C.semantic_normalization_weight
        (normalizerAbove
          (B.word.weight HEAddres.weight + 1) (by omega))).weaken hB
  normalize_defect_multiset := by
    intro ι B A C hB P
    let normalization :=
      C.semantic_normalization_weight
        (normalizerAbove
          (B.word.weight HEAddres.weight + 1) (by omega))
    simpa [TPSem.weaken] using
      normalization.multisetAppendSingleton P

end TSNormala

namespace TSFtry

/--
The cutoff-defect multiset recursion only needs a local sharp correction
normalizer, not a completed all-strata family.
-/
lemma nonempty_sharp_normalizer
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (pending : List (SPFactor H ι))
    (hpending :
      SPFactor.WordWeightLeast
        (lowerWeight + 1) pending) :
    Nonempty
      (THRoute
        (n := n) (lowerWeight := lowerWeight) H ι pending factor) := by
  refine
    (SPFactor.well_founded_defect
      (n := n) (H := H) (ι := ι)).induction
      (C := fun pending =>
        SPFactor.WordWeightLeast
            (lowerWeight + 1) pending →
          Nonempty
            (THRoute
              (n := n) (lowerWeight := lowerWeight) H ι pending factor))
      pending ?_ hpending
  intro pending ih hpending
  rcases pending.eq_nil_or_concat with rfl | ⟨P, B, rfl⟩
  · exact ⟨{
      higherSource := []
      higher_least_succ := by
        intro x hx
        simp at hx
      inserts := by
        simpa using
          (TSInsertb.nil
            (n := n) (lowerWeight := lowerWeight) factor)
    }⟩
  · have hP :
        SPFactor.WordWeightLeast (lowerWeight + 1) P :=
      fun x hx => hpending x (by simp [List.concat_eq_append, hx])
    have hBsucc :
        lowerWeight + 1 ≤ B.word.weight HEAddres.weight :=
      hpending B (by simp)
    have hB :
        lowerWeight ≤ B.word.weight HEAddres.weight :=
      (Nat.le_succ lowerWeight).trans hBsucc
    have hfactor :
        lowerWeight ≤ factor.word.weight HEAddres.weight := by
      omega
    let C := factory.packet B factor hB hfactor
    let normalization := sharp.normalize C hB
    have hnormalization :
        SPFactor.WordWeightLeast (lowerWeight + 1)
          (normalization.coordinates.factors (n := n)) :=
      normalization.weight_least_succ
    have hnextPending :
        SPFactor.WordWeightLeast (lowerWeight + 1)
          (P ++ normalization.coordinates.factors (n := n)) := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hP x hx
      · exact hnormalization x hx
    have hdescends :
        SPFactor.CutoffDefectMultiset n
          (P ++ normalization.coordinates.factors (n := n)) (P ++ [B]) := by
      dsimp [normalization]
      exact sharp.normalize_defect_multiset C hB P
    rcases ih _ (by simpa [List.concat_eq_append] using hdescends)
        hnextPending with
      ⟨route⟩
    exact ⟨{
      higherSource := route.higherSource ++ [B]
      higher_least_succ := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact route.higher_least_succ x hx
        · rcases List.mem_singleton.mp hx with rfl
          exact hBsucc
      inserts := by
        simpa [List.append_assoc] using
          (TSInsertb.obstruction
            (n := n) (lowerWeight := lowerWeight)
            P B factor C normalization
              (SSInserta.append_self
                (n := n) (lowerWeight := lowerWeight) P
                  (normalization.coordinates.factors (n := n)))
              route.inserts)
    }⟩

/-- Choose the restricted sharp route through a strictly higher pending list. -/
noncomputable def supported_higher_normalizer
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (pending : List (SPFactor H ι))
    (hpending :
      SPFactor.WordWeightLeast
        (lowerWeight + 1) pending) :
    THRoute
      (n := n) (lowerWeight := lowerWeight) H ι pending factor :=
  Classical.choice
    (factory.nonempty_sharp_normalizer
      sharp factor hfactorWeight pending hpending)

/-- Move an active factor through an endpoint tail using only deeper normalizers. -/
noncomputable def supported_route_normalizer
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (coordinates : CCRecipe H ι)
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight) :
    SHRoute
      (n := n) (lowerWeight := lowerWeight) H ι coordinates factor := by
  let route :=
    factory.supported_higher_normalizer
      sharp factor hfactorWeight
        (coordinates.tailFactors (n := n) lowerWeight)
          coordinates.word_least_factors
  exact
    { higherSource := route.higherSource
      higher_least_succ :=
        route.higher_least_succ
      rewrites := route.inserts.rewrites }

end TSFtry

end TCTex
end Towers

/-!
# Sharp semantic movements for active signed polynomial Hall blocks

The nonterminal fixed-weight merge collector needs a local operation stronger
than a normalized adjacent obstruction.  After swapping two active factors,
its normalized correction block lies before the swapped pair.  The active pair
must immediately be routed left across that heavier block so the correction
residual remains behind the active layer.

This file packages that movement for signed polynomial Hall factors.  It first
folds the sharp higher-tail router across a finite active block, then uses that
fold to turn one normalized active swap into an active pair followed by a
strictly heavier residual.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace SPFactor

/-- Every signed polynomial factor in a list has exactly the selected weight. -/
def WordWeightExactly
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (weight : ℕ)
    (L : List (SPFactor H ι)) :
    Prop :=
  ∀ x ∈ L, x.word.weight HEAddres.weight = weight

end SPFactor

/--
A route moving a finite active signed block left across an already-heavier
residual list.
-/
structure SupportedHigherRoute
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (higher active : List (SPFactor H ι)) where
  higherSource :
    List (SPFactor H ι)
  higher_least_succ :
    SPFactor.WordWeightLeast
      (lowerWeight + 1) higherSource
  rewrites :
    TSRw
      (n := n) (lowerWeight := lowerWeight)
        (higher ++ active) (active ++ higherSource)

namespace TSFtry

/--
Fold the sharp signed higher-tail router across a finite active block.  The
active block keeps its order and every emitted correction remains behind it.
-/
noncomputable def supportedHigherRoute
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (family :
      SNFam
        (n := n) H)
    (higher : List (SPFactor H ι))
    (hhigher :
      SPFactor.WordWeightLeast
        (lowerWeight + 1) higher) :
    ∀ (active : List (SPFactor H ι)),
      SPFactor.WordWeightExactly lowerWeight active →
        SupportedHigherRoute
          (n := n) (lowerWeight := lowerWeight) H ι higher active
  | [], _ =>
      { higherSource := higher
        higher_least_succ := hhigher
        rewrites := by
          simpa using
            (Relation.ReflTransGen.refl :
              TSRw
                (n := n) (lowerWeight := lowerWeight) higher higher) }
  | A :: active, hactive => by
      have hA :
          A.word.weight HEAddres.weight = lowerWeight :=
        hactive A (by simp)
      have htail :
          SPFactor.WordWeightExactly lowerWeight active :=
        fun x hx => hactive x (by simp [hx])
      let headRoute :=
        factory.supportedSemanticHigher family A hA higher
          hhigher
      let tailRoute :=
        factory.supportedHigherRoute family
          headRoute.higherSource
            headRoute.higher_least_succ active htail
      refine
        { higherSource := tailRoute.higherSource
          higher_least_succ :=
            tailRoute.higher_least_succ
          rewrites := ?_ }
      have hhead :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              (higher ++ A :: active)
              (([A] ++ headRoute.higherSource) ++ active) := by
        simpa [List.append_assoc] using
          headRoute.inserts.rewrites.context [] active
      have htailRoute :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              (([A] ++ headRoute.higherSource) ++ active)
              ((A :: active) ++ tailRoute.higherSource) := by
        simpa [List.append_assoc] using tailRoute.rewrites.context [A] []
      exact hhead.trans htailRoute

end TSFtry

/--
One equal-weight active signed swap with every normalized correction moved
behind the swapped active pair.
-/
structure SupportedSwapRoute
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (B A : SPFactor H ι) where
  higherSource :
    List (SPFactor H ι)
  higher_least_succ :
    SPFactor.WordWeightLeast
      (lowerWeight + 1) higherSource
  rewrites :
    TSRw
      (n := n) (lowerWeight := lowerWeight)
        [B, A] ([A, B] ++ higherSource)

namespace TSFtry

/--
Normalize the correction packet of one active signed swap sharply, then route
the swapped active pair left across that correction block.
-/
noncomputable def supportedSwapRoute
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (family :
      SNFam
        (n := n) H)
    (B A : SPFactor H ι)
    (hB :
      B.word.weight HEAddres.weight = lowerWeight)
    (hA :
      A.word.weight HEAddres.weight = lowerWeight) :
    SupportedSwapRoute
      (n := n) (lowerWeight := lowerWeight) H ι B A := by
  have hBSupported :
      lowerWeight ≤ B.word.weight HEAddres.weight := by
    omega
  have hASupported :
      lowerWeight ≤ A.word.weight HEAddres.weight := by
    omega
  let C := factory.packet B A hBSupported hASupported
  let normalization :=
    family.normalization_left_sharp C hBSupported
  let route :=
    factory.supportedHigherRoute family
      (normalization.coordinates.factors (n := n))
        normalization.weight_least_succ [A, B] (by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact hA
          · exact hB)
  refine
    { higherSource := route.higherSource
      higher_least_succ :=
        route.higher_least_succ
      rewrites := ?_ }
  have hswap :
      TSRw
        (n := n) (lowerWeight := lowerWeight)
          [B, A]
          (normalization.coordinates.factors (n := n) ++ [A, B]) := by
    apply
      TSRw.single
    simpa using
      (TSSem.obstruction
        (n := n) (lowerWeight := lowerWeight) [] [] B A C normalization)
  exact hswap.trans route.rewrites

end TSFtry

end TCTex
end Towers

/-!
# Universal signed recollection with a high-weight semantic terminal

The universal signed derivation builder already isolates the finite
one-stratum Hall-routing obligation.  Once graded Hall bases are supplied,
semantic Hall-normalization closes its filtration recursion in the
commutative range `n ≤ 2 * lowerWeight`.

This file records the resulting sharper global product and inverse Claim 8
adapters.  The file is intentionally not imported by the existing collection
proof.
-/

namespace Towers
namespace TCTex

universe u

namespace UDBuild

/--
A universal signed derivation builder and graded Hall bases supply the
high-weight-terminal semantic normalizer at every support stratum.
-/
noncomputable def supported_normalizer_high
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (builder :
      UDBuild
        (n := n) H)
    (lowerWeight : ℕ) :
    TSNormal
      (n := n) (lowerWeight := lowerWeight) H :=
  TSNormal.rec_insertion_high
    hn H hH
      (builder.recursiveDerivationSchedule
        |>.semanticInsertionSchedule
        |>.recursiveInsertionStep)
      lowerWeight

end UDBuild

/--
A universal signed derivation builder and graded Hall bases construct product
recollection polynomials with the commutative high-weight terminal.
-/
theorem collected_derivation_high
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (e : List (HEFam H))
    (builder :
      UDBuild
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  recursive_semantic_insertion
    hn H hH e
      (builder.recursiveDerivationSchedule
        |>.semanticInsertionSchedule
        |>.recursiveInsertionStep)

/--
A universal signed derivation builder and graded Hall bases construct inverse
recollection polynomials with the commutative high-weight terminal.
-/
theorem derivation_builder_high
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (e : HEFam H)
    (builder :
      UDBuild
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  recursive_insertion_high
    hn H hH e
      (builder.recursiveDerivationSchedule
        |>.semanticInsertionSchedule
        |>.recursiveInsertionStep)

end TCTex
end Towers

/-!
# Reachable universal boundary for signed Hall recollection

The high-weight semantic normalizer closes recursion as soon as
`n ≤ 2 * lowerWeight`.  Consequently, a universal signed collector should
not be required to provide insertion derivations in that unreachable region.
Moreover, in the remaining class-two band `n ≤ 3 * lowerWeight`, correction
packets are automatic.

This file records the exact reachable operational boundary:

* custom insertion derivations are required only while
  `¬ n ≤ 2 * lowerWeight`;
* custom correction packets are required only while
  `¬ n ≤ 3 * lowerWeight`;
* the intermediate class-two band uses the existing automatic packet factory.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
The reachable recursive signed insertion obligation.  The insertion kernel is
requested only below the commutative high-weight terminal region.
-/
structure ReachableRecursiveInsertion
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    Prop where
  insert :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        TSNormal
            (n := n) (lowerWeight := lowerWeight + 1) H →
          SSInsert
            (n := n) (lowerWeight := lowerWeight) H

namespace TSNormal

/--
Reachable successive-stratum insertion plus the commutative terminal case
constructs a signed semantic normalizer at every support stratum.
-/
noncomputable def reachable_rec_insertion
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (step :
      ReachableRecursiveInsertion
        (n := n) H)
    (lowerWeight : ℕ) :
    TSNormal
      (n := n) (lowerWeight := lowerWeight) H :=
  if hterminal : n ≤ 2 * lowerWeight then
    of_highWeight hn H hH hterminal
  else
    ofInsertionKernel
      (step.insert lowerWeight hterminal
        (reachable_rec_insertion hn H hH step (lowerWeight + 1)))
termination_by n - lowerWeight
decreasing_by omega

end TSNormal

/--
List-valued More3 derivations for every reachable active stratum.
-/
structure TIDeriva
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    Prop where
  insert :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        TSNormal
            (n := n) (lowerWeight := lowerWeight + 1) H →
          ∀ (coordinates : CCRecipe H ι)
            (factor : SPFactor H ι),
            coordinates.NTBelow lowerWeight →
            lowerWeight ≤ factor.word.weight HEAddres.weight →
            factor.word.weight HEAddres.weight < n →
              ∃ next : CCRecipe H ι,
                next.NTBelow lowerWeight ∧
                  TSInsertb
                    (n := n) H ι lowerWeight
                      (coordinates.factors (n := n)) factor
                        (next.factors (n := n))

namespace TIDeriva

/-- Reachable More3 derivations supply the reachable semantic insertion step. -/
def reachableRecursiveInsertion
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (schedule :
      TIDeriva
        (n := n) H) :
    ReachableRecursiveInsertion
      (n := n) H where
  insert lowerWeight hnonterminal normalizer :=
    { insert := by
        intro ι coordinates factor hcoordinates hfactorSupported
          hfactorTruncated
        rcases schedule.insert (ι := ι) lowerWeight hnonterminal normalizer
            coordinates factor hcoordinates hfactorSupported hfactorTruncated with
          ⟨next, hnextSupported, hinsert⟩
        exact ⟨next, hnextSupported, hinsert.listEval_eq⟩ }

end TIDeriva

/--
The exact remaining reachable universal derivation builder.

Above the commutative terminal it is never called.  In the class-two band it
receives the automatic packet factory; below that band it receives the custom
factory supplied by `correctionFactory`.
-/
structure CDBuild
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) where
  correctionFactory :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 3 * lowerWeight →
        TSFtry
          (n := n) H lowerWeight
  insert :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        TSNormal
            (n := n) (lowerWeight := lowerWeight + 1) H →
          TSFtry
              (n := n) H lowerWeight →
            ∀ (coordinates : CCRecipe H ι)
              (factor : SPFactor H ι),
              coordinates.NTBelow lowerWeight →
              lowerWeight ≤ factor.word.weight HEAddres.weight →
              factor.word.weight HEAddres.weight < n →
                ∃ next : CCRecipe H ι,
                  next.NTBelow lowerWeight ∧
                    TSInsertb
                      (n := n) H ι lowerWeight
                        (coordinates.factors (n := n)) factor
                          (next.factors (n := n))

namespace CDBuild

/-- Use the automatic class-two packets whenever the active stratum permits it. -/
def packetFactoryAt
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (builder :
      CDBuild
        (n := n) H)
    (lowerWeight : ℕ) :
    TSFtry
      (n := n) H lowerWeight :=
  if hclassTwo : n ≤ 3 * lowerWeight then
    TSFtry.of_classTwo
      H hclassTwo
  else
    builder.correctionFactory lowerWeight hclassTwo

/-- A reachable universal builder supplies the reachable More3 schedule. -/
def reachableInsertionDerivation
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (builder :
      CDBuild
        (n := n) H) :
    TIDeriva
      (n := n) H where
  insert lowerWeight hnonterminal normalizer :=
    builder.insert lowerWeight hnonterminal normalizer
      (builder.packetFactoryAt H lowerWeight)

/-- A reachable universal builder supplies a semantic normalizer at every stratum. -/
noncomputable def supportedCoordinateNormalizer
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (builder :
      CDBuild
        (n := n) H)
    (lowerWeight : ℕ) :
    TSNormal
      (n := n) (lowerWeight := lowerWeight) H :=
  TSNormal.reachable_rec_insertion
    hn H hH
      (builder.reachableInsertionDerivation
        |>.reachableRecursiveInsertion)
      lowerWeight

end CDBuild

/--
A reachable universal signed builder and graded Hall bases construct product
recollection polynomials.
-/
theorem reachable_semantic_derivation
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (e : List (HEFam H))
    (builder :
      CDBuild
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  open TSNormal in
    signed_semantic_normalizer
      H e
        (reachable_rec_insertion hn H hH
          (builder.reachableInsertionDerivation
            |>.reachableRecursiveInsertion)
          1)

/--
A reachable universal signed builder and graded Hall bases construct inverse
recollection polynomials.
-/
theorem reachable_derivation_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (e : HEFam H)
    (builder :
      CDBuild
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  open TSNormal in
    collected_data_normalizer
      H e
        (reachable_rec_insertion hn H hH
          (builder.reachableInsertionDerivation
            |>.reachableRecursiveInsertion)
          1)

end TCTex
end Towers

/-!
# Sharp routing between active signed polynomial Hall blocks

One normalized active signed swap can be composed into larger finite
movements.  A single active factor moves left across an active block by
swapping across the final parent, recursively crossing the remaining prefix,
and moving the final parent left across the newly emitted higher residual.
Folding that operation across a second active block swaps two active blocks
while retaining every correction behind the active output.

These are the finite movements needed by a stable fixed-weight interleaver.
The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
A route moving one active signed factor left across an active block, with
every emitted correction retained behind the active output.
-/
structure SupportedSemanticRoute
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (left : List (SPFactor H ι))
    (factor : SPFactor H ι) where
  higherSource :
    List (SPFactor H ι)
  higher_least_succ :
    SPFactor.WordWeightLeast
      (lowerWeight + 1) higherSource
  rewrites :
    TSRw
      (n := n) (lowerWeight := lowerWeight)
        (left ++ [factor]) ([factor] ++ left ++ higherSource)

namespace TSFtry

/--
Move one active signed factor left across an active block by recursively
composing sharp active swaps.
-/
noncomputable def supportedSemanticRoute
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (family :
      SNFam
        (n := n) H)
    (factor : SPFactor H ι)
    (hfactor :
      factor.word.weight HEAddres.weight = lowerWeight)
    (left : List (SPFactor H ι))
    (hleft :
      SPFactor.WordWeightExactly lowerWeight left) :
    SupportedSemanticRoute
      (n := n) (lowerWeight := lowerWeight) H ι left factor :=
  List.reverseRecOn
    (motive := fun left =>
      SPFactor.WordWeightExactly lowerWeight left →
        SupportedSemanticRoute
          (n := n) (lowerWeight := lowerWeight) H ι left factor)
    left
    (fun _ =>
      { higherSource := []
        higher_least_succ := by
          intro x hx
          simp at hx
        rewrites := by
          simpa using
            (Relation.ReflTransGen.refl :
              TSRw
                (n := n) (lowerWeight := lowerWeight) [factor] [factor]) })
    (fun P B routeP hPB => by
      have hP :
          SPFactor.WordWeightExactly lowerWeight P :=
        fun x hx => hPB x (by simp [hx])
      have hB :
          B.word.weight HEAddres.weight = lowerWeight :=
        hPB B (by simp)
      let swapRoute :=
        factory.supportedSwapRoute family B factor
          hB hfactor
      let prefixRoute := routeP hP
      let parentRoute :=
        factory.supportedHigherRoute family
          prefixRoute.higherSource
            prefixRoute.higher_least_succ [B] (by
              intro x hx
              rcases List.mem_singleton.mp hx with rfl
              exact hB)
      refine
        { higherSource := parentRoute.higherSource ++ swapRoute.higherSource
          higher_least_succ := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact parentRoute.higher_least_succ x hx
            · exact swapRoute.higher_least_succ x hx
          rewrites := ?_ }
      have hswap :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              ((P ++ [B]) ++ [factor])
              (P ++ [factor, B] ++ swapRoute.higherSource) := by
        simpa [List.append_assoc] using
          swapRoute.rewrites.context P []
      have hprefix :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              (P ++ [factor, B] ++ swapRoute.higherSource)
              (([factor] ++ P ++ prefixRoute.higherSource) ++ [B] ++
                swapRoute.higherSource) := by
        simpa [List.append_assoc] using
          prefixRoute.rewrites.context [] ([B] ++ swapRoute.higherSource)
      have hparent :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              (([factor] ++ P ++ prefixRoute.higherSource) ++ [B] ++
                swapRoute.higherSource)
              ([factor] ++ (P ++ [B]) ++
                (parentRoute.higherSource ++ swapRoute.higherSource)) := by
        simpa [List.append_assoc] using
          parentRoute.rewrites.context ([factor] ++ P) swapRoute.higherSource
      exact hswap.trans (hprefix.trans hparent))
    hleft

end TSFtry

/--
A route moving one active signed block left across another active block, with
all corrections retained behind the active output.
-/
structure TruncatedSupportedRoute
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (left right : List (SPFactor H ι)) where
  higherSource :
    List (SPFactor H ι)
  higher_least_succ :
    SPFactor.WordWeightLeast
      (lowerWeight + 1) higherSource
  rewrites :
    TSRw
      (n := n) (lowerWeight := lowerWeight)
        (left ++ right) (right ++ left ++ higherSource)

namespace TSFtry

/-- Fold single-factor active signed routing across a second active block. -/
noncomputable def supportedActiveRoute
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (family :
      SNFam
        (n := n) H)
    (left : List (SPFactor H ι))
    (hleft :
      SPFactor.WordWeightExactly lowerWeight left) :
    ∀ (right : List (SPFactor H ι)),
      SPFactor.WordWeightExactly lowerWeight right →
        TruncatedSupportedRoute
          (n := n) (lowerWeight := lowerWeight) H ι left right
  | [], _ =>
      { higherSource := []
        higher_least_succ := by
          intro x hx
          simp at hx
        rewrites := by
          simpa using
            (Relation.ReflTransGen.refl :
              TSRw
                (n := n) (lowerWeight := lowerWeight) left left) }
  | A :: right, hright => by
      have hA :
          A.word.weight HEAddres.weight = lowerWeight :=
        hright A (by simp)
      have htail :
          SPFactor.WordWeightExactly lowerWeight right :=
        fun x hx => hright x (by simp [hx])
      let headRoute :=
        factory.supportedSemanticRoute family
          A hA left hleft
      let tailAcrossHigher :=
        factory.supportedHigherRoute family
          headRoute.higherSource
            headRoute.higher_least_succ right htail
      let tailRoute :=
        factory.supportedActiveRoute family
          left hleft right htail
      refine
        { higherSource := tailRoute.higherSource ++ tailAcrossHigher.higherSource
          higher_least_succ := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact tailRoute.higher_least_succ x hx
            · exact tailAcrossHigher.higher_least_succ x hx
          rewrites := ?_ }
      have hhead :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              (left ++ A :: right)
              (([A] ++ left ++ headRoute.higherSource) ++ right) := by
        simpa [List.append_assoc] using headRoute.rewrites.context [] right
      have hhigher :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              (([A] ++ left ++ headRoute.higherSource) ++ right)
              ([A] ++ (left ++ right) ++
                tailAcrossHigher.higherSource) := by
        simpa [List.append_assoc] using
          tailAcrossHigher.rewrites.context ([A] ++ left) []
      have htailRoute :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              ([A] ++ (left ++ right) ++ tailAcrossHigher.higherSource)
              ((A :: right) ++ left ++
                (tailRoute.higherSource ++
                  tailAcrossHigher.higherSource)) := by
        simpa [List.append_assoc] using
          tailRoute.rewrites.context [A] tailAcrossHigher.higherSource
      exact hhead.trans (hhigher.trans htailRoute)

end TSFtry

end TCTex
end Towers

/-!
# Sharp stable interleaving for active signed polynomial Hall blocks

Coordinatewise append of signed Hall recipes is a stable interleave.  This
file builds that interleave from sharp active-block movements while retaining
every emitted correction behind the active output.  It then packages the
interleave as the delegated fixed-weight merge route for a coordinate block
and the Hall-normal signed recipe endpoint of one active factor.

The intrinsic discrepancy between that Hall-normal endpoint and the original
factor is deliberately left separate.  It is the remaining factor-normalizing
packet obligation outside the terminal high-weight region.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
A route stably interleaving two families of active signed blocks, with all
emitted corrections retained behind the active output.
-/
structure SupportedInterleaveRoute
    {κ : Type*}
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (indices : List κ)
    (left right : κ → List (SPFactor H ι)) where
  higherSource :
    List (SPFactor H ι)
  higher_least_succ :
    SPFactor.WordWeightLeast
      (lowerWeight + 1) higherSource
  rewrites :
    TSRw
      (n := n) (lowerWeight := lowerWeight)
        (indices.flatMap left ++ indices.flatMap right)
        (indices.flatMap (fun i => left i ++ right i) ++ higherSource)

namespace TSFtry

/--
Stably interleave two finite families of active signed blocks.  Each right
block moves left across the remaining left blocks, and its fresh higher
residual is pushed behind the remaining right blocks before recursively
interleaving the tail.
-/
noncomputable def supportedInterleaveRoute
    {κ : Type*}
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (family :
      SNFam
        (n := n) H) :
    ∀ (indices : List κ)
      (left right : κ → List (SPFactor H ι)),
      (∀ i ∈ indices,
        SPFactor.WordWeightExactly lowerWeight
          (left i)) →
      (∀ i ∈ indices,
        SPFactor.WordWeightExactly lowerWeight
          (right i)) →
        SupportedInterleaveRoute
          (n := n) (lowerWeight := lowerWeight) H ι indices left right
  | [], _left, _right, _hleft, _hright =>
      { higherSource := []
        higher_least_succ := by
          intro x hx
          simp at hx
        rewrites := by
          simpa using
            (Relation.ReflTransGen.refl :
              TSRw
                (n := n) (lowerWeight := lowerWeight) [] []) }
  | i :: indices, left, right, hleft, hright => by
      have hleftHead :
          SPFactor.WordWeightExactly lowerWeight
            (left i) :=
        hleft i (by simp)
      have hrightHead :
          SPFactor.WordWeightExactly lowerWeight
            (right i) :=
        hright i (by simp)
      have hleftTail :
          ∀ j ∈ indices,
            SPFactor.WordWeightExactly lowerWeight
              (left j) :=
        fun j hj => hleft j (by simp [hj])
      have hrightTail :
          ∀ j ∈ indices,
            SPFactor.WordWeightExactly lowerWeight
              (right j) :=
        fun j hj => hright j (by simp [hj])
      have hleftFlat :
          SPFactor.WordWeightExactly lowerWeight
            (indices.flatMap left) := by
        intro x hx
        rcases List.mem_flatMap.mp hx with ⟨j, hj, hx⟩
        exact hleftTail j hj x hx
      have hrightFlat :
          SPFactor.WordWeightExactly lowerWeight
            (indices.flatMap right) := by
        intro x hx
        rcases List.mem_flatMap.mp hx with ⟨j, hj, hx⟩
        exact hrightTail j hj x hx
      let move :=
        factory.supportedActiveRoute family
          (indices.flatMap left) hleftFlat (right i) hrightHead
      let push :=
        factory.supportedHigherRoute family
          move.higherSource move.higher_least_succ
            (indices.flatMap right) hrightFlat
      let tail :=
        factory.supportedInterleaveRoute
          family indices left right hleftTail hrightTail
      refine
        { higherSource := tail.higherSource ++ push.higherSource
          higher_least_succ := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact tail.higher_least_succ x hx
            · exact push.higher_least_succ x hx
          rewrites := ?_ }
      have hmove :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              (left i ++ indices.flatMap left ++ right i ++
                indices.flatMap right)
              (left i ++ right i ++ indices.flatMap left ++
                move.higherSource ++ indices.flatMap right) := by
        simpa [List.append_assoc] using
          move.rewrites.context (left i) (indices.flatMap right)
      have hpush :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              (left i ++ right i ++ indices.flatMap left ++
                move.higherSource ++ indices.flatMap right)
              (left i ++ right i ++ indices.flatMap left ++
                indices.flatMap right ++ push.higherSource) := by
        simpa [List.append_assoc] using
          push.rewrites.context (left i ++ right i ++ indices.flatMap left) []
      have htail :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              (left i ++ right i ++ indices.flatMap left ++
                indices.flatMap right ++ push.higherSource)
              ((left i ++ right i) ++
                indices.flatMap (fun j => left j ++ right j) ++
                  (tail.higherSource ++ push.higherSource)) := by
        simpa [List.append_assoc] using
          tail.rewrites.context (left i ++ right i) push.higherSource
      simpa only [List.flatMap_cons, List.append_assoc] using
        hmove.trans (hpush.trans htail)

end TSFtry

namespace CCRecipe

/-- Every signed factor in one normalized Hall layer has exactly its layer weight. -/
lemma word_exactly_factors
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (coordinates : CCRecipe H ι)
    (weight : ℕ) :
    SPFactor.WordWeightExactly weight
      (coordinates.weightFactors weight) :=
  fun _x hx => coordinates.word_weight_factors hx

end CCRecipe

/--
A delegated fixed-weight merge route.  Its signed obstruction run merges the
old active Hall block with the active layer of one factor's Hall-normal signed
recipe endpoint, leaving only strictly heavier corrections.
-/
structure TDMerge
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (ι : Type)
    (coordinates : CCRecipe H ι)
    (factor : SPFactor H ι) where
  higherSource :
    List (SPFactor H ι)
  higher_least_succ :
    SPFactor.WordWeightLeast
      (lowerWeight + 1) higherSource
  rewrites :
    TSRw
      (n := n) (lowerWeight := lowerWeight)
      (coordinates.weightFactors lowerWeight ++
        (factor.signedCoordinateRecipes hn H hH).weightFactors
          lowerWeight)
      ((coordinates.add
          (factor.signedCoordinateRecipes hn H hH)).weightFactors
            lowerWeight ++ higherSource)

namespace TSFtry

/--
The sharp stable signed interleaver supplies the delegated fixed-weight merge
route for a coordinate block and one factor's Hall-normal signed endpoint.
-/
noncomputable def delegatedMergeRoute
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (family :
      SNFam
        (n := n) H)
    (coordinates : CCRecipe H ι)
    (factor : SPFactor H ι) :
    TDMerge
      (lowerWeight := lowerWeight) hn H hH ι coordinates factor := by
  let X := factor.signedCoordinateRecipes hn H hH
  let indices := Finset.univ.sort fun i i' : (H lowerWeight).index => i ≤ i'
  let left := fun i =>
    (coordinates.formulas lowerWeight i).map fun formula =>
      formula.symbolicPolynomialFactor i
  let right := fun i =>
    (X.formulas lowerWeight i).map fun formula =>
      formula.symbolicPolynomialFactor i
  let route :=
    factory.supportedInterleaveRoute family
      indices left right
      (fun i _hi x hx => by
        rcases List.mem_map.mp hx with ⟨formula, _hformula, rfl⟩
        rfl)
      (fun i _hi x hx => by
        rcases List.mem_map.mp hx with ⟨formula, _hformula, rfl⟩
        rfl)
  refine
    { higherSource := route.higherSource
      higher_least_succ :=
        route.higher_least_succ
      rewrites := ?_ }
  change
    TSRw
      (n := n) (lowerWeight := lowerWeight)
        (indices.flatMap left ++ indices.flatMap right)
        ((coordinates.add X).weightFactors lowerWeight ++ route.higherSource)
  have htarget :
      indices.flatMap (fun i => left i ++ right i) =
        (coordinates.add X).weightFactors lowerWeight := by
    unfold CCRecipe.weightFactors
    dsimp [CCRecipe.add, X, indices, left, right]
    induction (Finset.univ.sort fun i i' : (H lowerWeight).index => i ≤ i') with
    | nil => rfl
    | cons i indices ih =>
        simp only [List.flatMap_cons, List.map_append]
  rw [← htarget]
  exact route.rewrites

end TSFtry

end TCTex
end Towers

/-!
# Active-block routing from strictly deeper signed normalizers

This file reconstructs sharp signed active-block movement and stable
fixed-weight interleaving from the local parent-sharp correction normalizer.
Unlike the earlier all-strata-family constructors, these routes only consume
normalizers strictly above the active stratum.  They are therefore suitable
for direct well-founded recursion on the remaining nilpotent cutoff depth.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace TSFtry

/-- Fold restricted sharp higher-tail routing across an active signed block. -/
noncomputable def higher_sharp_normalizer
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (higher : List (SPFactor H ι))
    (hhigher :
      SPFactor.WordWeightLeast
        (lowerWeight + 1) higher) :
    ∀ (active : List (SPFactor H ι)),
      SPFactor.WordWeightExactly lowerWeight active →
        SupportedHigherRoute
          (n := n) (lowerWeight := lowerWeight) H ι higher active
  | [], _ =>
      { higherSource := higher
        higher_least_succ := hhigher
        rewrites := by
          simpa using
            (Relation.ReflTransGen.refl :
              TSRw
                (n := n) (lowerWeight := lowerWeight) higher higher) }
  | A :: active, hactive => by
      have hA :
          A.word.weight HEAddres.weight = lowerWeight :=
        hactive A (by simp)
      have htail :
          SPFactor.WordWeightExactly lowerWeight active :=
        fun x hx => hactive x (by simp [hx])
      let headRoute :=
        factory.supported_higher_normalizer
          sharp A hA higher hhigher
      let tailRoute :=
        factory.higher_sharp_normalizer
          sharp headRoute.higherSource
            headRoute.higher_least_succ active htail
      refine
        { higherSource := tailRoute.higherSource
          higher_least_succ :=
            tailRoute.higher_least_succ
          rewrites := ?_ }
      have hhead :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              (higher ++ A :: active)
              (([A] ++ headRoute.higherSource) ++ active) := by
        simpa [List.append_assoc] using
          headRoute.inserts.rewrites.context [] active
      have htailRoute :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              (([A] ++ headRoute.higherSource) ++ active)
              ((A :: active) ++ tailRoute.higherSource) := by
        simpa [List.append_assoc] using tailRoute.rewrites.context [A] []
      exact hhead.trans htailRoute

/-- One active swap with all restricted sharp corrections moved behind it. -/
noncomputable def swap_sharp_normalizer
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (B A : SPFactor H ι)
    (hB : B.word.weight HEAddres.weight = lowerWeight)
    (hA : A.word.weight HEAddres.weight = lowerWeight) :
    SupportedSwapRoute
      (n := n) (lowerWeight := lowerWeight) H ι B A := by
  have hBSupported :
      lowerWeight ≤ B.word.weight HEAddres.weight := by
    omega
  have hASupported :
      lowerWeight ≤ A.word.weight HEAddres.weight := by
    omega
  let C := factory.packet B A hBSupported hASupported
  let normalization := sharp.normalize C hBSupported
  let route :=
    factory.higher_sharp_normalizer
      sharp (normalization.coordinates.factors (n := n))
        normalization.weight_least_succ [A, B] (by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact hA
          · exact hB)
  refine
    { higherSource := route.higherSource
      higher_least_succ :=
        route.higher_least_succ
      rewrites := ?_ }
  have hswap :
      TSRw
        (n := n) (lowerWeight := lowerWeight)
          [B, A]
          (normalization.coordinates.factors (n := n) ++ [A, B]) := by
    apply
      TSRw.single
    simpa using
      (TSSem.obstruction
        (n := n) (lowerWeight := lowerWeight) [] [] B A C normalization)
  exact hswap.trans route.rewrites

/-- Move one active factor across an active block using restricted sharp swaps. -/
noncomputable def supported_active_normalizer
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (factor : SPFactor H ι)
    (hfactor : factor.word.weight HEAddres.weight = lowerWeight)
    (left : List (SPFactor H ι))
    (hleft :
      SPFactor.WordWeightExactly lowerWeight left) :
    SupportedSemanticRoute
      (n := n) (lowerWeight := lowerWeight) H ι left factor :=
  List.reverseRecOn
    (motive := fun left =>
      SPFactor.WordWeightExactly lowerWeight left →
        SupportedSemanticRoute
          (n := n) (lowerWeight := lowerWeight) H ι left factor)
    left
    (fun _ =>
      { higherSource := []
        higher_least_succ := by
          intro x hx
          simp at hx
        rewrites := by
          simpa using
            (Relation.ReflTransGen.refl :
              TSRw
                (n := n) (lowerWeight := lowerWeight) [factor] [factor]) })
    (fun P B routeP hPB => by
      have hP :
          SPFactor.WordWeightExactly lowerWeight P :=
        fun x hx => hPB x (by simp [hx])
      have hB :
          B.word.weight HEAddres.weight = lowerWeight :=
        hPB B (by simp)
      let swapRoute :=
        factory.swap_sharp_normalizer
          sharp B factor hB hfactor
      let prefixRoute := routeP hP
      let parentRoute :=
        factory.higher_sharp_normalizer
          sharp prefixRoute.higherSource
            prefixRoute.higher_least_succ [B] (by
              intro x hx
              rcases List.mem_singleton.mp hx with rfl
              exact hB)
      refine
        { higherSource := parentRoute.higherSource ++ swapRoute.higherSource
          higher_least_succ := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact parentRoute.higher_least_succ x hx
            · exact swapRoute.higher_least_succ x hx
          rewrites := ?_ }
      have hswap :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              ((P ++ [B]) ++ [factor])
              (P ++ [factor, B] ++ swapRoute.higherSource) := by
        simpa [List.append_assoc] using swapRoute.rewrites.context P []
      have hprefix :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              (P ++ [factor, B] ++ swapRoute.higherSource)
              (([factor] ++ P ++ prefixRoute.higherSource) ++ [B] ++
                swapRoute.higherSource) := by
        simpa [List.append_assoc] using
          prefixRoute.rewrites.context [] ([B] ++ swapRoute.higherSource)
      have hparent :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              (([factor] ++ P ++ prefixRoute.higherSource) ++ [B] ++
                swapRoute.higherSource)
              ([factor] ++ (P ++ [B]) ++
                (parentRoute.higherSource ++ swapRoute.higherSource)) := by
        simpa [List.append_assoc] using
          parentRoute.rewrites.context ([factor] ++ P) swapRoute.higherSource
      exact hswap.trans (hprefix.trans hparent))
    hleft

/-- Move one active block across another using restricted sharp routing. -/
noncomputable def
  supported_sharp_normalizer
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (left : List (SPFactor H ι))
    (hleft :
      SPFactor.WordWeightExactly lowerWeight left) :
    ∀ (right : List (SPFactor H ι)),
      SPFactor.WordWeightExactly lowerWeight right →
        TruncatedSupportedRoute
          (n := n) (lowerWeight := lowerWeight) H ι left right
  | [], _ =>
      { higherSource := []
        higher_least_succ := by
          intro x hx
          simp at hx
        rewrites := by
          simpa using
            (Relation.ReflTransGen.refl :
              TSRw
                (n := n) (lowerWeight := lowerWeight) left left) }
  | A :: right, hright => by
      have hA :
          A.word.weight HEAddres.weight = lowerWeight :=
        hright A (by simp)
      have htail :
          SPFactor.WordWeightExactly lowerWeight right :=
        fun x hx => hright x (by simp [hx])
      let headRoute :=
        factory.supported_active_normalizer
          sharp A hA left hleft
      let tailAcrossHigher :=
        factory.higher_sharp_normalizer
          sharp headRoute.higherSource
            headRoute.higher_least_succ right htail
      let tailRoute :=
        factory.supported_sharp_normalizer
          sharp left hleft right htail
      refine
        { higherSource := tailRoute.higherSource ++ tailAcrossHigher.higherSource
          higher_least_succ := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact tailRoute.higher_least_succ x hx
            · exact tailAcrossHigher.higher_least_succ x hx
          rewrites := ?_ }
      have hhead :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              (left ++ A :: right)
              (([A] ++ left ++ headRoute.higherSource) ++ right) := by
        simpa [List.append_assoc] using headRoute.rewrites.context [] right
      have hhigher :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              (([A] ++ left ++ headRoute.higherSource) ++ right)
              ([A] ++ (left ++ right) ++ tailAcrossHigher.higherSource) := by
        simpa [List.append_assoc] using
          tailAcrossHigher.rewrites.context ([A] ++ left) []
      have htailRoute :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              ([A] ++ (left ++ right) ++ tailAcrossHigher.higherSource)
              ((A :: right) ++ left ++
                (tailRoute.higherSource ++ tailAcrossHigher.higherSource)) := by
        simpa [List.append_assoc] using
          tailRoute.rewrites.context [A] tailAcrossHigher.higherSource
      exact hhead.trans (hhigher.trans htailRoute)

/-- Stable fixed-weight signed interleaving from restricted sharp routing. -/
noncomputable def active_sharp_normalizer
    {κ : Type*}
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H) :
    ∀ (indices : List κ)
      (left right : κ → List (SPFactor H ι)),
      (∀ i ∈ indices,
        SPFactor.WordWeightExactly lowerWeight
          (left i)) →
      (∀ i ∈ indices,
        SPFactor.WordWeightExactly lowerWeight
          (right i)) →
        SupportedInterleaveRoute
          (n := n) (lowerWeight := lowerWeight) H ι indices left right
  | [], _left, _right, _hleft, _hright =>
      { higherSource := []
        higher_least_succ := by
          intro x hx
          simp at hx
        rewrites := by
          simpa using
            (Relation.ReflTransGen.refl :
              TSRw
                (n := n) (lowerWeight := lowerWeight) [] []) }
  | i :: indices, left, right, hleft, hright => by
      have hleftTail :
          ∀ j ∈ indices,
            SPFactor.WordWeightExactly lowerWeight
              (left j) :=
        fun j hj => hleft j (by simp [hj])
      have hrightTail :
          ∀ j ∈ indices,
            SPFactor.WordWeightExactly lowerWeight
              (right j) :=
        fun j hj => hright j (by simp [hj])
      have hleftFlat :
          SPFactor.WordWeightExactly lowerWeight
            (indices.flatMap left) := by
        intro x hx
        rcases List.mem_flatMap.mp hx with ⟨j, hj, hx⟩
        exact hleftTail j hj x hx
      have hrightFlat :
          SPFactor.WordWeightExactly lowerWeight
            (indices.flatMap right) := by
        intro x hx
        rcases List.mem_flatMap.mp hx with ⟨j, hj, hx⟩
        exact hrightTail j hj x hx
      let move :=
        factory.supported_sharp_normalizer
          sharp (indices.flatMap left) hleftFlat (right i)
            (hright i (by simp))
      let push :=
        factory.higher_sharp_normalizer
          sharp move.higherSource move.higher_least_succ
            (indices.flatMap right) hrightFlat
      let tail :=
        factory.active_sharp_normalizer
          sharp indices left right hleftTail hrightTail
      refine
        { higherSource := tail.higherSource ++ push.higherSource
          higher_least_succ := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact tail.higher_least_succ x hx
            · exact push.higher_least_succ x hx
          rewrites := ?_ }
      have hmove :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              (left i ++ indices.flatMap left ++ right i ++ indices.flatMap right)
              (left i ++ right i ++ indices.flatMap left ++
                move.higherSource ++ indices.flatMap right) := by
        simpa [List.append_assoc] using
          move.rewrites.context (left i) (indices.flatMap right)
      have hpush :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              (left i ++ right i ++ indices.flatMap left ++
                move.higherSource ++ indices.flatMap right)
              (left i ++ right i ++ indices.flatMap left ++
                indices.flatMap right ++ push.higherSource) := by
        simpa [List.append_assoc] using
          push.rewrites.context (left i ++ right i ++ indices.flatMap left) []
      have htail :
          TSRw
            (n := n) (lowerWeight := lowerWeight)
              (left i ++ right i ++ indices.flatMap left ++
                indices.flatMap right ++ push.higherSource)
              ((left i ++ right i) ++
                indices.flatMap (fun j => left j ++ right j) ++
                  (tail.higherSource ++ push.higherSource)) := by
        simpa [List.append_assoc] using
          tail.rewrites.context (left i ++ right i) push.higherSource
      simpa only [List.flatMap_cons, List.append_assoc] using
        hmove.trans (hpush.trans htail)

/-- The restricted sharp interleaver supplies the delegated coordinate merge route. -/
noncomputable def coord_sharp_normalizer
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (coordinates : CCRecipe H ι)
    (factor : SPFactor H ι) :
    TDMerge
      (lowerWeight := lowerWeight) hn H hH ι coordinates factor := by
  let X := factor.signedCoordinateRecipes hn H hH
  let indices := Finset.univ.sort fun i i' : (H lowerWeight).index => i ≤ i'
  let left := fun i =>
    (coordinates.formulas lowerWeight i).map fun formula =>
      formula.symbolicPolynomialFactor i
  let right := fun i =>
    (X.formulas lowerWeight i).map fun formula =>
      formula.symbolicPolynomialFactor i
  let route :=
    factory.active_sharp_normalizer
      sharp indices left right
      (fun i _hi x hx => by
        rcases List.mem_map.mp hx with ⟨formula, _hformula, rfl⟩
        rfl)
      (fun i _hi x hx => by
        rcases List.mem_map.mp hx with ⟨formula, _hformula, rfl⟩
        rfl)
  refine
    { higherSource := route.higherSource
      higher_least_succ :=
        route.higher_least_succ
      rewrites := ?_ }
  change
    TSRw
      (n := n) (lowerWeight := lowerWeight)
        (indices.flatMap left ++ indices.flatMap right)
        ((coordinates.add X).weightFactors lowerWeight ++ route.higherSource)
  have htarget :
      indices.flatMap (fun i => left i ++ right i) =
        (coordinates.add X).weightFactors lowerWeight := by
    unfold CCRecipe.weightFactors
    dsimp [CCRecipe.add, X, indices, left, right]
    induction (Finset.univ.sort fun i i' : (H lowerWeight).index => i ≤ i') with
    | nil => rfl
    | cons i indices ih =>
        simp only [List.flatMap_cons, List.map_append]
  rw [← htarget]
  exact route.rewrites

end TSFtry

end TCTex
end Towers

/-!
# Reducing signed active-block recollection to intrinsic factor residuals

The sharp stable interleaver constructs the residual created while merging
two normalized fixed-weight Hall blocks.  One independent discrepancy remains:
outside the terminal high-weight band, the Hall-normal signed recipe endpoint
of the inserted factor need not yet evaluate to the factor itself.

This file separates those two residuals.  It proves that sharp interleaving
supplies the merge residual automa, packages the intrinsic factor
normalization residual, and combines them into the active-block resolution
consumed by signed filtration recursion.  The terminal high-weight intrinsic
factor residual is the canonical Hall-normal tail.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace SPFactor

/-- The active Hall layer of one factor's Hall-normal signed endpoint. -/
noncomputable def activeNormalValue
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (factor : SPFactor H ι)
    (e : ι → HEFam H) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  SPFactor.listEval (n := n) e
    ((factor.signedCoordinateRecipes hn H hH).weightFactors
      lowerWeight)

/-- The intrinsic discrepancy after retaining only the factor's active layer. -/
noncomputable def activeBlockValue
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (factor : SPFactor H ι)
    (e : ι → HEFam H) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  (factor.activeNormalValue
      (lowerWeight := lowerWeight) hn H hH e)⁻¹ *
    factor.eval (n := n) e

end SPFactor

namespace CCRecipe

/--
The higher correction created while merging an old active layer with the
inserted factor's active Hall-normal layer.
-/
noncomputable def activeMergeValue
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (coordinates : CCRecipe H ι)
    (factor : SPFactor H ι)
    (e : ι → HEFam H) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  (SPFactor.listEval (n := n) e
      ((coordinates.add
        (factor.signedCoordinateRecipes hn H hH)).weightFactors
          lowerWeight))⁻¹ *
    (SPFactor.listEval e
        (coordinates.weightFactors lowerWeight) *
      factor.activeNormalValue
        (lowerWeight := lowerWeight) hn H hH e)

end CCRecipe

/-- A bounded signed expansion of one factor's intrinsic Hall-normal residual. -/
structure TPExp
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (ι : Type)
    (factor : SPFactor H ι) where
  higherSource :
    List (SPFactor H ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_least_succ :
    SPFactor.WordWeightLeast
      (lowerWeight + 1) higherSource
  list_factor_value :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e higherSource =
        factor.activeBlockValue
          (lowerWeight := lowerWeight) hn H hH e

/-- A bounded signed expansion of the fixed-weight coordinate merge residual. -/
structure TPMerge
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (ι : Type)
    (coordinates : CCRecipe H ι)
    (factor : SPFactor H ι) where
  higherSource :
    List (SPFactor H ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_least_succ :
    SPFactor.WordWeightLeast
      (lowerWeight + 1) higherSource
  list_merge_value :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e higherSource =
        coordinates.activeMergeValue
          (lowerWeight := lowerWeight) hn H hH factor e

namespace TDMerge

/-- A sharp delegated signed merge route supplies its semantic residual expansion. -/
noncomputable def mergeResidualExpansion
    {d n lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)}
    {ι : Type}
    {coordinates : CCRecipe H ι}
    {factor : SPFactor H ι}
    (route :
      TDMerge
        (lowerWeight := lowerWeight) hn H hH ι coordinates factor)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TPMerge
      (lowerWeight := lowerWeight) hn H hH ι coordinates factor := by
  let X := factor.signedCoordinateRecipes hn H hH
  have hlowerWeightTruncated : lowerWeight < n := by
    omega
  have hsourceTruncated :
      SPFactor.IsTruncated n
        (coordinates.weightFactors lowerWeight ++ X.weightFactors lowerWeight) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [coordinates.word_weight_factors hx]
      exact hlowerWeightTruncated
    · rw [X.word_weight_factors hx]
      exact hlowerWeightTruncated
  have houtputTruncated :
      SPFactor.IsTruncated n
        ((coordinates.add X).weightFactors lowerWeight ++
          route.higherSource) :=
    route.rewrites.isTruncated hsourceTruncated
  refine
    { higherSource := route.higherSource
      higher_source_truncated := ?_
      higher_least_succ :=
        route.higher_least_succ
      list_merge_value := ?_ }
  · intro x hx
    exact houtputTruncated x (List.mem_append_right _ hx)
  · intro e
    unfold CCRecipe.activeMergeValue
      SPFactor.activeNormalValue
    change
      SPFactor.listEval (n := n) e route.higherSource =
        (SPFactor.listEval e
            ((coordinates.add X).weightFactors lowerWeight))⁻¹ *
          (SPFactor.listEval e
              (coordinates.weightFactors lowerWeight) *
            SPFactor.listEval e
              (X.weightFactors lowerWeight))
    rw [← SPFactor.listEval_append,
      ← route.rewrites.listEval_eq e,
      SPFactor.listEval_append]
    dsimp [X]
    group

end TDMerge

namespace TPExp

/--
In the terminal high-weight band, the Hall-normal signed tail is the intrinsic
factor residual.
-/
noncomputable def of_highWeight
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (hcutoff : n ≤ 2 * lowerWeight)
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TPExp
      (lowerWeight := lowerWeight) hn H hH ι factor := by
  let X := factor.signedCoordinateRecipes hn H hH
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    have hfactorPos := factor.word_weight_pos
    omega
  have hlowerWeightCutoff : lowerWeight ≤ n - 1 := by
    omega
  have hXSupport : X.NTBelow lowerWeight := by
    exact factor.no_below_recipes
      hn H hH (by omega)
  refine
    { higherSource := X.tailFactors (n := n) lowerWeight
      higher_source_truncated := X.truncated_factors hlowerWeightCutoff
      higher_least_succ :=
        X.word_least_factors
      list_factor_value := ?_ }
  intro e
  change
    SPFactor.listEval (n := n) e
        (X.tailFactors (n := n) lowerWeight) =
      (SPFactor.listEval e
          (X.weightFactors lowerWeight))⁻¹ *
        factor.eval e
  rw [← factor.list_factors_recipes
    hn H hH hfactorTruncated (by omega) e]
  rw [X.append_no_below
    hXSupport hlowerWeightPos hlowerWeightCutoff]
  rw [SPFactor.listEval_append]
  group

end TPExp

namespace TPMerge

/--
Merge and intrinsic factor residuals assemble the active-block resolution
consumed by the next-stratum normalizer.
-/
noncomputable def activeBlockResolution
    {d n lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)}
    {ι : Type}
    {coordinates : CCRecipe H ι}
    {factor : SPFactor H ι}
    (merge :
      TPMerge
        (lowerWeight := lowerWeight) hn H hH ι coordinates factor)
    (factorTail :
      TPExp
        (lowerWeight := lowerWeight) hn H hH ι factor)
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight) :
    SupportedSemanticResolution
      (n := n) (lowerWeight := lowerWeight) H ι coordinates factor := by
  let X := factor.signedCoordinateRecipes hn H hH
  refine
    { activeCoordinates := coordinates.add X
      active_terms_below :=
        hcoordinates.add
          (factor.no_below_recipes
            hn H hH (by omega))
      higherSource := merge.higherSource ++ factorTail.higherSource
      higher_source_truncated := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact merge.higher_source_truncated x hx
        · exact factorTail.higher_source_truncated x hx
      higher_least_succ := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact merge.higher_least_succ x hx
        · exact factorTail.higher_least_succ x hx
      active_append_source := ?_ }
  intro e
  rw [SPFactor.listEval_append,
    SPFactor.listEval_append,
    merge.list_merge_value,
    factorTail.list_factor_value,
    SPFactor.listEval_append]
  unfold CCRecipe.activeMergeValue
    SPFactor.activeBlockValue
    SPFactor.activeNormalValue
  dsimp [X]
  simp only [SPFactor.listEval,     ]
  group

end TPMerge

namespace TSFtry

/--
Sharp fixed-weight merging and one intrinsic factor residual expansion supply
the signed active-block residual resolution.
-/
noncomputable def supportedSemanticResolution
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (family :
      SNFam
        (n := n) H)
    (coordinates : CCRecipe H ι)
    (factor : SPFactor H ι)
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (factorTail :
      TPExp
        (lowerWeight := lowerWeight) hn H hH ι factor) :
    SupportedSemanticResolution
      (n := n) (lowerWeight := lowerWeight) H ι coordinates factor :=
  (factory.delegatedMergeRoute
      hn H hH family coordinates factor
    |>.mergeResidualExpansion hfactorWeight hfactorTruncated)
    |>.activeBlockResolution factorTail hcoordinates hfactorWeight

end TSFtry

end TCTex
end Towers

/-!
# Direct recursive signed collection from restricted sharp routing

The restricted sharp router exposes the true recursive dependency of signed
Hall recollection: collecting at ordinary weight `lowerWeight` only asks for
semantic normalizers at strictly larger weights.  This permits a direct
well-founded construction of the global signed normalizer.

The remaining custom data is now narrow:

* correction packets below the automatic class-two band
  `n ≤ 3 * lowerWeight`;
* intrinsic factor-normalization residual expansions below the commutative
  terminal band `n ≤ 2 * lowerWeight`.

Stable fixed-weight merging, movement across the old higher tail, and all
recursive correction routing are constructed automa.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
The remaining reachable data for direct global signed Hall recollection.
-/
structure SRBuild
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)) where
  correctionFactory :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 3 * lowerWeight →
        TSFtry
          (n := n) H lowerWeight
  factorResidual :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        TSNormal
            (n := n) (lowerWeight := lowerWeight + 1) H →
          ∀ (factor : SPFactor H ι),
            factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TPExp
                (lowerWeight := lowerWeight) hn H hH ι factor

namespace SRBuild

/-- Select automatic class-two packets whenever the current stratum permits it. -/
def packetFactoryAt
    {d n : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)}
    (builder :
      SRBuild
        (n := n) hn H hH)
    (lowerWeight : ℕ) :
    TSFtry
      (n := n) H lowerWeight :=
  if hclassTwo : n ≤ 3 * lowerWeight then
    TSFtry.of_classTwo
      H hclassTwo
  else
    builder.correctionFactory lowerWeight hclassTwo

/--
Directly construct the signed semantic normalizer at one support bound.
Every recursive use occurs at a strictly larger support weight.
-/
noncomputable def supportedCoordinateNormalizer
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (builder :
      SRBuild
        (n := n) hn H hH)
    (lowerWeight : ℕ) :
    TSNormal
      (n := n) (lowerWeight := lowerWeight) H :=
  if hterminal : n ≤ 2 * lowerWeight then
    TSNormal.of_highWeight
      hn H hH hterminal
  else
    TSNormal.ofInsertionKernel
      { insert := by
          intro ι coordinates factor hcoordinates hfactorSupported
            hfactorTruncated
          let nextNormalizer :=
            builder.supportedCoordinateNormalizer
              hn H hH (lowerWeight + 1)
          by_cases hfactorStrict :
              lowerWeight <
                factor.word.weight HEAddres.weight
          · exact
              nextNormalizer.insertion_word_weight coordinates
                factor hcoordinates hfactorStrict hfactorTruncated
          · have hfactorWeight :
                factor.word.weight HEAddres.weight = lowerWeight := by
              omega
            let sharp :
                TSNormala
                  (n := n) (lowerWeight := lowerWeight) H :=
              TSNormala.ofNormalizerAbove
                (lowerWeight := lowerWeight)
                (fun strongerWeight
                    (_hstronger : lowerWeight < strongerWeight) =>
                  builder.supportedCoordinateNormalizer
                    hn H hH strongerWeight)
            let packetFactory := builder.packetFactoryAt lowerWeight
            let factorTail :=
              builder.factorResidual lowerWeight hterminal nextNormalizer
                factor hfactorWeight hfactorTruncated
            let merge :=
              (packetFactory
                |>.coord_sharp_normalizer
                  hn H hH sharp coordinates factor)
                |>.mergeResidualExpansion hfactorWeight hfactorTruncated
            let block :=
              merge.activeBlockResolution factorTail hcoordinates
                hfactorWeight
            let tail :=
              (packetFactory
                |>.supported_route_normalizer
                  sharp coordinates factor hfactorWeight)
                |>.higherTailResolution hfactorWeight hfactorTruncated
            exact
              (TPResolu.active_block_tail
                hcoordinates hfactorWeight hfactorTruncated block tail)
                |>.exists_insertion nextNormalizer hfactorWeight
                  hfactorTruncated }
termination_by n - lowerWeight
decreasing_by
  all_goals
    have hlowerWeightCutoff : lowerWeight < n := by
      omega
    omega

end SRBuild

/--
Restricted sharp recursive data and graded Hall bases construct product
recollection polynomials.
-/
theorem restricted_recursive_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : List (HEFam H))
    (builder :
      SRBuild
        (n := n) hn H hH) :
    CollectedCoordinateData (n := n) H e :=
  signed_semantic_normalizer
    H e
      (builder.supportedCoordinateNormalizer hn H hH 1)

/--
Restricted sharp recursive data and graded Hall bases construct inverse
recollection polynomials.
-/
theorem restricted_sharp_recursive
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : HEFam H)
    (builder :
      SRBuild
        (n := n) hn H hH) :
    CollectedInverseData (n := n) H e :=
  collected_data_normalizer
    H e
      (builder.supportedCoordinateNormalizer hn H hH 1)

end TCTex
end Towers

/-!
# Universal signed collection from intrinsic factor residual expansions

Sharp signed routing removes two operational obligations automa:

* stable fixed-weight active-block merging follows from correction packets;
* movement through the old strictly higher tail follows from the terminating
  parent-sharp multiset recursion.

The remaining local input is an expansion of the intrinsic discrepancy
between one active factor and the active layer of its Hall-normal signed
endpoint.  This file packages a stratum-indexed supply of those expansions
and compiles it, together with packet factories and a sharp normalizer family,
to the recursive signed collector and the product and inverse recollection
polynomials.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/-- Intrinsic signed factor-normalization residual expansions at every stratum. -/
structure TPSched
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)) where
  expand :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      TSNormal
          (n := n) (lowerWeight := lowerWeight + 1) H →
        ∀ (factor : SPFactor H ι),
          factor.word.weight HEAddres.weight = lowerWeight →
          factor.word.weight HEAddres.weight < n →
            TPExp
              (lowerWeight := lowerWeight) hn H hH ι factor

namespace TPSched

open TPResolu

/--
Intrinsic factor residual expansions, packet factories, and a sharp
normalizer family supply the active signed insertion branch.
-/
noncomputable def insertionBranch
    {d n : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)}
    (factorSchedule :
      TPSched
        (n := n) hn H hH)
    (packetSchedule :
      SFSched
        (n := n) H)
    (family :
      SNFam
        (n := n) H) :
    SupportedInsertionBranch
      (n := n) H where
  insert lowerWeight normalizer coordinates factor hcoordinates hfactorWeight
      hfactorTruncated := by
    let factorTail :=
      factorSchedule.expand lowerWeight normalizer factor hfactorWeight
        hfactorTruncated
    let block :=
      (packetSchedule.factory lowerWeight)
        |>.supportedSemanticResolution
          hn H hH family coordinates factor hcoordinates hfactorWeight
            hfactorTruncated factorTail
    let tail :=
      ((packetSchedule.recursiveRouteSchedule
          family).route lowerWeight normalizer coordinates factor hcoordinates
            hfactorWeight hfactorTruncated)
        |>.higherTailResolution hfactorWeight hfactorTruncated
    exact
      (active_block_tail hcoordinates hfactorWeight
        hfactorTruncated block tail)
        |>.exists_insertion normalizer hfactorWeight hfactorTruncated

/--
Intrinsic factor residual expansions, packet factories, and a sharp
normalizer family supply the complete recursive signed insertion step.
-/
noncomputable def recursiveInsertionStep
    {d n : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)}
    (factorSchedule :
      TPSched
        (n := n) hn H hH)
    (packetSchedule :
      SFSched
        (n := n) H)
    (family :
      SNFam
        (n := n) H) :
    TSInsert
      (n := n) H :=
  TSInsert.insertion_branch
    (factorSchedule.insertionBranch packetSchedule family)

end TPSched

/--
Intrinsic factor residual expansions, packet factories, and a sharp
normalizer family construct product recollection polynomials.
-/
theorem collected_expansion_schedule
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : List (HEFam H))
    (factorSchedule :
      TPSched
        (n := n) hn H hH)
    (packetSchedule :
      SFSched
        (n := n) H)
    (family :
      SNFam
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  collected_semantic_insertion
    H e
      (factorSchedule.recursiveInsertionStep
        packetSchedule family)

/--
Intrinsic factor residual expansions, packet factories, and a sharp
normalizer family construct inverse recollection polynomials.
-/
theorem collected_coord_schedule
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : HEFam H)
    (factorSchedule :
      TPSched
        (n := n) hn H hH)
    (packetSchedule :
      SFSched
        (n := n) H)
    (family :
      SNFam
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  recursive_insertion_step
    H e
      (factorSchedule.recursiveInsertionStep
        packetSchedule family)

end TCTex
end Towers

/-!
# Singleton normalization routes for signed polynomial factors

The intrinsic half of an active-block residual can be read from any semantic
normalization of the inserted signed polynomial factor.  Associated-graded
uniqueness forces the active Hall layer of that normalization to agree with
the canonical Hall-normal signed recipes of the factor.  The remaining
endpoint tail is therefore a strictly heavier intrinsic residual expansion.

This is the signed-polynomial analogue of the singleton-normalization bridge
for symbolic Hall powers.  The file is intentionally not imported by the
existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/-- A supported semantic normalization of one active-weight signed factor. -/
structure TPActive
    {d n lowerWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (ι : Type)
    (factor : SPFactor H ι) where
  coordinates :
    CCRecipe H ι
  coordinates_no_below :
    coordinates.NTBelow lowerWeight
  list_coordinates_factor :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e
          (coordinates.factors (n := n)) =
        factor.eval (n := n) e

namespace TPActive

/--
Any supported semantic normalization of a singleton signed factor has the
canonical active Hall coordinates.
-/
lemma recipes_active_weight
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    {ι : Type}
    {factor : SPFactor H ι}
    (normalization :
      TPActive
        (n := n) (lowerWeight := lowerWeight) H ι factor)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n)
    (e : ι → HEFam H) :
    normalization.coordinates.eval e lowerWeight =
      (factor.signedCoordinateRecipes hn H hH).eval e lowerWeight := by
  let X := factor.signedCoordinateRecipes hn H hH
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    have hfactorPos := factor.word_weight_pos
    omega
  have hfactorWordMem :
      factor.wordValue (n := n) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (lowerWeight - 1) := by
    simpa [hfactorWeight] using factor.value_lower_series (n := n)
  have hfactorCoordinates :
      normalFormCoordinates hn H hH (factor.eval (n := n) e) lowerWeight =
        X.eval e lowerWeight := by
    change
      normalFormCoordinates hn H hH
          ((factor.wordValue (n := n)) ^ factor.coefficient.eval e)
          lowerWeight =
        X.eval e lowerWeight
    rw [form_coordinates_zpow
      hn H hH hlowerWeightPos (by omega) _ hfactorWordMem]
    rw [factor.signed_coordinate_recipes
      hn H hH e lowerWeight hlowerWeightPos (by omega)]
    funext i
    simp [zscaledExponentFamily]
    ring
  have hcollected :
      collectedHallProduct (n := n) H (normalization.coordinates.eval e) =
        factor.eval (n := n) e := by
    rw [← normalization.coordinates.listEval_factors e]
    exact normalization.list_coordinates_factor e
  have hnormalizationCoordinates :
      normalFormCoordinates hn H hH (factor.eval (n := n) e) lowerWeight =
        normalization.coordinates.eval e lowerWeight :=
    form_coordinates_collected
      hn H hH (normalization.coordinates.eval e) (factor.eval (n := n) e)
        hcollected lowerWeight hlowerWeightPos (by omega)
  exact hnormalizationCoordinates.symm.trans hfactorCoordinates

/--
The strict tail of any supported singleton normalization is the intrinsic
signed factor residual expansion.
-/
noncomputable def factorExpansion
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    {ι : Type}
    {factor : SPFactor H ι}
    (normalization :
      TPActive
        (n := n) (lowerWeight := lowerWeight) H ι factor)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TPExp
      (lowerWeight := lowerWeight) hn H hH ι factor := by
  let X := factor.signedCoordinateRecipes hn H hH
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    have hfactorPos := factor.word_weight_pos
    omega
  have hlowerWeightCutoff : lowerWeight ≤ n - 1 := by
    omega
  refine
    { higherSource := normalization.coordinates.tailFactors (n := n) lowerWeight
      higher_source_truncated :=
        normalization.coordinates.truncated_factors hlowerWeightCutoff
      higher_least_succ :=
        normalization.coordinates.word_least_factors
      list_factor_value := ?_ }
  intro e
  unfold SPFactor.activeBlockValue
    SPFactor.activeNormalValue
  change
    SPFactor.listEval (n := n) e
        (normalization.coordinates.tailFactors (n := n) lowerWeight) =
      (SPFactor.listEval e
          (X.weightFactors lowerWeight))⁻¹ *
        factor.eval e
  rw [← normalization.list_coordinates_factor e]
  rw [normalization.coordinates.append_no_below
    normalization.coordinates_no_below hlowerWeightPos
      hlowerWeightCutoff]
  rw [SPFactor.listEval_append,
    X.list_weight_factors,
    normalization.coordinates.list_weight_factors,
    normalization.recipes_active_weight
      hn H hH hfactorWeight hfactorTruncated e]
  dsimp [X]
  group

/-- A current-stratum signed normalizer supplies a singleton normalization. -/
lemma nonempty_ofNormalizer
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight) H)
    (factor : SPFactor H ι)
    (hfactorSupported :
      lowerWeight ≤ factor.word.weight HEAddres.weight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    Nonempty
      (TPActive
        (n := n) (lowerWeight := lowerWeight) H ι factor) := by
  rcases normalizer.normalize [factor] (by
      intro x hx
      rcases List.mem_singleton.mp hx with rfl
      exact hfactorTruncated) (by
      intro x hx
      rcases List.mem_singleton.mp hx with rfl
      exact hfactorSupported) with
    ⟨coordinates, hcoordinates, hlistEval⟩
  exact ⟨{
      coordinates := coordinates
      coordinates_no_below := hcoordinates
      list_coordinates_factor := by
        intro e
        simpa [SPFactor.listEval] using hlistEval e }⟩

/-- Choose the singleton normalization supplied by a current-stratum normalizer. -/
noncomputable def ofNormalizer
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight) H)
    (factor : SPFactor H ι)
    (hfactorSupported :
      lowerWeight ≤ factor.word.weight HEAddres.weight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TPActive
      (n := n) (lowerWeight := lowerWeight) H ι factor :=
  Classical.choice
    (nonempty_ofNormalizer normalizer factor hfactorSupported hfactorTruncated)

/--
A current-stratum signed normalizer therefore supplies the intrinsic factor
residual expansion needed by active-block collection.
-/
noncomputable def factor_expansion_normalizer
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight) H)
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TPExp
      (lowerWeight := lowerWeight) hn H hH ι factor :=
  (ofNormalizer normalizer factor (by omega) hfactorTruncated)
    |>.factorExpansion hn H hH hfactorWeight hfactorTruncated

end TPActive

end TCTex
end Towers

/-!
# Recollecting intrinsic signed-polynomial factor residuals

The intrinsic residual of one signed polynomial Hall factor is represented by
one concrete source list: invert its canonical active Hall block and append the
original factor.  This file isolates the remaining local recollection theorem
from the global signed collector.  Any semantic compression of that explicit
source into strictly heavier truncated factors compiles to the residual
expansion consumed by active-block recursion.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace SPFactor

/-- Negate the signed coefficient carried by one polynomial Hall factor. -/
def neg
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι) :
    SPFactor H ι where
  word := factor.word
  coefficient := factor.coefficient.scale (-1)

@[simp]
lemma word_neg
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι) :
    factor.neg.word = factor.word :=
  rfl

@[simp]
lemma coefficient_eval_neg
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι)
    (e : ι → HEFam H) :
    factor.neg.coefficient.eval e = -factor.coefficient.eval e := by
  simp [neg]

@[simp]
lemma wordValue_neg
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι) :
    factor.neg.wordValue (n := n) = factor.wordValue :=
  rfl

@[simp]
lemma eval_neg
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι)
    (e : ι → HEFam H) :
    factor.neg.eval (n := n) e = (factor.eval e)⁻¹ := by
  rw [eval, eval, coefficient_eval_neg, zpow_neg, wordValue_neg]

/-- Reverse a signed factor list while negating every coefficient. -/
def inverseList
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (source : List (SPFactor H ι)) :
    List (SPFactor H ι) :=
  source.reverse.map neg

/-- The signed inverse list evaluates to the inverse group element. -/
lemma list_eval_inverse
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (source : List (SPFactor H ι))
    (e : ι → HEFam H) :
    listEval (n := n) e (inverseList source) = (listEval e source)⁻¹ := by
  induction source with
  | nil =>
      rfl
  | cons factor source ih =>
      rw [show inverseList (factor :: source) = inverseList source ++ [factor.neg] by
        simp [inverseList]]
      simp [ih]

/-- Inversion preserves physical truncation of signed polynomial source lists. -/
lemma truncated_inverse_list
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {source : List (SPFactor H ι)}
    (hsource : IsTruncated n source) :
    IsTruncated n (inverseList source) := by
  intro factor hfactor
  rw [inverseList] at hfactor
  rcases List.mem_map.mp hfactor with ⟨sourceFactor, hsourceFactor, rfl⟩
  exact hsource sourceFactor (by simpa using hsourceFactor)

/--
The intrinsic Hall-normal residual source: inverse active Hall layer followed
by the original signed polynomial factor.
-/
noncomputable def activeRawSource
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (factor : SPFactor H ι) :
    List (SPFactor H ι) :=
  inverseList
      ((factor.signedCoordinateRecipes hn H hH).weightFactors
        lowerWeight) ++
    [factor]

/-- The concrete residual source evaluates to the intrinsic residual value. -/
lemma active_raw_source
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (factor : SPFactor H ι)
    (e : ι → HEFam H) :
    listEval (n := n) e
        (factor.activeRawSource
          (lowerWeight := lowerWeight) hn H hH) =
      factor.activeBlockValue
        (lowerWeight := lowerWeight) hn H hH e := by
  simp [activeRawSource,
    activeBlockValue,
    activeNormalValue,
    list_eval_inverse]

/-- A truncated factor has a physically truncated intrinsic residual source. -/
lemma truncated_active_source
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    IsTruncated n
      (factor.activeRawSource
        (lowerWeight := lowerWeight) hn H hH) := by
  intro residualFactor hresidualFactor
  rcases List.mem_append.mp hresidualFactor with hactive | hfactor
  · apply
      truncated_inverse_list
        (source :=
          (factor.signedCoordinateRecipes hn H hH).weightFactors
            lowerWeight)
        (by
          intro activeFactor hactiveFactor
          have hactiveWeight :
              activeFactor.word.weight HEAddres.weight =
                lowerWeight :=
            (factor.signedCoordinateRecipes hn H hH)
              |>.word_weight_factors hactiveFactor
          rw [hactiveWeight, ← hfactorWeight]
          exact hfactorTruncated)
        residualFactor hactive
  · simp only [List.mem_singleton] at hfactor
    subst residualFactor
    exact hfactorTruncated

end SPFactor

/-- One signed semantic obstruction retains every factor already in its source. -/
lemma
    TSSem.mem_of_mem
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      TSSem
        (n := n) H ι lowerWeight L R)
    {factor : SPFactor H ι}
    (hfactor : factor ∈ L) :
    factor ∈ R := by
  cases h with
  | obstruction P S B A C normalization =>
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hfactor ⊢
      tauto

/-- Finite signed semantic obstruction runs retain every source factor. -/
lemma
    TSRw.mem_of_mem
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {L R : List (SPFactor H ι)}
    (h :
      TSRw
        (n := n) (lowerWeight := lowerWeight) L R)
    {factor : SPFactor H ι}
    (hfactor : factor ∈ L) :
    factor ∈ R := by
  induction h with
  | refl =>
      exact hfactor
  | tail hLR hstep ih =>
      exact hstep.mem_of_mem ih

/--
Swap-only signed semantic collection cannot recollect the intrinsic residual
source to a strictly heavier list: it preserves the original active factor.
-/
lemma
    TSRw.notfactor_residsource_highersource
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (higherSource : List (SPFactor H ι))
    (hhigherSource :
      SPFactor.WordWeightLeast
        (lowerWeight + 1) higherSource) :
    ¬
    TSRw
      (n := n) (lowerWeight := lowerWeight)
      (factor.activeRawSource
        (lowerWeight := lowerWeight) hn H hH)
      higherSource := by
  intro hrewrites
  have hfactorMem :
      factor ∈
        factor.activeRawSource
          (lowerWeight := lowerWeight) hn H hH := by
    simp [SPFactor.activeRawSource]
  have hfactorMemHigher := hrewrites.mem_of_mem hfactorMem
  have hfactorHigher := hhigherSource factor hfactorMemHigher
  omega

/--
Semantic recollection data for the explicit intrinsic residual source of one
signed polynomial factor.
-/
structure
    TPSrc
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (ι : Type)
    (factor : SPFactor H ι) where
  higherSource :
    List (SPFactor H ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_least_succ :
    SPFactor.WordWeightLeast
      (lowerWeight + 1) higherSource
  list_higher_raw :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e higherSource =
        SPFactor.listEval e
          (factor.activeRawSource
            (lowerWeight := lowerWeight) hn H hH)

namespace
  TPSrc

/--
Compile recollection of the concrete intrinsic residual source into the
higher-source package consumed by active-block recursion.
-/
def factorExpansion
    {d n lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)}
    {ι : Type}
    {factor : SPFactor H ι}
    (recollection :
      TPSrc
        (lowerWeight := lowerWeight) hn H hH ι factor) :
    TPExp
      (lowerWeight := lowerWeight) hn H hH ι factor where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_least_succ :=
    recollection.higher_least_succ
  list_factor_value e :=
    (recollection.list_higher_raw e).trans
      (factor.active_raw_source
        (lowerWeight := lowerWeight) hn H hH e)

/-- Present an intrinsic residual expansion as recollection of its concrete source. -/
def factorResidualExpansion
    {d n lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)}
    {ι : Type}
    {factor : SPFactor H ι}
    (expansion :
      TPExp
        (lowerWeight := lowerWeight) hn H hH ι factor) :
    TPSrc
      (lowerWeight := lowerWeight) hn H hH ι factor where
  higherSource := expansion.higherSource
  higher_source_truncated := expansion.higher_source_truncated
  higher_least_succ :=
    expansion.higher_least_succ
  list_higher_raw e :=
    (expansion.list_factor_value e).trans
      (factor.active_raw_source
        (lowerWeight := lowerWeight) hn H hH e).symm

open
  TPExp

private noncomputable def terminalResidualExpansion
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (hcutoff : n ≤ 2 * lowerWeight)
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TPExp
      (lowerWeight := lowerWeight) hn H hH ι factor :=
  of_highWeight hn H hH hcutoff factor hfactorWeight hfactorTruncated

/--
In the terminal high-weight range, the semantic Hall tail recollects the
concrete intrinsic residual source.
-/
noncomputable def of_highWeight
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (hcutoff : n ≤ 2 * lowerWeight)
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    TPSrc
      (lowerWeight := lowerWeight) hn H hH ι factor :=
  factorResidualExpansion
    (terminalResidualExpansion
      hn H hH hcutoff factor hfactorWeight hfactorTruncated)

end
  TPSrc

end TCTex
end Towers

/-!
# Recursive signed collection from word expansions and singleton normalizations

The direct restricted-sharp collector is phrased in terms of its immediate
operational inputs: truncated correction packets and intrinsic factor-residual
expansions.  Two generic bridges make a more mathematical interface possible:

* a finite all-integral higher-word correction expansion truncates to the
  required packet; and
* a semantic singleton normalization determines the canonical active layer
  and exposes its strictly higher residual tail.

This file packages precisely those two inputs and compiles them to the direct
recursive signed collector.  The remaining low-weight theorem is now stated
in terms of universal word expansion and singleton recollection, rather than
collector-internal routing records.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
The mathematical low-weight data sufficient for direct global signed Hall
recollection.
-/
structure RSSingle
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)) where
  correctionExpansionFactory :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 3 * lowerWeight →
        SSFtrya
          (n := n) H lowerWeight
  factorNormalization :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        TSNormal
            (n := n) (lowerWeight := lowerWeight + 1) H →
          ∀ (factor : SPFactor H ι),
            factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TPActive
                (n := n) (lowerWeight := lowerWeight) H ι factor

namespace RSSingle

/--
Compile universal expansions and singleton recollections to the operational
inputs of the restricted-sharp recursive collector.
-/
noncomputable def restrictedRecursiveBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)}
    (builder :
      RSSingle
        (n := n) hn H hH) :
    SRBuild
      (n := n) hn H hH where
  correctionFactory lowerWeight hterminal :=
    (builder.correctionExpansionFactory lowerWeight hterminal)
      |>.correctionPacketFactory
  factorResidual lowerWeight hterminal nextNormalizer factor hfactorWeight
      hfactorTruncated :=
    (builder.factorNormalization lowerWeight hterminal nextNormalizer factor
      hfactorWeight hfactorTruncated)
      |>.factorExpansion hn H hH hfactorWeight hfactorTruncated

end RSSingle

/--
Universal correction expansions, singleton recollections, and graded Hall
bases construct product recollection polynomials.
-/
theorem collected_coord_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : List (HEFam H))
    (builder :
      RSSingle
        (n := n) hn H hH) :
    CollectedCoordinateData (n := n) H e :=
  restricted_recursive_builder
    hn H hH e builder.restrictedRecursiveBuilder

/--
Universal correction expansions, singleton recollections, and graded Hall
bases construct inverse recollection polynomials.
-/
theorem collected_singleton_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : HEFam H)
    (builder :
      RSSingle
        (n := n) hn H hH) :
    CollectedInverseData (n := n) H e :=
  restricted_sharp_recursive
    hn H hH e builder.restrictedRecursiveBuilder

end TCTex
end Towers

/-!
# Conjugating recollected signed-polynomial higher tails

Suppose a signed-polynomial source has already been recollected one stratum
higher.  Conjugating that source by an active factor appears to reintroduce a
same-weight factor on each side.  The sharp higher-tail router removes those
wrappers operationally: move the right conjugator left across the recollected
higher tail, then cancel it semantically with the inverse conjugator.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace SPFactor

/-- A signed-polynomial source conjugated by one factor. -/
def conjugatedRawSource
    {d : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (conjugator : SPFactor H ι)
    (source : List (SPFactor H ι)) :
    List (SPFactor H ι) :=
  [conjugator.neg] ++ source ++ [conjugator]

end SPFactor

/--
An upward semantic recollection of a source conjugated by an active
signed-polynomial factor.
-/
structure
    SupportedConjugatedRecollection
    {d n lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    {ι : Type}
    (conjugator : SPFactor H ι)
    (rawSource : List (SPFactor H ι)) where
  higherSource :
    List (SPFactor H ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_least_succ :
    SPFactor.WordWeightLeast
      (lowerWeight + 1) higherSource
  higher_conjugated_raw :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e higherSource =
        SPFactor.listEval e
          (SPFactor.conjugatedRawSource
            conjugator rawSource)

namespace THRoute

/--
A sharp route moving the right conjugator across a recollected higher source
supplies an upward recollection of the conjugated raw source.
-/
noncomputable def conjugatedRecollection
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {higherSource rawSource : List (SPFactor H ι)}
    {conjugator : SPFactor H ι}
    (route :
      THRoute
        (n := n) (lowerWeight := lowerWeight) H ι higherSource conjugator)
    (hhigherSourceTruncated :
      SPFactor.IsTruncated n higherSource)
    (hconjugatorTruncated :
      conjugator.word.weight HEAddres.weight < n)
    (hhigherSourceEval :
      ∀ e : ι → HEFam H,
        SPFactor.listEval (n := n) e higherSource =
          SPFactor.listEval e rawSource) :
    SupportedConjugatedRecollection
      (n := n) (lowerWeight := lowerWeight) H conjugator rawSource where
  higherSource := route.higherSource
  higher_source_truncated := by
    have hrouteTruncated :
        SPFactor.IsTruncated n
          ([conjugator] ++ route.higherSource) :=
      route.inserts.isTruncated hhigherSourceTruncated hconjugatorTruncated
    intro x hx
    exact hrouteTruncated x (by simp [hx])
  higher_least_succ :=
    route.higher_least_succ
  higher_conjugated_raw := by
    intro e
    have hroute := route.inserts.listEval_eq e
    simp only [SPFactor.conjugatedRawSource,
      SPFactor.listEval_append,
      SPFactor.listEval_cons,
      SPFactor.listEval_nil, mul_one,
      SPFactor.eval_neg] at hroute ⊢
    rw [← hhigherSourceEval e]
    calc
      SPFactor.listEval (n := n) e route.higherSource =
          (conjugator.eval e)⁻¹ *
            (conjugator.eval e *
              SPFactor.listEval e route.higherSource) := by
        group
      _ =
          (conjugator.eval e)⁻¹ *
            (SPFactor.listEval e higherSource *
              conjugator.eval e) := by
        rw [hroute]
      _ =
          (conjugator.eval e)⁻¹ *
              SPFactor.listEval e higherSource *
            conjugator.eval e := by
        group

end THRoute

namespace TSFtry

/--
Sharp higher-tail routing recollects a conjugated source from any upward
recollection of its unconjugated body.
-/
noncomputable def conjugated_recollection_normalizer
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (conjugator : SPFactor H ι)
    (hconjugatorWeight :
      conjugator.word.weight HEAddres.weight = lowerWeight)
    (hconjugatorTruncated :
      conjugator.word.weight HEAddres.weight < n)
    (rawSource higherSource :
      List (SPFactor H ι))
    (hhigherSourceTruncated :
      SPFactor.IsTruncated n higherSource)
    (hhigherSourceSupported :
      SPFactor.WordWeightLeast
        (lowerWeight + 1) higherSource)
    (hhigherSourceEval :
      ∀ e : ι → HEFam H,
        SPFactor.listEval (n := n) e higherSource =
          SPFactor.listEval e rawSource) :
    SupportedConjugatedRecollection
      (n := n) (lowerWeight := lowerWeight) H conjugator rawSource :=
  (factory.supported_higher_normalizer
      sharp conjugator hconjugatorWeight higherSource hhigherSourceSupported
    |>.conjugatedRecollection
      hhigherSourceTruncated hconjugatorTruncated hhigherSourceEval)

end TSFtry

end TCTex
end Towers

/-!
# Recursive signed collection from packets and explicit residual sources

The intrinsic residual of one signed Hall-polynomial factor is the concrete
source obtained by removing its canonical active Hall layer.  This file uses
that source as the remaining singleton input to recursive signed collection.

Positive generalized-binomial arithmetic is constructed unconditionally.  The
remaining mathematical inputs are exactly:

* one cutoff-specific all-integral Hall-Petresco packet;
* semantic recollection of each explicit intrinsic residual source into
  strictly higher Hall weight.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
Cutoff Hall-Petresco expansion and explicit intrinsic residual recollection
data sufficient for direct global signed Hall recollection.
-/
structure
    SCBuilda
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)) where
  packet :
    PFSubsti.TAPkt.{u} d n
  factorResidualSource :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor : SPFactor H ι),
          factor.word.weight HEAddres.weight = lowerWeight →
          factor.word.weight HEAddres.weight < n →
            TPSrc
              (lowerWeight := lowerWeight) hn H hH ι factor

namespace
  SCBuilda

/--
Compile packet arithmetic and explicit intrinsic residual recollection to the
operational recursive signed collector.
-/
noncomputable def restrictedRecursiveBuilder
    {d n : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)}
    (builder :
      SCBuilda
        (n := n) hn H hH) :
    SRBuild
      (n := n) hn H hH where
  correctionFactory lowerWeight _hterminal :=
    (builder.packet.supportedWordFactory
      (WBForm.chooseNormalizerFamily H)
      lowerWeight)
      |>.correctionPacketFactory
  factorResidual lowerWeight hterminal _nextNormalizer factor hfactorWeight
      hfactorTruncated :=
    (builder.factorResidualSource lowerWeight hterminal factor hfactorWeight
      hfactorTruncated)
      |>.factorExpansion

end
  SCBuilda

/--
Cutoff Hall-Petresco packets, explicit intrinsic residual recollections, and
graded Hall bases construct product recollection polynomials.
-/
theorem
    collected_residual_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : List (HEFam H))
    (builder :
      SCBuilda
        (n := n) hn H hH) :
    CollectedCoordinateData (n := n) H e :=
  restricted_recursive_builder
    hn H hH e builder.restrictedRecursiveBuilder

/--
Cutoff Hall-Petresco packets, explicit intrinsic residual recollections, and
graded Hall bases construct inverse recollection polynomials.
-/
theorem
    coord_collect_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : HEFam H)
    (builder :
      SCBuilda
        (n := n) hn H hH) :
    CollectedInverseData (n := n) H e :=
  restricted_sharp_recursive
    hn H hH e builder.restrictedRecursiveBuilder

end TCTex
end Towers

/-!
# Exact weight-one residual reduction for signed Hall polynomials

A signed polynomial factor of ordinary word weight one is already a single
Hall address.  Its active Hall-normal layer therefore evaluates exactly to
the factor itself, and its intrinsic residual source recollects to the empty
list.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

lemma List.prodmap_iteeq_nodupmem
    {alpha G : Type*}
    [DecidableEq alpha]
    [Monoid G]
    (L : List alpha)
    (i : alpha)
    (g : G)
    (hL : L.Nodup)
    (hi : i ∈ L) :
    (L.map fun j => if j = i then g else 1).prod = g := by
  induction L with
  | nil =>
      simp at hi
  | cons head tail ih =>
      simp only [List.nodup_cons] at hL
      rcases hL with ⟨hhead, htail⟩
      by_cases h : head = i
      · subst head
        have htailProd :
            (tail.map fun j => if j = i then g else 1).prod = 1 := by
          apply List.prod_eq_one
          intro x hx
          rcases List.mem_map.mp hx with ⟨j, hj, rfl⟩
          simp only [ite_eq_right_iff]
          intro hji
          subst j
          exact (hhead hj).elim
        simp [htailProd]
      · have hiTail : i ∈ tail := by
          rcases List.mem_cons.mp hi with hi | hi
          · exact False.elim (h hi.symm)
          · exact hi
        simpa [h] using ih htail hiTail

/-- A fixed-weight collected Hall segment supported at one index is one zpower. -/
lemma BCWta.collectedweight_productite_eqzpow
    {d n r : ℕ}
    (H : BCWta.{u} d r)
    (i : H.index)
    (z : ℤ) :
    H.collectedWeightProduct (n := n) (fun j => if j = i then z else 0) =
      (H.commutator i).freeLowerTruncation ^ z := by
  unfold BCWta.collectedWeightProduct
    BCWta.collected_lower_centralterm
  have hterm :
      ((Finset.univ.sort fun j j' : H.index => j ≤ j').map fun j =>
          (H.commutator j).evalin_freelower_centtrunterm (n := n) ^
            (if j = i then z else 0)).prod =
        (H.commutator i).evalin_freelower_centtrunterm (n := n) ^ z := by
    rw [show
        ((Finset.univ.sort fun j j' : H.index => j ≤ j').map fun j =>
            (H.commutator j).evalin_freelower_centtrunterm (n := n) ^
              (if j = i then z else 0)).prod =
          ((Finset.univ.sort fun j j' : H.index => j ≤ j').map fun j =>
            if j = i then
              (H.commutator i).evalin_freelower_centtrunterm (n := n) ^ z
            else
              1).prod by
          congr 1
          apply List.map_congr_left
          intro j _hj
          by_cases hji : j = i
          · subst j
            simp
          · simp [hji]]
    exact List.prodmap_iteeq_nodupmem
      (Finset.univ.sort fun j j' : H.index => j ≤ j')
      i
      ((H.commutator i).evalin_freelower_centtrunterm (n := n) ^ z)
      (Finset.sort_nodup _ _)
      (by simp)
  exact congrArg Subtype.val hterm

namespace CWord

/-- A positively weighted commutator word of total weight one is one atom. -/
lemma atom_weight_one
    {alpha : Type*}
    (weight : alpha → ℕ)
    (hweight : ∀ a, 0 < weight a) :
    ∀ word : CWord alpha,
      word.weight weight = 1 →
        ∃ a, word = .atom a
  | .atom a, _ =>
      ⟨a, rfl⟩
  | .commutator left right, hword => by
      have hleft := CWord.weight_pos weight hweight left
      have hright := CWord.weight_pos weight hweight right
      simp only [CWord.weight_commutator] at hword
      omega

end CWord

/--
The Hall-normal coordinates in the selected basic commutator's own layer are
the corresponding Kronecker row.
-/
lemma
    BCWta.hallnormalform_coordsevalin_frelowcentru
    {d n r : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hr : 1 ≤ r)
    (hrn : r < n)
    (i : (H r).index) :
    normalFormCoordinates hn H hH
        ((H r).commutator i).freeLowerTruncation r =
      fun j => if j = i then 1 else 0 := by
  apply form_coordinates_next
    hn H hH hr hrn
  · exact
      ((H r).commutator i)
        |>.free_truncation_series
  · rw [(H r).collectedweight_productite_eqzpow]
    simp

namespace SPFactor

/--
The active Hall-normal layer of a weight-one signed polynomial factor is
exactly the factor itself.
-/
lemma active_block_value
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = 1)
    (e : ι → HEFam H) :
    factor.activeNormalValue
        (lowerWeight := 1) hn H hH e =
      factor.eval (n := n) e := by
  obtain ⟨address, hword⟩ :=
    CWord.atom_weight_one
      HEAddres.weight HEAddres.weight_pos factor.word
        hfactorWeight
  rcases address with ⟨s, i⟩
  have hs : s = 1 := by
    rw [hword] at hfactorWeight
    simpa [HEAddres.weight] using hfactorWeight
  subst s
  have hwordValue :
      factor.wordValue (n := n) =
        ((H 1).commutator i).freeLowerTruncation := by
    unfold wordValue
    rw [hword]
    rfl
  unfold activeNormalValue
  rw [CCRecipe.list_weight_factors]
  rw [factor.signed_coordinate_recipes hn H hH e 1 (by omega)
    (by omega)]
  have hcoordinates :
      normalFormCoordinates hn H hH (factor.wordValue (n := n)) 1 =
        fun j => if j = i then 1 else 0 := by
    rw [hwordValue]
    exact
      BCWta.hallnormalform_coordsevalin_frelowcentru
        hn H hH (by omega) (by omega) i
  change
    (H 1).collectedWeightProduct
        (fun j =>
          normalFormCoordinates hn H hH (factor.wordValue (n := n)) 1 j *
            factor.coefficient.eval e) =
      factor.eval e
  rw [hcoordinates]
  rw [show
      (fun j => (if j = i then 1 else 0) * factor.coefficient.eval e) =
        fun j => if j = i then factor.coefficient.eval e else 0 by
      funext j
      split_ifs <;> simp]
  rw [(H 1).collectedweight_productite_eqzpow]
  unfold eval
  rw [hwordValue]

end SPFactor

namespace
  TPSrc

/--
A weight-one signed polynomial factor has trivial intrinsic residual source:
its active Hall-normal block already evaluates to the factor.
-/
noncomputable def of_weight_one
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (factor : SPFactor H ι)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = 1) :
    TPSrc
      (lowerWeight := 1) hn H hH ι factor where
  higherSource := []
  higher_source_truncated := by
    simp [SPFactor.IsTruncated]
  higher_least_succ := by
    simp [SPFactor.WordWeightLeast]
  list_higher_raw e := by
    rw [factor.active_raw_source
      (lowerWeight := 1) hn H hH e]
    unfold SPFactor.activeBlockValue
    rw [factor.active_block_value
      hn H hH hfactorWeight e]
    simp [SPFactor.listEval]

end
  TPSrc

end TCTex
end Towers

/-!
# Recursive signed collection from Hall-Petresco packets and choose normalization

The word-expansion recursive collector accepts a correction-expansion factory
for every active support stratum.  A cutoff-specific all-integral
Hall-Petresco packet and a uniform normalizer for positive generalized
binomial coefficients construct all of those factories automa.

This file packages the resulting sharper mathematical boundary.  The
remaining singleton field asks only for semantic recollection of one signed
factor after the strictly higher strata have already been normalized.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
Cutoff Hall-Petresco expansion, positive-choose arithmetic, and singleton
recollection data sufficient for direct global signed Hall recollection.
-/
structure SCBuild
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)) where
  packet :
    PFSubsti.TAPkt.{u} d n
  formulaChooseNormalizers :
    WBForm.PositiveChooseNormalizer H
  factorNormalization :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        TSNormal
            (n := n) (lowerWeight := lowerWeight + 1) H →
          ∀ (factor : SPFactor H ι),
            factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TPActive
                (n := n) (lowerWeight := lowerWeight) H ι factor

namespace SCBuild

/--
Compile cutoff Hall-Petresco expansion and formula arithmetic into the
word-expansion boundary of the recursive signed collector.
-/
def restrictedSharpExpansion
    {d n : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)}
    (builder :
      SCBuild
        (n := n) hn H hH) :
    RSSingle
      (n := n) hn H hH where
  correctionExpansionFactory lowerWeight _hterminal :=
    builder.packet.supportedWordFactory
      builder.formulaChooseNormalizers lowerWeight
  factorNormalization :=
    builder.factorNormalization

end SCBuild

/--
Cutoff Hall-Petresco packets, positive-choose arithmetic, singleton
recollections, and graded Hall bases construct product recollection
polynomials.
-/
theorem choose_collect_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : List (HEFam H))
    (builder :
      SCBuild
        (n := n) hn H hH) :
    CollectedCoordinateData (n := n) H e :=
  collected_coord_builder
    hn H hH e builder.restrictedSharpExpansion

/--
Cutoff Hall-Petresco packets, positive-choose arithmetic, singleton
recollections, and graded Hall bases construct inverse recollection
polynomials.
-/
theorem collected_choose_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : HEFam H)
    (builder :
      SCBuild
        (n := n) hn H hH) :
    CollectedInverseData (n := n) H e :=
  collected_singleton_builder
    hn H hH e builder.restrictedSharpExpansion

end TCTex
end Towers

/-!
# Conjugating recollected signed-polynomial higher tails by factor lists

An active signed-polynomial block is generally a finite list of factors.  This
file iterates the one-factor sharp higher-tail router while preserving the
ordered product represented by the complete list.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace SPFactor

/--
Conjugate a signed-polynomial source successively by a list of factors.  The
first factor is the innermost conjugator.
-/
def conjugatedRawList
    {d : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type} :
    List (SPFactor H ι) →
      List (SPFactor H ι) →
        List (SPFactor H ι)
  | [], source => source
  | conjugator :: conjugators, source =>
      conjugatedRawList conjugators
        (conjugatedRawSource conjugator source)

/-- Successive source conjugation agrees with conjugation by the list product. -/
lemma conjugated_raw_source
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (e : ι → HEFam H)
    (conjugators source : List (SPFactor H ι)) :
    listEval (n := n) e (conjugatedRawList conjugators source) =
      (listEval e conjugators)⁻¹ * listEval e source *
        listEval e conjugators := by
  induction conjugators generalizing source with
  | nil =>
      simp [conjugatedRawList]
  | cons conjugator conjugators ih =>
      rw [conjugatedRawList, ih]
      simp only [conjugatedRawSource, listEval_append, listEval_cons,
        listEval_nil, eval_neg, mul_one]
      group

end SPFactor

/--
An upward semantic recollection of a source conjugated by an ordered list of
active signed-polynomial factors.
-/
structure
    SemanticConjugatedRecollection
    {d n lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    {ι : Type}
    (conjugators rawSource : List (SPFactor H ι)) where
  higherSource :
    List (SPFactor H ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_least_succ :
    SPFactor.WordWeightLeast
      (lowerWeight + 1) higherSource
  list_conjugated_raw :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e higherSource =
        SPFactor.listEval e
          (SPFactor.conjugatedRawList conjugators
            rawSource)

namespace TSFtry

/-- Iterate sharp higher-tail routing over a finite ordered conjugator list. -/
noncomputable def
    conjugated_sharp_normalizer
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H) :
    ∀ (conjugators rawSource higherSource :
        List (SPFactor H ι)),
      (∀ conjugator ∈ conjugators,
        conjugator.word.weight HEAddres.weight = lowerWeight) →
      SPFactor.IsTruncated n conjugators →
      SPFactor.IsTruncated n higherSource →
      SPFactor.WordWeightLeast
        (lowerWeight + 1) higherSource →
      (∀ e : ι → HEFam H,
        SPFactor.listEval (n := n) e higherSource =
          SPFactor.listEval e rawSource) →
      SemanticConjugatedRecollection
        (n := n) (lowerWeight := lowerWeight) H conjugators rawSource
  | [], rawSource, higherSource, _, _, hhigherSourceTruncated,
      hhigherSourceSupported, hhigherSourceEval =>
        { higherSource := higherSource
          higher_source_truncated := hhigherSourceTruncated
          higher_least_succ := hhigherSourceSupported
          list_conjugated_raw := by
            intro e
            simpa [SPFactor.conjugatedRawList] using
              hhigherSourceEval e }
  | conjugator :: conjugators, rawSource, higherSource, hconjugatorWeights,
      hconjugatorsTruncated, hhigherSourceTruncated,
      hhigherSourceSupported, hhigherSourceEval => by
        let head :=
          factory.conjugated_recollection_normalizer
            sharp conjugator (hconjugatorWeights conjugator (by simp))
              (hconjugatorsTruncated conjugator (by simp))
                rawSource higherSource hhigherSourceTruncated
                  hhigherSourceSupported hhigherSourceEval
        let tail :=
          conjugated_sharp_normalizer
            factory sharp conjugators
              (SPFactor.conjugatedRawSource conjugator
                rawSource)
                head.higherSource
                  (fun next hnext =>
                    hconjugatorWeights next (by simp [hnext]))
                  (fun next hnext =>
                    hconjugatorsTruncated next (by simp [hnext]))
                  head.higher_source_truncated
                  head.higher_least_succ
                  head.higher_conjugated_raw
        exact
          { higherSource := tail.higherSource
            higher_source_truncated := tail.higher_source_truncated
            higher_least_succ :=
              tail.higher_least_succ
            list_conjugated_raw := by
              intro e
              simpa [SPFactor.conjugatedRawList] using
                tail.list_conjugated_raw e }

end TSFtry

end TCTex
end Towers

/-!
# Exact atomic residual reduction for signed Hall polynomials

A signed polynomial factor whose commutator word is already one Hall address
has no intrinsic Hall-normalization tail in its own weight layer.  This is the
all-weight atomic analogue of the weight-one residual reduction.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace SPFactor

/--
The active Hall-normal layer of an atomic signed polynomial factor is exactly
the factor itself.
-/
lemma active_block_atom
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (factor : SPFactor H ι)
    (address : HEAddres H)
    (hword : factor.word = .atom address)
    (htruncated : address.weight < n)
    (e : ι → HEFam H) :
    factor.activeNormalValue
        (lowerWeight := address.weight) hn H hH e =
      factor.eval (n := n) e := by
  rcases address with ⟨s, i⟩
  have hwordValue :
      factor.wordValue (n := n) =
        ((H s).commutator i).freeLowerTruncation := by
    unfold wordValue
    rw [hword]
    rfl
  unfold activeNormalValue
  rw [CCRecipe.list_weight_factors]
  change
    (H s).collectedWeightProduct
        ((factor.signedCoordinateRecipes hn H hH).eval e s) =
      factor.eval e
  rw [factor.signed_coordinate_recipes hn H hH e s
    (HEAddres.weight_pos ⟨s, i⟩) htruncated]
  have hcoordinates :
      normalFormCoordinates hn H hH (factor.wordValue (n := n)) s =
        fun j => if j = i then 1 else 0 := by
    rw [hwordValue]
    exact
      BCWta.hallnormalform_coordsevalin_frelowcentru
        hn H hH (HEAddres.weight_pos ⟨s, i⟩) htruncated i
  change
    (H s).collectedWeightProduct
        (fun j =>
          normalFormCoordinates hn H hH (factor.wordValue (n := n)) s j *
            factor.coefficient.eval e) =
      factor.eval e
  rw [hcoordinates]
  rw [show
      (fun j => (if j = i then 1 else 0) * factor.coefficient.eval e) =
        fun j => if j = i then factor.coefficient.eval e else 0 by
      funext j
      split_ifs <;> simp]
  rw [(H s).collectedweight_productite_eqzpow]
  unfold eval
  rw [hwordValue]

end SPFactor

namespace
  TPSrc

/--
An atomic signed polynomial factor has trivial intrinsic residual source: its
active Hall-normal block already evaluates to the factor.
-/
noncomputable def of_atom
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (factor : SPFactor H ι)
    (address : HEAddres H)
    (hword : factor.word = .atom address)
    (htruncated : address.weight < n) :
    TPSrc
      (lowerWeight := address.weight) hn H hH ι factor where
  higherSource := []
  higher_source_truncated := by
    simp [SPFactor.IsTruncated]
  higher_least_succ := by
    simp [SPFactor.WordWeightLeast]
  list_higher_raw e := by
    rw [factor.active_raw_source
      (lowerWeight := address.weight) hn H hH e]
    unfold SPFactor.activeBlockValue
    rw [factor.active_block_atom
      hn H hH address hword htruncated e]
    simp [SPFactor.listEval]

end
  TPSrc

end TCTex
end Towers

/-!
# Recursive signed collection from Hall-Petresco packets and singleton recollection

The positive-choose arithmetic required by Hall-Petresco substitution is now
constructed unconditionally from finite Newton expansions.  This file removes
that arithmetic field from the recursive collector boundary.

The remaining mathematical inputs are exactly:

* one cutoff-specific all-integral Hall-Petresco packet;
* semantic recollection of one signed factor after higher strata have already
  been normalized.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
Cutoff Hall-Petresco expansion and singleton recollection data sufficient for
direct global signed Hall recollection.
-/
structure RSBuilda
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)) where
  packet :
    PFSubsti.TAPkt.{u} d n
  factorNormalization :
    ∀ {ι : Type}
      (lowerWeight : ℕ),
      ¬n ≤ 2 * lowerWeight →
        TSNormal
            (n := n) (lowerWeight := lowerWeight + 1) H →
          ∀ (factor : SPFactor H ι),
            factor.word.weight HEAddres.weight = lowerWeight →
            factor.word.weight HEAddres.weight < n →
              TPActive
                (n := n) (lowerWeight := lowerWeight) H ι factor

namespace RSBuilda

/--
Insert the constructed positive-choose arithmetic family into the earlier
packet-plus-arithmetic collector boundary.
-/
noncomputable def restrictedSharpChoose
    {d n : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)}
    (builder :
      RSBuilda
        (n := n) hn H hH) :
    SCBuild
      (n := n) hn H hH where
  packet :=
    builder.packet
  formulaChooseNormalizers :=
    WBForm.chooseNormalizerFamily H
  factorNormalization :=
    builder.factorNormalization

end RSBuilda

/--
Cutoff Hall-Petresco packets, singleton recollections, and graded Hall bases
construct product recollection polynomials.
-/
theorem
  collected_sharp_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : List (HEFam H))
    (builder :
      RSBuilda
        (n := n) hn H hH) :
    CollectedCoordinateData (n := n) H e :=
  choose_collect_builder
    hn H hH e builder.restrictedSharpChoose

/--
Cutoff Hall-Petresco packets, singleton recollections, and graded Hall bases
construct inverse recollection polynomials.
-/
theorem
  restricted_sharp_builder
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : HEFam H)
    (builder :
      RSBuilda
        (n := n) hn H hH) :
    CollectedInverseData (n := n) H e :=
  collected_choose_builder
    hn H hH e builder.restrictedSharpChoose

end TCTex
end Towers

/-!
# Normalizing fixed-weight atomic signed-polynomial sources

The restricted-sharp collector resolves an active signed-polynomial factor
once its intrinsic residual is available one stratum higher.  Atomic Hall
factors have empty intrinsic residuals, so a fixed-weight atomic list can be
normalized using only the correction packet factory and deeper normalizers.

If the value of that list already lies in the next lower-central stratum, its
normalized active Hall block evaluates trivially.  The normalized higher tail
then gives a finite symbolic recollection of the original source.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace TSFtry

/-- Insert one atomic active-weight factor using restricted-sharp routing. -/
noncomputable def semantic_insertion_atom
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (nextNormalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1) H)
    (coordinates : CCRecipe H ι)
    (factor : SPFactor H ι)
    (address : HEAddres H)
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hword : factor.word = .atom address)
    (haddressWeight : address.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight HEAddres.weight < n) :
    ∃ next : CCRecipe H ι,
      next.NTBelow lowerWeight ∧
        ∀ e : ι → HEFam H,
          SPFactor.listEval (n := n) e
              (next.factors (n := n)) =
            SPFactor.listEval (n := n) e
              (coordinates.factors (n := n) ++ [factor]) := by
  subst lowerWeight
  have hfactorWeight :
      factor.word.weight HEAddres.weight = address.weight := by
    rw [hword]
    rfl
  have haddressTruncated : address.weight < n := by
    omega
  let factorTail :=
    (TPSrc.of_atom
      hn H hH factor address hword haddressTruncated).factorExpansion
  let merge :=
    (factory
      |>.coord_sharp_normalizer
        hn H hH sharp coordinates factor)
      |>.mergeResidualExpansion hfactorWeight hfactorTruncated
  let block :=
    merge.activeBlockResolution factorTail hcoordinates hfactorWeight
  let tail :=
    (factory
      |>.supported_route_normalizer
        sharp coordinates factor hfactorWeight)
      |>.higherTailResolution hfactorWeight hfactorTruncated
  exact
    (TPResolu.active_block_tail
      hcoordinates hfactorWeight hfactorTruncated block tail)
      |>.exists_insertion nextNormalizer hfactorWeight hfactorTruncated

/--
Normalize a finite list of atomic factors lying in one fixed Hall-weight
layer.
-/
noncomputable def signed_normalization_atoms
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (nextNormalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1) H) :
    ∀ source : List (SPFactor H ι),
      SPFactor.IsTruncated n source →
      (∀ factor ∈ source,
        ∃ address : HEAddres H,
          factor.word = .atom address ∧ address.weight = lowerWeight) →
        ∃ coordinates : CCRecipe H ι,
          coordinates.NTBelow lowerWeight ∧
            ∀ e : ι → HEFam H,
              SPFactor.listEval (n := n) e
                  (coordinates.factors (n := n)) =
                SPFactor.listEval (n := n) e source := by
  intro source hsourceTruncated hsourceAtomic
  induction source using List.reverseRecOn with
  | nil =>
      exact
        ⟨CCRecipe.empty H ι,
          CCRecipe.no_below_empty H ι,
          by intro e; simp⟩
  | append_singleton initial factor ih =>
      have hinitialTruncated :
          SPFactor.IsTruncated n initial := by
        intro x hx
        exact hsourceTruncated x (by simp [hx])
      have hinitialAtomic :
          ∀ x ∈ initial,
            ∃ address : HEAddres H,
              x.word = .atom address ∧ address.weight = lowerWeight := by
        intro x hx
        exact hsourceAtomic x (by simp [hx])
      rcases ih hinitialTruncated hinitialAtomic with
        ⟨coordinates, hcoordinates, heval⟩
      rcases hsourceAtomic factor (by simp) with
        ⟨address, hword, haddressWeight⟩
      have hfactorTruncated :
          factor.word.weight HEAddres.weight < n :=
        hsourceTruncated factor (by simp)
      rcases factory.semantic_insertion_atom
          hn H hH sharp nextNormalizer coordinates factor address hcoordinates
            hword haddressWeight hfactorTruncated with
        ⟨next, hnext, hnextEval⟩
      refine ⟨next, hnext, ?_⟩
      intro e
      calc
        SPFactor.listEval (n := n) e
              (next.factors (n := n)) =
            SPFactor.listEval (n := n) e
              (coordinates.factors (n := n) ++ [factor]) :=
          hnextEval e
        _ = SPFactor.listEval (n := n) e
              (coordinates.factors (n := n)) * factor.eval (n := n) e := by
          rw [SPFactor.listEval_append]
          simp
        _ = SPFactor.listEval (n := n) e initial *
            factor.eval (n := n) e := by
          rw [heval e]
        _ = SPFactor.listEval (n := n) e
              (initial ++ [factor]) := by
          rw [SPFactor.listEval_append]
          simp

/--
An atomic fixed-weight source whose value starts one stratum higher has a
finite symbolic recollection supported one stratum higher.
-/
noncomputable def higher_atoms_series
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (nextNormalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight + 1) H)
    (source : List (SPFactor H ι))
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n)
    (hsourceTruncated : SPFactor.IsTruncated n source)
    (hsourceAtomic :
      ∀ factor ∈ source,
        ∃ address : HEAddres H,
          factor.word = .atom address ∧ address.weight = lowerWeight)
    (hsourceMem :
      ∀ e : ι → HEFam H,
        SPFactor.listEval (n := n) e source ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            lowerWeight) :
    ∃ higherSource : List (SPFactor H ι),
      SPFactor.IsTruncated n higherSource ∧
        SPFactor.WordWeightLeast
          (lowerWeight + 1) higherSource ∧
            ∀ e : ι → HEFam H,
              SPFactor.listEval (n := n) e higherSource =
                SPFactor.listEval (n := n) e source := by
  rcases factory.signed_normalization_atoms
      hn H hH sharp nextNormalizer source hsourceTruncated hsourceAtomic with
    ⟨coordinates, hcoordinates, heval⟩
  refine
    ⟨coordinates.tailFactors (n := n) lowerWeight,
      coordinates.truncated_factors (by omega),
      coordinates.word_least_factors, ?_⟩
  intro e
  have hcoordinatesMem :
      collectedHallProduct (n := n) H (coordinates.eval e) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          lowerWeight := by
    rw [← coordinates.listEval_factors]
    rw [heval e]
    exact hsourceMem e
  have hactiveCoordinates :
      coordinates.eval e lowerWeight = 0 := by
    exact
      imp_coordinates_below
        (r := lowerWeight + 1) hn H hH (coordinates.eval e)
          (by simpa using hcoordinatesMem) lowerWeight hlowerWeightPos
            (by omega) hlowerWeightTruncated
  rw [← heval e,
    coordinates.append_no_below
      hcoordinates hlowerWeightPos (by omega),
    SPFactor.listEval_append,
    coordinates.list_weight_factors,
    hactiveCoordinates,
    BCWta.collected_weight_productzero,
    one_mul]

end TSFtry

end TCTex
end Towers
