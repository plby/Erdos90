import Towers.Group.Zassenhaus.SignedCorrectionSemantics
import Towers.Group.Zassenhaus.Polynomial
import Towers.Group.Zassenhaus.SignedReductionFactors
import Towers.Group.Zassenhaus.PolynomialConcreteSemantic
import Towers.Group.Zassenhaus.InverseUniversalClosure

-- Merged from PolynomialOuterBracketPacketWorklist.lean

/-!
# Polynomial packet worklists for brackets with finite left products

The unrestricted group-level outer-bracket worklist retains conjugations.
For signed Hall polynomials, each terminal commutator in that worklist is
represented by an existing truncated Hall-Petresco correction packet.

This file packages the resulting finite symbolic source.  Its evaluation is
exactly the bracket of the evaluated left source with one fixed factor.  It
also preserves a common lower support bound and physical truncation.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

namespace SBWork

/--
Replace every terminal bracket in the unrestricted left-product worklist by
its truncated signed-polynomial correction packet.
-/
def factors
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (right : SPFactor H ι)
    (packet :
      ∀ left : SPFactor H ι,
        TSPkt n left right) :
    List (SPFactor H ι) →
      List (SPFactor H ι)
  | [] => []
  | left :: tail =>
      [left] ++ factors right packet tail ++ [left.neg] ++
        (packet left).factors

@[simp]
theorem factors_nil
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (right : SPFactor H ι)
    (packet :
      ∀ left : SPFactor H ι,
        TSPkt n left right) :
    factors right packet [] = [] :=
  rfl

@[simp]
theorem factors_cons
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (right left : SPFactor H ι)
    (packet :
      ∀ x : SPFactor H ι,
        TSPkt n x right)
    (tail : List (SPFactor H ι)) :
    factors right packet (left :: tail) =
      [left] ++ factors right packet tail ++ [left.neg] ++
        (packet left).factors :=
  rfl

/--
The signed-polynomial worklist evaluates exactly to the bracket of the
evaluated left source with the fixed outer-right factor.
-/
theorem listEval_factors
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (right : SPFactor H ι)
    (packet :
      ∀ left : SPFactor H ι,
        TSPkt n left right)
    (e : ι → HEFam H) :
    ∀ left : List (SPFactor H ι),
      SPFactor.listEval (n := n) e
          (factors right packet left) =
        ⁅SPFactor.listEval (n := n) e left,
          right.eval (n := n) e⁆ := by
  intro left
  induction left with
  | nil =>
      simp [SPFactor.listEval]
  | cons head tail ih =>
      rw [factors_cons]
      simp only [SPFactor.listEval_append,
        SPFactor.listEval_cons,
        SPFactor.listEval_nil, mul_one,
        SPFactor.eval_neg, ih, (packet head).listEval_eq]
      rw [element_mul_left]

/-- The signed-polynomial worklist preserves any common lower support bound. -/
theorem weight_least_factors
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (right : SPFactor H ι)
    (packet :
      ∀ left : SPFactor H ι,
        TSPkt n left right) :
    ∀ {left : List (SPFactor H ι)},
      SPFactor.WordWeightLeast lowerWeight left →
        SPFactor.WordWeightLeast lowerWeight
          (factors right packet left) := by
  intro left hleft
  induction left with
  | nil =>
      intro x hx
      simp at hx
  | cons head tail ih =>
      have hhead :
          lowerWeight ≤ head.word.weight HEAddres.weight :=
        hleft head (by simp)
      have htail :
          SPFactor.WordWeightLeast lowerWeight tail := by
        intro x hx
        exact hleft x (by simp [hx])
      intro x hx
      simp only [factors_cons, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with ((rfl | hx) | rfl) | hx
      · exact hhead
      · exact ih htail x hx
      · simpa only [SPFactor.word_neg] using hhead
      · exact
          hhead.trans
            (Nat.le_of_lt ((packet head).word_weight_left x hx))

/-- The signed-polynomial worklist is truncated when its left source is. -/
theorem isTruncated_factors
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (right : SPFactor H ι)
    (packet :
      ∀ left : SPFactor H ι,
        TSPkt n left right) :
    ∀ {left : List (SPFactor H ι)},
      SPFactor.IsTruncated n left →
        SPFactor.IsTruncated n
          (factors right packet left) := by
  intro left hleft
  induction left with
  | nil =>
      intro x hx
      simp at hx
  | cons head tail ih =>
      have hhead :
          head.word.weight HEAddres.weight < n :=
        hleft head (by simp)
      have htail : SPFactor.IsTruncated n tail := by
        intro x hx
        exact hleft x (by simp [hx])
      intro x hx
      simp only [factors_cons, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with ((rfl | hx) | rfl) | hx
      · exact hhead
      · exact ih htail x hx
      · simpa only [SPFactor.word_neg] using hhead
      · exact (packet head).word_weight_cutoff x hx

end SBWork
end TCTex
end Towers

-- Merged from PolynomialSignedSemantic.lean

/-!
# Operations on signed-polynomial source recollections

An upward recollection of a signed-polynomial source can be inverted without
running the collector again.  Inverting both lists preserves truncation and
physical support, while list evaluation changes by group inversion on both
sides.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/-- Semantic upward recollection of an arbitrary signed-polynomial source. -/
structure SSRecol
    {d n lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    {ι : Type}
    (rawSource : List (SPFactor H ι)) where
  higherSource : List (SPFactor H ι)
  higher_source_truncated :
    SPFactor.IsTruncated n higherSource
  higher_weight_least :
    SPFactor.WordWeightLeast lowerWeight higherSource
  list_higher_raw :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e higherSource =
        SPFactor.listEval e rawSource

namespace
  SSRecol

/-- Invert an upward recollection by inverting its collected source. -/
noncomputable def inverse
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {rawSource : List (SPFactor H ι)}
    (recollection :
      SSRecol
        (n := n) (lowerWeight := lowerWeight) H rawSource) :
    SSRecol
      (n := n) (lowerWeight := lowerWeight) H
        (SPFactor.inverseList rawSource) where
  higherSource :=
    SPFactor.inverseList recollection.higherSource
  higher_source_truncated :=
    SPFactor.truncated_inverse_list
      recollection.higher_source_truncated
  higher_weight_least :=
    SPFactor.least_inverse_list
      recollection.higher_weight_least
  list_higher_raw := by
    intro e
    rw [SPFactor.list_eval_inverse,
      SPFactor.list_eval_inverse,
      recollection.list_higher_raw]

end
  SSRecol

end TCTex
end Towers

/-!
# Normalizing signed-polynomial sources with atomic active layer

The restricted-sharp atomic router extends from pure fixed-weight atomic lists
to sources whose factors are either atoms in the active layer or already lie
strictly above it. Stronger factors delegate to the next-stratum normalizer.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace TSFtry

/-- Normalize a source whose active factors are atoms and others are stronger. -/
noncomputable def normalization_atoms_higher
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
        lowerWeight <
            factor.word.weight HEAddres.weight ∨
          ∃ address : HEAddres H,
            factor.word = .atom address ∧ address.weight = lowerWeight) →
        ∃ coordinates : CCRecipe H ι,
          coordinates.NTBelow lowerWeight ∧
            ∀ e : ι → HEFam H,
              SPFactor.listEval (n := n) e
                  (coordinates.factors (n := n)) =
                SPFactor.listEval (n := n) e source := by
  intro source hsourceTruncated hsourceShape
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
      have hinitialShape :
          ∀ x ∈ initial,
            lowerWeight <
                x.word.weight HEAddres.weight ∨
              ∃ address : HEAddres H,
                x.word = .atom address ∧ address.weight = lowerWeight := by
        intro x hx
        exact hsourceShape x (by simp [hx])
      have hfactorTruncated :
          factor.word.weight HEAddres.weight < n :=
        hsourceTruncated factor (by simp)
      rcases ih hinitialTruncated hinitialShape with
        ⟨coordinates, hcoordinates, heval⟩
      rcases hsourceShape factor (by simp) with hfactorHigher |
          ⟨address, hword, haddressWeight⟩
      · rcases nextNormalizer.insertion_word_weight coordinates
            factor hcoordinates hfactorHigher hfactorTruncated with
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
                (coordinates.factors (n := n)) *
              factor.eval (n := n) e := by
            rw [SPFactor.listEval_append]
            simp
          _ = SPFactor.listEval (n := n) e initial *
              factor.eval (n := n) e := by
            rw [heval e]
          _ = SPFactor.listEval (n := n) e
                (initial ++ [factor]) := by
            rw [SPFactor.listEval_append]
            simp
      · rcases factory.semantic_insertion_atom hn H hH sharp
            nextNormalizer coordinates factor address hcoordinates hword
              haddressWeight hfactorTruncated with
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
                (coordinates.factors (n := n)) *
              factor.eval (n := n) e := by
            rw [SPFactor.listEval_append]
            simp
          _ = SPFactor.listEval (n := n) e initial *
              factor.eval (n := n) e := by
            rw [heval e]
          _ = SPFactor.listEval (n := n) e
                (initial ++ [factor]) := by
            rw [SPFactor.listEval_append]
            simp

/-- A semantically deeper mixed source has a strictly stronger finite tail. -/
noncomputable def
    higher_atoms_or
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
    (hsourceShape :
      ∀ factor ∈ source,
        lowerWeight <
            factor.word.weight HEAddres.weight ∨
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
  rcases factory.normalization_atoms_higher
      hn H hH sharp nextNormalizer source hsourceTruncated hsourceShape with
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

/-- Package mixed-source normalization as an upward semantic recollection. -/
noncomputable def
    atoms_or_higher
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
    (hsourceShape :
      ∀ factor ∈ source,
        lowerWeight <
            factor.word.weight HEAddres.weight ∨
          ∃ address : HEAddres H,
            factor.word = .atom address ∧ address.weight = lowerWeight)
    (hsourceMem :
      ∀ e : ι → HEFam H,
        SPFactor.listEval (n := n) e source ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            lowerWeight) :
    SSRecol
      (n := n) (lowerWeight := lowerWeight + 1) H source := by
  let result :=
    factory.higher_atoms_or
      hn H hH sharp nextNormalizer source hlowerWeightPos
        hlowerWeightTruncated hsourceTruncated hsourceShape hsourceMem
  let higherSource := Classical.choose result
  have hhigherSource := Classical.choose_spec result
  exact
    {
      higherSource := higherSource
      higher_source_truncated := hhigherSource.1
      higher_weight_least := hhigherSource.2.1
      list_higher_raw := hhigherSource.2.2
    }

end TSFtry

end TCTex
end Towers

/-!
# Composition operations for signed-polynomial source recollections

Recursive collection produces finite families of independently recollected
signed-polynomial sources.  This file records the source-level operations
needed to assemble them: the empty recollection, concatenation, and finite
`flatMap` composition.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u v

namespace
  SSRecol

/-- The empty source recollects to itself at every support bound. -/
def empty
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type} :
    SSRecol
      (n := n) (lowerWeight := lowerWeight) H
        ([] : List (SPFactor H ι)) where
  higherSource := []
  higher_source_truncated := by
    intro factor hfactor
    simp at hfactor
  higher_weight_least := by
    intro factor hfactor
    simp at hfactor
  list_higher_raw := by
    intro e
    rfl

/-- Concatenate independently recollected signed-polynomial sources. -/
def append
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {leftSource rightSource : List (SPFactor H ι)}
    (left :
      SSRecol
        (n := n) (lowerWeight := lowerWeight) H leftSource)
    (right :
      SSRecol
        (n := n) (lowerWeight := lowerWeight) H rightSource) :
    SSRecol
      (n := n) (lowerWeight := lowerWeight) H
        (leftSource ++ rightSource) where
  higherSource := left.higherSource ++ right.higherSource
  higher_source_truncated := by
    intro factor hfactor
    rcases List.mem_append.mp hfactor with hfactor | hfactor
    · exact left.higher_source_truncated factor hfactor
    · exact right.higher_source_truncated factor hfactor
  higher_weight_least := by
    intro factor hfactor
    rcases List.mem_append.mp hfactor with hfactor | hfactor
    · exact left.higher_weight_least factor hfactor
    · exact right.higher_weight_least factor hfactor
  list_higher_raw := by
    intro e
    rw [SPFactor.listEval_append,
      SPFactor.listEval_append,
      left.list_higher_raw,
      right.list_higher_raw]

/-- Recollect a finite `flatMap` source from recollections of its pieces. -/
def flatMap
    {α : Type v}
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (items : List α)
    (rawSource : α → List (SPFactor H ι))
    (recollection :
      ∀ item ∈ items,
        SSRecol
          (n := n) (lowerWeight := lowerWeight) H (rawSource item)) :
    SSRecol
      (n := n) (lowerWeight := lowerWeight) H
        (items.flatMap rawSource) := by
  induction items with
  | nil =>
      exact empty
  | cons head tail ih =>
      exact
        append
          (recollection head (by simp))
          (ih fun item hitem => recollection item (by simp [hitem]))

end
  SSRecol

end TCTex
end Towers

/-!
# Congruence for signed-polynomial source recollections

Semantic recollection depends only on the evaluated value of a raw symbolic
source.  A recollected source can therefore be reused for any pointwise
evaluation-equivalent raw source.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace
  SSRecol

/-- Transport a semantic recollection across source evaluation equality. -/
def of_list_eq
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {source target : List (SPFactor H ι)}
    (recollection :
      SSRecol
        (n := n) (lowerWeight := lowerWeight) H source)
    (heval :
      ∀ e : ι → HEFam H,
        SPFactor.listEval (n := n) e source =
          SPFactor.listEval e target) :
    SSRecol
      (n := n) (lowerWeight := lowerWeight) H target where
  higherSource := recollection.higherSource
  higher_source_truncated := recollection.higher_source_truncated
  higher_weight_least :=
    recollection.higher_weight_least
  list_higher_raw := by
    intro e
    exact
      (recollection.list_higher_raw e).trans (heval e)

end
  SSRecol
end TCTex
end Towers

/-!
# Normalizing recollected signed-polynomial sources

Once a signed-polynomial source has been recollected at a stronger support
bound, a normalizer at that stronger bound yields a coordinate endpoint
without returning to the weaker physical support of the raw source.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace
  SSRecol

/-- Normalize an upward-recollected source at its reached support bound. -/
lemma exists_normalizedCoordinates
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {rawSource : List (SPFactor H ι)}
    (recollection :
      SSRecol
        (n := n) (lowerWeight := lowerWeight) H rawSource)
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight) H) :
    ∃ coordinates : CCRecipe H ι,
      coordinates.NTBelow lowerWeight ∧
        ∀ e : ι → HEFam H,
          SPFactor.listEval (n := n) e
              (coordinates.factors (n := n)) =
            SPFactor.listEval (n := n) e rawSource := by
  rcases normalizer.normalize recollection.higherSource
      recollection.higher_source_truncated
      recollection.higher_weight_least with
    ⟨coordinates, hcoordinates, heval⟩
  exact
    ⟨coordinates, hcoordinates, fun e =>
      (heval e).trans (recollection.list_higher_raw e)⟩

end
  SSRecol

namespace TSPkt

/-- A recollected correction packet admits an endpoint at reached support. -/
lemma nonempty_normalization_support
    {d n supportWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (recollection :
      SSRecol
        (n := n) (lowerWeight := supportWeight) H C.factors)
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := supportWeight) H)
    (hsupportWeightPos : 1 ≤ supportWeight) :
    Nonempty
      (TPSem
        (supportWeight - 1) C) := by
  rcases recollection.exists_normalizedCoordinates normalizer with
    ⟨coordinates, hcoordinates, heval⟩
  exact ⟨{
      coordinates := coordinates
      coordinates_no_below := by
        simpa [Nat.sub_add_cancel hsupportWeightPos] using hcoordinates
      list_eval_coordinates := fun e => (heval e).trans (C.listEval_eq e)
    }⟩

/-- Normalize a recollected correction packet at its reached support. -/
noncomputable def semantic_normalization_support
    {d n supportWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (recollection :
      SSRecol
        (n := n) (lowerWeight := supportWeight) H C.factors)
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := supportWeight) H)
    (hsupportWeightPos : 1 ≤ supportWeight) :
    TPSem
      (supportWeight - 1) C :=
  Classical.choice
    (C.nonempty_normalization_support
      recollection normalizer hsupportWeightPos)

/-- Expose a recollected packet through a weaker parent-support interface. -/
noncomputable def semantic_normalization_recollection
    {d n lowerWeight supportWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {B A : SPFactor H ι}
    (C : TSPkt n B A)
    (recollection :
      SSRecol
        (n := n) (lowerWeight := supportWeight) H C.factors)
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := supportWeight) H)
    (hsupport : lowerWeight + 1 ≤ supportWeight) :
    TPSem
      lowerWeight C :=
  (C.semantic_normalization_support recollection
    normalizer (by omega)).weaken (by omega)

end TSPkt

end TCTex
end Towers

/-!
# Multiset descent for sharply supported source recollections

Any signed semantic source recollection supported strictly above a parent
factor can replace that parent in cutoff-defect multiset recursion.  This is
the source-level counterpart of sharp correction-packet descent.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace
  SSRecol

/-- Every retained sharply supported source factor improves the parent defect. -/
lemma higher_defect_parent
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {rawSource : List (SPFactor H ι)}
    (recollection :
      SSRecol
        (n := n) (lowerWeight := lowerWeight) H rawSource)
    (parent : SPFactor H ι)
    (hparent :
      parent.word.weight HEAddres.weight < lowerWeight)
    {x : SPFactor H ι}
    (hx : x ∈ recollection.higherSource) :
    SPFactor.cutoffDefect n x <
      SPFactor.cutoffDefect n parent := by
  have hxSupported :=
    recollection.higher_weight_least x hx
  have hxTruncated := recollection.higher_source_truncated x hx
  simp only [SPFactor.cutoffDefect]
  omega

/-- Replacing a parent by any sharply supported recollected source descends. -/
lemma defect_multiset_singleton
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {rawSource : List (SPFactor H ι)}
    (recollection :
      SSRecol
        (n := n) (lowerWeight := lowerWeight) H rawSource)
    (parent : SPFactor H ι)
    (hparent :
      parent.word.weight HEAddres.weight < lowerWeight)
    (P : List (SPFactor H ι)) :
    SPFactor.CutoffDefectMultiset n
      (P ++ recollection.higherSource) (P ++ [parent]) := by
  unfold SPFactor.CutoffDefectMultiset
  rw [SPFactor.defect_multiset_append,
    SPFactor.defect_multiset_append,
    SPFactor.cutoff_multiset_singleton]
  apply Multiset.dershowitz_manna_forall
  intro y hy
  rw [SPFactor.cutoffDefectMultiset] at hy
  rcases List.mem_map.mp (Multiset.mem_coe.mp hy) with ⟨x, hx, rfl⟩
  exact recollection.higher_defect_parent parent hparent hx

end
  SSRecol

end TCTex
end Towers

/-!
# Recollecting semantically higher signed-polynomial sources

A symbolic source can be physically supported in one Hall-weight stratum
while its evaluated product starts one lower-central layer higher.  Normalize
the source at its physical support bound.  The lower-central membership
hypothesis forces the normalized active coordinate block to vanish, so the
strictly higher coordinate tail recollects the original source.

This assumes a current-stratum signed semantic normalizer rather than
constructing that normalizer from atomic factors.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace
  TSNormal

/--
Extract an upward recollection from a physically supported source whose
evaluated product starts one lower-central layer higher.
-/
noncomputable def source_recollection_series
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight) H)
    {ι : Type}
    (source : List (SPFactor H ι))
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n)
    (hsourceTruncated : SPFactor.IsTruncated n source)
    (hsourceSupported :
      SPFactor.WordWeightLeast lowerWeight source)
    (hsourceMem :
      ∀ e : ι → HEFam H,
        SPFactor.listEval (n := n) e source ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            lowerWeight) :
    SSRecol
      (n := n) (lowerWeight := lowerWeight + 1) H source := by
  let normalization :=
    normalizer.normalize source hsourceTruncated hsourceSupported
  let coordinates := Classical.choose normalization
  have hcoordinates := (Classical.choose_spec normalization).1
  have heval := (Classical.choose_spec normalization).2
  refine
    {
      higherSource := coordinates.tailFactors (n := n) lowerWeight
      higher_source_truncated :=
        coordinates.truncated_factors (by omega)
      higher_weight_least :=
        coordinates.word_least_factors
      list_higher_raw := ?_
    }
  intro e
  have hcoordinatesMem :
      collectedHallProduct (n := n) H (coordinates.eval e) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          lowerWeight := by
    rw [← coordinates.listEval_factors, heval e]
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

end
  TSNormal

end TCTex
end Towers

/-!
# Automatic signed Hall collection through the class-three cutoff

At cutoff at most four, every nonterminal intrinsic factor residual has word
weight one.  Such a factor is already its own active Hall layer, so its
intrinsic residual source recollects semantically to the empty list.

Combining this empty residual source with the explicit class-three
Hall-Petresco packet constructs product and inverse coordinate polynomials
without any remaining residual-source hypothesis.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
Through the class-three cutoff, graded Hall bases construct global
product-coordinate polynomials.
-/
theorem collected_data_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : List (HEFam H)) :
    CollectedCoordinateData (n := n) H e :=
  collected_residual_builder
    hn H hH e
      (SCBuilda.n_four_unconditional
        hn4)

/--
Through the class-three cutoff, graded Hall bases construct global
inverse-coordinate polynomials.
-/
theorem data_n_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : HEFam H) :
    CollectedInverseData (n := n) H e :=
  coord_collect_builder
    hn H hH e
      (SCBuilda.n_four_unconditional
        hn4)

end TCTex
end Towers

/-!
# Coordinate normalizations of arbitrary recollected signed sources

Correction packets already have a dedicated signed semantic normalization
record.  Structural restart also produces arbitrary quotient sources.  This
file records the corresponding coordinate endpoint for an arbitrary source
after it has been recollected to a stronger support bound.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


/-- A signed coordinate endpoint for an arbitrary symbolic source. -/
structure SSNorm
    {d n lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    {ι : Type}
    (rawSource : List (SPFactor H ι)) where
  coordinates :
    CCRecipe H ι
  coordinates_no_below :
    coordinates.NTBelow lowerWeight
  coordinates_raw_source :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e
          (coordinates.factors (n := n)) =
        SPFactor.listEval e rawSource

namespace
  SSRecol

/--
Normalize an arbitrary recollected source at its reached semantic support
bound.
-/
noncomputable def toSourceNormalization
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {rawSource : List (SPFactor H ι)}
    (recollection :
      SSRecol
        (n := n) (lowerWeight := lowerWeight) H rawSource)
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight) H) :
    SSNorm
      (n := n) (lowerWeight := lowerWeight) H rawSource := by
  let normalization := recollection.exists_normalizedCoordinates normalizer
  let coordinates := Classical.choose normalization
  have hcoordinates := (Classical.choose_spec normalization).1
  have heval := (Classical.choose_spec normalization).2
  exact
    {
      coordinates := coordinates
      coordinates_no_below := hcoordinates
      coordinates_raw_source := heval
    }

end
  SSRecol

namespace
  SSNorm

/-- Arbitrary normalized sources remain in their reached support stratum. -/
lemma factors_weight_least
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {rawSource : List (SPFactor H ι)}
    (normalization :
      SSNorm
        (n := n) (lowerWeight := lowerWeight) H rawSource) :
    SPFactor.WordWeightLeast lowerWeight
      (normalization.coordinates.factors (n := n)) :=
  normalization.coordinates.no_terms_below
    normalization.coordinates_no_below

/-- Arbitrary normalized source endpoints are physically truncated. -/
lemma factors_isTruncated
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {rawSource : List (SPFactor H ι)}
    (normalization :
      SSNorm
        (n := n) (lowerWeight := lowerWeight) H rawSource) :
    SPFactor.IsTruncated n
      (normalization.coordinates.factors (n := n)) :=
  normalization.coordinates.isTruncated_factors

end
  SSNorm

end TCTex
end Towers

/-!
# Raising support of semantically deeper signed-polynomial recollections

After one operational rewrite removes same-stratum wrappers, a source may be
physically supported above its original stratum while its value is known to
lie much deeper in the lower-central filtration.  Repeatedly normalize the
current physical stratum and discard its vanishing active block until the
full semantic support bound is reached.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace
  SSRecol

/-- Compose two semantic source recollections. -/
noncomputable def trans
    {d n firstWeight secondWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    {rawSource : List (SPFactor H ι)}
    (first :
      SSRecol
        (n := n) (lowerWeight := firstWeight) H rawSource)
    (second :
      SSRecol
        (n := n) (lowerWeight := secondWeight) H first.higherSource) :
    SSRecol
      (n := n) (lowerWeight := secondWeight) H rawSource where
  higherSource := second.higherSource
  higher_source_truncated := second.higher_source_truncated
  higher_weight_least :=
    second.higher_weight_least
  list_higher_raw := by
    intro e
    rw [second.list_higher_raw,
      first.list_higher_raw]

/--
Raise a recollected source by one support stratum when its value lies one
lower-central layer above the current physical support.
-/
noncomputable def succOfNormalizer
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight) H)
    {ι : Type}
    {rawSource : List (SPFactor H ι)}
    (recollection :
      SSRecol
        (n := n) (lowerWeight := lowerWeight) H rawSource)
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n)
    (hrawSourceMem :
      ∀ e : ι → HEFam H,
        SPFactor.listEval (n := n) e rawSource ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            lowerWeight) :
    SSRecol
      (n := n) (lowerWeight := lowerWeight + 1) H rawSource :=
  recollection.trans
    (normalizer.source_recollection_series
      hn H hH recollection.higherSource hlowerWeightPos
        hlowerWeightTruncated recollection.higher_source_truncated
          recollection.higher_weight_least
            (fun e => by
              rw [recollection.list_higher_raw]
              exact hrawSourceMem e))

/--
Raise a recollected source through finitely many semantically vanishing
strata.  A normalizer is required only from the initial physical support
upward.
-/
noncomputable def raiseSupportBy
    {d n initialWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (normalizerFrom :
      ∀ strongerWeight : ℕ,
        initialWeight ≤ strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight) H)
    {ι : Type}
    {rawSource : List (SPFactor H ι)}
    (recollection :
      SSRecol
        (n := n) (lowerWeight := initialWeight) H rawSource)
    (hinitialWeightPos : 1 ≤ initialWeight) :
    ∀ steps : ℕ,
      initialWeight + steps ≤ n →
        (∀ e : ι → HEFam H,
          SPFactor.listEval (n := n) e rawSource ∈
            Subgroup.lowerCentralSeries
              (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
              (initialWeight + steps - 1)) →
          SSRecol
            (n := n) (lowerWeight := initialWeight + steps) H rawSource
  | 0, _htargetTruncated, _hrawSourceMem => by
      simpa using recollection
  | steps + 1, htargetTruncated, hrawSourceMem => by
      have hinitialWeightTruncated : initialWeight < n := by
        omega
      let next :=
        recollection.succOfNormalizer hn H hH
          (normalizerFrom initialWeight (Nat.le_refl _))
          hinitialWeightPos hinitialWeightTruncated
          (fun e =>
            Subgroup.lowerCentralSeries_antitone (by omega) (hrawSourceMem e))
      let raised :=
        next.raiseSupportBy hn H hH
          (fun strongerWeight hstrongerWeight =>
            normalizerFrom strongerWeight (by omega))
          (by omega) steps (by omega)
          (by
            intro e
            simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              hrawSourceMem e)
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using raised

end
  SSRecol
end TCTex
end Towers

/-!
# Endpoint support raising for signed-polynomial recollections

Finite support raising is most convenient to consume by naming its target
stratum directly.  This file packages the subtraction arithmetic needed to
reach any semantically justified endpoint from an initial recollection.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace
  SSRecol

/--
Raise a recollected source directly to a chosen semantic support endpoint.
Normalizers are required only from the initial physical support upward.
-/
noncomputable def raiseSupportTo
    {d n initialWeight targetWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (normalizerFrom :
      ∀ strongerWeight : ℕ,
        initialWeight ≤ strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight) H)
    {ι : Type}
    {rawSource : List (SPFactor H ι)}
    (recollection :
      SSRecol
        (n := n) (lowerWeight := initialWeight) H rawSource)
    (hinitialWeightPos : 1 ≤ initialWeight)
    (hinitialTarget : initialWeight ≤ targetWeight)
    (htargetTruncated : targetWeight ≤ n)
    (hrawSourceMem :
      ∀ e : ι → HEFam H,
        SPFactor.listEval (n := n) e rawSource ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            (targetWeight - 1)) :
    SSRecol
      (n := n) (lowerWeight := targetWeight) H rawSource := by
  have htarget :
      initialWeight + (targetWeight - initialWeight) = targetWeight :=
    Nat.add_sub_of_le hinitialTarget
  let raised :=
    recollection.raiseSupportBy hn H hH normalizerFrom hinitialWeightPos
      (targetWeight - initialWeight)
      (by simpa only [htarget] using htargetTruncated)
      (by simpa only [htarget] using hrawSourceMem)
  simpa only [htarget] using raised

end
  SSRecol
end TCTex
end Towers

/-!
# Automatic polynomial collection from retained class-three recipes

Through cutoff four, the selected retained recipes form the Hall-Petresco
packet consumed by recursive signed polynomial collection.  Every nonterminal
intrinsic residual has weight one, so exact weight-one residual cancellation
completes product and inverse recollection.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open
  CCThree
open
  TPSrc

namespace
  SCBuilda

/--
Through cutoff four, retained recipes and exact weight-one residual
cancellation construct a complete signed polynomial recollection builder.
-/
noncomputable def automatic_recipe_four
    {d n : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)}
    (hn4 : n ≤ 4) :
    SCBuilda
      (n := n) hn H hH where
  packet :=
    all_n_four hn4
  factorResidualSource lowerWeight hnonterminal factor hfactorWeight
      _hfactorTruncated := by
    have hfactorPos := factor.word_weight_pos
    have hlowerWeight : lowerWeight = 1 := by
      omega
    have hfactorWeightOne :
        factor.word.weight HEAddres.weight = 1 := by
      omega
    simpa [hlowerWeight] using
      of_weight_one hn H hH factor hfactorWeightOne

end
  SCBuilda

open
  SCBuilda

/--
Through cutoff four, retained recipes construct collected-product coordinate
polynomials for arbitrary graded Hall families.
-/
theorem
    recipe_n_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : List (HEFam H)) :
    CollectedCoordinateData (n := n) H e :=
  restricted_recursive_builder
    hn H hH e
      ((automatic_recipe_four hn4)
        |>.restrictedRecursiveBuilder)

/--
Through cutoff four, retained recipes construct collected-inverse coordinate
polynomials for arbitrary graded Hall families.
-/
theorem
    collected_n_four
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : HEFam H) :
    CollectedInverseData (n := n) H e :=
  restricted_sharp_recursive
    hn H hH e
      ((automatic_recipe_four hn4)
        |>.restrictedRecursiveBuilder)

end TCTex
end Towers

/-!
# Reachable signed collection from retained recipe traces

The retained recipe-coefficient product law already supplies every custom
correction packet needed below the class-two range.  This file compiles that
law to the reachable signed-semantic collection builder, leaving only the
packet-free insertion schedule as an operational input.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u


open
  CCThree
open
  CPSplita

namespace
  CDBuild

/--
Compile the retained recipe-coefficient product law to the correction-packet
factory at one support stratum.
-/
noncomputable def retainedRecipeFactory
    {d n lowerWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n) :
    TSFtry
      (n := n) H lowerWeight :=
  (retainedAllPacket hrecipes
    |>.supportedWordFactory
      (WBForm.chooseNormalizerFamily H)
      lowerWeight)
    |>.correctionPacketFactory

/--
The retained recipe-coefficient product law fills the custom correction
factories in a reachable universal signed collector.  The only remaining
input is the packet-free reachable insertion schedule.
-/
noncomputable def recipe_coeff_trace
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (schedule :
      TIDeriva
        (n := n) H) :
    CDBuild
      (n := n) H where
  correctionFactory lowerWeight _hbelowClassTwoRange :=
    retainedRecipeFactory
      (lowerWeight := lowerWeight) hrecipes
  insert lowerWeight hnonterminal normalizer _factory :=
    schedule.insert lowerWeight hnonterminal normalizer

end
  CDBuild

open
  CDBuild

/--
The retained recipe-coefficient product law and packet-free reachable
insertion derivations construct product recollection polynomials.
-/
theorem
    collected_reachable_insertion
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : List (HEFam H))
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (schedule :
      TIDeriva
        (n := n) H) :
    CollectedCoordinateData (n := n) H e :=
  reachable_semantic_derivation
    hn H hH e
      (recipe_coeff_trace hrecipes schedule)

/--
The retained recipe-coefficient product law and packet-free reachable
insertion derivations construct inverse recollection polynomials.
-/
theorem
    reachable_insertion_schedule
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : HEFam H)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (schedule :
      TIDeriva
        (n := n) H) :
    CollectedInverseData (n := n) H e :=
  reachable_derivation_builder
    hn H hH e
      (recipe_coeff_trace hrecipes schedule)

end TCTex
end Towers

/-!
# Restricted sharp signed collection from retained recipe traces

The retained recipe-coefficient product law is already a cutoff-specific
all-integral Hall-Petresco packet.  This file compiles that one ordered law to
the correction factories required by direct recursive signed collection at
every support stratum.

The only remaining signed-collection input is intrinsic factor-residual
normalization.  The file is intentionally not imported by the existing
collection proof.
-/

namespace Towers
namespace TCTex

universe u


open
  CCThree
open
  CPSplita

namespace
  SRBuild

/--
Compile the retained recipe-coefficient product law to the correction-packet
factories used by recursive signed collection.
-/
noncomputable def recipe_coeff_trace
    {d n : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)}
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (factorResidual :
      ∀ {ι : Type}
        (lowerWeight : ℕ),
        ¬n ≤ 2 * lowerWeight →
          TSNormal
              (n := n) (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactor H ι),
              factor.word.weight HEAddres.weight = lowerWeight →
              factor.word.weight HEAddres.weight < n →
                TPExp
                  (lowerWeight := lowerWeight) hn H hH ι factor) :
    SRBuild
      (n := n) hn H hH where
  correctionFactory lowerWeight _hterminal :=
    (retainedAllPacket hrecipes
      |>.supportedWordFactory
        (WBForm.chooseNormalizerFamily H)
        lowerWeight)
      |>.correctionPacketFactory
  factorResidual := factorResidual

end
  SRBuild

open
  SRBuild

/--
The retained recipe-coefficient product law and intrinsic residual
normalization construct product recollection polynomials.
-/
theorem
    collected_coeff_residual
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : List (HEFam H))
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (factorResidual :
      ∀ {ι : Type}
        (lowerWeight : ℕ),
        ¬n ≤ 2 * lowerWeight →
          TSNormal
              (n := n) (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactor H ι),
              factor.word.weight HEAddres.weight = lowerWeight →
              factor.word.weight HEAddres.weight < n →
                TPExp
                  (lowerWeight := lowerWeight) hn H hH ι factor) :
    CollectedCoordinateData (n := n) H e :=
  restricted_recursive_builder
    hn H hH e
      (recipe_coeff_trace hrecipes factorResidual)

/--
The retained recipe-coefficient product law and intrinsic residual
normalization construct inverse recollection polynomials.
-/
theorem
    collected_coord_residual
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : HEFam H)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (factorResidual :
      ∀ {ι : Type}
        (lowerWeight : ℕ),
        ¬n ≤ 2 * lowerWeight →
          TSNormal
              (n := n) (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactor H ι),
              factor.word.weight HEAddres.weight = lowerWeight →
              factor.word.weight HEAddres.weight < n →
                TPExp
                  (lowerWeight := lowerWeight) hn H hH ι factor) :
    CollectedInverseData (n := n) H e :=
  restricted_sharp_recursive
    hn H hH e
      (recipe_coeff_trace hrecipes factorResidual)

end TCTex
end Towers

/-!
# Restricted sharp signed collection from retained traces and singleton normalization

The retained recipe-coefficient product law is a cutoff Hall-Petresco packet.
Together with semantic normalization of each active signed factor after higher
strata have been normalized, it constructs global product and inverse
recollection polynomials.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u


open
  CCThree
open
  CPSplita

namespace
  RSBuilda

/--
Use one retained recipe-coefficient product law as the cutoff packet for
recursive signed collection from singleton normalizations.
-/
noncomputable def recipe_coeff_trace
    {d n : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n)}
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (factorNormalization :
      ∀ {ι : Type}
        (lowerWeight : ℕ),
        ¬n ≤ 2 * lowerWeight →
          TSNormal
              (n := n) (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactor H ι),
              factor.word.weight HEAddres.weight = lowerWeight →
              factor.word.weight HEAddres.weight < n →
                TPActive
                  (n := n) (lowerWeight := lowerWeight) H ι factor) :
    RSBuilda
      (n := n) hn H hH where
  packet :=
    retainedAllPacket hrecipes
  factorNormalization := factorNormalization

end
  RSBuilda

open
  RSBuilda

/--
The retained recipe-coefficient product law and singleton normalizations
construct product recollection polynomials.
-/
theorem
    collected_coord_norm
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : List (HEFam H))
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (factorNormalization :
      ∀ {ι : Type}
        (lowerWeight : ℕ),
        ¬n ≤ 2 * lowerWeight →
          TSNormal
              (n := n) (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactor H ι),
              factor.word.weight HEAddres.weight = lowerWeight →
              factor.word.weight HEAddres.weight < n →
                TPActive
                  (n := n) (lowerWeight := lowerWeight) H ι factor) :
    CollectedCoordinateData (n := n) H e :=
  collected_sharp_builder
    hn H hH e
      (recipe_coeff_trace hrecipes factorNormalization)

/--
The retained recipe-coefficient product law and singleton normalizations
construct inverse recollection polynomials.
-/
theorem
    collected_coord_coeff
    {d n : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (hH :
      ∀ r : ℕ,
        1 ≤ r →
          r < n →
            (H r).FormsAssocGradedbasis (n := n))
    (e : HEFam H)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    (factorNormalization :
      ∀ {ι : Type}
        (lowerWeight : ℕ),
        ¬n ≤ 2 * lowerWeight →
          TSNormal
              (n := n) (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactor H ι),
              factor.word.weight HEAddres.weight = lowerWeight →
              factor.word.weight HEAddres.weight < n →
                TPActive
                  (n := n) (lowerWeight := lowerWeight) H ι factor) :
    CollectedInverseData (n := n) H e :=
  restricted_sharp_builder
    hn H hH e
      (recipe_coeff_trace hrecipes factorNormalization)

end TCTex
end Towers

-- Merged from PolynomialOuterBracketPacketWorklistInventory.lean

/-!
# Inventory of polynomial outer-bracket packet worklists

The exact signed-polynomial worklist for a bracket with a finite left product
contains three kinds of factors: retained left factors, their signed
inverses, and terminal correction-packet factors.  This file records that
finite inventory without imposing any concrete Hall-family specialization.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

namespace SBWork

/-- Every worklist factor comes from a wrapper or one terminal packet. -/
theorem left_or_factors
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (right : SPFactor H ι)
    (packet :
      ∀ left : SPFactor H ι,
        TSPkt n left right)
    {left : List (SPFactor H ι)}
    {x : SPFactor H ι}
    (hx : x ∈ factors right packet left) :
    (∃ source ∈ left, x = source) ∨
      (∃ source ∈ left, x = source.neg) ∨
        ∃ source ∈ left, x ∈ (packet source).factors := by
  induction left with
  | nil =>
      simp at hx
  | cons head tail ih =>
      simp only [factors_cons, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with ((hhead | hx) | hheadNeg) | hx
      · exact Or.inl ⟨head, List.mem_cons_self, hhead⟩
      · rcases ih hx with hsource | hsource | hsource
        · rcases hsource with ⟨source, hsource, hx⟩
          exact Or.inl ⟨source, List.mem_cons_of_mem head hsource, hx⟩
        · rcases hsource with ⟨source, hsource, hx⟩
          exact
            Or.inr
              (Or.inl ⟨source, List.mem_cons_of_mem head hsource, hx⟩)
        · rcases hsource with ⟨source, hsource, hx⟩
          exact
            Or.inr
              (Or.inr ⟨source, List.mem_cons_of_mem head hsource, hx⟩)
      · exact Or.inr (Or.inl ⟨head, List.mem_cons_self, hheadNeg⟩)
      · exact Or.inr (Or.inr ⟨head, List.mem_cons_self, hx⟩)

end SBWork
end TCTex
end Towers

-- Merged from PolynomialOuterBracketPacketWorklistRecursiveRecollection.lean

/-!
# Recursive recollection of polynomial outer-bracket worklists

An outer-bracket packet worklist retains conjugating copies of each left
factor.  If the recursive tail has already been recollected one layer higher,
sharp higher-tail routing removes the wrappers around that tail.  Appending
the terminal correction packet then recollects the complete worklist.

The recursion is structural on the finite left source.  It assumes a sharp
router at the left factors' common stratum and does not assume a semantic
normalizer at that same stratum.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace SBWork

/--
Structurally recollect an exact outer-bracket worklist whose left factors all
lie in one ordinary Hall-weight stratum.
-/
noncomputable def source_recollect_normalizer
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (right : SPFactor H ι)
    (packet :
      ∀ left : SPFactor H ι,
        TSPkt n left right) :
    ∀ left : List (SPFactor H ι),
      SPFactor.IsTruncated n left →
        (∀ x ∈ left,
          x.word.weight HEAddres.weight = lowerWeight) →
          SSRecol
            (n := n) (lowerWeight := lowerWeight + 1) H
            (factors right packet left)
  | [], _hleftTruncated, _hleftWeight =>
      SSRecol.empty
  | head :: tail, hleftTruncated, hleftWeight => by
      have hheadTruncated :
          head.word.weight HEAddres.weight < n :=
        hleftTruncated head (by simp)
      have htailTruncated :
          SPFactor.IsTruncated n tail := by
        intro x hx
        exact hleftTruncated x (by simp [hx])
      have hheadWeight :
          head.word.weight HEAddres.weight = lowerWeight :=
        hleftWeight head (by simp)
      have htailWeight :
          ∀ x ∈ tail,
            x.word.weight HEAddres.weight = lowerWeight := by
        intro x hx
        exact hleftWeight x (by simp [hx])
      let tailRecollection :=
        source_recollect_normalizer factory sharp right
          packet tail htailTruncated htailWeight
      let conjugated :=
        factory.conjugated_recollection_normalizer sharp
          head.neg
          (by simpa only [SPFactor.word_neg] using
            hheadWeight)
          (by simpa only [SPFactor.word_neg] using
            hheadTruncated)
          (factors right packet tail)
          tailRecollection.higherSource
          tailRecollection.higher_source_truncated
          tailRecollection.higher_weight_least
          tailRecollection.list_higher_raw
      exact
        {
          higherSource := conjugated.higherSource ++ (packet head).factors
          higher_source_truncated := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact conjugated.higher_source_truncated x hx
            · exact (packet head).word_weight_cutoff x hx
          higher_weight_least := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact conjugated.higher_least_succ x hx
            · have hterminal := (packet head).word_weight_left x hx
              omega
          list_higher_raw := by
            intro e
            rw [SPFactor.listEval_append,
              conjugated.higher_conjugated_raw]
            simp only [factors_cons,
              SPFactor.conjugatedRawSource,
              SPFactor.listEval_append,
              SPFactor.listEval_cons,
              SPFactor.listEval_nil, mul_one,
              SPFactor.eval_neg, inv_inv]
        }

end SBWork
end TCTex
end Towers
