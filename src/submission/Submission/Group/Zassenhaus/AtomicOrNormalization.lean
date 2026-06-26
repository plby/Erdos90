import Submission.Group.Zassenhaus.AtomicSourceNormalization
import Submission.Group.Zassenhaus.SourceRecollectionOperations

/-!
# Normalizing symbolic Hall-power sources with atomic active layer

The restricted-sharp atomic router extends from pure fixed-weight atomic lists
to sources whose factors are either atoms in the active layer or already lie
strictly above it.  Stronger factors delegate to the next-stratum normalizer.

If the complete source evaluates one lower-central layer deeper, its normalized
active block vanishes.  The remaining coordinate tail is therefore an upward
semantic recollection of the original mixed source.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace TSFtrya

/--
Normalize a finite source whose active-weight factors are atoms and whose
remaining factors already have strictly larger weight.
-/
noncomputable def semantic_normalization_atoms
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight) H)
    (nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H) :
    ∀ source : List (SPFactora H inputWeight),
      SPFactora.IsTruncated n source →
      (∀ factor ∈ source,
        lowerWeight <
            factor.word.weight PEAddres.weight ∨
          ∃ address : HEAddres H,
            factor.word = .atom address ∧ address.weight = lowerWeight) →
        ∃ coordinates : CCExpans H inputWeight,
          coordinates.NTBelow lowerWeight ∧
            ∀ q : ℕ,
              SPFactora.listEval (n := n) q
                  (coordinates.factors (n := n)) =
                SPFactora.listEval (n := n) q source := by
  intro source hsourceTruncated hsourceShape
  induction source using List.reverseRecOn with
  | nil =>
      exact
        ⟨CCExpans.empty H inputWeight,
          by
            intro s i hs
            rfl,
          by intro q; simp⟩
  | append_singleton initial factor ih =>
      have hinitialTruncated :
          SPFactora.IsTruncated n initial := by
        intro x hx
        exact hsourceTruncated x (by simp [hx])
      have hinitialShape :
          ∀ x ∈ initial,
            lowerWeight <
                x.word.weight PEAddres.weight ∨
              ∃ address : HEAddres H,
                x.word = .atom address ∧ address.weight = lowerWeight := by
        intro x hx
        exact hsourceShape x (by simp [hx])
      have hfactorTruncated :
          factor.word.weight PEAddres.weight < n :=
        hsourceTruncated factor (by simp)
      rcases ih hinitialTruncated hinitialShape with
        ⟨coordinates, hcoordinates, heval⟩
      rcases hsourceShape factor (by simp) with hfactorHigher |
          ⟨address, hword, haddressWeight⟩
      · rcases nextNormalizer.insertion_word_weight coordinates
            factor hcoordinates hfactorHigher hfactorTruncated with
          ⟨next, hnext, hnextEval⟩
        refine ⟨next, hnext, ?_⟩
        intro q
        calc
          SPFactora.listEval (n := n) q
                (next.factors (n := n)) =
              SPFactora.listEval (n := n) q
                (coordinates.factors (n := n) ++ [factor]) :=
            hnextEval q
          _ = SPFactora.listEval (n := n) q
                (coordinates.factors (n := n)) *
              factor.eval (n := n) q := by
            rw [SPFactora.listEval_append]
            simp
          _ = SPFactora.listEval (n := n) q initial *
              factor.eval (n := n) q := by
            rw [heval q]
          _ = SPFactora.listEval (n := n) q
                (initial ++ [factor]) := by
            rw [SPFactora.listEval_append]
            simp
      · rcases factory.insertion_atom hn H hH sharp
            nextNormalizer coordinates factor address hcoordinates hword
              haddressWeight hfactorTruncated with
          ⟨next, hnext, hnextEval⟩
        refine ⟨next, hnext, ?_⟩
        intro q
        calc
          SPFactora.listEval (n := n) q
                (next.factors (n := n)) =
              SPFactora.listEval (n := n) q
                (coordinates.factors (n := n) ++ [factor]) :=
            hnextEval q
          _ = SPFactora.listEval (n := n) q
                (coordinates.factors (n := n)) *
              factor.eval (n := n) q := by
            rw [SPFactora.listEval_append]
            simp
          _ = SPFactora.listEval (n := n) q initial *
              factor.eval (n := n) q := by
            rw [heval q]
          _ = SPFactora.listEval (n := n) q
                (initial ++ [factor]) := by
            rw [SPFactora.listEval_append]
            simp

/--
A mixed source whose active-weight factors are atoms and whose value starts one
stratum higher has a finite symbolic recollection supported one stratum higher.
-/
noncomputable def
    higher_atoms_or
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight) H)
    (nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H)
    (source : List (SPFactora H inputWeight))
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n)
    (hsourceTruncated : SPFactora.IsTruncated n source)
    (hsourceShape :
      ∀ factor ∈ source,
        lowerWeight <
            factor.word.weight PEAddres.weight ∨
          ∃ address : HEAddres H,
            factor.word = .atom address ∧ address.weight = lowerWeight)
    (hsourceMem :
      ∀ q : ℕ,
        SPFactora.listEval (n := n) q source ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            lowerWeight) :
    ∃ higherSource : List (SPFactora H inputWeight),
      SPFactora.IsTruncated n higherSource ∧
        SPFactora.WordWeightLeast
          (lowerWeight + 1) higherSource ∧
            ∀ q : ℕ,
              SPFactora.listEval (n := n) q higherSource =
                SPFactora.listEval (n := n) q source := by
  rcases factory.semantic_normalization_atoms
      hn H hH sharp nextNormalizer source hsourceTruncated hsourceShape with
    ⟨coordinates, hcoordinates, heval⟩
  refine
    ⟨coordinates.tailFactors (n := n) lowerWeight,
      coordinates.truncated_factors (by omega),
      coordinates.word_least_factors, ?_⟩
  intro q
  have hcoordinatesMem :
      collectedHallProduct (n := n) H (coordinates.eval q) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          lowerWeight := by
    rw [← coordinates.listEval_factors]
    rw [heval q]
    exact hsourceMem q
  have hactiveCoordinates :
      coordinates.eval q lowerWeight = 0 := by
    exact
      imp_coordinates_below
        (r := lowerWeight + 1) hn H hH (coordinates.eval q)
          (by simpa using hcoordinatesMem) lowerWeight hlowerWeightPos
            (by omega) hlowerWeightTruncated
  rw [← heval q,
    coordinates.append_no_below
      hcoordinates hlowerWeightPos (by omega),
    SPFactora.listEval_append,
    coordinates.list_weight_factors,
    hactiveCoordinates,
    BCWta.collected_weight_productzero,
    one_mul]

/-- Package mixed-source normalization as an upward semantic recollection. -/
noncomputable def
    atoms_or_higher
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight) H)
    (nextNormalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H)
    (source : List (SPFactora H inputWeight))
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n)
    (hsourceTruncated : SPFactora.IsTruncated n source)
    (hsourceShape :
      ∀ factor ∈ source,
        lowerWeight <
            factor.word.weight PEAddres.weight ∨
          ∃ address : HEAddres H,
            factor.word = .atom address ∧ address.weight = lowerWeight)
    (hsourceMem :
      ∀ q : ℕ,
        SPFactora.listEval (n := n) q source ∈
          Subgroup.lowerCentralSeries
            (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
            lowerWeight) :
    TSRecol
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

end TSFtrya

end TCTex
end Submission
