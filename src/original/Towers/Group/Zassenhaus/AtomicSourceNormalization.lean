import Towers.Group.Zassenhaus.AtomicSourceReduction
import Towers.Group.Zassenhaus.RestrictedSharp

/-!
# Normalizing fixed-weight atomic symbolic Hall-power sources

The restricted-sharp collector resolves an active symbolic Hall-power factor
once its intrinsic residual is available one stratum higher. Atomic Hall
factors have empty intrinsic residuals, so a fixed-weight atomic list can be
normalized using only the correction packet factory and deeper normalizers.

If the value of that list already lies in the next lower-central stratum, its
normalized active Hall block evaluates trivially. The normalized higher tail
then gives a finite symbolic recollection of the original source.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace TSFtrya

open
  TSSrc
open
  TAExp
open
  TAResolua

/-- Insert one atomic active-weight factor using restricted-sharp routing. -/
noncomputable def insertion_atom
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
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight)
    (address : HEAddres H)
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hword : factor.word = .atom address)
    (haddressWeight : address.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    ∃ next : CCExpans H inputWeight,
      next.NTBelow lowerWeight ∧
        ∀ q : ℕ,
          SPFactora.listEval (n := n) q
              (next.factors (n := n)) =
            SPFactora.listEval (n := n) q
              (coordinates.factors (n := n) ++ [factor]) := by
  subst lowerWeight
  have hfactorWeight :
      factor.word.weight PEAddres.weight = address.weight := by
    rw [hword]
    rfl
  have haddressTruncated : address.weight < n := by
    omega
  let factorTail :=
    (of_atom hn H hH factor address hword haddressTruncated)
      |>.factorExpansion
  let merge :=
    (factory
      |>.semantic_merge_sharp
        hn H hH sharp coordinates factor)
      |>.mergeResidualExpansion hfactorWeight hfactorTruncated
  let block :=
    mergeFactor merge factorTail
  let tail :=
    (factory
      |>.supported_route_sharp
        sharp coordinates factor hfactorWeight)
      |>.higherTailResolution hfactorWeight hfactorTruncated
  exact
    (active_block_tail
      hcoordinates hfactorWeight hfactorTruncated
        (block.activeBlockResolution hcoordinates hfactorWeight)
        tail)
      |>.exists_insertion nextNormalizer hfactorWeight hfactorTruncated

/--
Normalize a finite list of atomic factors lying in one fixed Hall-weight
layer.
-/
noncomputable def normalization_atoms
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
        ∃ address : HEAddres H,
          factor.word = .atom address ∧ address.weight = lowerWeight) →
        ∃ coordinates : CCExpans H inputWeight,
          coordinates.NTBelow lowerWeight ∧
            ∀ q : ℕ,
              SPFactora.listEval (n := n) q
                  (coordinates.factors (n := n)) =
                SPFactora.listEval (n := n) q source := by
  intro source hsourceTruncated hsourceAtomic
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
          factor.word.weight PEAddres.weight < n :=
        hsourceTruncated factor (by simp)
      rcases factory.insertion_atom
          hn H hH sharp nextNormalizer coordinates factor address hcoordinates
            hword haddressWeight hfactorTruncated with
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
              (coordinates.factors (n := n)) * factor.eval (n := n) q := by
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
An atomic fixed-weight source whose value starts one stratum higher has a
finite symbolic recollection supported one stratum higher.
-/
noncomputable def higher_atoms_series
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
    (hsourceAtomic :
      ∀ factor ∈ source,
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
  rcases factory.normalization_atoms
      hn H hH sharp nextNormalizer source hsourceTruncated hsourceAtomic with
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

end TSFtrya

end TCTex
end Towers
