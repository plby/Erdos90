import Submission.Group.Zassenhaus.Truncation
import Submission.Group.Zassenhaus.WordExpansions
import Submission.Group.Zassenhaus.FamilyData

/-!
# Constructing Claim 5 data from symbolic Hall power rewrites

A repeated-power Hall collector ends in a normalized list of atomic Hall
factors.  This file packages explicit repeated-block coordinate expansions as
such an endpoint and proves that it evaluates to the corresponding collected
Hall product.

The final adapters deliberately keep the source-evaluation theorem explicit.
A concrete repeated-block scheduler must still construct a source list whose
evaluation is the power of the input collected Hall word and a truncated
rewrite run from that source to the normalized endpoint.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/-- Explicit repeated-block expansions for every normalized Hall coordinate. -/
structure CCExpans
    {d : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (inputWeight : ℕ) where
  expansion :
    ∀ s : ℕ, (H s).index → BCExp inputWeight s

namespace CCExpans

/-- Evaluate every normalized repeated-block coordinate expansion. -/
def eval
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight)
    (q : ℕ) :
    HEFam H :=
  fun s i => (R.expansion s i).eval q

/-- Normalized repeated-power factors in one fixed Hall-weight layer. -/
def weightFactors
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight)
    (s : ℕ) :
    List (SPFactora H inputWeight) :=
  (Finset.univ.sort fun i i' : (H s).index => i ≤ i').flatMap fun i =>
    (R.expansion s i).symbolicPowerFactors
      (.atom (⟨s, i⟩ : HEAddres H))

/-- Fixed-weight normalized power factors evaluate to their Hall segment. -/
lemma list_weight_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight)
    (q s : ℕ) :
    SPFactora.listEval (n := n) q (R.weightFactors s) =
      (H s).collectedWeightProduct (n := n) (R.eval q s) := by
  rw [weightFactors]
  simp only [eval, BCWta.collectedWeightProduct,
    BCWta.collected_lower_centralterm,
    BCWt.evalin_freelower_centtrunterm]
  induction (Finset.univ.sort fun i i' : (H s).index => i ≤ i') with
  | nil =>
      simp
  | cons i indices ih =>
      simp only [List.flatMap_cons, List.map_cons, List.prod_cons,
        SPFactora.listEval_append]
      rw [BCExp.list_power_factors, ih]
      rfl

/-- Normalized repeated-power factors through ordinary Hall weight `k`. -/
def prefixFactors
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight)
    (k : ℕ) :
    List (SPFactora H inputWeight) :=
  (List.range k).flatMap fun s => R.weightFactors (s + 1)

/-- Prefix normalized power factors evaluate to the collected Hall prefix. -/
lemma eval_prefix_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight)
    (q k : ℕ) :
    SPFactora.listEval (n := n) q (R.prefixFactors k) =
      collectedPrefixProduct (n := n) H (R.eval q) k := by
  induction k with
  | zero =>
      simp [prefixFactors, collectedPrefixProduct,
        SPFactora.listEval]
  | succ k ih =>
      rw [prefixFactors, List.range_succ, List.flatMap_append,
        List.flatMap_singleton, SPFactora.listEval_append,
        collected_prefix_succ]
      change
        SPFactora.listEval q (R.prefixFactors k) *
            SPFactora.listEval q (R.weightFactors (k + 1)) =
          collectedPrefixProduct H (R.eval q) k *
            (H (k + 1)).collectedWeightProduct (R.eval q (k + 1))
      rw [ih, R.list_weight_factors]

/-- Full normalized repeated-power endpoint represented by the expansions. -/
def factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight) :
    List (SPFactora H inputWeight) :=
  R.prefixFactors (n - 1)

/-- Full normalized endpoint factors evaluate to their collected Hall product. -/
lemma listEval_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q (R.factors (n := n)) =
      collectedHallProduct (n := n) H (R.eval q) := by
  simp [factors, collectedHallProduct, R.eval_prefix_factors]

/-- Every normalized endpoint factor in one layer has exactly that layer weight. -/
lemma word_weight_factors
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight)
    {s : ℕ}
    {x : SPFactora H inputWeight}
    (hx : x ∈ R.weightFactors s) :
    x.word.weight PEAddres.weight = s := by
  rcases List.mem_flatMap.mp hx with ⟨i, _hi, hx⟩
  rw [BCExp.symbolic_power_factors
    (.atom (⟨s, i⟩ : HEAddres H)) (R.expansion s i) hx]
  rfl

/-- Prefix endpoint factors have weight bounded by the prefix length. -/
lemma word_prefix_factors
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight)
    {k : ℕ}
    {x : SPFactora H inputWeight}
    (hx : x ∈ R.prefixFactors k) :
    x.word.weight PEAddres.weight ≤ k := by
  rcases List.mem_flatMap.mp hx with ⟨s, hs, hx⟩
  rw [R.word_weight_factors hx]
  exact List.mem_range.mp hs

/-- Canonical normalized power endpoints are physically below the quotient cutoff. -/
lemma isTruncated_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (R : CCExpans H inputWeight) :
    SPFactora.IsTruncated n (R.factors (n := n)) := by
  intro x hx
  have hweight := R.word_prefix_factors hx
  have hpos := x.word_weight_pos
  omega

end CCExpans

/--
A correctly sourced truncated symbolic repeated-power collection run
constructs explicit coordinate expansion data for Claim 5.
-/
theorem expansion_truncated_rewrites
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (source : List (SPFactora H inputWeight))
    (R : CCExpans H inputWeight)
    (hsource :
      ∀ q : ℕ,
        SPFactora.listEval (n := n) q source =
          collectedHallProduct (n := n) H e ^ q)
    (hrewrites :
      TSRwa (n := n)
        source (R.factors (n := n))) :
    CEData (n := n) H e inputWeight := by
  intro _heBelow
  refine ⟨R.eval, ?_, ?_⟩
  · intro q
    exact (R.listEval_factors q).symm.trans
      ((hrewrites.listEval_eq q).trans (hsource q))
  · intro s _hs _hsn i
    exact ⟨R.expansion s i, rfl⟩

/--
The same truncated symbolic collection run constructs the polynomial data
consumed directly by Claim 5.
-/
theorem data_truncated_rewrites
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (hinputWeight : 1 ≤ inputWeight)
    (source : List (SPFactora H inputWeight))
    (R : CCExpans H inputWeight)
    (hsource :
      ∀ q : ℕ,
        SPFactora.listEval (n := n) q source =
          collectedHallProduct (n := n) H e ^ q)
    (hrewrites :
      TSRwa (n := n)
        source (R.factors (n := n))) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  CEData.toPolynomialData hinputWeight
    (expansion_truncated_rewrites
      source R hsource hrewrites)

/--
The exact cutoff-specific output required from a symbolic repeated-block Hall
collector.  Its source identity is explicit: a coordinatewise-scaled atomic
list is not silently identified with a power of a noncommutative Hall block.
-/
structure TCRun
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (e : HEFam H) where
  source :
    List (SPFactora H inputWeight)
  coordinates :
    CCExpans H inputWeight
  source_isTruncated :
    SPFactora.IsTruncated n source
  list_eval_source :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q source =
        collectedHallProduct (n := n) H e ^ q
  rewrites :
    TSRwa (n := n)
      source (coordinates.factors (n := n))

namespace TCRun

/-- The normalized endpoint is truncated as a consequence of the rewrite run. -/
lemma coordinates_truncated_rewrites
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (run : TCRun (n := n)
      (inputWeight := inputWeight) H e) :
    SPFactora.IsTruncated n
      (run.coordinates.factors (n := n)) :=
  run.rewrites.isTruncated run.source_isTruncated

/-- A symbolic repeated-block Hall collection run supplies explicit Claim 5 data. -/
lemma coordinateExpansionData
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (run : TCRun (n := n)
      (inputWeight := inputWeight) H e) :
    CEData (n := n) H e inputWeight :=
  expansion_truncated_rewrites
    run.source run.coordinates run.list_eval_source run.rewrites

/-- A symbolic repeated-block Hall collection run supplies Claim 5 polynomial data. -/
lemma coordinatePolynomialData
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (run : TCRun (n := n)
      (inputWeight := inputWeight) H e)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  data_truncated_rewrites
    hinputWeight run.source run.coordinates run.list_eval_source run.rewrites

end TCRun

end TCTex
end Submission
