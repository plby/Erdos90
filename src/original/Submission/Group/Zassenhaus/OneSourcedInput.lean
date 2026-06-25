import Submission.Group.Zassenhaus.ClassThreeCollection
import Submission.Group.Zassenhaus.ClassAutomaticCollection
import Submission.Group.Zassenhaus.ClassTwo

/-!
# Weight-one sourced input through class three

At cutoff at most four, the explicit finite class-three symbolic source
supplies the missing weight-one endpoint for Claim 5.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/-- The explicit finite class-three source for a collected Hall block at initial weight one. -/
noncomputable def collectedSourceFactors
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H) :
    List (SPFactora H 1) :=
  SSAtom.classThreeFactors
    (collectedHallAtoms (n := n) (inputWeight := 1)
      (HEFam.zeroBelow e 1))

/-- The explicit weight-one class-three source evaluates to the powered collected Hall block. -/
lemma collected_source_factors
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hn4 : n ≤ 4)
    (e : HEFam H)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (collectedSourceFactors (n := n) e) =
      collectedHallProduct (n := n) H e ^ q := by
  let e' : HEFam H :=
    HEFam.zeroBelow e 1
  have he'Below :
      ∀ s : ℕ, s < 1 → e' s = 0 := by
    intro s hs
    simp [e', hs]
  have he'Product :
      collectedHallProduct (n := n) H e' =
        collectedHallProduct (n := n) H e := by
    simpa [e'] using
      (collected_below_self (n := n) (r := 1) e (by
        intro s hs hsOne
        omega))
  rw [collectedSourceFactors,
    SSAtom.list_three_factors hn4,
    list_collected_atoms e' he'Below,
    he'Product]

/-- The physically truncated explicit weight-one class-three source. -/
noncomputable def truncatedCollectedFactors
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H) :
    List (SPFactora H 1) :=
  SPFactora.truncate n
    (collectedSourceFactors (n := n) e)

/-- Truncating the explicit weight-one class-three source preserves its powered-block identity. -/
lemma list_collected_factors
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hn4 : n ≤ 4)
    (e : HEFam H)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (truncatedCollectedFactors (n := n) e) =
      collectedHallProduct (n := n) H e ^ q := by
  rw [truncatedCollectedFactors,
    SPFactora.listEval_truncate,
    collected_source_factors hn4 e]

/-- The retained explicit weight-one source is physically below the truncation cutoff. -/
lemma truncated_collected_factors
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H) :
    SPFactora.IsTruncated n
      (truncatedCollectedFactors (n := n) e) :=
  SPFactora.isTruncated_truncate _

/-- Every retained explicit weight-one source factor has positive ordinary Hall weight. -/
lemma least_collected_factors
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (e : HEFam H) :
    SPFactora.WordWeightLeast 1
      (truncatedCollectedFactors (n := n) e) := by
  intro factor hfactor
  exact factor.word_weight_pos

namespace TSInput

/-- The explicit weight-one class-three source packaged for the automatic recursive collector. -/
noncomputable def classThreeSource
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hn4 : n ≤ 4)
    (e : HEFam H) :
    TSInput
      (n := n) (inputWeight := 1) H e where
  source :=
    truncatedCollectedFactors (n := n) e
  source_isTruncated :=
    truncated_collected_factors e
  list_eval_source :=
    list_collected_factors hn4 e

/-- The explicit weight-one class-three sourced input satisfies the collector support invariant. -/
lemma word_least_source
    {d n : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (hn4 : n ≤ 4)
    (e : HEFam H) :
    SPFactora.WordWeightLeast 1
      ((classThreeSource hn4 e).source) :=
  least_collected_factors e

/-- Claim 5 power-coordinate polynomials at the formerly missing weight-one class-three endpoint. -/
theorem coordinate_data_source
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hn4 : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {e : HEFam H} :
    CollectedPolynomialData (n := n) H e 1 :=
  (classThreeSource hn4 e).dataAutomaticCollection
    hn hn4 H hH (word_least_source hn4 e) (by
      omega)

end TSInput

end TCTex
end Submission
