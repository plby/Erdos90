import Submission.Group.Zassenhaus.Constructors
import Submission.Group.Zassenhaus.RewriteContexts

/-!
# Coordinate-endpoint insertion scheduling for symbolic Hall powers

A universal repeated-power collector may be assembled incrementally.  Once a
prefix has been recollected into normalized coordinate expansions, the only
remaining scheduler obligation is to insert one additional truncated symbolic
factor into that endpoint.

This file packages that one-factor obligation and proves that it folds over
every finite truncated source list.  Combined with a source-evaluation theorem,
the resulting normalization constructs the Claim 5 polynomial data.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace CCExpans

/-- The normalized coordinate endpoint with no factors. -/
def empty
    {d : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (inputWeight : ℕ) :
    CCExpans H inputWeight where
  expansion s _ := BCExp.zero inputWeight s

@[simp]
lemma weightFactors_empty
    {d inputWeight s : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    (empty H inputWeight).weightFactors s = [] := by
  rw [weightFactors]
  apply List.flatMap_eq_nil_iff.2
  intro i _hi
  rfl

@[simp]
lemma prefixFactors_empty
    {d inputWeight k : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    (empty H inputWeight).prefixFactors k = [] := by
  simp [prefixFactors]

@[simp]
lemma factors_empty
    {d n inputWeight : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r) :
    (empty H inputWeight).factors (n := n) = [] := by
  simp [factors]

end CCExpans

/--
The remaining local scheduling obligation for a universal symbolic power
collector: insert one physically truncated factor into any normalized
coordinate endpoint and recollect the result into another such endpoint.
-/
structure TSInserte
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) : Prop where
  insert :
    ∀ (coordinates : CCExpans H inputWeight)
      (factor : SPFactora H inputWeight),
      factor.word.weight PEAddres.weight < n →
        ∃ next : CCExpans H inputWeight,
          TSRwa (n := n)
            (coordinates.factors (n := n) ++ [factor])
            (next.factors (n := n))

namespace TSInserte

/--
Repeated endpoint insertion recollects every finite physically truncated
source list into normalized coordinate expansions.
-/
lemma exists_normalization
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (kernel :
      TSInserte
        (n := n) (inputWeight := inputWeight) H) :
    ∀ source : List (SPFactora H inputWeight),
      SPFactora.IsTruncated n source →
        ∃ coordinates : CCExpans H inputWeight,
          TSRwa (n := n)
            source (coordinates.factors (n := n)) := by
  intro source hsource
  induction source using List.reverseRecOn with
  | nil =>
      refine ⟨CCExpans.empty H inputWeight, ?_⟩
      simpa using
        (Relation.ReflTransGen.refl :
          TSRwa (n := n) [] [])
  | append_singleton initial factor ih =>
      have hinitial : SPFactora.IsTruncated n initial := by
        intro x hx
        exact hsource x (by simp [hx])
      have hfactor :
          factor.word.weight PEAddres.weight < n :=
        hsource factor (by simp)
      rcases ih hinitial with ⟨coordinates, hcoordinates⟩
      rcases kernel.insert coordinates factor hfactor with ⟨next, hnext⟩
      refine ⟨next, ?_⟩
      exact
        (hcoordinates.append
          (Relation.ReflTransGen.refl :
            TSRwa (n := n)
              [factor] [factor])).trans hnext

end TSInserte

/--
A symbolic source list together with the semantic identity identifying its
evaluation with the repeated power of the original collected Hall block.
-/
structure TSInput
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (e : HEFam H) where
  source :
    List (SPFactora H inputWeight)
  source_isTruncated :
    SPFactora.IsTruncated n source
  list_eval_source :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q source =
        collectedHallProduct (n := n) H e ^ q

namespace TSInput

/--
A coordinate insertion kernel upgrades any correctly sourced input to a
complete truncated repeated-power collection run.
-/
lemma exists_collectionRun
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (kernel :
      TSInserte
        (n := n) (inputWeight := inputWeight) H) :
    Nonempty
      (TCRun
        (n := n) (inputWeight := inputWeight) H e) := by
  rcases kernel.exists_normalization input.source input.source_isTruncated with
    ⟨coordinates, hrewrites⟩
  exact ⟨{
    source := input.source
    coordinates := coordinates
    source_isTruncated := input.source_isTruncated
    list_eval_source := input.list_eval_source
    rewrites := hrewrites }⟩

/-- Choose the collection run supplied by a coordinate insertion kernel. -/
noncomputable def toCollectionRun
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (kernel :
      TSInserte
        (n := n) (inputWeight := inputWeight) H) :
    TCRun
      (n := n) (inputWeight := inputWeight) H e :=
  Classical.choice (input.exists_collectionRun kernel)

/--
The insertion-kernel reduction for Claim 5: it remains to construct the local
one-factor coordinate insertion kernel and a correctly sourced input list.
-/
lemma coordinatePolynomialData
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (kernel :
      TSInserte
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  (input.toCollectionRun kernel).coordinatePolynomialData hinputWeight

end TSInput

end TCTex
end Submission
