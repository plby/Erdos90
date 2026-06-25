import Towers.Group.Zassenhaus.CtexInputBridges
import Towers.Group.Zassenhaus.PowerScheduleAdapter

/-!
# Occurrence-schedule bridge for retained Ctex inputs

The retained-recipe collection bound consumes the semantic product law
`SatisfiesRecipeCoefficient`.  The product/inverse
collection development also has an occurrence-aware schedule formulation
`COSched`, and proves that such a schedule implies the semantic
law.  This file packages that implication at the same boundary as the public
free-truncation collection theorem.
-/

namespace Towers
namespace TCTex

universe u


open PTOcc

/--
Retained-recipe collection inputs with the retained law supplied in its
occurrence-schedule form.  The remaining fields are exactly those of
`RCInputs`.
-/
structure OCInputs (d n : ℕ) where
  schedule : COSched.{u} d n
  lowWeightSource :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ),
      1 ≤ inputWeight →
        ¬n ≤ 3 * inputWeight →
          TSInput
            (n := n) (inputWeight := inputWeight)
              (concreteCommutatorsWeight.{u} d) e
  lowWeightSupported :
    ∀ (e :
        HEFam
          (concreteCommutatorsWeight.{u} d))
      (inputWeight : ℕ)
      (hinputWeight : 1 ≤ inputWeight)
      (hbelowClassTwoRange : ¬n ≤ 3 * inputWeight),
        SPFactora.WordWeightLeast inputWeight
          (lowWeightSource e inputWeight hinputWeight
            hbelowClassTwoRange).source
  powerBuilders :
    ∀ inputWeight : ℕ,
      1 ≤ inputWeight →
        TCBuildb.{u}
          (d := d) (n := n) (inputWeight := inputWeight)
  signedBuilder :
    TBBuild.{u} (d := d) (n := n)

/-- Forget the occurrence-level retained schedule to the semantic retained
recipe law consumed by the existing Ctex endpoint. -/
noncomputable def OCInputs.retained_recipe_collectinputs
    {d n : ℕ}
    (I : OCInputs.{u} d n) :
    _root_.Towers.Ctex.RCInputs.{u} d n where
  retainedRecipeLaw :=
    I.schedule.satisfiesRecipeCoefficient
  lowWeightSource := I.lowWeightSource
  lowWeightSupported := I.lowWeightSupported
  powerBuilders := I.powerBuilders
  signedBuilder := I.signedBuilder

/--
Occurrence-schedule retained inputs imply the target free lower-central
truncation collection bound.
-/
theorem free_occurrence_inputs
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : OCInputs.{u} d n) :
    ∃ k : ℕ, TruncationCollectionBound.{u} p d n k :=
  free_collection_inputs
    (p := p) (d := d) (n := n) hn
    I.retained_recipe_collectinputs

theorem collection_occurrence_inputs
    (p d n : ℕ) [Fact p.Prime]
    (hn : 2 ≤ n)
    (I : OCInputs.{u} d n) :
    Nonempty (PGColl.{u} p d n) :=
  collection_recipe_inputs
    (p := p) (d := d) (n := n) hn
    I.retained_recipe_collectinputs

end TCTex
end Towers
