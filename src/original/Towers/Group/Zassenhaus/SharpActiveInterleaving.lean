import Towers.Group.Zassenhaus.SharpActiveBlock
import Towers.Group.Zassenhaus.SharpHigherReduction

/-!
# Sharp stable interleaving for active symbolic Hall-power blocks

Coordinatewise addition of active Hall blocks is a stable interleave.  This
file builds that interleave from sharp active-block movements while retaining
every emitted correction behind the active output.  It then packages the
interleave as the delegated fixed-weight merge route required by filtration
recursion.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
A route stably interleaving two families of active blocks, with all emitted
corrections retained behind the active output.
-/
structure SemanticInterleaveRoute
    {ι : Type*}
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (indices : List ι)
    (left right : ι → List (SPFactora H inputWeight)) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_least_succ :
    SPFactora.WordWeightLeast
      (lowerWeight + 1) higherSource
  rewrites :
    SCRw
      (n := n) (lowerWeight := lowerWeight)
        (indices.flatMap left ++ indices.flatMap right)
        (indices.flatMap (fun i => left i ++ right i) ++ higherSource)

namespace TSFtrya

/--
Stably interleave two finite families of active blocks.  Each right block
moves left across the remaining left blocks, and its fresh higher residual is
pushed behind the remaining right blocks before recursively interleaving the
tail.
-/
noncomputable def semanticInterleaveRoute
    {ι : Type*}
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H) :
    ∀ (indices : List ι)
      (left right : ι → List (SPFactora H inputWeight)),
      (∀ i ∈ indices,
        SPFactora.WordWeightExactly lowerWeight (left i)) →
      (∀ i ∈ indices,
        SPFactora.WordWeightExactly lowerWeight (right i)) →
        SemanticInterleaveRoute
          (n := n) (lowerWeight := lowerWeight) H indices left right
  | [], _left, _right, _hleft, _hright =>
      { higherSource := []
        higher_least_succ := by
          intro x hx
          simp at hx
        rewrites := by
          simpa using
            (Relation.ReflTransGen.refl :
              SCRw
                (n := n) (lowerWeight := lowerWeight) [] []) }
  | i :: indices, left, right, hleft, hright => by
      have hleftHead :
          SPFactora.WordWeightExactly lowerWeight (left i) :=
        hleft i (by simp)
      have hrightHead :
          SPFactora.WordWeightExactly lowerWeight (right i) :=
        hright i (by simp)
      have hleftTail :
          ∀ j ∈ indices,
            SPFactora.WordWeightExactly lowerWeight (left j) :=
        fun j hj => hleft j (by simp [hj])
      have hrightTail :
          ∀ j ∈ indices,
            SPFactora.WordWeightExactly lowerWeight (right j) :=
        fun j hj => hright j (by simp [hj])
      have hleftFlat :
          SPFactora.WordWeightExactly lowerWeight
            (indices.flatMap left) := by
        intro x hx
        rcases List.mem_flatMap.mp hx with ⟨j, hj, hx⟩
        exact hleftTail j hj x hx
      have hrightFlat :
          SPFactora.WordWeightExactly lowerWeight
            (indices.flatMap right) := by
        intro x hx
        rcases List.mem_flatMap.mp hx with ⟨j, hj, hx⟩
        exact hrightTail j hj x hx
      let move :=
        factory.semanticActiveRoute family
          (indices.flatMap left) hleftFlat (right i) hrightHead
      let push :=
        factory.semanticHigherRoute family
          move.higherSource move.higher_least_succ
            (indices.flatMap right) hrightFlat
      let tail :=
        factory.semanticInterleaveRoute
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
          SCRw
            (n := n) (lowerWeight := lowerWeight)
              (left i ++ indices.flatMap left ++ right i ++
                indices.flatMap right)
              (left i ++ right i ++ indices.flatMap left ++
                move.higherSource ++ indices.flatMap right) := by
        simpa [List.append_assoc] using
          move.rewrites.context (left i) (indices.flatMap right)
      have hpush :
          SCRw
            (n := n) (lowerWeight := lowerWeight)
              (left i ++ right i ++ indices.flatMap left ++
                move.higherSource ++ indices.flatMap right)
              (left i ++ right i ++ indices.flatMap left ++
                indices.flatMap right ++ push.higherSource) := by
        simpa [List.append_assoc] using
          push.rewrites.context (left i ++ right i ++ indices.flatMap left) []
      have htail :
          SCRw
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

end TSFtrya

namespace CCExpans

/-- Every factor in one normalized Hall layer has exactly its layer weight. -/
lemma word_exactly_factors
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (coordinates : CCExpans H inputWeight)
    (weight : ℕ) :
    SPFactora.WordWeightExactly weight
      (coordinates.weightFactors weight) :=
  fun _x hx => coordinates.word_weight_factors hx

end CCExpans

namespace TSFtrya

/--
The sharp stable interleaver supplies the delegated fixed-weight merge route
for a coordinate block and the Hall-normal coordinate expansion of one active
factor.
-/
noncomputable def supportedDelegatedMerge
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
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight) :
    DMRoute
      (lowerWeight := lowerWeight) hn H hH coordinates factor := by
  let X := factor.normalCoordinateExpansions hn H hH
  let indices := Finset.univ.sort fun i i' : (H lowerWeight).index => i ≤ i'
  let left := fun i =>
    (coordinates.expansion lowerWeight i).symbolicPowerFactors
      (.atom (⟨lowerWeight, i⟩ : HEAddres H))
  let right := fun i =>
    (X.expansion lowerWeight i).symbolicPowerFactors
      (.atom (⟨lowerWeight, i⟩ : HEAddres H))
  let route :=
    factory.semanticInterleaveRoute family indices
      left right
      (fun i _hi x hx => by
        rw [BCExp.symbolic_power_factors
          (.atom (⟨lowerWeight, i⟩ : HEAddres H))
          (coordinates.expansion lowerWeight i) hx]
        rfl)
      (fun i _hi x hx => by
        rw [BCExp.symbolic_power_factors
          (.atom (⟨lowerWeight, i⟩ : HEAddres H))
          (X.expansion lowerWeight i) hx]
        rfl)
  refine
    { higherSource := route.higherSource
      higher_least_succ :=
        route.higher_least_succ
      rewrites := ?_ }
  change
    SCRw
      (n := n) (lowerWeight := lowerWeight)
        (indices.flatMap left ++ indices.flatMap right)
        ((coordinates.activeBlockUpdate hn H hH factor).weightFactors
          lowerWeight ++ route.higherSource)
  have htarget :
      indices.flatMap (fun i => left i ++ right i) =
        (coordinates.activeBlockUpdate hn H hH factor).weightFactors
          lowerWeight := by
    unfold CCExpans.weightFactors
    dsimp [CCExpans.activeBlockUpdate,
      CCExpans.add, X, indices, left, right]
    induction (Finset.univ.sort fun i i' : (H lowerWeight).index => i ≤ i') with
    | nil => rfl
    | cons i indices ih =>
        simp only [List.flatMap_cons]
        have hhead :
            ((coordinates.expansion lowerWeight i).add
                ((factor.normalCoordinateExpansions hn H hH).expansion
                  lowerWeight i)).symbolicPowerFactors
                  (.atom (⟨lowerWeight, i⟩ : HEAddres H)) =
              (coordinates.expansion lowerWeight i).symbolicPowerFactors
                  (.atom (⟨lowerWeight, i⟩ : HEAddres H)) ++
                ((factor.normalCoordinateExpansions hn H hH).expansion
                  lowerWeight i).symbolicPowerFactors
                    (.atom (⟨lowerWeight, i⟩ : HEAddres H)) :=
          BCExp.symbolic_factors_add _ _ _
        rw [hhead, ih, List.append_assoc]
  rw [← htarget]
  exact route.rewrites

end TSFtrya

end TCTex
end Towers
