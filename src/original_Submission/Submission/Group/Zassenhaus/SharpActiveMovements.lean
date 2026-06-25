import Submission.Group.Zassenhaus.SharpHigherRouting

/-!
# Sharp semantic movements for active symbolic Hall-power blocks

The nonterminal fixed-weight merge collector needs a local operation stronger
than a normalized adjacent obstruction.  After swapping two active factors,
its normalized correction block lies before the swapped pair.  The active pair
must immediately be routed left across that heavier block so the correction
residual remains behind the active layer.

This file packages that movement.  It first folds the sharp higher-tail router
across a finite active block, then uses that fold to turn one normalized active
swap into an active pair followed by a strictly heavier residual.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace SPFactora

/-- Every factor in a list has exactly the selected ordinary Hall weight. -/
def WordWeightExactly
    {d inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (weight : ℕ)
    (L : List (SPFactora H inputWeight)) :
    Prop :=
  ∀ x ∈ L, x.word.weight PEAddres.weight = weight

end SPFactora

/--
A route moving a finite active block left across an already-heavier residual
list.
-/
structure ActiveHigherRoute
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (higher active : List (SPFactora H inputWeight)) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_least_succ :
    SPFactora.WordWeightLeast
      (lowerWeight + 1) higherSource
  rewrites :
    SCRw
      (n := n) (lowerWeight := lowerWeight)
        (higher ++ active) (active ++ higherSource)

namespace TSFtrya

/--
Fold the sharp higher-tail router across a finite active block.  The active
block keeps its order and every emitted correction remains behind it.
-/
noncomputable def semanticHigherRoute
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H)
    (higher : List (SPFactora H inputWeight))
    (hhigher :
      SPFactora.WordWeightLeast
        (lowerWeight + 1) higher) :
    ∀ (active : List (SPFactora H inputWeight)),
      SPFactora.WordWeightExactly lowerWeight active →
        ActiveHigherRoute
          (n := n) (lowerWeight := lowerWeight) H higher active
  | [], _ =>
      { higherSource := higher
        higher_least_succ := hhigher
        rewrites := by
          simpa using
            (Relation.ReflTransGen.refl :
              SCRw
                (n := n) (lowerWeight := lowerWeight) higher higher) }
  | A :: active, hactive => by
      have hA :
          A.word.weight PEAddres.weight = lowerWeight :=
        hactive A (by simp)
      have htail :
          SPFactora.WordWeightExactly lowerWeight active :=
        fun x hx => hactive x (by simp [hx])
      let headRoute :=
        factory.supportedListRoute family A hA higher hhigher
      let tailRoute :=
        factory.semanticHigherRoute family
          headRoute.higherSource
            headRoute.higher_least_succ active htail
      refine
        { higherSource := tailRoute.higherSource
          higher_least_succ :=
            tailRoute.higher_least_succ
          rewrites := ?_ }
      have hhead :
          SCRw
            (n := n) (lowerWeight := lowerWeight)
              (higher ++ A :: active)
              (([A] ++ headRoute.higherSource) ++ active) := by
        simpa [List.append_assoc] using
          headRoute.inserts.rewrites.context [] active
      have htailRoute :
          SCRw
            (n := n) (lowerWeight := lowerWeight)
              (([A] ++ headRoute.higherSource) ++ active)
              ((A :: active) ++ tailRoute.higherSource) := by
        simpa [List.append_assoc] using tailRoute.rewrites.context [A] []
      exact hhead.trans htailRoute

end TSFtrya

/--
One equal-weight active swap with every normalized correction moved behind the
swapped active pair.
-/
structure SemanticSwapRoute
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (B A : SPFactora H inputWeight) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_least_succ :
    SPFactora.WordWeightLeast
      (lowerWeight + 1) higherSource
  rewrites :
    SCRw
      (n := n) (lowerWeight := lowerWeight)
        [B, A] ([A, B] ++ higherSource)

namespace TSFtrya

/--
Normalize the correction packet of one active swap sharply, then route the
swapped active pair left across that correction block.
-/
noncomputable def semanticSwapRoute
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H)
    (B A : SPFactora H inputWeight)
    (hB :
      B.word.weight PEAddres.weight = lowerWeight)
    (hA :
      A.word.weight PEAddres.weight = lowerWeight) :
    SemanticSwapRoute
      (n := n) (lowerWeight := lowerWeight) H B A := by
  have hBSupported :
      lowerWeight ≤ B.word.weight PEAddres.weight := by
    omega
  have hASupported :
      lowerWeight ≤ A.word.weight PEAddres.weight := by
    omega
  let C := factory.packet B A hBSupported hASupported
  let normalization :=
    family.semantic_left_sharp C hBSupported
  let route :=
    factory.semanticHigherRoute family
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
      SCRw
        (n := n) (lowerWeight := lowerWeight)
          [B, A]
          (normalization.coordinates.factors (n := n) ++ [A, B]) := by
    apply SCRw.single
    simpa using
      (SSStep.obstruction
        (n := n) (lowerWeight := lowerWeight) [] [] B A C normalization)
  exact hswap.trans route.rewrites

end TSFtrya

end TCTex
end Submission
