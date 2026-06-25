import Submission.Group.Zassenhaus.SharpActiveMovements

/-!
# Sharp routing between active symbolic Hall-power blocks

One normalized active swap can be composed into larger finite movements.  A
single active factor moves left across an active block by swapping across the
final parent, recursively crossing the remaining prefix, and moving the final
parent left across the newly emitted higher residual.  Folding that operation
across a second active block swaps two active blocks while retaining every
correction behind the active output.

These are the finite movements needed by the stable interleaver for
coordinatewise active-block addition.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
A route moving one active factor left across an active block, with every
emitted correction retained behind the active output.
-/
structure SemanticActiveRoute
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (left : List (SPFactora H inputWeight))
    (factor : SPFactora H inputWeight) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_least_succ :
    SPFactora.WordWeightLeast
      (lowerWeight + 1) higherSource
  rewrites :
    SCRw
      (n := n) (lowerWeight := lowerWeight)
        (left ++ [factor]) ([factor] ++ left ++ higherSource)

namespace TSFtrya

/--
Move one active factor left across an active block by recursively composing
sharp active swaps.
-/
noncomputable def supportedBlockRoute
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H)
    (factor : SPFactora H inputWeight)
    (hfactor :
      factor.word.weight PEAddres.weight = lowerWeight)
    (left : List (SPFactora H inputWeight))
    (hleft :
      SPFactora.WordWeightExactly lowerWeight left) :
    SemanticActiveRoute
      (n := n) (lowerWeight := lowerWeight) H left factor :=
  List.reverseRecOn
    (motive := fun left =>
      SPFactora.WordWeightExactly lowerWeight left →
        SemanticActiveRoute
          (n := n) (lowerWeight := lowerWeight) H left factor)
    left
    (fun _ =>
      { higherSource := []
        higher_least_succ := by
          intro x hx
          simp at hx
        rewrites := by
          simpa using
            (Relation.ReflTransGen.refl :
              SCRw
                (n := n) (lowerWeight := lowerWeight) [factor] [factor]) })
    (fun P B routeP hPB => by
      have hP :
          SPFactora.WordWeightExactly lowerWeight P :=
        fun x hx => hPB x (by simp [hx])
      have hB :
          B.word.weight PEAddres.weight = lowerWeight :=
        hPB B (by simp)
      let swapRoute :=
        factory.semanticSwapRoute family B factor hB
          hfactor
      let prefixRoute := routeP hP
      let parentRoute :=
        factory.semanticHigherRoute family
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
          SCRw
            (n := n) (lowerWeight := lowerWeight)
              ((P ++ [B]) ++ [factor])
              (P ++ [factor, B] ++ swapRoute.higherSource) := by
        simpa [List.append_assoc] using
          swapRoute.rewrites.context P []
      have hprefix :
          SCRw
            (n := n) (lowerWeight := lowerWeight)
              (P ++ [factor, B] ++ swapRoute.higherSource)
              (([factor] ++ P ++ prefixRoute.higherSource) ++ [B] ++
                swapRoute.higherSource) := by
        simpa [List.append_assoc] using
          prefixRoute.rewrites.context [] ([B] ++ swapRoute.higherSource)
      have hparent :
          SCRw
            (n := n) (lowerWeight := lowerWeight)
              (([factor] ++ P ++ prefixRoute.higherSource) ++ [B] ++
                swapRoute.higherSource)
              ([factor] ++ (P ++ [B]) ++
                (parentRoute.higherSource ++ swapRoute.higherSource)) := by
        simpa [List.append_assoc] using
          parentRoute.rewrites.context ([factor] ++ P) swapRoute.higherSource
      exact hswap.trans (hprefix.trans hparent))
    hleft

end TSFtrya

/--
A route moving one active block left across another active block, with all
corrections retained behind the active output.
-/
structure SupportedActiveRoute
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (left right : List (SPFactora H inputWeight)) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_least_succ :
    SPFactora.WordWeightLeast
      (lowerWeight + 1) higherSource
  rewrites :
    SCRw
      (n := n) (lowerWeight := lowerWeight)
        (left ++ right) (right ++ left ++ higherSource)

namespace TSFtrya

/--
Fold single-factor active routing across a second active block.
-/
noncomputable def semanticActiveRoute
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H)
    (left : List (SPFactora H inputWeight))
    (hleft :
      SPFactora.WordWeightExactly lowerWeight left) :
    ∀ (right : List (SPFactora H inputWeight)),
      SPFactora.WordWeightExactly lowerWeight right →
        SupportedActiveRoute
          (n := n) (lowerWeight := lowerWeight) H left right
  | [], _ =>
      { higherSource := []
        higher_least_succ := by
          intro x hx
          simp at hx
        rewrites := by
          simpa using
            (Relation.ReflTransGen.refl :
              SCRw
                (n := n) (lowerWeight := lowerWeight) left left) }
  | A :: right, hright => by
      have hA :
          A.word.weight PEAddres.weight = lowerWeight :=
        hright A (by simp)
      have htail :
          SPFactora.WordWeightExactly lowerWeight right :=
        fun x hx => hright x (by simp [hx])
      let headRoute :=
        factory.supportedBlockRoute family A hA
          left hleft
      let tailAcrossHigher :=
        factory.semanticHigherRoute family
          headRoute.higherSource
            headRoute.higher_least_succ right htail
      let tailRoute :=
        factory.semanticActiveRoute family left
          hleft right htail
      refine
        { higherSource := tailRoute.higherSource ++ tailAcrossHigher.higherSource
          higher_least_succ := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact tailRoute.higher_least_succ x hx
            · exact tailAcrossHigher.higher_least_succ x hx
          rewrites := ?_ }
      have hhead :
          SCRw
            (n := n) (lowerWeight := lowerWeight)
              (left ++ A :: right)
              (([A] ++ left ++ headRoute.higherSource) ++ right) := by
        simpa [List.append_assoc] using headRoute.rewrites.context [] right
      have hhigher :
          SCRw
            (n := n) (lowerWeight := lowerWeight)
              (([A] ++ left ++ headRoute.higherSource) ++ right)
              ([A] ++ (left ++ right) ++
                tailAcrossHigher.higherSource) := by
        simpa [List.append_assoc] using
          tailAcrossHigher.rewrites.context ([A] ++ left) []
      have htailRoute :
          SCRw
            (n := n) (lowerWeight := lowerWeight)
              ([A] ++ (left ++ right) ++ tailAcrossHigher.higherSource)
              ((A :: right) ++ left ++
                (tailRoute.higherSource ++
                  tailAcrossHigher.higherSource)) := by
        simpa [List.append_assoc] using
          tailRoute.rewrites.context [A] tailAcrossHigher.higherSource
      exact hhead.trans (hhigher.trans htailRoute)

end TSFtrya

end TCTex
end Submission
