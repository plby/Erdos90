import Submission.Group.Zassenhaus.SharpHigherRouting
import Submission.Group.Zassenhaus.SharpActiveInterleaving
import Submission.Group.Zassenhaus.FactorSourceReduction
import Submission.Group.Zassenhaus.FormulaChooseSubstitution
import Submission.Group.Zassenhaus.Active
import Submission.Group.Zassenhaus.UniversalCorrectionFactories
import Submission.Group.Zassenhaus.BlockFormulaSubstitution
import Submission.Group.Zassenhaus.ErasedWordSkeleton
import Submission.Group.Zassenhaus.SignedProfilePackets
import Submission.Group.Zassenhaus.InverseUniversalBlock

-- Merged from RestrictedSharpHigherTailRouting.lean

/-!
# Higher-tail routing from strictly deeper symbolic Hall-power normalizers

The first sharp Hall-power router consumed a semantic normalizer family indexed
by all support bounds.  That interface is stronger than the recursion needs.
While collecting at `lowerWeight`, every crossed higher-tail parent has weight
strictly above `lowerWeight`, so its sharply normalized correction packet only
uses a normalizer at a strictly deeper support bound.

This file records that narrower local interface and reconstructs the
terminating higher-tail route from it.  The restricted interface is suitable
for a well-founded recursive global collector.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
A local parent-sharp correction normalizer at one ambient stratum.  Its output
is exposed at the ambient support bound, but its descent witness records that
it was normalized sharply above the crossed parent's true weight.
-/
structure SSNormal
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) where
  normalize :
    ∀ {B A : SPFactora H inputWeight}
      (C : TCPkt n B A),
      lowerWeight ≤ B.word.weight PEAddres.weight →
        TSNorma
          lowerWeight C
  normalize_defect_multiset :
    ∀ {B A : SPFactora H inputWeight}
      (C : TCPkt n B A)
      (hB : lowerWeight ≤ B.word.weight PEAddres.weight)
      (P : List (SPFactora H inputWeight)),
      SPFactora.CutoffDefectMultiset n
        (P ++ (normalize C hB).coordinates.factors (n := n))
        (P ++ [B])

namespace SSNormal

open TSNorma

/--
Strictly deeper semantic normalizers construct the local parent-sharp
normalizer required at one ambient stratum.
-/
noncomputable def ofNormalizerAbove
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        lowerWeight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight) H) :
    SSNormal
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H where
  normalize := by
    intro B A C hB
    exact
      (C.normalization_left_weight
        (normalizerAbove
          (B.word.weight PEAddres.weight + 1) (by omega))).weaken hB
  normalize_defect_multiset := by
    intro B A C hB P
    simpa [TSNorma.weaken] using
      multisetAppendSingleton
        (C.normalization_left_weight
          (normalizerAbove
            (B.word.weight PEAddres.weight + 1) (by omega)))
        P

end SSNormal

namespace TSFtrya

/--
The cutoff-defect multiset recursion only needs a local sharp correction
normalizer, not a completed all-strata family.
-/
lemma nonempty_supported_normalizer
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (pending : List (SPFactora H inputWeight))
    (hpending :
      SPFactora.WordWeightLeast
        (lowerWeight + 1) pending) :
    Nonempty
      (SSHigher
        (n := n) (lowerWeight := lowerWeight) H pending factor) := by
  refine
    (SPFactora.well_founded_defect
      (n := n) (H := H) (inputWeight := inputWeight)).induction
      (C := fun pending =>
        SPFactora.WordWeightLeast
            (lowerWeight + 1) pending →
          Nonempty
            (SSHigher
              (n := n) (lowerWeight := lowerWeight) H pending factor))
      pending ?_ hpending
  intro pending ih hpending
  rcases pending.eq_nil_or_concat with rfl | ⟨P, B, rfl⟩
  · exact ⟨{
      higherSource := []
      higher_least_succ := by
        intro x hx
        simp at hx
      inserts := by
        simpa using
          (SSInsertc.nil
            (n := n) (lowerWeight := lowerWeight) factor)
    }⟩
  · have hP :
        SPFactora.WordWeightLeast (lowerWeight + 1) P :=
      fun x hx => hpending x (by simp [List.concat_eq_append, hx])
    have hBsucc :
        lowerWeight + 1 ≤ B.word.weight PEAddres.weight :=
      hpending B (by simp)
    have hB :
        lowerWeight ≤ B.word.weight PEAddres.weight :=
      (Nat.le_succ lowerWeight).trans hBsucc
    have hfactor :
        lowerWeight ≤ factor.word.weight PEAddres.weight := by
      omega
    let C := factory.packet B factor hB hfactor
    let normalization := sharp.normalize C hB
    have hnormalization :
        SPFactora.WordWeightLeast (lowerWeight + 1)
          (normalization.coordinates.factors (n := n)) :=
      normalization.weight_least_succ
    have hnextPending :
        SPFactora.WordWeightLeast (lowerWeight + 1)
          (P ++ normalization.coordinates.factors (n := n)) := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hP x hx
      · exact hnormalization x hx
    have hdescends :
        SPFactora.CutoffDefectMultiset n
          (P ++ normalization.coordinates.factors (n := n)) (P ++ [B]) := by
      dsimp [normalization]
      exact sharp.normalize_defect_multiset C hB P
    rcases ih _ (by simpa [List.concat_eq_append] using hdescends)
        hnextPending with
      ⟨route⟩
    exact ⟨{
      higherSource := route.higherSource ++ [B]
      higher_least_succ := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact route.higher_least_succ x hx
        · rcases List.mem_singleton.mp hx with rfl
          exact hBsucc
      inserts := by
        simpa [List.append_assoc] using
          (SSInsertc.obstruction
            (n := n) (lowerWeight := lowerWeight)
            P B factor C normalization
              (SBInsert.append_self
                (n := n) (lowerWeight := lowerWeight) P
                  (normalization.coordinates.factors (n := n)))
              route.inserts)
    }⟩

/-- Choose the restricted sharp route through a strictly higher pending list. -/
noncomputable def semantic_higher_normalizer
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (pending : List (SPFactora H inputWeight))
    (hpending :
      SPFactora.WordWeightLeast
        (lowerWeight + 1) pending) :
    SSHigher
      (n := n) (lowerWeight := lowerWeight) H pending factor :=
  Classical.choice
    (factory.nonempty_supported_normalizer
      sharp factor hfactorWeight pending hpending)

/-- Move an active factor through an endpoint tail using only deeper normalizers. -/
noncomputable def supported_route_sharp
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight) :
    STRoute
      (n := n) (lowerWeight := lowerWeight) H coordinates factor := by
  let route :=
    factory.semantic_higher_normalizer
      sharp factor hfactorWeight
        (coordinates.tailFactors (n := n) lowerWeight)
          coordinates.word_least_factors
  exact
    { higherSource := route.higherSource
      higher_least_succ :=
        route.higher_least_succ
      inserts := route.inserts }

end TSFtrya

end TCTex
end Submission

-- Merged from RestrictedSharpActiveBlockRouting.lean

/-!
# Active-block routing from strictly deeper symbolic Hall-power normalizers

This file reconstructs sharp Hall-power active-block movement and stable
fixed-weight interleaving from the local parent-sharp correction normalizer.
Unlike the earlier all-strata-family constructors, these routes only consume
normalizers strictly above the active stratum.  They are therefore suitable
for direct well-founded recursion on the remaining nilpotent cutoff depth.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace TSFtrya

/-- Fold restricted sharp higher-tail routing across an active block. -/
noncomputable def semantic_sharp_normalizer
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
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
        factory.semantic_higher_normalizer
          sharp A hA higher hhigher
      let tailRoute :=
        factory.semantic_sharp_normalizer
          sharp headRoute.higherSource
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

/-- One active swap with all restricted sharp corrections moved behind it. -/
noncomputable def supported_swap_normalizer
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (B A : SPFactora H inputWeight)
    (hB : B.word.weight PEAddres.weight = lowerWeight)
    (hA : A.word.weight PEAddres.weight = lowerWeight) :
    SemanticSwapRoute
      (n := n) (lowerWeight := lowerWeight) H B A := by
  have hBSupported :
      lowerWeight ≤ B.word.weight PEAddres.weight := by
    omega
  have hASupported :
      lowerWeight ≤ A.word.weight PEAddres.weight := by
    omega
  let C := factory.packet B A hBSupported hASupported
  let normalization := sharp.normalize C hBSupported
  let route :=
    factory.semantic_sharp_normalizer
      sharp (normalization.coordinates.factors (n := n))
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

/-- Move one active factor across an active block using restricted sharp swaps. -/
noncomputable def route_sharp_normalizer
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (factor : SPFactora H inputWeight)
    (hfactor : factor.word.weight PEAddres.weight = lowerWeight)
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
        factory.supported_swap_normalizer
          sharp B factor hB hfactor
      let prefixRoute := routeP hP
      let parentRoute :=
        factory.semantic_sharp_normalizer
          sharp prefixRoute.higherSource
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

/-- Move one active block across another using restricted sharp routing. -/
noncomputable def supported_semantic_normalizer
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
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
        factory.route_sharp_normalizer
          sharp A hA left hleft
      let tailAcrossHigher :=
        factory.semantic_sharp_normalizer
          sharp headRoute.higherSource
            headRoute.higher_least_succ right htail
      let tailRoute :=
        factory.supported_semantic_normalizer
          sharp left hleft right htail
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
              ([A] ++ (left ++ right) ++ tailAcrossHigher.higherSource) := by
        simpa [List.append_assoc] using
          tailAcrossHigher.rewrites.context ([A] ++ left) []
      have htailRoute :
          SCRw
            (n := n) (lowerWeight := lowerWeight)
              ([A] ++ (left ++ right) ++ tailAcrossHigher.higherSource)
              ((A :: right) ++ left ++
                (tailRoute.higherSource ++ tailAcrossHigher.higherSource)) := by
        simpa [List.append_assoc] using
          tailRoute.rewrites.context [A] tailAcrossHigher.higherSource
      exact hhead.trans (hhigher.trans htailRoute)

/-- Stable fixed-weight interleaving from restricted sharp routing. -/
noncomputable def interleave_sharp_normalizer
    {ι : Type*}
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (sharp :
      SSNormal
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H) :
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
        factory.supported_semantic_normalizer
          sharp (indices.flatMap left) hleftFlat (right i) hrightHead
      let push :=
        factory.semantic_sharp_normalizer
          sharp move.higherSource move.higher_least_succ
            (indices.flatMap right) hrightFlat
      let tail :=
        factory.interleave_sharp_normalizer
          sharp indices left right hleftTail hrightTail
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

/--
The restricted sharp interleaver supplies the delegated coordinate merge
route.
-/
noncomputable def
    delegated_merge_normalizer
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
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
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
    factory.interleave_sharp_normalizer
      sharp indices left right
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

/-- A concise call-site alias for the restricted sharp delegated merge route. -/
noncomputable def semantic_merge_sharp
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
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight) :
    DMRoute
      (lowerWeight := lowerWeight) hn H hH coordinates factor :=
  delegated_merge_normalizer
    hn H hH factory sharp coordinates factor

end TSFtrya

end TCTex
end Submission

-- Merged from RestrictedSharpRecursiveCollection.lean

/-!
# Direct recursive symbolic Hall-power collection from restricted sharp routing

The restricted sharp router exposes the true recursive dependency of
Hall-power recollection: collecting at ordinary weight `lowerWeight` only asks
for semantic normalizers at strictly larger weights.  This permits a direct
well-founded construction of the global semantic normalizer.

The remaining custom data is now narrow:

* correction packets below the automatic class-two band
  `n ≤ 3 * lowerWeight`;
* intrinsic factor-normalization residual expansions below the commutative
  terminal band `n ≤ 2 * lowerWeight`.

Stable fixed-weight merging, movement across the old higher tail, and all
recursive correction routing are constructed automa.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
The remaining reachable data for direct global symbolic Hall-power
recollection.
-/
structure RSRec
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) where
  correctionFactory :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 3 * lowerWeight →
        TSFtrya
          (n := n) (inputWeight := inputWeight) H lowerWeight
  factorResidual :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := lowerWeight + 1) H →
          ∀ (factor : SPFactora H inputWeight),
            factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
          TSExp
            (lowerWeight := lowerWeight) hn H hH factor

namespace RSRec

open TAExp
open TAResolua

/-- Select automatic class-two packets whenever the current stratum permits it. -/
def packetFactoryAt
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (builder :
      RSRec
        (n := n) (inputWeight := inputWeight) hn H hH)
    (lowerWeight : ℕ) :
    TSFtrya
      (n := n) (inputWeight := inputWeight) H lowerWeight :=
  if hclassTwo : n ≤ 3 * lowerWeight then
    TSFtrya.of_classTwo
      H hclassTwo
  else
    builder.correctionFactory lowerWeight hclassTwo

/--
Directly construct the semantic normalizer at one support bound.  Every
recursive use occurs at a strictly larger support weight.
-/
noncomputable def semanticCoordinateNormalizer
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (builder :
      RSRec
        (n := n) (inputWeight := inputWeight) hn H hH)
    (lowerWeight : ℕ) :
    TSNormalb
      (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H :=
  if hterminal : n ≤ 2 * lowerWeight then
    TSNormalb.of_highWeight
      hn H hH hterminal
  else
    TSNormalb.ofInsertionKernel
      { insert := by
          intro coordinates factor hcoordinates hfactorSupported
            hfactorTruncated
          let nextNormalizer :=
            builder.semanticCoordinateNormalizer
              hn H hH (lowerWeight + 1)
          by_cases hfactorStrict :
              lowerWeight <
                factor.word.weight PEAddres.weight
          · exact
              nextNormalizer.insertion_word_weight coordinates
                factor hcoordinates hfactorStrict hfactorTruncated
          · have hfactorWeight :
                factor.word.weight PEAddres.weight =
                  lowerWeight := by
              omega
            let sharp :
                SSNormal
                  (n := n) (inputWeight := inputWeight)
                    (lowerWeight := lowerWeight) H :=
              SSNormal.ofNormalizerAbove
                (lowerWeight := lowerWeight)
                (fun strongerWeight
                    (_hstronger : lowerWeight < strongerWeight) =>
                  builder.semanticCoordinateNormalizer
                    hn H hH strongerWeight)
            let packetFactory := builder.packetFactoryAt lowerWeight
            let factorTail :=
              builder.factorResidual lowerWeight hterminal nextNormalizer
                factor hfactorWeight hfactorTruncated
            let merge :=
              (packetFactory
                |>.semantic_merge_sharp
                  hn H hH sharp coordinates factor)
                |>.mergeResidualExpansion hfactorWeight hfactorTruncated
            let block :=
              mergeFactor merge factorTail
            let tail :=
              (packetFactory
                |>.supported_route_sharp
                  sharp coordinates factor hfactorWeight)
                |>.higherTailResolution hfactorWeight hfactorTruncated
            exact
              (active_block_tail
                hcoordinates hfactorWeight hfactorTruncated
                  (block.activeBlockResolution hcoordinates
                    hfactorWeight)
                  tail)
                |>.exists_insertion nextNormalizer hfactorWeight
                  hfactorTruncated }
termination_by n - lowerWeight
decreasing_by
  all_goals
    have hlowerWeightCutoff : lowerWeight < n := by
      omega
    omega

end RSRec

namespace TSInput

/--
Restricted sharp recursive data and graded Hall bases construct the
integer-valued coordinate polynomials required by Claim 5.
-/
theorem restrictedSharpRecursive
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      RSRec
        (n := n) (inputWeight := inputWeight) hn H hH)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.supportedSemanticNormalizer
    hsourceSupported
    (builder.semanticCoordinateNormalizer hn H hH inputWeight)
    hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from RestrictedSharpPacketResidualSourceCollection.lean

/-!
# Hall-power collection from cutoff packets and residual sources

A cutoff-specific Hall-Petresco packet supplies all powered adjacent-swap
corrections.  Explicit recollections of the intrinsic residual source of each
nonterminal active factor supply the remaining local input.

This file compiles those two inputs directly to the restricted-sharp recursive
collector and hence to the Claim 5 coordinate polynomials.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
A cutoff Hall-Petresco packet and explicit intrinsic residual-source
recollections sufficient for direct global symbolic Hall-power recollection.
-/
structure
    TSBuilda
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) where
  packet :
    PFSubsti.TAPkt.{u} d n
  factorResidualSource :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        ∀ (factor : SPFactora H inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
          factor.word.weight PEAddres.weight < n →
            TSSrc
              (lowerWeight := lowerWeight) hn H hH factor

namespace
  TSBuilda

/--
Compile cutoff adjacent-swap packets and local residual-source recollections
to the direct restricted-sharp recursive collector.
-/
noncomputable def restrictedRecursiveBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (builder :
      TSBuilda
        (n := n) (inputWeight := inputWeight) hn H hH)
    (hinputWeight : 1 ≤ inputWeight) :
    RSRec
      (n := n) (inputWeight := inputWeight) hn H hH where
  correctionFactory lowerWeight _hterminal :=
    (builder.packet.powerSupportedFactory
      (by omega) lowerWeight)
      |>.correctionPacketFactory
  factorResidual lowerWeight hterminal _nextNormalizer factor hfactorWeight
      hfactorTruncated :=
    (builder.factorResidualSource lowerWeight hterminal factor hfactorWeight
      hfactorTruncated)
      |>.factorExpansion

end
  TSBuilda

namespace TSInput

/--
A cutoff Hall-Petresco packet, explicit residual-source recollections, and
graded Hall bases construct the integer-valued coordinate polynomials required
by Claim 5.
-/
theorem
    sharpCollectionBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      TSBuilda
        (n := n) (inputWeight := inputWeight) hn H hH)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.restrictedSharpRecursive
    hn H hH hsourceSupported
      (builder.restrictedRecursiveBuilder hinputWeight)
      hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from RestrictedSharpWordExpansionSingletonCollection.lean

/-!
# Recursive symbolic Hall-power collection from word expansions and singleton normalizations

The direct restricted-sharp collector is phrased in terms of its immediate
operational inputs: truncated correction packets and intrinsic factor-residual
expansions.  Two generic bridges make a more mathematical interface possible:

* a finite higher-word correction expansion truncates to the required packet;
  and
* a semantic singleton normalization determines the canonical active layer
  and exposes its strictly higher residual tail.

This file packages precisely those two inputs and compiles them to the direct
recursive Hall-power collector.  The remaining low-weight theorem is now
stated in terms of universal word expansion and singleton recollection, rather
than collector-internal routing records.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
The mathematical low-weight data sufficient for direct global symbolic
Hall-power recollection.
-/
structure
    TSBuildd
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) where
  correctionExpansionFactory :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 3 * lowerWeight →
        SEFtry
          (n := n) (inputWeight := inputWeight) H lowerWeight
  factorNormalization :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := lowerWeight + 1) H →
          ∀ (factor : SPFactora H inputWeight),
            factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
          TANorm
            (n := n) (lowerWeight := lowerWeight) H factor

namespace
  TSBuildd

/--
Compile universal expansions and singleton recollections to the operational
inputs of the restricted-sharp recursive collector.
-/
noncomputable def restrictedRecursiveBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (builder :
      TSBuildd
        (n := n) (inputWeight := inputWeight) hn H hH) :
    RSRec
      (n := n) (inputWeight := inputWeight) hn H hH where
  correctionFactory lowerWeight hterminal :=
    (builder.correctionExpansionFactory lowerWeight hterminal)
      |>.correctionPacketFactory
  factorResidual lowerWeight hterminal nextNormalizer factor hfactorWeight
      hfactorTruncated :=
    (builder.factorNormalization lowerWeight hterminal nextNormalizer factor
      hfactorWeight hfactorTruncated)
      |>.factorResidualRoute hn H hH hfactorWeight hfactorTruncated
      |>.factorExpansion

end
  TSBuildd

namespace TSInput

/--
Universal correction expansions, singleton recollections, and graded Hall
bases construct the integer-valued coordinate polynomials required by Claim 5.
-/
theorem
    restrictedSingletonBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      TSBuildd
        (n := n) (inputWeight := inputWeight) hn H hH)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.restrictedSharpRecursive
    hn H hH hsourceSupported
      builder.restrictedRecursiveBuilder hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from RestrictedSharpPacketSingletonCollection.lean

/-!
# Recursive Hall-power collection from Hall-Petresco packets

The restricted-sharp powered collector accepts a correction-expansion factory
at every active support stratum.  A cutoff-specific all-integral Hall-Petresco
packet constructs all of those factories automa: the powered
substitution layer normalizes each generalized-binomial block coefficient into
an explicit repeated-block expansion.

This file packages the resulting mathematical boundary.  The only remaining
local field is semantic recollection of one powered factor after strictly
higher strata have already been normalized.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
Cutoff Hall-Petresco expansion and singleton recollection data sufficient for
direct global symbolic Hall-power recollection.
-/
structure
    SCBuildb
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) where
  packet :
    PFSubsti.TAPkt.{u} d n
  factorNormalization :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := lowerWeight + 1) H →
          ∀ (factor : SPFactora H inputWeight),
            factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
          TANorm
            (n := n) (lowerWeight := lowerWeight) H factor

namespace
  SCBuildb

/--
Compile a cutoff Hall-Petresco packet into the word-expansion boundary of the
restricted-sharp powered collector.
-/
noncomputable def restrictedSharpExpansion
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (builder :
      SCBuildb
        (n := n) (inputWeight := inputWeight) hn H hH)
    (hinputWeight : 1 ≤ inputWeight) :
    TSBuildd
      (n := n) (inputWeight := inputWeight) hn H hH where
  correctionExpansionFactory lowerWeight _hterminal :=
    builder.packet.powerSupportedFactory
      (by omega) lowerWeight
  factorNormalization :=
    builder.factorNormalization

end
  SCBuildb

namespace TSInput

/--
A cutoff Hall-Petresco packet, singleton recollections, and graded Hall bases
construct the integer-valued coordinate polynomials required by Claim 5.
-/
theorem
    restrictedSharpCollection
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      SCBuildb
        (n := n) (inputWeight := inputWeight) hn H hH)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.restrictedSingletonBuilder
    hn H hH hsourceSupported
      (builder.restrictedSharpExpansion
        hinputWeight)
      hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from RestrictedSharpSignedBlockPacketSingletonCollection.lean

/-!
# Recursive Hall-power collection from signed-block packets

The support-pattern collector produces signed generalized-binomial profiles,
rather than a positive recipe list.  A cutoff-specific all-integral signed
packet still supplies the powered correction-expansion factory consumed by
the restricted-sharp collector.

This file packages that direct boundary.  The remaining local obligation is
semantic recollection of one powered factor after strictly higher strata have
already been normalized.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open
  CFExp

/--
A cutoff signed-block Hall-Petresco packet and singleton recollection data
sufficient for direct global symbolic Hall-power recollection.
-/
structure
    SSBuild
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) where
  packet :
    TAInt.{u} d n
  factorNormalization :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := lowerWeight + 1) H →
          ∀ (factor : SPFactora H inputWeight),
            factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
          TANorm
            (n := n) (lowerWeight := lowerWeight) H factor

namespace
  SSBuild

/--
Compile a cutoff signed-block packet into the word-expansion boundary of the
restricted-sharp powered collector.
-/
noncomputable def restrictedSharpExpansion
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (builder :
      SSBuild
        (n := n) (inputWeight := inputWeight) hn H hH)
    (hinputWeight : 1 ≤ inputWeight) :
    TSBuildd
      (n := n) (inputWeight := inputWeight) hn H hH where
  correctionExpansionFactory lowerWeight _hterminal :=
    builder.packet.powerSupportedFactory
      (by omega) lowerWeight
  factorNormalization :=
    builder.factorNormalization

end
  SSBuild

namespace TSInput

/--
A cutoff signed-block packet, singleton recollections, and graded Hall bases
construct the integer-valued coordinate polynomials required by Claim 5.
-/
theorem
    restrictedSharpSingleton
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      SSBuild
        (n := n) (inputWeight := inputWeight) hn H hH)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.restrictedSingletonBuilder
    hn H hH hsourceSupported
      (builder.restrictedSharpExpansion
        hinputWeight)
      hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from RestrictedSharpUniversalSignedBlockProfileAssignmentSingletonCollection.lean

/-!
# Claim 5 from universal signed-block profile assignments

The support-pattern collector naturally produces a universal signed-block
profile assignment on the finite cutoff skeleton.  Signed powered substitution
turns that assignment into the correction-expansion factory required by the
restricted-sharp Hall-power collector.

This file records the direct Claim 5 boundary.  After the universal profile
assignment is supplied, the only remaining local obligation is semantic
normalization of one powered factor after all strictly higher strata have
already been normalized.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open UWSkelet

namespace
  UWSkelet.UPAssign

/--
A universal signed-profile assignment supplies powered adjacent-swap
correction expansions at every support stratum.
-/
noncomputable def powerSupportedFactory
    {n leftWeight rightWeight d inputWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (assignment :
      UPAssign.{u}
        n leftWeight rightWeight hleftWeight hrightWeight)
    (hinputWeight : 0 < inputWeight)
    (lowerWeight : ℕ) :
    SEFtry
      (n := n) (inputWeight := inputWeight) H lowerWeight :=
  assignment.universalAllPacket
    |>.powerSupportedFactory
      hinputWeight lowerWeight

end
  UWSkelet.UPAssign

/--
A universal signed-profile assignment and singleton recollection data
sufficient for direct global symbolic Hall-power recollection.
-/
structure
    RSBuild
    {d n inputWeight leftWeight rightWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  assignment :
    UPAssign.{u}
      n leftWeight rightWeight hleftWeight hrightWeight
  factorNormalization :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := lowerWeight + 1) H →
          ∀ (factor : SPFactora H inputWeight),
            factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
          TANorm
            (n := n) (lowerWeight := lowerWeight) H factor

namespace
  RSBuild

/--
Compile the universal signed assignment into the word-expansion boundary of
the restricted-sharp powered collector.
-/
noncomputable def restrictedSharpExpansion
    {d n inputWeight leftWeight rightWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (builder :
      RSBuild
        (n := n) (inputWeight := inputWeight)
          hn H hH hleftWeight hrightWeight)
    (hinputWeight : 1 ≤ inputWeight) :
    TSBuildd
      (n := n) (inputWeight := inputWeight) hn H hH where
  correctionExpansionFactory lowerWeight _hterminal :=
    builder.assignment.powerSupportedFactory
      (by omega) lowerWeight
  factorNormalization :=
    builder.factorNormalization

end
  RSBuild

namespace TSInput

/--
A universal signed-profile assignment, singleton recollections, and graded
Hall bases construct the integer-valued coordinate polynomials required by
Claim 5.
-/
theorem
    sharpUniversalBuilder
    {d n inputWeight leftWeight rightWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      RSBuild
        (n := n) (inputWeight := inputWeight)
          hn H hH hleftWeight hrightWeight)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.restrictedSingletonBuilder
    hn H hH hsourceSupported
      (builder.restrictedSharpExpansion
        hinputWeight)
      hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from RestrictedSharpUniversalPacketSingletonCollection.lean

/-!
# Recursive Hall-power collection from universal Hall-Petresco packets

A universal all-integral Hall-Petresco packet specializes to every
lower-central cutoff.  The powered packet substitution layer then constructs
the correction expansions required by the restricted-sharp recursive
collector.

This file records the cutoff-independent version of the packet-plus-singleton
boundary.  The remaining local obligation is semantic recollection of one
powered factor after strictly higher strata have been normalized.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
A universal Hall-Petresco packet and singleton recollection data sufficient for
direct global symbolic Hall-power recollection at one lower-central cutoff.
-/
structure
    RSUniv
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) where
  packet :
    PFSubsti.UAInt.{u}
  factorNormalization :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := lowerWeight + 1) H →
          ∀ (factor : SPFactora H inputWeight),
            factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
          TANorm
            (n := n) (lowerWeight := lowerWeight) H factor

namespace
  RSUniv

/-- Specialize the universal packet to the requested lower-central cutoff. -/
def restrictedSingletonCollection
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (builder :
      RSUniv
        (n := n) (inputWeight := inputWeight) hn H hH) :
    SCBuildb
      (n := n) (inputWeight := inputWeight) hn H hH where
  packet :=
    builder.packet.truncatedAll
  factorNormalization :=
    builder.factorNormalization

end
  RSUniv

namespace TSInput

/--
A universal Hall-Petresco packet, singleton recollections, and graded Hall
bases construct the integer-valued coordinate polynomials required by Claim 5.
-/
theorem
    restrictedSharpUniversal
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      RSUniv
        (n := n) (inputWeight := inputWeight) hn H hH)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.restrictedSharpCollection
    hn H hH hsourceSupported
      builder.restrictedSingletonCollection
      hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from RestrictedSharpConcreteSignedBlockStabilizationSingletonCollection.lean

/-!
# Claim 5 from stabilized concrete signed-block packets

Concrete operational collection constructs one finite signed-block packet at
every pair of natural multiplicities.  Cutoff truncation discards factors
which vanish in the lower-central quotient.  The remaining combinatorial
theorem is a finite stabilization statement: one fixed below-cutoff packet
has the same evaluations as all of those concrete packets.

This file composes cutoff stabilization and its all-integral extension with
the powered restricted-sharp collector.  It exposes the exact remaining
obligations without requiring a cutoff-independent universal packet.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open
  CSAggreg
open
  CCTrunc
open
  CFExp
open
  CFSubsti
open
  UNPkt
open USOrdere

namespace
  CCTrunc
namespace TNStab

/--
A root-layer cutoff stabilization and its signed extension give the
all-integral packet consumed by powered signed-block substitution.
-/
def truncatedAllLift
    {kernel : OCShape}
    {d n : ℕ}
    {fixedPackets : List RFPkt}
    (stabilization :
      TNStab.{u}
        kernel d n 1 1 fixedPackets)
    (lift :
      stabilization.truncNaturalPacket.AILift) :
    TAInt d n :=
  lift.truncatedAllIntegral

@[simp]
lemma packets_all_lift
    {kernel : OCShape}
    {d n : ℕ}
    {fixedPackets : List RFPkt}
    (stabilization :
      TNStab.{u}
        kernel d n 1 1 fixedPackets)
    (lift :
      stabilization.truncNaturalPacket.AILift) :
    (stabilization.truncatedAllLift lift).packets =
      fixedPackets :=
  rfl

end TNStab
end
  CCTrunc

/--
Operational cutoff stabilization, its signed extension, and singleton
recollection data sufficient for direct global symbolic Hall-power
recollection.
-/
structure
    SSBuilda
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (kernel : OCShape)
    (fixedPackets : List RFPkt) where
  stabilization :
    TNStab.{u}
      kernel d n 1 1 fixedPackets
  lift :
    stabilization.truncNaturalPacket.AILift
  factorNormalization :
    ∀ lowerWeight : ℕ,
      ¬n ≤ 2 * lowerWeight →
        TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := lowerWeight + 1) H →
          ∀ (factor : SPFactora H inputWeight),
            factor.word.weight PEAddres.weight = lowerWeight →
            factor.word.weight PEAddres.weight < n →
          TANorm
            (n := n) (lowerWeight := lowerWeight) H factor

namespace
  SSBuilda

/--
An ordered supported stabilization supplies the operational stabilization
field while retaining its explicit finite cutoff schedule.
-/
def stabilizedCutoffPacket
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {kernel : OCShape}
    (packet :
      SBPkt.{u}
        kernel d n 1 1)
    (lift :
      packet.truncNaturalPacket.AILift)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor) :
    SSBuilda
      (n := n) (inputWeight := inputWeight) hn H hH kernel packet.packets where
  stabilization :=
    packet.truncatedNaturalStabilization
  lift :=
    lift
  factorNormalization :=
    factorNormalization

/--
Compile stabilized concrete operational data into the signed-block packet
boundary of the powered collector.
-/
def restrictedCollectionBuilder
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {kernel : OCShape}
    {fixedPackets : List RFPkt}
    (builder :
      SSBuilda
        (n := n) (inputWeight := inputWeight)
          hn H hH kernel fixedPackets) :
    SSBuild
      (n := n) (inputWeight := inputWeight) hn H hH where
  packet :=
    builder.stabilization.truncatedAllLift
      builder.lift
  factorNormalization :=
    builder.factorNormalization

end
  SSBuilda

namespace TSInput

open
  SSBuilda

/--
Cutoff stabilization of concrete operational signed-block packets, a signed
extension, singleton recollections, and graded Hall bases construct the
integer-valued coordinate polynomials required by Claim 5.
-/
theorem
    sharpStabilizationBuilder
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
    {fixedPackets : List RFPkt}
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (builder :
      SSBuilda
        (n := n) (inputWeight := inputWeight)
          hn H hH kernel fixedPackets)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.restrictedSharpSingleton
    hn H hH hsourceSupported
      builder.restrictedCollectionBuilder
      hinputWeight

/--
An explicitly ordered, finite-support cutoff stabilization and its signed
extension construct the integer-valued coordinate polynomials of Claim 5.
-/
theorem
    restrictedSharpStabilized
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {kernel : OCShape}
    (packet :
      SBPkt.{u}
        kernel d n 1 1)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (lift :
      packet.truncNaturalPacket.AILift)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.sharpStabilizationBuilder
    hn H hH hsourceSupported
      (stabilizedCutoffPacket
        packet lift factorNormalization)
      hinputWeight

end TSInput

end TCTex
end Submission
