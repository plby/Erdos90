import Submission.Group.Zassenhaus.Active
import Submission.Group.Zassenhaus.SharpCorrectionDescent

/-!
# Sharp recursive routing through symbolic Hall-power higher tails

To move one active factor left across a strictly higher tail, cross the final
tail parent `B`, normalize its correction packet sharply above the actual
weight of `B`, append that normalized correction block to the remaining
prefix, and recurse.  The pending prefix changes from `P ++ [B]` to
`P ++ correctionFactors`, which strictly decreases the cutoff-defect multiset.

This file implements that More3 recursion and adapts it to the higher-tail
route schedule consumed by active-layer resolution.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace SSInsertc

/-- Appending one factor verbatim is always a valid semantic insertion. -/
lemma append_self
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (L : List (SPFactora H inputWeight))
    (A : SPFactora H inputWeight) :
    SSInsertc
      (n := n) H inputWeight lowerWeight L A (L ++ [A]) := by
  rcases L.eq_nil_or_concat with rfl | ⟨P, B, rfl⟩
  · simpa using
      (SSInsertc.nil
        (n := n) (lowerWeight := lowerWeight) A)
  · exact
      (by
        simpa [List.concat_eq_append] using
          (SSInsertc.append
            (n := n) (lowerWeight := lowerWeight) P B A))

end SSInsertc

namespace SBInsert

/-- Appending a finite correction block verbatim is a valid block insertion. -/
lemma append_self
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (P source : List (SPFactora H inputWeight)) :
    SBInsert
      (n := n) H inputWeight lowerWeight P source (P ++ source) := by
  induction source using List.reverseRecOn with
  | nil =>
      simpa using
        (SBInsert.nil
          (n := n) (lowerWeight := lowerWeight) P)
  | append_singleton source A ih =>
      simpa [List.append_assoc] using
        (SBInsert.snoc
          (n := n) (lowerWeight := lowerWeight) P source A ih
            (SSInsertc.append_self
              (n := n) (lowerWeight := lowerWeight) (P ++ source) A))

end SBInsert

/--
A More3 route moving one active factor to the front of a strictly higher
pending list.
-/
structure SSHigher
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (pending : List (SPFactora H inputWeight))
    (factor : SPFactora H inputWeight) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_least_succ :
    SPFactora.WordWeightLeast
      (lowerWeight + 1) higherSource
  inserts :
    SSInsertc
      (n := n) H inputWeight lowerWeight pending factor
        ([factor] ++ higherSource)

namespace TSFtrya

/--
Sharp parent-relative correction normalization constructs a More3 route
moving one active factor left across any strictly higher pending list.
-/
lemma nonempty_higher_route
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H)
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
      fun x hx => hpending x (by
        simp [List.concat_eq_append, hx])
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
    let normalization := family.semantic_left_sharp C hB
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
      exact
        family.semantic_normalization_sharp
          C hB P
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

/--
Choose the sharp More3 route moving one active factor through a strictly
higher pending list.
-/
noncomputable def supportedListRoute
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H)
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
    (factory.nonempty_higher_route family factor
      hfactorWeight pending hpending)

/--
The generic sharp list router moves an active factor through the higher tail
of a normalized coordinate endpoint.
-/
noncomputable def higherTailRoute
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight) :
    STRoute
      (n := n) (lowerWeight := lowerWeight) H coordinates factor := by
  let route :=
    factory.supportedListRoute family factor hfactorWeight
      (coordinates.tailFactors (n := n) lowerWeight)
        coordinates.word_least_factors
  exact
    { higherSource := route.higherSource
      higher_least_succ :=
        route.higher_least_succ
      inserts := route.inserts }

end TSFtrya

/-- A supported correction-packet factory available at every support stratum. -/
structure TFSched
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) where
  factory :
    ∀ lowerWeight : ℕ,
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight

namespace TFSched

/--
A stratum-indexed packet supply and a sharp normalizer family construct the
recursive higher-tail route schedule used by active-layer resolution.
-/
noncomputable def recursiveSemanticSchedule
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (schedule :
      TFSched
        (n := n) (inputWeight := inputWeight) H)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H) :
    RHRoute
      (n := n) (inputWeight := inputWeight) H where
  route lowerWeight _normalizer coordinates factor _hcoordinates hfactorWeight
      _hfactorTruncated :=
    (schedule.factory lowerWeight).higherTailRoute
      family coordinates factor hfactorWeight

end TFSched

end TCTex
end Submission
