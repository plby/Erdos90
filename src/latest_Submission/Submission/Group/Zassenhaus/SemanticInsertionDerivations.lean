import Submission.Group.Zassenhaus.SemanticPacketFactories

/-!
# List-valued semantic insertion derivations for symbolic Hall powers

The More3 collector recursively inserts one correction term before continuing
an obstructed insertion.  Powered Hall collection has the same shape, except
that a delegated correction packet is normalized to a whole list of
higher-weight coordinate factors.

This file packages that list-valued recursion.  A single-factor insertion may
swap one adjacent obstruction, recursively fold its normalized correction
block into the preceding prefix, and then continue inserting the original
factor.  A block insertion folds a finite correction list by repeated
single-factor insertion.

Both certificates compile to finite normalized semantic obstruction rewrites.
The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

mutual

  /--
  A list-valued More3 insertion derivation for one supported semantic
  stratum.
  -/
  inductive SSInsertc
      {d n : ℕ}
      (H : ∀ s : ℕ, BCWta.{u} d s)
      (inputWeight lowerWeight : ℕ) :
      List (SPFactora H inputWeight) →
        SPFactora H inputWeight →
          List (SPFactora H inputWeight) → Prop where
    | nil
        (A : SPFactora H inputWeight) :
        SSInsertc (n := n) H
          inputWeight lowerWeight [] A [A]
    | append
        (P : List (SPFactora H inputWeight))
        (B A : SPFactora H inputWeight) :
        SSInsertc (n := n) H
          inputWeight lowerWeight (P ++ [B]) A (P ++ [B, A])
    | obstruction
        (P : List (SPFactora H inputWeight))
        (B A : SPFactora H inputWeight)
        (C : TCPkt n B A)
        (normalization :
          TSNorma
            lowerWeight C)
        {Q R : List (SPFactora H inputWeight)}
        (hcorrections :
          SBInsert (n := n) H
            inputWeight lowerWeight P
              (normalization.coordinates.factors (n := n)) Q)
        (hinsert :
          SSInsertc (n := n) H
            inputWeight lowerWeight Q A R) :
        SSInsertc (n := n) H
          inputWeight lowerWeight (P ++ [B]) A (R ++ [B])

  /--
  Fold a finite normalized correction block into a preceding prefix by
  repeated semantic insertion.
  -/
  inductive SBInsert
      {d n : ℕ}
      (H : ∀ s : ℕ, BCWta.{u} d s)
      (inputWeight lowerWeight : ℕ) :
      List (SPFactora H inputWeight) →
        List (SPFactora H inputWeight) →
          List (SPFactora H inputWeight) → Prop where
    | nil
        (P : List (SPFactora H inputWeight)) :
        SBInsert (n := n) H
          inputWeight lowerWeight P [] P
    | snoc
        (P source : List (SPFactora H inputWeight))
        (A : SPFactora H inputWeight)
        {Q R : List (SPFactora H inputWeight)}
        (hsource :
          SBInsert (n := n) H
            inputWeight lowerWeight P source Q)
        (hinsert :
          SSInsertc (n := n) H
            inputWeight lowerWeight Q A R) :
        SBInsert (n := n) H
          inputWeight lowerWeight P (source ++ [A]) R

end

namespace SSInsertc

/-- A semantic insertion certificate compiles to a finite obstruction run. -/
lemma rewrites
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    {A : SPFactora H inputWeight}
    (h :
      SSInsertc
        (n := n) H inputWeight lowerWeight L A R) :
    SCRw
      (n := n) (lowerWeight := lowerWeight) (L ++ [A]) R := by
  refine
    SSInsertc.recOn
      (motive_1 := fun L A R _h =>
        SCRw
          (n := n) (lowerWeight := lowerWeight) (L ++ [A]) R)
      (motive_2 := fun P source R _h =>
        SCRw
          (n := n) (lowerWeight := lowerWeight) (P ++ source) R)
      h ?_ ?_ ?_ ?_ ?_
  · intro A
    simpa using
      (Relation.ReflTransGen.refl :
        SCRw
          (n := n) (lowerWeight := lowerWeight) [A] [A])
  · intro P B A
    simpa [List.append_assoc] using
      (Relation.ReflTransGen.refl :
        SCRw
          (n := n) (lowerWeight := lowerWeight)
          (P ++ [B, A]) (P ++ [B, A]))
  · intro P B A C normalization Q R hcorrections hinsert
      ihcorrections ihinsert
    have hswap :
        SCRw
          (n := n) (lowerWeight := lowerWeight)
          (P ++ [B, A])
          (P ++ normalization.coordinates.factors (n := n) ++ [A, B]) := by
      apply SCRw.single
      simpa using
        (SSStep.obstruction
          P [] B A C normalization)
    have hrouteCorrections :
        SCRw
          (n := n) (lowerWeight := lowerWeight)
          (P ++ normalization.coordinates.factors (n := n) ++ [A, B])
          (Q ++ [A, B]) := by
      simpa [List.append_assoc] using
        ihcorrections.context [] [A, B]
    have hrouteA :
        SCRw
          (n := n) (lowerWeight := lowerWeight)
          (Q ++ [A, B]) (R ++ [B]) := by
      simpa [List.append_assoc] using ihinsert.context [] [B]
    simpa [List.append_assoc] using
      hswap.trans (hrouteCorrections.trans hrouteA)
  · intro P
    simpa using
      (Relation.ReflTransGen.refl :
        SCRw
          (n := n) (lowerWeight := lowerWeight) P P)
  · intro P source A Q R hsource hinsert ihsource ihinsert
    have hroutePrefix :
        SCRw
          (n := n) (lowerWeight := lowerWeight)
          ((P ++ source) ++ [A]) (Q ++ [A]) := by
      simpa [List.append_assoc] using ihsource.context [] [A]
    simpa [List.append_assoc] using hroutePrefix.trans ihinsert

end SSInsertc

namespace SBInsert

/-- A block-folding certificate compiles to a finite obstruction run. -/
lemma rewrites
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {P source R : List (SPFactora H inputWeight)}
    (h :
      SBInsert
        (n := n) H inputWeight lowerWeight P source R) :
    SCRw
      (n := n) (lowerWeight := lowerWeight) (P ++ source) R := by
  refine
    SBInsert.recOn
      (motive_1 := fun L A R _h =>
        SCRw
          (n := n) (lowerWeight := lowerWeight) (L ++ [A]) R)
      (motive_2 := fun P source R _h =>
        SCRw
          (n := n) (lowerWeight := lowerWeight) (P ++ source) R)
      h ?_ ?_ ?_ ?_ ?_
  · intro A
    simpa using
      (Relation.ReflTransGen.refl :
        SCRw
          (n := n) (lowerWeight := lowerWeight) [A] [A])
  · intro P B A
    simpa [List.append_assoc] using
      (Relation.ReflTransGen.refl :
        SCRw
          (n := n) (lowerWeight := lowerWeight)
          (P ++ [B, A]) (P ++ [B, A]))
  · intro P B A C normalization Q R hcorrections hinsert
      ihcorrections ihinsert
    have hswap :
        SCRw
          (n := n) (lowerWeight := lowerWeight)
          (P ++ [B, A])
          (P ++ normalization.coordinates.factors (n := n) ++ [A, B]) :=
      by
        apply SCRw.single
        simpa using
          (SSStep.obstruction
            P [] B A C normalization)
    have hrouteCorrections :
        SCRw
          (n := n) (lowerWeight := lowerWeight)
          (P ++ normalization.coordinates.factors (n := n) ++ [A, B])
          (Q ++ [A, B]) := by
      simpa [List.append_assoc] using
        ihcorrections.context [] [A, B]
    have hrouteA :
        SCRw
          (n := n) (lowerWeight := lowerWeight)
          (Q ++ [A, B]) (R ++ [B]) := by
      simpa [List.append_assoc] using ihinsert.context [] [B]
    simpa [List.append_assoc] using
      hswap.trans (hrouteCorrections.trans hrouteA)
  · intro P
    simpa using
      (Relation.ReflTransGen.refl :
        SCRw
          (n := n) (lowerWeight := lowerWeight) P P)
  · intro P source A Q R hsource hinsert ihsource ihinsert
    have hroutePrefix :
        SCRw
          (n := n) (lowerWeight := lowerWeight)
          ((P ++ source) ++ [A]) (Q ++ [A]) := by
      simpa [List.append_assoc] using ihsource.context [] [A]
    simpa [List.append_assoc] using hroutePrefix.trans ihinsert

end SBInsert

namespace SSInsertc

/-- A semantic insertion certificate preserves evaluation exactly. -/
lemma listEval_eq
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    {A : SPFactora H inputWeight}
    (h :
      SSInsertc
        (n := n) H inputWeight lowerWeight L A R)
    (q : ℕ) :
    SPFactora.listEval (n := n) q R =
      SPFactora.listEval (n := n) q (L ++ [A]) :=
  h.rewrites.listEval_eq q

/-- A semantic insertion certificate preserves physical truncation. -/
lemma isTruncated
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    {A : SPFactora H inputWeight}
    (h :
      SSInsertc
        (n := n) H inputWeight lowerWeight L A R)
    (hL : SPFactora.IsTruncated n L)
    (hA : A.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n R := by
  apply h.rewrites.isTruncated
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hL x hx
  · rcases List.mem_singleton.mp hx with rfl
    exact hA

/-- A semantic insertion certificate preserves its current-stratum bound. -/
lemma wordWeightLeast
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    {A : SPFactora H inputWeight}
    (h :
      SSInsertc
        (n := n) H inputWeight lowerWeight L A R)
    (hL : SPFactora.WordWeightLeast lowerWeight L)
    (hA :
      lowerWeight ≤ A.word.weight PEAddres.weight) :
    SPFactora.WordWeightLeast lowerWeight R := by
  apply h.rewrites.wordWeightLeast
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hL x hx
  · rcases List.mem_singleton.mp hx with rfl
    exact hA

end SSInsertc

namespace SBInsert

/-- Folding a normalized correction block preserves evaluation exactly. -/
lemma listEval_eq
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {P source R : List (SPFactora H inputWeight)}
    (h :
      SBInsert
        (n := n) H inputWeight lowerWeight P source R)
    (q : ℕ) :
    SPFactora.listEval (n := n) q R =
      SPFactora.listEval (n := n) q (P ++ source) :=
  h.rewrites.listEval_eq q

/-- Folding a normalized correction block preserves physical truncation. -/
lemma isTruncated
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {P source R : List (SPFactora H inputWeight)}
    (h :
      SBInsert
        (n := n) H inputWeight lowerWeight P source R)
    (hP : SPFactora.IsTruncated n P)
    (hsource : SPFactora.IsTruncated n source) :
    SPFactora.IsTruncated n R := by
  apply h.rewrites.isTruncated
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hP x hx
  · exact hsource x hx

/-- Folding a normalized correction block preserves lower word-weight bounds. -/
lemma wordWeightLeast
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {P source R : List (SPFactora H inputWeight)}
    (h :
      SBInsert
        (n := n) H inputWeight lowerWeight P source R)
    (hP : SPFactora.WordWeightLeast lowerWeight P)
    (hsource :
      SPFactora.WordWeightLeast lowerWeight source) :
    SPFactora.WordWeightLeast lowerWeight R := by
  apply h.rewrites.wordWeightLeast
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hP x hx
  · exact hsource x hx

end SBInsert

namespace TSFtrya

/--
A supported packet factory reduces one obstructed insertion to routing its
normalized higher correction block and then continuing the original
insertion.
-/
lemma semantic_inserts_obstruction
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      TSFtrya
        (n := n) (inputWeight := inputWeight) H lowerWeight)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H)
    (P : List (SPFactora H inputWeight))
    (B A : SPFactora H inputWeight)
    (hB : lowerWeight ≤ B.word.weight PEAddres.weight)
    (hA : lowerWeight ≤ A.word.weight PEAddres.weight)
    (hcontinue :
      ∀ normalization :
          TSNorma
            lowerWeight (factory.packet B A hB hA),
        ∃ Q R : List (SPFactora H inputWeight),
          SBInsert
              (n := n) H inputWeight lowerWeight P
                (normalization.coordinates.factors (n := n)) Q ∧
            SSInsertc
              (n := n) H inputWeight lowerWeight Q A R) :
    ∃ R : List (SPFactora H inputWeight),
      SSInsertc
        (n := n) H inputWeight lowerWeight (P ++ [B]) A R := by
  rcases (factory.packet B A hB hA).normalization_left
      hB normalizer with
    ⟨normalization⟩
  rcases hcontinue normalization with ⟨Q, R, hcorrections, hinsert⟩
  exact
    ⟨R ++ [B],
      SSInsertc.obstruction
        P B A (factory.packet B A hB hA) normalization
          hcorrections hinsert⟩

end TSFtrya

/--
A structured one-stratum scheduler obligation: endpoint insertion is witnessed
by a list-valued semantic insertion derivation.
-/
structure SIDeriva
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) : Prop where
  insert :
    ∀ lowerWeight : ℕ,
      TSNormalb
          (n := n) (inputWeight := inputWeight)
            (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CCExpans H inputWeight)
          (factor : SPFactora H inputWeight),
          coordinates.NTBelow lowerWeight →
          lowerWeight ≤ factor.word.weight PEAddres.weight →
          factor.word.weight PEAddres.weight < n →
            ∃ next : CCExpans H inputWeight,
              next.NTBelow lowerWeight ∧
                SSInsertc
                  (n := n) H inputWeight lowerWeight
                    (coordinates.factors (n := n)) factor
                      (next.factors (n := n))

namespace SIDeriva

/-- Structured insertion derivations supply the finite-rewrite scheduler. -/
def recursiveCoordinateInsertion
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (schedule :
      SIDeriva
        (n := n) (inputWeight := inputWeight) H) :
    TRInserta
      (n := n) (inputWeight := inputWeight) H where
  insert lowerWeight normalizer coordinates factor hcoordinates
      hfactorSupported hfactorTruncated := by
    rcases schedule.insert lowerWeight normalizer coordinates factor
        hcoordinates hfactorSupported hfactorTruncated with
      ⟨next, hnextSupported, hinsert⟩
    exact ⟨next, hnextSupported, hinsert.rewrites⟩

end SIDeriva

namespace TSInput

/--
A correctly sourced repeated-block input and a structured list-valued
insertion schedule construct the Claim 5 polynomial data.
-/
theorem recursiveInsertionDerivation
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
    (schedule :
      SIDeriva
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.recursiveInsertionSchedule
    hn H hH hsourceSupported
      schedule.recursiveCoordinateInsertion hinputWeight

end TSInput

end TCTex
end Submission
