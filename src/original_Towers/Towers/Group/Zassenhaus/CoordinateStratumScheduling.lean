import Towers.Group.Zassenhaus.CoordinateEndpointStrata
import Towers.Group.Zassenhaus.SemanticNormalizerRecursion

/-!
# One-stratum scheduling interface for symbolic Hall powers

A recursive symbolic Hall collector works one ordinary Hall-weight stratum at
a time.  At the current stratum, a normalized endpoint is its visible
fixed-weight block followed by a tail supported one stratum higher.

This file packages that endpoint view and exposes the remaining operational
scheduler obligation: finite normalized obstruction rewrites must insert one
factor into the endpoint.  Such a schedule immediately supplies the semantic
insertion kernel consumed by filtration recursion.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

/--
A supported coordinate endpoint viewed at one active ordinary Hall-weight
stratum.
-/
structure PSView
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (lowerWeight : ℕ)
    (coordinates : CCExpans H inputWeight) :
    Prop where
  lowerWeight_pos : 1 ≤ lowerWeight
  lowerWeight_cutoff : lowerWeight ≤ n - 1
  coordinates_no_below : coordinates.NTBelow lowerWeight

namespace PSView

/-- The normalized endpoint block at the active stratum. -/
def currentFactors
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {coordinates : CCExpans H inputWeight}
    (_view :
      PSView
        (n := n) lowerWeight coordinates) :
    List (SPFactora H inputWeight) :=
  coordinates.weightFactors lowerWeight

/-- The normalized endpoint tail strictly above the active stratum. -/
def higherFactors
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {coordinates : CCExpans H inputWeight}
    (_view :
      PSView
        (n := n) lowerWeight coordinates) :
    List (SPFactora H inputWeight) :=
  coordinates.tailFactors (n := n) lowerWeight

/-- The complete normalized endpoint is its active block followed by its tail. -/
lemma factors_current_higher
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {coordinates : CCExpans H inputWeight}
    (view :
      PSView
        (n := n) lowerWeight coordinates) :
    coordinates.factors (n := n) =
      view.currentFactors ++ view.higherFactors := by
  exact
    coordinates.append_no_below
      view.coordinates_no_below view.lowerWeight_pos
        view.lowerWeight_cutoff

/-- Every active-block factor has exactly the active ordinary Hall weight. -/
lemma word_current_factors
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {coordinates : CCExpans H inputWeight}
    (view :
      PSView
        (n := n) lowerWeight coordinates)
    {x : SPFactora H inputWeight}
    (hx : x ∈ view.currentFactors) :
    x.word.weight PEAddres.weight = lowerWeight :=
  coordinates.word_weight_factors hx

/-- The active block is supported at the active stratum. -/
lemma least_current_factors
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {coordinates : CCExpans H inputWeight}
    (view :
      PSView
        (n := n) lowerWeight coordinates) :
    SPFactora.WordWeightLeast lowerWeight
      view.currentFactors := by
  intro x hx
  rw [view.word_current_factors hx]

/-- The higher tail is supported one stratum above the active block. -/
lemma least_higher_factors
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {coordinates : CCExpans H inputWeight}
    (view :
      PSView
        (n := n) lowerWeight coordinates) :
    SPFactora.WordWeightLeast (lowerWeight + 1)
      view.higherFactors :=
  coordinates.word_least_factors

/-- The higher tail remains physically below the quotient cutoff. -/
lemma truncated_higher_factors
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {coordinates : CCExpans H inputWeight}
    (view :
      PSView
        (n := n) lowerWeight coordinates) :
    SPFactora.IsTruncated n view.higherFactors :=
  coordinates.truncated_factors view.lowerWeight_cutoff

/-- The delegated tail evaluates to the ordinary collected Hall tail. -/
lemma list_higher_factors
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {coordinates : CCExpans H inputWeight}
    (view :
      PSView
        (n := n) lowerWeight coordinates)
    (q : ℕ) :
    SPFactora.listEval (n := n) q view.higherFactors =
      collectedTailProduct (n := n) H (coordinates.eval q) lowerWeight :=
  coordinates.list_tail_factors q lowerWeight

end PSView

namespace SCRw

/-- A single normalized semantic obstruction is a finite rewrite run. -/
lemma single
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L R : List (SPFactora H inputWeight)}
    (h :
      SSStep
        (n := n) H inputWeight lowerWeight L R) :
    SCRw
      (n := n) (lowerWeight := lowerWeight) L R :=
  Relation.ReflTransGen.single h

/-- Finite normalized semantic obstruction runs compose under concatenation. -/
lemma append
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {L₁ R₁ L₂ R₂ : List (SPFactora H inputWeight)}
    (hleft :
      SCRw
        (n := n) (lowerWeight := lowerWeight) L₁ R₁)
    (hright :
      SCRw
        (n := n) (lowerWeight := lowerWeight) L₂ R₂) :
    SCRw
      (n := n) (lowerWeight := lowerWeight)
      (L₁ ++ L₂) (R₁ ++ R₂) := by
  have hleft' :
      SCRw
        (n := n) (lowerWeight := lowerWeight)
        (L₁ ++ L₂) (R₁ ++ L₂) := by
    simpa using hleft.context [] L₂
  have hright' :
      SCRw
        (n := n) (lowerWeight := lowerWeight)
        (R₁ ++ L₂) (R₁ ++ R₂) := by
    simpa using hright.context R₁ []
  exact hleft'.trans hright'

end SCRw

/--
The operational one-stratum scheduler obligation.  Assuming correction
packets can already be normalized one stratum higher, inserting one factor
must be witnessed by a finite run of normalized obstruction swaps.
-/
structure TRInserta
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
                SCRw
                  (n := n) (lowerWeight := lowerWeight)
                  (coordinates.factors (n := n) ++ [factor])
                  (next.factors (n := n))

namespace TRInserta

/--
An operational one-stratum schedule supplies the semantic insertion step used
by well-founded filtration recursion.
-/
def recSemanticInsertion
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (schedule :
      TRInserta
        (n := n) (inputWeight := inputWeight) H) :
    RIStep
      (n := n) (inputWeight := inputWeight) H where
  insert lowerWeight normalizer := {
    insert := by
      intro coordinates factor hcoordinates hfactorSupported hfactorTruncated
      rcases schedule.insert lowerWeight normalizer coordinates factor
          hcoordinates hfactorSupported hfactorTruncated with
        ⟨next, hnextSupported, hrewrites⟩
      exact ⟨next, hnextSupported, hrewrites.listEval_eq⟩ }

end TRInserta

namespace TSInput

/--
A correctly sourced repeated-block input and an operational one-stratum
schedule construct the Claim 5 polynomial data.
-/
theorem recursiveInsertionSchedule
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
      TRInserta
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.recursiveSemanticInsertion
    hn H hH hsourceSupported schedule.recSemanticInsertion
      hinputWeight

end TSInput

end TCTex
end Towers
