import Submission.Group.Zassenhaus.CoordinateTailSplicing
import Submission.Group.Zassenhaus.UniversalCorrectionFactories

-- Merged from ActiveLayerResolution.lean

/-!
# Active-layer resolutions for symbolic Hall power coordinates

After strictly heavier insertions have been delegated automa, the
remaining local operation occurs at one active Hall-weight stratum.  It must
replace the old endpoint followed by one active-weight factor by:

* a new normalized coordinate block at the active weight; and
* a residual source supported strictly above that weight.

The next-stratum normalizer recollects the residual source, and canonical
higher-tail splicing assembles the final endpoint.  This file packages that
reduction.  It also records a stronger collector-facing interface: a
list-valued More3 insertion derivation ending in the new active block followed
by the higher residual source.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

open scoped IsMulCommutative

universe u

/--
The semantic output of resolving one active-weight insertion.  The active
coordinate block has already been updated; every remaining factor belongs to
the next support stratum.
-/
structure TAResolua
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight) where
  activeCoordinates :
    CCExpans H inputWeight
  active_terms_below :
    activeCoordinates.NTBelow lowerWeight
  higherSource :
    List (SPFactora H inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast (lowerWeight + 1) higherSource
  active_append_source :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q
          (activeCoordinates.weightFactors lowerWeight ++ higherSource) =
        SPFactora.listEval (n := n) q
          (coordinates.factors (n := n) ++ [factor])

namespace TAResolua

/--
Normalize the strictly higher residual source and splice it above the updated
active block.
-/
lemma exists_insertion
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {coordinates : CCExpans H inputWeight}
    {factor : SPFactora H inputWeight}
    (resolution :
      TAResolua
        (n := n) (lowerWeight := lowerWeight) H coordinates factor)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    ∃ next : CCExpans H inputWeight,
      next.NTBelow lowerWeight ∧
        ∀ q : ℕ,
          SPFactora.listEval (n := n) q
              (next.factors (n := n)) =
            SPFactora.listEval (n := n) q
              (coordinates.factors (n := n) ++ [factor]) := by
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    have hfactorPos := SPFactora.word_weight_pos factor
    omega
  have hlowerWeightCutoff : lowerWeight ≤ n - 1 := by
    omega
  rcases normalizer.normalize resolution.higherSource
      resolution.higher_source_truncated
      resolution.higher_least_succ with
    ⟨higher, hhigher, hhigherEval⟩
  refine
    ⟨resolution.activeCoordinates.spliceHigherTail higher lowerWeight,
      resolution.activeCoordinates.no_below_splice higher
        resolution.active_terms_below, ?_⟩
  intro q
  rw [resolution.activeCoordinates.factors_higher_tail higher
      resolution.active_terms_below hhigher hlowerWeightPos
        hlowerWeightCutoff,
    SPFactora.listEval_append,
    hhigherEval q,
    ← SPFactora.listEval_append]
  exact resolution.active_append_source q

end TAResolua

/--
A supply of semantic active-layer resolutions.  This is the exact remaining
local semantic obligation after higher-tail delegation.
-/
structure SRFtryb
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) where
  resolve :
    ∀ (lowerWeight : ℕ)
      (coordinates : CCExpans H inputWeight)
      (factor : SPFactora H inputWeight),
      coordinates.NTBelow lowerWeight →
      factor.word.weight PEAddres.weight = lowerWeight →
      factor.word.weight PEAddres.weight < n →
        TAResolua
          (n := n) (lowerWeight := lowerWeight) H coordinates factor

namespace SRFtryb

/-- Active-layer resolutions supply the residual active insertion branch. -/
def insertionBranch
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      SRFtryb
        (n := n) (inputWeight := inputWeight) H) :
    TruncatedInsertionBranch
      (n := n) (inputWeight := inputWeight) H where
  insert lowerWeight normalizer coordinates factor hcoordinates hfactorWeight
      hfactorTruncated :=
    (factory.resolve lowerWeight coordinates factor hcoordinates hfactorWeight
      hfactorTruncated).exists_insertion normalizer hfactorWeight
        hfactorTruncated

/--
An active-layer resolution factory supplies the complete filtration-recursive
semantic insertion step.
-/
def recSemanticInsertion
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (factory :
      SRFtryb
        (n := n) (inputWeight := inputWeight) H) :
    RIStep
      (n := n) (inputWeight := inputWeight) H :=
  RIStep.insertion_branch
    factory.insertionBranch

end SRFtryb

/--
A collector-facing active-layer certificate.  The More3 derivation routes one
active-weight insertion to a new active coordinate block followed by a
strictly higher residual source.
-/
structure SCRoute
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight) where
  activeCoordinates :
    CCExpans H inputWeight
  active_terms_below :
    activeCoordinates.NTBelow lowerWeight
  higherSource :
    List (SPFactora H inputWeight)
  higher_least_succ :
    SPFactora.WordWeightLeast (lowerWeight + 1) higherSource
  inserts :
    SSInsertc
      (n := n) H inputWeight lowerWeight
        (coordinates.factors (n := n)) factor
          (activeCoordinates.weightFactors lowerWeight ++ higherSource)

namespace SCRoute

/-- A More3 route certificate supplies the corresponding semantic resolution. -/
def activeLayerResolution
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {coordinates : CCExpans H inputWeight}
    {factor : SPFactora H inputWeight}
    (route :
      SCRoute
        (n := n) (lowerWeight := lowerWeight) H coordinates factor)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TAResolua
      (n := n) (lowerWeight := lowerWeight) H coordinates factor where
  activeCoordinates := route.activeCoordinates
  active_terms_below :=
    route.active_terms_below
  higherSource := route.higherSource
  higher_source_truncated := by
    have houtput :
        SPFactora.IsTruncated n
          (route.activeCoordinates.weightFactors lowerWeight ++
            route.higherSource) :=
      route.inserts.isTruncated coordinates.isTruncated_factors
        hfactorTruncated
    intro x hx
    exact houtput x (List.mem_append_right _ hx)
  higher_least_succ :=
    route.higher_least_succ
  active_append_source :=
    route.inserts.listEval_eq

end SCRoute

/--
A structured More3-style route schedule for the only nonautomatic branch:
inserting one factor whose weight is exactly the active stratum.
-/
structure TRRouteb
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) where
  route :
    ∀ lowerWeight : ℕ,
      TSNormalb
          (n := n) (inputWeight := inputWeight)
            (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CCExpans H inputWeight)
          (factor : SPFactora H inputWeight),
          coordinates.NTBelow lowerWeight →
          factor.word.weight PEAddres.weight = lowerWeight →
          factor.word.weight PEAddres.weight < n →
            SCRoute
              (n := n) (lowerWeight := lowerWeight) H coordinates factor

namespace TRRouteb

/--
A structured active-layer More3 route schedule supplies the residual active
insertion branch.
-/
def insertionBranch
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (schedule :
      TRRouteb
        (n := n) (inputWeight := inputWeight) H) :
    TruncatedInsertionBranch
      (n := n) (inputWeight := inputWeight) H where
  insert lowerWeight normalizer coordinates factor hcoordinates hfactorWeight
      hfactorTruncated :=
    ((schedule.route lowerWeight normalizer coordinates factor hcoordinates
      hfactorWeight hfactorTruncated).activeLayerResolution
        hfactorTruncated).exists_insertion normalizer hfactorWeight
          hfactorTruncated

/--
A structured active-layer More3 route schedule supplies the complete
filtration-recursive semantic insertion step.
-/
def recSemanticInsertion
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (schedule :
      TRRouteb
        (n := n) (inputWeight := inputWeight) H) :
    RIStep
      (n := n) (inputWeight := inputWeight) H :=
  RIStep.insertion_branch
    schedule.insertionBranch

end TRRouteb

namespace TSInput

/--
A correctly sourced repeated block and an active-layer resolution factory
construct the Claim 5 polynomial data.
-/
theorem activeResolutionFactory
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
    (factory :
      SRFtryb
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.recursiveSemanticInsertion
    hn H hH hsourceSupported factory.recSemanticInsertion
      hinputWeight

/--
A correctly sourced repeated block and a structured active-layer More3 route
schedule construct the Claim 5 polynomial data.
-/
theorem activeRouteSchedule
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
      TRRouteb
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.recursiveSemanticInsertion
    hn H hH hsourceSupported schedule.recSemanticInsertion
      hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from ActiveLayerRouting.lean

/-!
# Splitting active-layer symbolic Hall power routing

Resolving one active-weight insertion has two independent parts:

* update the normalized block in the active Hall-weight stratum; and
* move the inserted factor left across the old strictly higher tail, leaving
  a residual source supported in the next stratum.

This file proves that these two witnesses compose to an active-layer
resolution.  It also packages a More3-style certificate for the higher-tail
route and derives the complete filtration-recursive Claim 5 adapter.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

open scoped IsMulCommutative

universe u

/--
The same-stratum part of an active insertion: absorb one active-weight factor
into the normalized active coordinate block.
-/
structure SemanticActiveResolution
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight) where
  activeCoordinates :
    CCExpans H inputWeight
  active_terms_below :
    activeCoordinates.NTBelow lowerWeight
  list_eval_active :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q
          (activeCoordinates.weightFactors lowerWeight) =
        SPFactora.listEval (n := n) q
          (coordinates.weightFactors lowerWeight ++ [factor])

/--
The higher-tail part of an active insertion: move the inserted active factor
left across the old higher tail and retain only a next-stratum residual source.
-/
structure TruncatedHigherResolution
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast (lowerWeight + 1) higherSource
  factor_append_source :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q ([factor] ++ higherSource) =
        SPFactora.listEval (n := n) q
          (coordinates.tailFactors (n := n) lowerWeight ++ [factor])

namespace TAResolua

/--
An active block update and a higher-tail route compose to the active-layer
resolution required by canonical tail splicing.
-/
def activeHigherTail
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {coordinates : CCExpans H inputWeight}
    {factor : SPFactora H inputWeight}
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (block :
      SemanticActiveResolution
        (n := n) (lowerWeight := lowerWeight) H coordinates factor)
    (tail :
      TruncatedHigherResolution
        (n := n) (lowerWeight := lowerWeight) H coordinates factor) :
    TAResolua
      (n := n) (lowerWeight := lowerWeight) H coordinates factor where
  activeCoordinates := block.activeCoordinates
  active_terms_below :=
    block.active_terms_below
  higherSource := tail.higherSource
  higher_source_truncated := tail.higher_source_truncated
  higher_least_succ :=
    tail.higher_least_succ
  active_append_source := by
    have hlowerWeightPos : 1 ≤ lowerWeight := by
      have hfactorPos := SPFactora.word_weight_pos factor
      omega
    have hlowerWeightCutoff : lowerWeight ≤ n - 1 := by
      omega
    intro q
    calc
      SPFactora.listEval (n := n) q
            (block.activeCoordinates.weightFactors lowerWeight ++
              tail.higherSource) =
          SPFactora.listEval q
              (block.activeCoordinates.weightFactors lowerWeight) *
            SPFactora.listEval q tail.higherSource := by
              rw [SPFactora.listEval_append]
      _ =
          SPFactora.listEval q
              (coordinates.weightFactors lowerWeight ++ [factor]) *
            SPFactora.listEval q tail.higherSource := by
              rw [block.list_eval_active q]
      _ =
          SPFactora.listEval q
              (coordinates.weightFactors lowerWeight) *
            SPFactora.listEval q
              ([factor] ++ tail.higherSource) := by
              simp [SPFactora.listEval_append, mul_assoc]
      _ =
          SPFactora.listEval q
              (coordinates.weightFactors lowerWeight) *
            SPFactora.listEval q
              (coordinates.tailFactors (n := n) lowerWeight ++ [factor]) := by
              rw [tail.factor_append_source q]
      _ =
          SPFactora.listEval q
            (coordinates.weightFactors lowerWeight ++
              coordinates.tailFactors (n := n) lowerWeight ++ [factor]) := by
              simp [SPFactora.listEval_append]
      _ =
          SPFactora.listEval q
            (coordinates.factors (n := n) ++ [factor]) := by
              rw [coordinates.append_no_below
                hcoordinates hlowerWeightPos hlowerWeightCutoff]

end TAResolua

/--
A list-valued More3 certificate for routing one active factor across the old
higher tail.
-/
structure STRoute
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_least_succ :
    SPFactora.WordWeightLeast (lowerWeight + 1) higherSource
  inserts :
    SSInsertc
      (n := n) H inputWeight lowerWeight
        (coordinates.tailFactors (n := n) lowerWeight) factor
          ([factor] ++ higherSource)

namespace STRoute

/-- A More3 higher-tail route supplies its semantic routing resolution. -/
def higherTailResolution
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {coordinates : CCExpans H inputWeight}
    {factor : SPFactora H inputWeight}
    (route :
      STRoute
        (n := n) (lowerWeight := lowerWeight) H coordinates factor)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TruncatedHigherResolution
      (n := n) (lowerWeight := lowerWeight) H coordinates factor where
  higherSource := route.higherSource
  higher_source_truncated := by
    have hlowerWeightCutoff : lowerWeight ≤ n - 1 := by
      omega
    have houtput :
        SPFactora.IsTruncated n ([factor] ++ route.higherSource) :=
      route.inserts.isTruncated
        (coordinates.truncated_factors hlowerWeightCutoff)
          hfactorTruncated
    intro x hx
    exact houtput x (List.mem_append_right _ hx)
  higher_least_succ :=
    route.higher_least_succ
  factor_append_source :=
    route.inserts.listEval_eq

/-- If the old higher tail is empty, its More3 route emits no residuals. -/
def tail_factors
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight)
    (htail :
      coordinates.tailFactors (n := n) lowerWeight = []) :
    STRoute
      (n := n) (lowerWeight := lowerWeight) H coordinates factor where
  higherSource := []
  higher_least_succ := by
    intro x hx
    simp at hx
  inserts := by
    simpa [htail] using
      (SSInsertc.nil
        (n := n) (lowerWeight := lowerWeight) factor)

end STRoute

/-- A supply of same-stratum active-block updates. -/
structure ActiveResolutionFactory
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) where
  resolve :
    ∀ (lowerWeight : ℕ)
      (coordinates : CCExpans H inputWeight)
      (factor : SPFactora H inputWeight),
      coordinates.NTBelow lowerWeight →
      factor.word.weight PEAddres.weight = lowerWeight →
      factor.word.weight PEAddres.weight < n →
        SemanticActiveResolution
          (n := n) (lowerWeight := lowerWeight) H coordinates factor

/--
A recursive More3-style schedule for routing an active factor across the old
strictly higher endpoint tail.
-/
structure RHRoute
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) where
  route :
    ∀ lowerWeight : ℕ,
      TSNormalb
          (n := n) (inputWeight := inputWeight)
            (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CCExpans H inputWeight)
          (factor : SPFactora H inputWeight),
          coordinates.NTBelow lowerWeight →
          factor.word.weight PEAddres.weight = lowerWeight →
          factor.word.weight PEAddres.weight < n →
            STRoute
              (n := n) (lowerWeight := lowerWeight) H coordinates factor

namespace RHRoute

open TAResolua

/--
Same-stratum active-block updates and More3 higher-tail routes supply the
residual active insertion branch.
-/
def insertionBranch
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (schedule :
      RHRoute
        (n := n) (inputWeight := inputWeight) H)
    (blockFactory :
      ActiveResolutionFactory
        (n := n) (inputWeight := inputWeight) H) :
    TruncatedInsertionBranch
      (n := n) (inputWeight := inputWeight) H where
  insert lowerWeight normalizer coordinates factor hcoordinates hfactorWeight
      hfactorTruncated :=
    (activeHigherTail
      hcoordinates hfactorWeight hfactorTruncated
        (blockFactory.resolve lowerWeight coordinates factor hcoordinates
          hfactorWeight hfactorTruncated)
        ((schedule.route lowerWeight normalizer coordinates factor hcoordinates
          hfactorWeight hfactorTruncated).higherTailResolution hfactorWeight
            hfactorTruncated)).exists_insertion normalizer hfactorWeight
              hfactorTruncated

/--
Same-stratum active-block updates and More3 higher-tail routes supply the
complete filtration-recursive semantic insertion step.
-/
def recSemanticInsertion
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (schedule :
      RHRoute
        (n := n) (inputWeight := inputWeight) H)
    (blockFactory :
      ActiveResolutionFactory
        (n := n) (inputWeight := inputWeight) H) :
    RIStep
      (n := n) (inputWeight := inputWeight) H :=
  RIStep.insertion_branch
    (schedule.insertionBranch blockFactory)

end RHRoute

namespace TSInput

/--
A correctly sourced repeated block, same-stratum block updates, and More3
higher-tail routes construct the Claim 5 polynomial data.
-/
theorem resolutionFactoryHigher
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
    (blockFactory :
      ActiveResolutionFactory
        (n := n) (inputWeight := inputWeight) H)
    (schedule :
      RHRoute
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.recursiveSemanticInsertion
    hn H hH hsourceSupported
      (schedule.recSemanticInsertion blockFactory)
        hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from ActiveLayerResidualRouting.lean

/-!
# Residual routing inside an active symbolic Hall power layer

Absorbing one active-weight factor into a normalized coordinate block may
itself emit strictly higher corrections.  Thus the honest active-layer split
has two residual sources:

* an active-block residual produced while normalizing the current stratum; and
* a higher-tail residual produced while moving the inserted factor left across
  the old tail.

Both residuals start in the next support stratum.  Their concatenation can be
delegated to the next-stratum normalizer and spliced above the updated active
block.  This file proves that composition and packages More3-style route
certificates for the active-block part.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
Normalize one active-weight factor against the current coordinate block,
retaining a strictly higher residual source.
-/
structure TAResolu
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight) where
  activeCoordinates :
    CCExpans H inputWeight
  active_terms_below :
    activeCoordinates.NTBelow lowerWeight
  higherSource :
    List (SPFactora H inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast (lowerWeight + 1) higherSource
  active_append_source :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q
          (activeCoordinates.weightFactors lowerWeight ++ higherSource) =
        SPFactora.listEval (n := n) q
          (coordinates.weightFactors lowerWeight ++ [factor])

namespace TAResolu

/-- A pure active-block update is the special case with no higher residual. -/
def activeResolution
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {coordinates : CCExpans H inputWeight}
    {factor : SPFactora H inputWeight}
    (block :
      SemanticActiveResolution
        (n := n) (lowerWeight := lowerWeight) H coordinates factor) :
    TAResolu
      (n := n) (lowerWeight := lowerWeight) H coordinates factor where
  activeCoordinates := block.activeCoordinates
  active_terms_below :=
    block.active_terms_below
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_least_succ := by
    intro x hx
    simp at hx
  active_append_source := by
    intro q
    simpa using block.list_eval_active q

end TAResolu

namespace TAResolua

/--
An active-block residual and a higher-tail residual compose to the complete
active-layer resolution consumed by canonical tail splicing.
-/
def active_block_tail
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {coordinates : CCExpans H inputWeight}
    {factor : SPFactora H inputWeight}
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (block :
      TAResolu
        (n := n) (lowerWeight := lowerWeight) H coordinates factor)
    (tail :
      TruncatedHigherResolution
        (n := n) (lowerWeight := lowerWeight) H coordinates factor) :
    TAResolua
      (n := n) (lowerWeight := lowerWeight) H coordinates factor where
  activeCoordinates := block.activeCoordinates
  active_terms_below :=
    block.active_terms_below
  higherSource := block.higherSource ++ tail.higherSource
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact block.higher_source_truncated x hx
    · exact tail.higher_source_truncated x hx
  higher_least_succ := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact block.higher_least_succ x hx
    · exact tail.higher_least_succ x hx
  active_append_source := by
    have hlowerWeightPos : 1 ≤ lowerWeight := by
      have hfactorPos := SPFactora.word_weight_pos factor
      omega
    have hlowerWeightCutoff : lowerWeight ≤ n - 1 := by
      omega
    intro q
    calc
      SPFactora.listEval (n := n) q
            (block.activeCoordinates.weightFactors lowerWeight ++
              (block.higherSource ++ tail.higherSource)) =
          SPFactora.listEval q
              (block.activeCoordinates.weightFactors lowerWeight ++
                block.higherSource) *
            SPFactora.listEval q tail.higherSource := by
              simp [SPFactora.listEval_append, mul_assoc]
      _ =
          SPFactora.listEval q
              (coordinates.weightFactors lowerWeight ++ [factor]) *
            SPFactora.listEval q tail.higherSource := by
              rw [block.active_append_source q]
      _ =
          SPFactora.listEval q
              (coordinates.weightFactors lowerWeight) *
            SPFactora.listEval q
              ([factor] ++ tail.higherSource) := by
              simp [SPFactora.listEval_append, mul_assoc]
      _ =
          SPFactora.listEval q
              (coordinates.weightFactors lowerWeight) *
            SPFactora.listEval q
              (coordinates.tailFactors (n := n) lowerWeight ++ [factor]) := by
              rw [tail.factor_append_source q]
      _ =
          SPFactora.listEval q
            (coordinates.weightFactors lowerWeight ++
              coordinates.tailFactors (n := n) lowerWeight ++ [factor]) := by
              simp [SPFactora.listEval_append]
      _ =
          SPFactora.listEval q
            (coordinates.factors (n := n) ++ [factor]) := by
              rw [coordinates.append_no_below
                hcoordinates hlowerWeightPos hlowerWeightCutoff]

end TAResolua

/--
A list-valued More3 certificate for normalizing one active-weight factor
against the current coordinate block.
-/
structure TSRouteb
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight) where
  activeCoordinates :
    CCExpans H inputWeight
  active_terms_below :
    activeCoordinates.NTBelow lowerWeight
  higherSource :
    List (SPFactora H inputWeight)
  higher_least_succ :
    SPFactora.WordWeightLeast (lowerWeight + 1) higherSource
  inserts :
    SSInsertc
      (n := n) H inputWeight lowerWeight
        (coordinates.weightFactors lowerWeight) factor
          (activeCoordinates.weightFactors lowerWeight ++ higherSource)

namespace TSRouteb

/-- An active-block More3 route supplies its semantic residual resolution. -/
def activeBlockResolution
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {coordinates : CCExpans H inputWeight}
    {factor : SPFactora H inputWeight}
    (route :
      TSRouteb
        (n := n) (lowerWeight := lowerWeight) H coordinates factor)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TAResolu
      (n := n) (lowerWeight := lowerWeight) H coordinates factor where
  activeCoordinates := route.activeCoordinates
  active_terms_below :=
    route.active_terms_below
  higherSource := route.higherSource
  higher_source_truncated := by
    have hblock :
        SPFactora.IsTruncated n
          (coordinates.weightFactors lowerWeight) := by
      intro x hx
      rw [coordinates.word_weight_factors hx]
      omega
    have houtput :
        SPFactora.IsTruncated n
          (route.activeCoordinates.weightFactors lowerWeight ++
            route.higherSource) :=
      route.inserts.isTruncated hblock hfactorTruncated
    intro x hx
    exact houtput x (List.mem_append_right _ hx)
  higher_least_succ :=
    route.higher_least_succ
  active_append_source :=
    route.inserts.listEval_eq

end TSRouteb

/--
A recursive More3-style schedule for normalizing one active factor against
the current coordinate block.
-/
structure TRScheda
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) where
  route :
    ∀ lowerWeight : ℕ,
      TSNormalb
          (n := n) (inputWeight := inputWeight)
            (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CCExpans H inputWeight)
          (factor : SPFactora H inputWeight),
          coordinates.NTBelow lowerWeight →
          factor.word.weight PEAddres.weight = lowerWeight →
          factor.word.weight PEAddres.weight < n →
            TSRouteb
              (n := n) (lowerWeight := lowerWeight) H coordinates factor

namespace TRScheda

open TAResolua

/--
Active-block residual routes and higher-tail routes supply the residual active
insertion branch.
-/
def insertionBranch
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (blockSchedule :
      TRScheda
        (n := n) (inputWeight := inputWeight) H)
    (tailSchedule :
      RHRoute
        (n := n) (inputWeight := inputWeight) H) :
    TruncatedInsertionBranch
      (n := n) (inputWeight := inputWeight) H where
  insert lowerWeight normalizer coordinates factor hcoordinates hfactorWeight
      hfactorTruncated := by
    let blockRoute :=
      blockSchedule.route lowerWeight normalizer coordinates factor
        hcoordinates hfactorWeight hfactorTruncated
    let tailRoute :=
      tailSchedule.route lowerWeight normalizer coordinates factor
        hcoordinates hfactorWeight hfactorTruncated
    exact
      (active_block_tail hcoordinates hfactorWeight
        hfactorTruncated
          (blockRoute.activeBlockResolution hfactorWeight
            hfactorTruncated)
          (tailRoute.higherTailResolution hfactorWeight
            hfactorTruncated)).exists_insertion normalizer hfactorWeight
              hfactorTruncated

/--
Active-block residual routes and higher-tail routes supply the complete
filtration-recursive semantic insertion step.
-/
def recSemanticInsertion
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (blockSchedule :
      TRScheda
        (n := n) (inputWeight := inputWeight) H)
    (tailSchedule :
      RHRoute
        (n := n) (inputWeight := inputWeight) H) :
    RIStep
      (n := n) (inputWeight := inputWeight) H :=
  RIStep.insertion_branch
    (blockSchedule.insertionBranch tailSchedule)

end TRScheda

namespace TSInput

/--
A correctly sourced repeated block plus the two More3 active-layer route
schedules construct the Claim 5 polynomial data.
-/
theorem activeRouteSchedules
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
    (blockSchedule :
      TRScheda
        (n := n) (inputWeight := inputWeight) H)
    (tailSchedule :
      RHRoute
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.recursiveSemanticInsertion
    hn H hH hsourceSupported
      (blockSchedule.recSemanticInsertion tailSchedule)
        hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from ActiveBlockTerminalResolution.lean

/-!
# Terminal active-block resolutions for symbolic Hall powers

In the commutative high-weight range `n ≤ 2 * lowerWeight`, one active factor
can be semantically Hall-normalized and merged into the current active
coordinate block.  Any higher Hall coordinates introduced by that semantic
normal form become a residual source in the next stratum.

The filtration recursion already uses a direct terminal normalizer in this
range.  The result here is nevertheless useful: it verifies the residual
active-block interface against the known terminal semantics and isolates the
precise construction that a nonterminal symbolic collector must generalize.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace TAResolu

/--
In the high-weight terminal range, semantically normalize one active factor,
merge its active coordinate block, and retain its strictly higher Hall tail as
the residual source.
-/
noncomputable def of_highWeight
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hcutoff : n ≤ 2 * lowerWeight)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight)
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TAResolu
      (n := n) (lowerWeight := lowerWeight) H coordinates factor := by
  let X := factor.normalCoordinateExpansions hn H hH
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    have hfactorPos := SPFactora.word_weight_pos factor
    omega
  have hlowerWeightCutoff : lowerWeight ≤ n - 1 := by
    omega
  have hXSupport : X.NTBelow lowerWeight := by
    exact factor.no_terms_expansions hn H hH
      (by omega)
  have hmerge :
      TSRwa (n := n)
        (coordinates.weightFactors lowerWeight ++ X.weightFactors lowerWeight)
        ((coordinates.add X).weightFactors lowerWeight) := by
    apply coordinates.append_rewrites_add
    intro B hB A hA
    rw [coordinates.word_weight_factors hB,
      X.word_weight_factors hA]
    omega
  refine
    { activeCoordinates := coordinates.add X
      active_terms_below := hcoordinates.add hXSupport
      higherSource := X.tailFactors (n := n) lowerWeight
      higher_source_truncated := X.truncated_factors hlowerWeightCutoff
      higher_least_succ :=
        X.word_least_factors
      active_append_source := ?_ }
  intro q
  calc
    SPFactora.listEval (n := n) q
          ((coordinates.add X).weightFactors lowerWeight ++
            X.tailFactors (n := n) lowerWeight) =
        SPFactora.listEval q
            ((coordinates.add X).weightFactors lowerWeight) *
          SPFactora.listEval q
            (X.tailFactors (n := n) lowerWeight) := by
              rw [SPFactora.listEval_append]
    _ =
        SPFactora.listEval q
            (coordinates.weightFactors lowerWeight ++ X.weightFactors lowerWeight) *
          SPFactora.listEval q
            (X.tailFactors (n := n) lowerWeight) := by
              rw [hmerge.listEval_eq q]
    _ =
        SPFactora.listEval q
            (coordinates.weightFactors lowerWeight) *
          SPFactora.listEval q
            (X.weightFactors lowerWeight ++
              X.tailFactors (n := n) lowerWeight) := by
              simp [SPFactora.listEval_append, mul_assoc]
    _ =
        SPFactora.listEval q
            (coordinates.weightFactors lowerWeight) *
          SPFactora.listEval q (X.factors (n := n)) := by
              rw [X.append_no_below
                hXSupport hlowerWeightPos hlowerWeightCutoff]
    _ =
        SPFactora.listEval q
            (coordinates.weightFactors lowerWeight) *
          factor.eval (n := n) q := by
              rw [SPFactora.list_coordinate_expansions
                hn H hH factor hfactorTruncated (by omega) q]
    _ =
        SPFactora.listEval q
          (coordinates.weightFactors lowerWeight ++ [factor]) := by
            simp [SPFactora.listEval_append]

end TAResolu

end TCTex
end Submission

-- Merged from ActiveBlockGradedUpdate.lean

/-!
# Associated-graded active-block updates for symbolic Hall powers

Outside the terminal class-two range, semantically Hall-normalizing one active
factor need not yet provide an explicit bounded expansion of every higher
correction.  Its active-weight coordinates are nevertheless canonical: add the
factor's semantic Hall-coordinate expansion to the current coordinate block.

This file proves that the resulting active block differs from the old active
block followed by the inserted factor by an element of the next lower-central
stratum.  Thus the remaining symbolic collection problem is precisely to
expand that higher residual by bounded recipes.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
Taking an integer power multiplies the Hall coordinates in the first
nonvanishing lower-central layer by that integer.
-/
lemma form_coordinates_zpow
    {d n r : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hr : 1 ≤ r)
    (hrn : r < n)
    (y : LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
    (hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n) (r - 1))
    (z : ℤ) :
    normalFormCoordinates hn H hH (y ^ z) r =
      fun i => z * normalFormCoordinates hn H hH y r i := by
  obtain ⟨e, he⟩ :=
    (H r).existscollected_weigprodinv_mulmemnext (hH r hr hrn) hy
  have hcoordinates :
      normalFormCoordinates hn H hH y r = e :=
    form_coordinates_next
      hn H hH hr hrn y hy e he
  let ez : (H r).index → ℤ := fun i => z * e i
  let N : Type u := LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  let A : Subgroup N := Subgroup.lowerCentralSeries N (r - 1)
  let B : Subgroup A := (Subgroup.lowerCentralSeries N r).subgroupOf A
  let quotientMap : A →* A ⧸ B := QuotientGroup.mk' B
  letI : IsMulCommutative (AssociatedGradedLayer N r) :=
    associated_graded_commutative r
  letI : CommGroup (AssociatedGradedLayer N r) :=
    { (inferInstance : Group (AssociatedGradedLayer N r)) with
      mul_comm := mul_comm' }
  let yTerm : A := ⟨y, hy⟩
  let eTerm : A := (H r).collected_lower_centralterm (n := n) e
  let ezTerm : A := (H r).collected_lower_centralterm (n := n) ez
  have heClass : quotientMap eTerm = quotientMap yTerm := by
    have hone :
        quotientMap (eTerm⁻¹ * yTerm) = 1 :=
      (QuotientGroup.eq_one_iff (N := B) (eTerm⁻¹ * yTerm)).mpr he
    rw [map_mul, map_inv] at hone
    exact inv_mul_eq_one.mp hone
  have hezClass : quotientMap ezTerm = quotientMap (eTerm ^ z) := by
    rw [(H r).collectedlower_centtermclas_eqmulsum (n := n) ez,
      map_zpow,
      (H r).collectedlower_centtermclas_eqmulsum (n := n) e]
    have hsum :
        (∑ i, ez i • ((H r).commutator i).associatedGradedClass (n := n)) =
          z • ∑ i, e i • ((H r).commutator i).associatedGradedClass (n := n) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      simp [ez, mul_smul]
    rw [hsum]
    change
      Additive.toMul
          (z •
            ∑ i, e i • ((H r).commutator i).associatedGradedClass (n := n)) =
        Additive.toMul
            (∑ i, e i • ((H r).commutator i).associatedGradedClass (n := n)) ^ z
    rw [toMul_zsmul]
  have hezYClass : quotientMap ezTerm = quotientMap (yTerm ^ z) := by
    rw [hezClass, map_zpow, heClass, ← map_zpow]
  have hezY :
      ((H r).collectedWeightProduct (n := n) ez)⁻¹ * y ^ z ∈
        Subgroup.lowerCentralSeries N r := by
    apply (QuotientGroup.eq_one_iff (N := B) (ezTerm⁻¹ * yTerm ^ z)).mp
    change quotientMap (ezTerm⁻¹ * yTerm ^ z) = 1
    rw [map_mul, map_inv, hezYClass, inv_mul_cancel]
  have hzCoordinates :
      normalFormCoordinates hn H hH (y ^ z) r = ez :=
    form_coordinates_next
      hn H hH hr hrn (y ^ z)
        ((Subgroup.lowerCentralSeries N (r - 1)).zpow_mem hy z)
        ez hezY
  rw [hzCoordinates, hcoordinates]

namespace CCExpans

/-- Read the Hall coordinates represented by one normalized symbolic layer. -/
lemma form_coordinates_factors
    {d n inputWeight r : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (R : CCExpans H inputWeight)
    (hr : 1 ≤ r)
    (hrn : r < n)
    (q : ℕ) :
    normalFormCoordinates hn H hH
        (SPFactora.listEval (n := n) q (R.weightFactors r)) r =
      R.eval q r := by
  rw [R.list_weight_factors]
  apply form_coordinates_next
    hn H hH hr hrn
  · exact (H r).collectedweight_productmem_lowecentseri (R.eval q r)
  · simp

/--
Canonically update one active Hall-coordinate block by adding the semantic
Hall-coordinate expansion of the inserted factor.
-/
noncomputable def activeBlockUpdate
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight) :
    CCExpans H inputWeight :=
  coordinates.add (factor.normalCoordinateExpansions hn H hH)

/-- The canonical active-block update introduces no lower coordinate terms. -/
lemma update_no_below
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight)
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hfactorWeight :
      lowerWeight ≤ factor.word.weight PEAddres.weight) :
    (activeBlockUpdate hn H hH coordinates factor).NTBelow
      lowerWeight :=
  hcoordinates.add
    (factor.no_terms_expansions hn H hH hfactorWeight)

/--
The canonical active-block update and the old active block followed by the
inserted factor have identical active-layer Hall coordinates.  Equivalently,
their quotient lies in the next lower-central stratum.
-/
lemma active_update_series
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (q : ℕ) :
    (SPFactora.listEval (n := n) q
        ((activeBlockUpdate hn H hH coordinates factor).weightFactors
          lowerWeight))⁻¹ *
      SPFactora.listEval q
        (coordinates.weightFactors lowerWeight ++ [factor]) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        lowerWeight := by
  let X := factor.normalCoordinateExpansions hn H hH
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    have hfactorPos := factor.word_weight_pos
    omega
  have hfactorWordMem :
      factor.wordValue (n := n) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (lowerWeight - 1) := by
    simpa [hfactorWeight] using factor.value_lower_series (n := n)
  have hfactorMem :
      factor.eval (n := n) q ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (lowerWeight - 1) := by
    simpa [hfactorWeight] using factor.eval_lower_series (n := n) q
  have hcoordinatesMem :
      SPFactora.listEval (n := n) q
          (coordinates.weightFactors lowerWeight) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (lowerWeight - 1) := by
    rw [coordinates.list_weight_factors]
    exact
      (H lowerWeight).collectedweight_productmem_lowecentseri
        (coordinates.eval q lowerWeight)
  have hupdateMem :
      SPFactora.listEval (n := n) q
          ((activeBlockUpdate hn H hH coordinates factor).weightFactors
            lowerWeight) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (lowerWeight - 1) := by
    rw [(activeBlockUpdate hn H hH coordinates factor).list_weight_factors]
    exact
      (H lowerWeight).collectedweight_productmem_lowecentseri
        ((activeBlockUpdate hn H hH coordinates factor).eval q
          lowerWeight)
  have hsourceMem :
      SPFactora.listEval (n := n) q
          (coordinates.weightFactors lowerWeight ++ [factor]) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (lowerWeight - 1) := by
    rw [SPFactora.listEval_append]
    exact
      (Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (lowerWeight - 1)).mul_mem hcoordinatesMem
          (by simpa [SPFactora.listEval] using hfactorMem)
  apply inv_form_coordinates
    hn H hH hlowerWeightPos (by omega) _ _ hupdateMem hsourceMem
  have hsingleton :
      SPFactora.listEval (n := n) q [factor] = factor.eval q := by
    simp [SPFactora.listEval]
  rw [SPFactora.listEval_append, hsingleton]
  rw [normal_form_coordinates
    hn H hH hlowerWeightPos (by omega) _ _ hcoordinatesMem hfactorMem]
  rw [form_coordinates_factors
    hn H hH (activeBlockUpdate hn H hH coordinates factor)
      hlowerWeightPos (by omega) q]
  rw [coordinates.form_coordinates_factors
    hn H hH hlowerWeightPos (by omega) q]
  have hfactorCoordinates :
      normalFormCoordinates hn H hH (factor.eval (n := n) q) lowerWeight =
        X.eval q lowerWeight := by
    change
      normalFormCoordinates hn H hH
          ((factor.wordValue (n := n)) ^ factor.exponent q) lowerWeight =
        X.eval q lowerWeight
    rw [form_coordinates_zpow
      hn H hH hlowerWeightPos (by omega) _ hfactorWordMem]
    rw [factor.normal_coordinate_expansions
      hn H hH q lowerWeight hlowerWeightPos (by omega)]
    funext i
    simp [zscaledExponentFamily]
    ring
  rw [hfactorCoordinates]
  simp only [activeBlockUpdate, eval_add, X]
  rfl

end CCExpans

end TCTex
end Submission

-- Merged from ActiveBlockResidualExpansion.lean

/-!
# Explicit higher residuals for active symbolic Hall power blocks

The canonical associated-graded active-block update leaves one discrepancy in
the next lower-central stratum.  A nonterminal symbolic Hall collector must do
more than prove that filtration statement: it must expand the discrepancy as a
finite list of bounded symbolic packet families supported in the next weight
stratum.

This file packages exactly that remaining output.  Such an expansion supplies
the active-block residual resolution consumed by the filtration recursion.
The terminal high-weight collector is recorded as a concrete instance.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace CCExpans

/--
The exact higher residual left after the canonical active-block update.
-/
noncomputable def activeResidualValue
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight)
    (lowerWeight q : ℕ) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  (SPFactora.listEval (n := n) q
      ((coordinates.activeBlockUpdate hn H hH factor).weightFactors
        lowerWeight))⁻¹ *
    SPFactora.listEval q
      (coordinates.weightFactors lowerWeight ++ [factor])

/-- The canonical active-block residual starts in the next support stratum. -/
lemma active_value_series
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (q : ℕ) :
    coordinates.activeResidualValue hn H hH factor
        lowerWeight q ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        lowerWeight :=
  coordinates.active_update_series
    hn H hH factor hfactorWeight hfactorTruncated q

end CCExpans

/--
An explicit bounded symbolic expansion of the canonical higher residual left
by one active-block update.
-/
structure TAExp
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast (lowerWeight + 1) higherSource
  list_higher_value :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        coordinates.activeResidualValue hn H hH factor
          lowerWeight q

namespace TAExp

/-- An explicit residual expansion evaluates inside the next lower-central stratum. -/
lemma list_higher_series
    {d n inputWeight lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {coordinates : CCExpans H inputWeight}
    {factor : SPFactora H inputWeight}
    (expansion :
      TAExp
        (lowerWeight := lowerWeight) hn H hH coordinates factor)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (q : ℕ) :
    SPFactora.listEval (n := n) q expansion.higherSource ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        lowerWeight := by
  rw [expansion.list_higher_value]
  exact
    coordinates.active_value_series
      hn H hH factor hfactorWeight hfactorTruncated q

/--
An explicit canonical residual expansion supplies the active-block residual
resolution consumed by the next-stratum normalizer.
-/
noncomputable def activeBlockResolution
    {d n inputWeight lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {coordinates : CCExpans H inputWeight}
    {factor : SPFactora H inputWeight}
    (expansion :
      TAExp
        (lowerWeight := lowerWeight) hn H hH coordinates factor)
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight) :
    TAResolu
      (n := n) (lowerWeight := lowerWeight) H coordinates factor where
  activeCoordinates :=
    coordinates.activeBlockUpdate hn H hH factor
  active_terms_below :=
    coordinates.update_no_below
      hn H hH factor hcoordinates (by omega)
  higherSource := expansion.higherSource
  higher_source_truncated := expansion.higher_source_truncated
  higher_least_succ :=
    expansion.higher_least_succ
  active_append_source := by
    intro q
    rw [SPFactora.listEval_append,
      expansion.list_higher_value]
    unfold CCExpans.activeResidualValue
    group

/--
In the terminal high-weight range, the semantic Hall tail is an explicit
canonical residual expansion.
-/
noncomputable def of_highWeight
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hcutoff : n ≤ 2 * lowerWeight)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight)
    (hcoordinates : coordinates.NTBelow lowerWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TAExp
      (lowerWeight := lowerWeight) hn H hH coordinates factor := by
  let block :=
    TAResolu.of_highWeight
      (n := n) hn H hH hcutoff coordinates factor hcoordinates hfactorWeight
        hfactorTruncated
  refine
    { higherSource := block.higherSource
      higher_source_truncated := block.higher_source_truncated
      higher_least_succ :=
        block.higher_least_succ
      list_higher_value := ?_ }
  intro q
  change
    SPFactora.listEval (n := n) q block.higherSource =
      (SPFactora.listEval q
          (block.activeCoordinates.weightFactors lowerWeight))⁻¹ *
        SPFactora.listEval q
          (coordinates.weightFactors lowerWeight ++ [factor])
  rw [← block.active_append_source q,
    SPFactora.listEval_append]
  group

end TAExp

/-- A supply of canonical bounded higher-residual expansions. -/
structure SSFtry
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) where
  expand :
    ∀ (lowerWeight : ℕ)
      (coordinates : CCExpans H inputWeight)
      (factor : SPFactora H inputWeight),
      coordinates.NTBelow lowerWeight →
      factor.word.weight PEAddres.weight = lowerWeight →
      factor.word.weight PEAddres.weight < n →
        TAExp
          (lowerWeight := lowerWeight) hn H hH coordinates factor

namespace SSFtry

open TAResolua

/--
Canonical active-block residual expansions and higher-tail routes supply the
residual active insertion branch.
-/
noncomputable def insertionBranch
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (factory :
      SSFtry
        (n := n) (inputWeight := inputWeight) hn H hH)
    (tailSchedule :
      RHRoute
        (n := n) (inputWeight := inputWeight) H) :
    TruncatedInsertionBranch
      (n := n) (inputWeight := inputWeight) H where
  insert lowerWeight normalizer coordinates factor hcoordinates hfactorWeight
      hfactorTruncated := by
    let block :=
      factory.expand lowerWeight coordinates factor hcoordinates hfactorWeight
        hfactorTruncated
    let tail :=
      (tailSchedule.route lowerWeight normalizer coordinates factor hcoordinates
        hfactorWeight hfactorTruncated).higherTailResolution hfactorWeight
          hfactorTruncated
    exact
      (active_block_tail hcoordinates hfactorWeight
        hfactorTruncated
          (block.activeBlockResolution hcoordinates hfactorWeight)
          tail).exists_insertion normalizer hfactorWeight hfactorTruncated

/--
Canonical active-block residual expansions and higher-tail routes supply the
complete filtration-recursive semantic insertion step.
-/
noncomputable def recSemanticInsertion
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (factory :
      SSFtry
        (n := n) (inputWeight := inputWeight) hn H hH)
    (tailSchedule :
      RHRoute
        (n := n) (inputWeight := inputWeight) H) :
    RIStep
      (n := n) (inputWeight := inputWeight) H :=
  RIStep.insertion_branch
    (factory.insertionBranch tailSchedule)

end SSFtry

namespace TSInput

/--
A correctly sourced repeated block, canonical active-block residual
expansions, and higher-tail routes construct the Claim 5 polynomial data.
-/
theorem coordRouteSchedule
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
    (factory :
      SSFtry
        (n := n) (inputWeight := inputWeight) hn H hH)
    (tailSchedule :
      RHRoute
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.recursiveSemanticInsertion
    hn H hH hsourceSupported
      (factory.recSemanticInsertion tailSchedule)
        hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from ActiveBlockResidualDecomposition.lean

/-!
# Decomposing active-block residuals for symbolic Hall powers

The higher residual left by the canonical active-block update has two
independent causes:

* the old active Hall block and the inserted factor's active Hall block must be
  merged into one coordinatewise sum; and
* the inserted factor may have a Hall-normal tail strictly above its own
  active weight.

This file defines those two residual values, proves their exact product is the
canonical residual, and packages separate bounded symbolic expansions whose
concatenation supplies the active-block residual expansion interface.

In the terminal high-weight range the merge residual is empty and the factor
residual is exactly the semantic Hall tail.  This records a concrete base case
for both halves of a future nonterminal collector.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

namespace CCExpans

/-- The active Hall block of one inserted symbolic factor. -/
noncomputable def activeNormalValue
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factor : SPFactora H inputWeight)
    (lowerWeight q : ℕ) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  SPFactora.listEval (n := n) q
    ((factor.normalCoordinateExpansions hn H hH).weightFactors lowerWeight)

/-- The higher Hall-normalization tail intrinsic to the inserted factor. -/
noncomputable def activeBlockValue
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factor : SPFactora H inputWeight)
    (lowerWeight q : ℕ) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  (activeNormalValue hn H hH factor lowerWeight q)⁻¹ *
    factor.eval q

/--
The higher correction created while merging the old active block with the
inserted factor's active Hall block.
-/
noncomputable def activeMergeValue
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight)
    (lowerWeight q : ℕ) :
    LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n :=
  (SPFactora.listEval (n := n) q
      ((coordinates.activeBlockUpdate hn H hH factor).weightFactors
        lowerWeight))⁻¹ *
    (SPFactora.listEval q
        (coordinates.weightFactors lowerWeight) *
      activeNormalValue hn H hH factor lowerWeight q)

/-- The canonical residual is the product of merge and factor-tail residuals. -/
lemma active_merge_factor
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight)
    (q : ℕ) :
    coordinates.activeResidualValue hn H hH factor
        lowerWeight q =
      coordinates.activeMergeValue hn H hH factor
          lowerWeight q *
        activeBlockValue hn H hH factor lowerWeight q := by
  unfold activeResidualValue
    activeMergeValue
    activeBlockValue
    activeNormalValue
  rw [SPFactora.listEval_append]
  simp only [SPFactora.listEval, List.map_singleton,
    List.prod_singleton]
  group

/-- The intrinsic factor Hall-normalization residual starts in the next stratum. -/
lemma active_block_series
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (q : ℕ) :
    activeBlockValue hn H hH factor lowerWeight q ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        lowerWeight := by
  let X := factor.normalCoordinateExpansions hn H hH
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    have hfactorPos := factor.word_weight_pos
    omega
  have hfactorWordMem :
      factor.wordValue (n := n) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (lowerWeight - 1) := by
    simpa [hfactorWeight] using factor.value_lower_series (n := n)
  have hfactorMem :
      factor.eval (n := n) q ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (lowerWeight - 1) := by
    simpa [hfactorWeight] using factor.eval_lower_series (n := n) q
  have hXMem :
      SPFactora.listEval (n := n) q
          (X.weightFactors lowerWeight) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (lowerWeight - 1) := by
    rw [X.list_weight_factors]
    exact
      (H lowerWeight).collectedweight_productmem_lowecentseri
        (X.eval q lowerWeight)
  unfold activeBlockValue
    activeNormalValue
  apply inv_form_coordinates
    hn H hH hlowerWeightPos (by omega) _ _ hXMem hfactorMem
  rw [X.form_coordinates_factors
    hn H hH hlowerWeightPos (by omega) q]
  have hfactorCoordinates :
      normalFormCoordinates hn H hH (factor.eval (n := n) q) lowerWeight =
        X.eval q lowerWeight := by
    change
      normalFormCoordinates hn H hH
          ((factor.wordValue (n := n)) ^ factor.exponent q) lowerWeight =
        X.eval q lowerWeight
    rw [form_coordinates_zpow
      hn H hH hlowerWeightPos (by omega) _ hfactorWordMem]
    rw [factor.normal_coordinate_expansions
      hn H hH q lowerWeight hlowerWeightPos (by omega)]
    funext i
    simp [zscaledExponentFamily]
    ring
  exact hfactorCoordinates.symm

/-- The active-layer coordinate merge residual starts in the next stratum. -/
lemma active_merge_series
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (q : ℕ) :
    coordinates.activeMergeValue hn H hH factor
        lowerWeight q ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        lowerWeight := by
  let X := factor.normalCoordinateExpansions hn H hH
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    have hfactorPos := factor.word_weight_pos
    omega
  have hcoordinatesMem :
      SPFactora.listEval (n := n) q
          (coordinates.weightFactors lowerWeight) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (lowerWeight - 1) := by
    rw [coordinates.list_weight_factors]
    exact
      (H lowerWeight).collectedweight_productmem_lowecentseri
        (coordinates.eval q lowerWeight)
  have hXMem :
      SPFactora.listEval (n := n) q
          (X.weightFactors lowerWeight) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (lowerWeight - 1) := by
    rw [X.list_weight_factors]
    exact
      (H lowerWeight).collectedweight_productmem_lowecentseri
        (X.eval q lowerWeight)
  have hupdateMem :
      SPFactora.listEval (n := n) q
          ((coordinates.activeBlockUpdate hn H hH factor).weightFactors
            lowerWeight) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (lowerWeight - 1) := by
    rw [list_weight_factors
      (coordinates.activeBlockUpdate hn H hH factor) q lowerWeight]
    exact
      (H lowerWeight).collectedweight_productmem_lowecentseri
        ((coordinates.activeBlockUpdate hn H hH factor).eval q
          lowerWeight)
  unfold activeMergeValue
    activeNormalValue
  apply inv_form_coordinates
    hn H hH hlowerWeightPos (by omega) _ _ hupdateMem
      ((Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (lowerWeight - 1)).mul_mem hcoordinatesMem hXMem)
  rw [normal_form_coordinates
    hn H hH hlowerWeightPos (by omega) _ _ hcoordinatesMem hXMem]
  rw [form_coordinates_factors
    hn H hH (coordinates.activeBlockUpdate hn H hH factor)
      hlowerWeightPos (by omega) q]
  rw [coordinates.form_coordinates_factors
    hn H hH hlowerWeightPos (by omega) q]
  rw [X.form_coordinates_factors
    hn H hH hlowerWeightPos (by omega) q]
  simp only [activeBlockUpdate, eval_add, X]
  rfl

end CCExpans

/-- A bounded symbolic expansion of the intrinsic factor Hall-normal tail. -/
structure TSExp
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factor : SPFactora H inputWeight) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast (lowerWeight + 1) higherSource
  list_factor_value :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        CCExpans.activeBlockValue
          hn H hH factor lowerWeight q

/-- A bounded symbolic expansion of the fixed-weight coordinate merge residual. -/
structure TMExp
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast (lowerWeight + 1) higherSource
  list_merge_value :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q higherSource =
        coordinates.activeMergeValue hn H hH factor
          lowerWeight q

namespace TAExp

/--
Concatenate a coordinate-merge residual expansion and an intrinsic factor-tail
expansion into the complete canonical active-block residual expansion.
-/
def mergeFactor
    {d n inputWeight lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {coordinates : CCExpans H inputWeight}
    {factor : SPFactora H inputWeight}
    (merge :
      TMExp
        (lowerWeight := lowerWeight) hn H hH coordinates factor)
    (factorTail :
      TSExp
        (lowerWeight := lowerWeight) hn H hH factor) :
    TAExp
      (lowerWeight := lowerWeight) hn H hH coordinates factor where
  higherSource := merge.higherSource ++ factorTail.higherSource
  higher_source_truncated := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact merge.higher_source_truncated x hx
    · exact factorTail.higher_source_truncated x hx
  higher_least_succ := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact merge.higher_least_succ x hx
    · exact factorTail.higher_least_succ x hx
  list_higher_value := by
    intro q
    rw [SPFactora.listEval_append,
      merge.list_merge_value,
      factorTail.list_factor_value,
      coordinates.active_merge_factor]

end TAExp

namespace TMExp

/-- In the terminal high-weight range, active Hall blocks merge without a residual. -/
noncomputable def of_highWeight
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hcutoff : n ≤ 2 * lowerWeight)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight) :
    TMExp
      (lowerWeight := lowerWeight) hn H hH coordinates factor := by
  let X := factor.normalCoordinateExpansions hn H hH
  have hmerge :
      TSRwa (n := n)
        (coordinates.weightFactors lowerWeight ++ X.weightFactors lowerWeight)
        ((coordinates.activeBlockUpdate hn H hH factor).weightFactors
          lowerWeight) := by
    apply coordinates.append_rewrites_add
    intro B hB A hA
    rw [coordinates.word_weight_factors hB,
      X.word_weight_factors hA]
    omega
  refine
    { higherSource := []
      higher_source_truncated := by
        intro x hx
        simp at hx
      higher_least_succ := by
        intro x hx
        simp at hx
      list_merge_value := ?_ }
  intro q
  change
    SPFactora.listEval (n := n) q [] =
      (SPFactora.listEval q
          ((coordinates.activeBlockUpdate hn H hH factor).weightFactors
            lowerWeight))⁻¹ *
        (SPFactora.listEval q
            (coordinates.weightFactors lowerWeight) *
          SPFactora.listEval q (X.weightFactors lowerWeight))
  rw [hmerge.listEval_eq q, ← SPFactora.listEval_append]
  simp

end TMExp

namespace TSExp

/-- In the terminal high-weight range, the semantic Hall tail is the factor residual. -/
noncomputable def of_highWeight
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hcutoff : n ≤ 2 * lowerWeight)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSExp
      (lowerWeight := lowerWeight) hn H hH factor := by
  let X := factor.normalCoordinateExpansions hn H hH
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    have hfactorPos := factor.word_weight_pos
    omega
  have hlowerWeightCutoff : lowerWeight ≤ n - 1 := by
    omega
  have hXSupport : X.NTBelow lowerWeight := by
    exact factor.no_terms_expansions hn H hH
      (by omega)
  refine
    { higherSource := X.tailFactors (n := n) lowerWeight
      higher_source_truncated := X.truncated_factors hlowerWeightCutoff
      higher_least_succ :=
        X.word_least_factors
      list_factor_value := ?_ }
  intro q
  change
    SPFactora.listEval (n := n) q
        (X.tailFactors (n := n) lowerWeight) =
      (SPFactora.listEval q (X.weightFactors lowerWeight))⁻¹ *
        factor.eval q
  rw [← SPFactora.list_coordinate_expansions
    hn H hH factor hfactorTruncated (by omega) q]
  rw [X.append_no_below
    hXSupport hlowerWeightPos hlowerWeightCutoff]
  rw [SPFactora.listEval_append]
  group

end TSExp

namespace TAExp

/--
In the terminal high-weight range, the decomposed merge and factor-tail
constructors assemble the complete canonical active-block residual expansion.
-/
noncomputable def high_weight_decomposition
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hcutoff : n ≤ 2 * lowerWeight)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TAExp
      (lowerWeight := lowerWeight) hn H hH coordinates factor :=
  mergeFactor
    (TMExp.of_highWeight
      hn H hH hcutoff coordinates factor)
    (TSExp.of_highWeight
      hn H hH hcutoff factor hfactorWeight hfactorTruncated)

end TAExp

/--
A supply of separately constructed coordinate-merge and factor-tail residual
expansions.
-/
structure TDFtry
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) where
  expandMerge :
    ∀ (lowerWeight : ℕ)
      (coordinates : CCExpans H inputWeight)
      (factor : SPFactora H inputWeight),
      coordinates.NTBelow lowerWeight →
      factor.word.weight PEAddres.weight = lowerWeight →
      factor.word.weight PEAddres.weight < n →
        TMExp
          (lowerWeight := lowerWeight) hn H hH coordinates factor
  expandFactor :
    ∀ (lowerWeight : ℕ)
      (factor : SPFactora H inputWeight),
      factor.word.weight PEAddres.weight = lowerWeight →
      factor.word.weight PEAddres.weight < n →
        TSExp
          (lowerWeight := lowerWeight) hn H hH factor

namespace TDFtry

/-- Separate merge and factor-tail constructors supply complete residual expansions. -/
noncomputable def activeExpansionFactory
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (factory :
      TDFtry
      (n := n) (inputWeight := inputWeight) hn H hH) :
    SSFtry
      (n := n) (inputWeight := inputWeight) hn H hH where
  expand lowerWeight coordinates factor hcoordinates hfactorWeight
      hfactorTruncated :=
    TAExp.mergeFactor
      (factory.expandMerge lowerWeight coordinates factor hcoordinates
        hfactorWeight hfactorTruncated)
      (factory.expandFactor lowerWeight factor hfactorWeight hfactorTruncated)

/--
If every requested active stratum is already in the terminal high-weight
range, the concrete terminal merge and factor-tail constructors supply the
decomposition factory.
-/
noncomputable def of_highWeight
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hcutoff :
      ∀ (lowerWeight : ℕ)
        (factor : SPFactora H inputWeight),
        factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          n ≤ 2 * lowerWeight) :
    TDFtry
      (n := n) (inputWeight := inputWeight) hn H hH where
  expandMerge lowerWeight coordinates factor _hcoordinates hfactorWeight
      hfactorTruncated :=
    TMExp.of_highWeight
      hn H hH (hcutoff lowerWeight factor hfactorWeight hfactorTruncated)
        coordinates factor
  expandFactor lowerWeight factor hfactorWeight hfactorTruncated :=
    TSExp.of_highWeight
      hn H hH (hcutoff lowerWeight factor hfactorWeight hfactorTruncated)
        factor hfactorWeight hfactorTruncated

end TDFtry

namespace TSInput

/--
A correctly sourced repeated block, decomposed active-block residual
constructors, and higher-tail routes construct the Claim 5 polynomial data.
-/
theorem coordDecompHigher
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
    (factory :
      TDFtry
        (n := n) (inputWeight := inputWeight) hn H hH)
    (tailSchedule :
      RHRoute
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.coordRouteSchedule
    hn H hH hsourceSupported factory.activeExpansionFactory
      tailSchedule hinputWeight

/--
Terminal active-block cutoff evidence and higher-tail routes construct the
Claim 5 polynomial data through the concrete decomposed residual expansions.
-/
theorem
  terminalRouteSchedule
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
    (hcutoff :
      ∀ (lowerWeight : ℕ)
        (factor : SPFactora H inputWeight),
        factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          n ≤ 2 * lowerWeight)
    (tailSchedule :
      RHRoute
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.coordDecompHigher
    hn H hH hsourceSupported
      (TDFtry.of_highWeight
        hn H hH hcutoff)
      tailSchedule hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from ActiveBlockResidualRoutes.lean

/-!
# Operational routes for active-block residuals

The canonical active-block residual splits into a fixed-weight coordinate
merge and the higher Hall-normal tail intrinsic to the inserted factor.
This file gives collector-facing route interfaces for those two pieces.

For the merge piece, a route is an actual truncated adjacent-swap rewrite from
the two old fixed-weight Hall blocks to the canonical updated block followed by
strictly heavier corrections.  For the intrinsic factor piece, a route records
an exact semantic normalization into the factor's active Hall layer followed
by a strictly heavier symbolic tail.  Both routes compile to the residual
expansion interfaces consumed by the filtration-recursive Claim 5 reduction.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
An exact semantic route from one inserted factor to its active Hall layer plus
a strictly heavier symbolic tail.
-/
structure TSRoute
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (factor : SPFactora H inputWeight) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_source_truncated :
    SPFactora.IsTruncated n higherSource
  higher_least_succ :
    SPFactora.WordWeightLeast (lowerWeight + 1) higherSource
  active_append_factor :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q
          ((factor.normalCoordinateExpansions hn H hH).weightFactors
            lowerWeight ++ higherSource) =
        factor.eval (n := n) q

namespace TSRoute

/-- A factor normalization route supplies its intrinsic residual expansion. -/
def factorExpansion
    {d n inputWeight lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {factor : SPFactora H inputWeight}
    (route :
      TSRoute
        (lowerWeight := lowerWeight) hn H hH factor) :
    TSExp
      (lowerWeight := lowerWeight) hn H hH factor where
  higherSource := route.higherSource
  higher_source_truncated := route.higher_source_truncated
  higher_least_succ :=
    route.higher_least_succ
  list_factor_value := by
    intro q
    unfold
      CCExpans.activeBlockValue
      CCExpans.activeNormalValue
    rw [← route.active_append_factor q,
      SPFactora.listEval_append]
    group

/-- Every intrinsic residual expansion can be presented as a factor route. -/
def factorResidualExpansion
    {d n inputWeight lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {factor : SPFactora H inputWeight}
    (expansion :
      TSExp
        (lowerWeight := lowerWeight) hn H hH factor) :
    TSRoute
      (lowerWeight := lowerWeight) hn H hH factor where
  higherSource := expansion.higherSource
  higher_source_truncated := expansion.higher_source_truncated
  higher_least_succ :=
    expansion.higher_least_succ
  active_append_factor := by
    intro q
    rw [SPFactora.listEval_append,
      expansion.list_factor_value]
    unfold
      CCExpans.activeBlockValue
      CCExpans.activeNormalValue
    group

/-- The terminal Hall-normal tail constructor also supplies a factor route. -/
noncomputable def of_highWeight
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hcutoff : n ≤ 2 * lowerWeight)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRoute
      (lowerWeight := lowerWeight) hn H hH factor :=
  factorResidualExpansion
    (TSExp.of_highWeight
      hn H hH hcutoff factor hfactorWeight hfactorTruncated)

end TSRoute

/--
An operational fixed-weight merge route.  Its actual truncated rewrite
recollects two normalized active Hall blocks into their coordinatewise sum and
leaves only strictly heavier symbolic corrections.
-/
structure TMRoute
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_least_succ :
    SPFactora.WordWeightLeast (lowerWeight + 1) higherSource
  rewrites :
    TSRwa (n := n)
      (coordinates.weightFactors lowerWeight ++
        (factor.normalCoordinateExpansions hn H hH).weightFactors
          lowerWeight)
      ((coordinates.activeBlockUpdate hn H hH factor).weightFactors
          lowerWeight ++ higherSource)

namespace TMRoute

/-- An operational merge route supplies the fixed-weight merge residual expansion. -/
noncomputable def mergeResidualExpansion
    {d n inputWeight lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {coordinates : CCExpans H inputWeight}
    {factor : SPFactora H inputWeight}
    (route :
      TMRoute
        (lowerWeight := lowerWeight) hn H hH coordinates factor)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TMExp
      (lowerWeight := lowerWeight) hn H hH coordinates factor := by
  let X := factor.normalCoordinateExpansions hn H hH
  have hlowerWeightTruncated : lowerWeight < n := by
    omega
  have hsourceTruncated :
      SPFactora.IsTruncated n
        (coordinates.weightFactors lowerWeight ++ X.weightFactors lowerWeight) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [coordinates.word_weight_factors hx]
      exact hlowerWeightTruncated
    · rw [X.word_weight_factors hx]
      exact hlowerWeightTruncated
  have houtputTruncated :
      SPFactora.IsTruncated n
        ((coordinates.activeBlockUpdate hn H hH factor).weightFactors
            lowerWeight ++ route.higherSource) :=
    route.rewrites.isTruncated hsourceTruncated
  refine
    { higherSource := route.higherSource
      higher_source_truncated := ?_
      higher_least_succ :=
        route.higher_least_succ
      list_merge_value := ?_ }
  · intro x hx
    exact houtputTruncated x (List.mem_append_right _ hx)
  · intro q
    unfold
      CCExpans.activeMergeValue
      CCExpans.activeNormalValue
    change
      SPFactora.listEval (n := n) q route.higherSource =
        (SPFactora.listEval q
            ((coordinates.activeBlockUpdate hn H hH factor).weightFactors
              lowerWeight))⁻¹ *
          (SPFactora.listEval q
              (coordinates.weightFactors lowerWeight) *
            SPFactora.listEval q (X.weightFactors lowerWeight))
    rw [← SPFactora.listEval_append,
      ← route.rewrites.listEval_eq q,
      SPFactora.listEval_append]
    group

/-- In the terminal high-weight range, the merge route emits no corrections. -/
noncomputable def of_highWeight
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hcutoff : n ≤ 2 * lowerWeight)
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight) :
    TMRoute
      (lowerWeight := lowerWeight) hn H hH coordinates factor := by
  let X := factor.normalCoordinateExpansions hn H hH
  refine
    { higherSource := []
      higher_least_succ := by
        intro x hx
        simp at hx
      rewrites := ?_ }
  simpa using
    CCExpans.append_rewrites_add
      coordinates X lowerWeight (by
        intro B hB A hA
        rw [coordinates.word_weight_factors hB,
          X.word_weight_factors hA]
        omega)

end TMRoute

/--
A supply of operational active-block merge routes and semantic intrinsic
factor routes.
-/
structure SRFtrya
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) where
  routeMerge :
    ∀ (lowerWeight : ℕ)
      (coordinates : CCExpans H inputWeight)
      (factor : SPFactora H inputWeight),
      coordinates.NTBelow lowerWeight →
      factor.word.weight PEAddres.weight = lowerWeight →
      factor.word.weight PEAddres.weight < n →
        TMRoute
          (lowerWeight := lowerWeight) hn H hH coordinates factor
  routeFactor :
    ∀ (lowerWeight : ℕ)
      (factor : SPFactora H inputWeight),
      factor.word.weight PEAddres.weight = lowerWeight →
      factor.word.weight PEAddres.weight < n →
        TSRoute
          (lowerWeight := lowerWeight) hn H hH factor

namespace SRFtrya

/-- Operational residual routes supply the decomposed active-block factory. -/
noncomputable def activeDecompositionFactory
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (factory :
      SRFtrya
        (n := n) (inputWeight := inputWeight) hn H hH) :
    TDFtry
      (n := n) (inputWeight := inputWeight) hn H hH where
  expandMerge lowerWeight coordinates factor hcoordinates hfactorWeight
      hfactorTruncated :=
    (factory.routeMerge lowerWeight coordinates factor hcoordinates
      hfactorWeight hfactorTruncated).mergeResidualExpansion hfactorWeight
        hfactorTruncated
  expandFactor lowerWeight factor hfactorWeight hfactorTruncated :=
    (factory.routeFactor lowerWeight factor hfactorWeight
      hfactorTruncated).factorExpansion

/-- Terminal high-weight routes supply the operational residual-route factory. -/
noncomputable def of_highWeight
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (hcutoff :
      ∀ (lowerWeight : ℕ)
        (factor : SPFactora H inputWeight),
        factor.word.weight PEAddres.weight = lowerWeight →
        factor.word.weight PEAddres.weight < n →
          n ≤ 2 * lowerWeight) :
    SRFtrya
      (n := n) (inputWeight := inputWeight) hn H hH where
  routeMerge lowerWeight coordinates factor _hcoordinates hfactorWeight
      hfactorTruncated :=
    TMRoute.of_highWeight
      hn H hH (hcutoff lowerWeight factor hfactorWeight hfactorTruncated)
        coordinates factor
  routeFactor lowerWeight factor hfactorWeight hfactorTruncated :=
    TSRoute.of_highWeight
      hn H hH (hcutoff lowerWeight factor hfactorWeight hfactorTruncated)
        factor hfactorWeight hfactorTruncated

end SRFtrya

namespace TSInput

/--
Operational active-block residual routes and higher-tail routes construct the
Claim 5 polynomial data.
-/
theorem routeFactoryHigher
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
    (factory :
      SRFtrya
        (n := n) (inputWeight := inputWeight) hn H hH)
    (tailSchedule :
      RHRoute
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.coordDecompHigher
    hn H hH hsourceSupported
      factory.activeDecompositionFactory tailSchedule
        hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from ActiveBlockDelegatedResidualRoutes.lean

/-!
# Delegated active-block residual routes

Nonterminal active-block collection emits strictly heavier corrections while
merging two normalized fixed-weight Hall blocks.  Those corrections are
normalized one stratum upward during the merge, so the operational certificate
is a semantic obstruction run rather than a raw truncated rewrite.

This file packages that delegated route, a stronger More3 block-insertion
presentation of it, and the dynamic schedule consumed by filtration recursion.
The route still compiles to the same exact merge residual expansion used by
the canonical active-block decomposition.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
A delegated fixed-weight merge route.  Its semantic obstruction run
recollects the two active Hall blocks into the canonical coordinatewise sum
followed by strictly heavier symbolic corrections.
-/
structure DMRoute
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_least_succ :
    SPFactora.WordWeightLeast (lowerWeight + 1) higherSource
  rewrites :
    SCRw
      (n := n) (lowerWeight := lowerWeight)
      (coordinates.weightFactors lowerWeight ++
        (factor.normalCoordinateExpansions hn H hH).weightFactors
          lowerWeight)
      ((coordinates.activeBlockUpdate hn H hH factor).weightFactors
          lowerWeight ++ higherSource)

namespace DMRoute

/--
A delegated semantic merge route supplies the fixed-weight merge residual
expansion.
-/
noncomputable def mergeResidualExpansion
    {d n inputWeight lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {coordinates : CCExpans H inputWeight}
    {factor : SPFactora H inputWeight}
    (route :
      DMRoute
        (lowerWeight := lowerWeight) hn H hH coordinates factor)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TMExp
      (lowerWeight := lowerWeight) hn H hH coordinates factor := by
  let X := factor.normalCoordinateExpansions hn H hH
  have hlowerWeightTruncated : lowerWeight < n := by
    omega
  have hsourceTruncated :
      SPFactora.IsTruncated n
        (coordinates.weightFactors lowerWeight ++ X.weightFactors lowerWeight) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [coordinates.word_weight_factors hx]
      exact hlowerWeightTruncated
    · rw [X.word_weight_factors hx]
      exact hlowerWeightTruncated
  have houtputTruncated :
      SPFactora.IsTruncated n
        ((coordinates.activeBlockUpdate hn H hH factor).weightFactors
            lowerWeight ++ route.higherSource) :=
    route.rewrites.isTruncated hsourceTruncated
  refine
    { higherSource := route.higherSource
      higher_source_truncated := ?_
      higher_least_succ :=
        route.higher_least_succ
      list_merge_value := ?_ }
  · intro x hx
    exact houtputTruncated x (List.mem_append_right _ hx)
  · intro q
    unfold
      CCExpans.activeMergeValue
      CCExpans.activeNormalValue
    change
      SPFactora.listEval (n := n) q route.higherSource =
        (SPFactora.listEval q
            ((coordinates.activeBlockUpdate hn H hH factor).weightFactors
              lowerWeight))⁻¹ *
          (SPFactora.listEval q
              (coordinates.weightFactors lowerWeight) *
            SPFactora.listEval q (X.weightFactors lowerWeight))
    rw [← SPFactora.listEval_append,
      ← route.rewrites.listEval_eq q,
      SPFactora.listEval_append]
    group

end DMRoute

/--
A More3 block-insertion presentation of a delegated fixed-weight merge route.
The inserted block is the active Hall layer of the new factor.
-/
structure SMRoute
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (coordinates : CCExpans H inputWeight)
    (factor : SPFactora H inputWeight) where
  higherSource :
    List (SPFactora H inputWeight)
  higher_least_succ :
    SPFactora.WordWeightLeast (lowerWeight + 1) higherSource
  inserts :
    SBInsert
      (n := n) H inputWeight lowerWeight
      (coordinates.weightFactors lowerWeight)
      ((factor.normalCoordinateExpansions hn H hH).weightFactors
        lowerWeight)
      ((coordinates.activeBlockUpdate hn H hH factor).weightFactors
          lowerWeight ++ higherSource)

namespace SMRoute

/-- A More3 block route compiles to its delegated semantic merge route. -/
def delegatedMergeResidual
    {d n inputWeight lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {coordinates : CCExpans H inputWeight}
    {factor : SPFactora H inputWeight}
    (route :
      SMRoute
        (lowerWeight := lowerWeight) hn H hH coordinates factor) :
    DMRoute
      (lowerWeight := lowerWeight) hn H hH coordinates factor where
  higherSource := route.higherSource
  higher_least_succ :=
    route.higher_least_succ
  rewrites := route.inserts.rewrites

/-- A More3 block route supplies its fixed-weight merge residual expansion. -/
noncomputable def mergeResidualExpansion
    {d n inputWeight lowerWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    {coordinates : CCExpans H inputWeight}
    {factor : SPFactora H inputWeight}
    (route :
      SMRoute
        (lowerWeight := lowerWeight) hn H hH coordinates factor)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TMExp
      (lowerWeight := lowerWeight) hn H hH coordinates factor :=
  route.delegatedMergeResidual.mergeResidualExpansion
    hfactorWeight hfactorTruncated

end SMRoute

/--
A dynamic supply of More3 block-insertion merge routes and semantic
factor-normalization routes.
-/
structure RRSchedb
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) where
  routeMerge :
    ∀ lowerWeight : ℕ,
      TSNormalb
          (n := n) (inputWeight := inputWeight)
            (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CCExpans H inputWeight)
          (factor : SPFactora H inputWeight),
          coordinates.NTBelow lowerWeight →
          factor.word.weight PEAddres.weight = lowerWeight →
          factor.word.weight PEAddres.weight < n →
            SMRoute
              (lowerWeight := lowerWeight) hn H hH coordinates factor
  routeFactor :
    ∀ lowerWeight : ℕ,
      TSNormalb
          (n := n) (inputWeight := inputWeight)
            (lowerWeight := lowerWeight + 1) H →
        ∀ (factor : SPFactora H inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
          factor.word.weight PEAddres.weight < n →
            TSRoute
              (lowerWeight := lowerWeight) hn H hH factor

/--
A dynamic supply of delegated merge routes and factor-normalization routes.
The next-stratum normalizer is explicit because nonterminal swap corrections
must be normalized upward while the active block is recollected.
-/
structure TDSched
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) where
  routeMerge :
    ∀ lowerWeight : ℕ,
      TSNormalb
          (n := n) (inputWeight := inputWeight)
            (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CCExpans H inputWeight)
          (factor : SPFactora H inputWeight),
          coordinates.NTBelow lowerWeight →
          factor.word.weight PEAddres.weight = lowerWeight →
          factor.word.weight PEAddres.weight < n →
            DMRoute
              (lowerWeight := lowerWeight) hn H hH coordinates factor
  routeFactor :
    ∀ lowerWeight : ℕ,
      TSNormalb
          (n := n) (inputWeight := inputWeight)
            (lowerWeight := lowerWeight + 1) H →
        ∀ (factor : SPFactora H inputWeight),
          factor.word.weight PEAddres.weight = lowerWeight →
          factor.word.weight PEAddres.weight < n →
            TSRoute
              (lowerWeight := lowerWeight) hn H hH factor

namespace TDSched

open TAResolua

/--
Dynamic delegated residual routes and higher-tail routes supply the residual
active insertion branch.
-/
noncomputable def insertionBranch
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (schedule :
      TDSched
        (n := n) (inputWeight := inputWeight) hn H hH)
    (tailSchedule :
      RHRoute
        (n := n) (inputWeight := inputWeight) H) :
    TruncatedInsertionBranch
      (n := n) (inputWeight := inputWeight) H where
  insert lowerWeight normalizer coordinates factor hcoordinates hfactorWeight
      hfactorTruncated := by
    let merge :=
      (schedule.routeMerge lowerWeight normalizer coordinates factor hcoordinates
        hfactorWeight hfactorTruncated).mergeResidualExpansion hfactorWeight
          hfactorTruncated
    let factorTail :=
      (schedule.routeFactor lowerWeight normalizer factor hfactorWeight
        hfactorTruncated).factorExpansion
    let block :=
      TAExp.mergeFactor
        merge factorTail
    let tail :=
      (tailSchedule.route lowerWeight normalizer coordinates factor hcoordinates
        hfactorWeight hfactorTruncated).higherTailResolution hfactorWeight
          hfactorTruncated
    exact
      (active_block_tail hcoordinates hfactorWeight
        hfactorTruncated
          (block.activeBlockResolution hcoordinates hfactorWeight)
          tail).exists_insertion normalizer hfactorWeight hfactorTruncated

/--
Dynamic delegated residual routes and higher-tail routes supply the complete
filtration-recursive semantic insertion step.
-/
noncomputable def recSemanticInsertion
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (schedule :
      TDSched
        (n := n) (inputWeight := inputWeight) hn H hH)
    (tailSchedule :
      RHRoute
        (n := n) (inputWeight := inputWeight) H) :
    RIStep
      (n := n) (inputWeight := inputWeight) H :=
  RIStep.insertion_branch
    (schedule.insertionBranch tailSchedule)

end TDSched

namespace RRSchedb

/-- More3 block routes compile to delegated semantic merge routes. -/
def delegatedRouteSchedule
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (schedule :
      RRSchedb
        (n := n) (inputWeight := inputWeight) hn H hH) :
    TDSched
      (n := n) (inputWeight := inputWeight) hn H hH where
  routeMerge lowerWeight normalizer coordinates factor hcoordinates
      hfactorWeight hfactorTruncated :=
    (schedule.routeMerge lowerWeight normalizer coordinates factor hcoordinates
      hfactorWeight hfactorTruncated).delegatedMergeResidual
  routeFactor := schedule.routeFactor

end RRSchedb

namespace TSInput

/--
Dynamic delegated active-block residual routes and higher-tail routes
construct the Claim 5 polynomial data.
-/
theorem coordRecTail
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
      TDSched
        (n := n) (inputWeight := inputWeight) hn H hH)
    (tailSchedule :
      RHRoute
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.recursiveSemanticInsertion
    hn H hH hsourceSupported
      (schedule.recSemanticInsertion tailSchedule)
        hinputWeight

/--
Structured More3 active-block merge routes and higher-tail routes construct
the Claim 5 polynomial data.
-/
theorem coordRecRoute
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
      RRSchedb
        (n := n) (inputWeight := inputWeight) hn H hH)
    (tailSchedule :
      RHRoute
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.coordRecTail
    hn H hH hsourceSupported
      schedule.delegatedRouteSchedule tailSchedule
        hinputWeight

end TSInput

end TCTex
end Submission

-- Merged from ActiveBlockFactorNormalizationRoutes.lean

/-!
# Factor normalization routes for active-block residuals

The intrinsic half of an active-block residual can be obtained from any
semantic normalization of the inserted factor.  Associated-graded uniqueness
forces the active Hall layer of that normalization to agree with the canonical
Hall-normal coordinate expansion of the factor.  Its remaining endpoint tail
therefore gives the strictly heavier intrinsic residual route.

This file also extracts such a singleton normalization from the broader
universal semantic collection derivation builder by inserting the factor into
the empty endpoint.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
A supported semantic normalization of one active-weight symbolic factor.
-/
structure TANorm
    {d n inputWeight lowerWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (factor : SPFactora H inputWeight) where
  coordinates :
    CCExpans H inputWeight
  coordinates_no_below :
    coordinates.NTBelow lowerWeight
  list_coordinates_factor :
    ∀ q : ℕ,
      SPFactora.listEval (n := n) q
          (coordinates.factors (n := n)) =
        factor.eval (n := n) q

namespace TANorm

/--
Any supported semantic normalization of a singleton factor has the canonical
active Hall coordinates.
-/
lemma expansions_active_weight
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {factor : SPFactora H inputWeight}
    (normalization :
      TANorm
        (n := n) (lowerWeight := lowerWeight) H factor)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n)
    (q : ℕ) :
    normalization.coordinates.eval q lowerWeight =
      (factor.normalCoordinateExpansions hn H hH).eval q lowerWeight := by
  let X := factor.normalCoordinateExpansions hn H hH
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    have hfactorPos := factor.word_weight_pos
    omega
  have hfactorWordMem :
      factor.wordValue (n := n) ∈
        Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (lowerWeight - 1) := by
    simpa [hfactorWeight] using factor.value_lower_series (n := n)
  have hfactorCoordinates :
      normalFormCoordinates hn H hH (factor.eval (n := n) q) lowerWeight =
        X.eval q lowerWeight := by
    change
      normalFormCoordinates hn H hH
          ((factor.wordValue (n := n)) ^ factor.exponent q) lowerWeight =
        X.eval q lowerWeight
    rw [form_coordinates_zpow
      hn H hH hlowerWeightPos (by omega) _ hfactorWordMem]
    rw [factor.normal_coordinate_expansions
      hn H hH q lowerWeight hlowerWeightPos (by omega)]
    funext i
    simp [zscaledExponentFamily]
    ring
  have hcollected :
      collectedHallProduct (n := n) H (normalization.coordinates.eval q) =
        factor.eval (n := n) q := by
    rw [← normalization.coordinates.listEval_factors q]
    exact normalization.list_coordinates_factor q
  have hnormalizationCoordinates :
      normalFormCoordinates hn H hH (factor.eval (n := n) q) lowerWeight =
        normalization.coordinates.eval q lowerWeight :=
    form_coordinates_collected
      hn H hH (normalization.coordinates.eval q) (factor.eval (n := n) q)
        hcollected lowerWeight hlowerWeightPos (by omega)
  exact hnormalizationCoordinates.symm.trans hfactorCoordinates

/--
The tail of any supported singleton normalization is the intrinsic factor
residual route.
-/
noncomputable def factorResidualRoute
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {factor : SPFactora H inputWeight}
    (normalization :
      TANorm
        (n := n) (lowerWeight := lowerWeight) H factor)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRoute
      (lowerWeight := lowerWeight) hn H hH factor := by
  let X := factor.normalCoordinateExpansions hn H hH
  have hlowerWeightPos : 1 ≤ lowerWeight := by
    have hfactorPos := factor.word_weight_pos
    omega
  have hlowerWeightCutoff : lowerWeight ≤ n - 1 := by
    omega
  refine
    { higherSource := normalization.coordinates.tailFactors (n := n) lowerWeight
      higher_source_truncated :=
        normalization.coordinates.truncated_factors hlowerWeightCutoff
      higher_least_succ :=
        normalization.coordinates.word_least_factors
      active_append_factor := ?_ }
  intro q
  calc
    SPFactora.listEval (n := n) q
          (X.weightFactors lowerWeight ++
            normalization.coordinates.tailFactors (n := n) lowerWeight) =
        SPFactora.listEval (n := n) q
          (normalization.coordinates.weightFactors lowerWeight ++
            normalization.coordinates.tailFactors (n := n) lowerWeight) := by
      rw [SPFactora.listEval_append,
        SPFactora.listEval_append,
        X.list_weight_factors,
        normalization.coordinates.list_weight_factors,
        normalization.expansions_active_weight
          hn H hH hfactorWeight hfactorTruncated q]
    _ =
        SPFactora.listEval (n := n) q
          (normalization.coordinates.factors (n := n)) := by
      rw [normalization.coordinates.append_no_below
        normalization.coordinates_no_below hlowerWeightPos
          hlowerWeightCutoff]
    _ = factor.eval (n := n) q :=
      normalization.list_coordinates_factor q

/-- A current-stratum normalizer supplies a singleton factor normalization. -/
lemma nonempty_ofNormalizer
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (factor : SPFactora H inputWeight)
    (hfactorSupported :
      lowerWeight ≤ factor.word.weight PEAddres.weight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    Nonempty
      (TANorm
        (n := n) (lowerWeight := lowerWeight) H factor) := by
  rcases normalizer.normalize [factor] (by
      intro x hx
      rcases List.mem_singleton.mp hx with rfl
      exact hfactorTruncated) (by
      intro x hx
      rcases List.mem_singleton.mp hx with rfl
      exact hfactorSupported) with
    ⟨coordinates, hcoordinates, hlistEval⟩
  exact ⟨{
      coordinates := coordinates
      coordinates_no_below := hcoordinates
      list_coordinates_factor := by
        intro q
        simpa [SPFactora.listEval] using hlistEval q }⟩

/-- Choose the singleton normalization supplied by a current-stratum normalizer. -/
noncomputable def ofNormalizer
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight) (lowerWeight := lowerWeight) H)
    (factor : SPFactora H inputWeight)
    (hfactorSupported :
      lowerWeight ≤ factor.word.weight PEAddres.weight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TANorm
      (n := n) (lowerWeight := lowerWeight) H factor :=
  Classical.choice
    (nonempty_ofNormalizer normalizer factor hfactorSupported hfactorTruncated)

end TANorm

namespace TDBuildb

/--
Insert one factor into the empty endpoint to obtain a supported singleton
normalization.
-/
lemma nonempty_active_normalization
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (builder :
      TDBuildb
        (n := n) (inputWeight := inputWeight) H)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H)
    (factor : SPFactora H inputWeight)
    (hfactorSupported :
      lowerWeight ≤ factor.word.weight PEAddres.weight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    Nonempty
      (TANorm
        (n := n) (lowerWeight := lowerWeight) H factor) := by
  rcases builder.insert lowerWeight normalizer
      (CCExpans.empty H inputWeight)
      factor (by
        intro s i hs
        rfl) hfactorSupported hfactorTruncated with
    ⟨coordinates, hcoordinates, hinserts⟩
  refine ⟨{
      coordinates := coordinates
      coordinates_no_below := hcoordinates
      list_coordinates_factor := ?_ }⟩
  intro q
  simpa [SPFactora.listEval] using hinserts.listEval_eq q

/-- Choose the supported singleton normalization supplied by the universal builder. -/
noncomputable def activeBlockNormalization
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (builder :
      TDBuildb
        (n := n) (inputWeight := inputWeight) H)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H)
    (factor : SPFactora H inputWeight)
    (hfactorSupported :
      lowerWeight ≤ factor.word.weight PEAddres.weight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TANorm
      (n := n) (lowerWeight := lowerWeight) H factor :=
  Classical.choice
    (builder.nonempty_active_normalization normalizer factor
      hfactorSupported hfactorTruncated)

/--
The universal semantic derivation builder therefore supplies the intrinsic
factor residual route at every active stratum.
-/
lemma nonempty_active_route
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (builder :
      TDBuildb
        (n := n) (inputWeight := inputWeight) H)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    Nonempty
      (TSRoute
        (lowerWeight := lowerWeight) hn H hH factor) := by
  rcases builder.nonempty_active_normalization normalizer factor
      (by omega) hfactorTruncated with
    ⟨normalization⟩
  exact
    ⟨normalization.factorResidualRoute
      hn H hH hfactorWeight hfactorTruncated⟩

/-- Choose the intrinsic factor residual route supplied by the universal builder. -/
noncomputable def activeBlockRoute
    {d n inputWeight lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (builder :
      TDBuildb
        (n := n) (inputWeight := inputWeight) H)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight + 1) H)
    (factor : SPFactora H inputWeight)
    (hfactorWeight :
      factor.word.weight PEAddres.weight = lowerWeight)
    (hfactorTruncated :
      factor.word.weight PEAddres.weight < n) :
    TSRoute
      (lowerWeight := lowerWeight) hn H hH factor :=
  Classical.choice
    (builder.nonempty_active_route
      hn H hH normalizer factor hfactorWeight hfactorTruncated)

end TDBuildb

end TCTex
end Submission

-- Merged from ActiveBlockMergeResidualReduction.lean

/-!
# Reducing active-block residual routing to merge routing

The universal semantic collection derivation builder already normalizes each
inserted singleton factor.  Its strictly heavier tail therefore supplies the
intrinsic factor residual route.  Consequently the remaining active-block
obligation is only the More3 block route that recollects the merged old and new
active coordinate blocks.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/--
A dynamic supply of the genuinely unresolved More3 merge routes.  Intrinsic
factor tails are omitted because the universal builder supplies them.
-/
structure TRSched
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)) where
  routeMerge :
    ∀ lowerWeight : ℕ,
      TSNormalb
          (n := n) (inputWeight := inputWeight)
            (lowerWeight := lowerWeight + 1) H →
        ∀ (coordinates : CCExpans H inputWeight)
          (factor : SPFactora H inputWeight),
          coordinates.NTBelow lowerWeight →
          factor.word.weight PEAddres.weight = lowerWeight →
          factor.word.weight PEAddres.weight < n →
            SMRoute
              (lowerWeight := lowerWeight) hn H hH coordinates factor

namespace TRSched

/--
The universal builder fills the intrinsic factor-route field of a merge-only
active-block residual schedule.
-/
noncomputable def activeBlockSchedule
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (schedule :
      TRSched
        (n := n) (inputWeight := inputWeight) hn H hH)
    (builder :
      TDBuildb
        (n := n) (inputWeight := inputWeight) H) :
    RRSchedb
      (n := n) (inputWeight := inputWeight) hn H hH where
  routeMerge := schedule.routeMerge
  routeFactor _lowerWeight normalizer factor hfactorWeight hfactorTruncated :=
    builder.activeBlockRoute
      hn H hH normalizer factor hfactorWeight hfactorTruncated

/--
The merge-only schedule and the universal builder supply delegated residual
routes at every active stratum.
-/
noncomputable def delegatedRouteSchedule
    {d n inputWeight : ℕ}
    {hn : 2 ≤ n}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n)}
    (schedule :
      TRSched
        (n := n) (inputWeight := inputWeight) hn H hH)
    (builder :
      TDBuildb
        (n := n) (inputWeight := inputWeight) H) :
    TDSched
      (n := n) (inputWeight := inputWeight) hn H hH :=
  (schedule.activeBlockSchedule
    builder).delegatedRouteSchedule

end TRSched

namespace TSInput

/--
Fixed-weight More3 merge routes, the universal semantic builder, and
higher-tail routes construct the Claim 5 polynomial data.
-/
theorem coordMergeHigher
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
      TRSched
        (n := n) (inputWeight := inputWeight) hn H hH)
    (builder :
      TDBuildb
        (n := n) (inputWeight := inputWeight) H)
    (tailSchedule :
      RHRoute
        (n := n) (inputWeight := inputWeight) H)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.coordRecTail
    hn H hH hsourceSupported
      (schedule.delegatedRouteSchedule builder)
        tailSchedule hinputWeight

end TSInput

end TCTex
end Submission
