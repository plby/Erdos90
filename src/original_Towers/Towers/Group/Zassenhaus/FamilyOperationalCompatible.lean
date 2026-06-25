import Towers.Group.Zassenhaus.SignedProfilePackets
import Towers.Group.Zassenhaus.PolynomialOrbitVocabulary
import Towers.Group.Zassenhaus.CompatiblePacketRouting

/-!
# Residual shape-sorted adapter to Claim 5 coordinate polynomials

The sound aggregate-presentation residual-aware route constructs the
shape-block signed-block kernel consumed by retained finite-index traces.  This
file threads that route into the Claim 5 coordinate-polynomial adapter.

The remaining hypotheses are the genuine repeated-block recollection
obligations: one fixed retained trace must align with every natural endpoint,
and its natural packet must extend to all integral exponents.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  CCAdapta

universe u

open
  PRPolysa
open
  CIComp
open
  WRPolys
open
  SAPres
open
  CSAggreg
open
  RITrace
open
  ENStab
open
  ESLift

/-- Compile the repaired aggregate-presentation residual-aware route to the
shape-block signed-block interface consumed by retained finite-index traces. -/
noncomputable def
    shapeAggregatedSorted
    (kernel :
      CARecoll) :
    OCShape :=
  kernel.presentationGlobalRecollection
    |>.aggregatedGlobalRecollection
    |>.shapeBlockSigned

/-- Compile the smaller per-grid-cancellation interface to the shape-block
signed-block kernel consumed by retained finite-index traces. -/
noncomputable def shapeBlockSorted
    (kernel :
      OCSorted) :
    OCShape :=
  shapeAggregatedSorted
    kernel.aggregatedSortedGlobal

namespace TSInput

/--
An endpoint-aligned retained trace and signed extension instantiate Claim 5
from the repaired aggregate-presentation residual-aware route.
-/
theorem
    coordAggregatedLift
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (kernel :
      CARecoll)
    (trace : List (RetainedOrbitIndex n 1 1))
    (halignment :
      SatisfiesOccurrenceAlignment.{u}
        (d := d) (by simp) (by simp) trace)
    (lift :
      OccurrenceAllLift
        (shapeAggregatedSorted kernel)
          trace halignment)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
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
  ESLift.TSInput.coordOccLift
    hn H hH
      (kernel :=
        shapeAggregatedSorted kernel)
      trace halignment lift
      input hsourceSupported factorNormalization hinputWeight

/--
The per-grid-cancellation facade supplies the same Claim 5 adapter after
compiling its aggregate presentations.
-/
theorem
    coordAllLift
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (kernel :
      OCSorted)
    (trace : List (RetainedOrbitIndex n 1 1))
    (halignment :
      SatisfiesOccurrenceAlignment.{u}
        (d := d) (by simp) (by simp) trace)
    (lift :
      OccurrenceAllLift
        (shapeBlockSorted kernel) trace halignment)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
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
  ESLift.TSInput.coordOccLift
    hn H hH (kernel := shapeBlockSorted kernel)
      trace halignment lift
      input hsourceSupported factorNormalization hinputWeight

end TSInput

end
  CCAdapta
end TCTex
end Towers

/-!
# Residual shape-sorted retained-transversal Claim 5 adapter

The retained closure transversal supplies a fixed occurrence-preserving trace at
every cutoff.  Its ordered retained-recipe product theorem is the remaining
schedule-sensitive symbolic recollection obligation.  This file composes that
precise obligation with the sound residual shape-sorted route.

Through cutoff four the retained-recipe product theorem is already available,
so the resulting Claim 5 adapter is unconditional in that base range.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  RCAdapt

universe u

open
  PRPolysa
open
  SAPres
open
  CCAdapta
open
  CTAssigna
open
  CCThree
open
  ECThree
open
  ENStab
open
  ERTransv
open
  ESLift

/--
For the repaired aggregate-presentation residual-aware route, the retained
recipe-product theorem is equivalent to endpoint alignment of its fixed
retained trace together with the signed lift of that alignment.
-/
theorem
    satisfies_alignment_all
    {d n : ℕ}
    (kernel :
      CARecoll) :
    SatisfiesRecipeCoefficient.{u} d n ↔
      ∃ halignment :
          SatisfiesOccurrenceAlignment.{u}
            (d := d) (by simp) (by simp)
              (retainedRecipeCoefficient n),
        OccurrenceAllLift
          (shapeAggregatedSorted
            kernel)
          (retainedRecipeCoefficient n) halignment :=
  satisfies_alignment_lift
    (shapeAggregatedSorted kernel)

/--
For the per-grid-cancellation facade, the retained recipe-product theorem is
the same pair of operational endpoint obligations.
-/
theorem
    alignment_all_lift
    {d n : ℕ}
    (kernel :
      OCSorted) :
    SatisfiesRecipeCoefficient.{u} d n ↔
      ∃ halignment :
          SatisfiesOccurrenceAlignment.{u}
            (d := d) (by simp) (by simp)
              (retainedRecipeCoefficient n),
        OccurrenceAllLift
          (shapeBlockSorted kernel)
          (retainedRecipeCoefficient n) halignment :=
  satisfies_alignment_lift
    (shapeBlockSorted kernel)

namespace TSInput

/--
The arbitrary-cutoff retained-transversal schedule theorem instantiates Claim 5
through the repaired aggregate-presentation residual-aware route.
-/
theorem
    coordPresentationOcc
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (kernel :
      CARecoll)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
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
  ERTransv.TSInput.coordCollectedOcc
    hn H hH
      (kernel :=
        shapeAggregatedSorted kernel)
      hrecipes input hsourceSupported factorNormalization hinputWeight

/--
The arbitrary-cutoff retained-transversal schedule theorem instantiates Claim 5
through the smaller per-grid-cancellation facade.
-/
theorem
    coordSortedOcc
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (kernel :
      OCSorted)
    (hrecipes :
      SatisfiesRecipeCoefficient.{u} d n)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
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
  ERTransv.TSInput.coordCollectedOcc
    hn H hH (kernel := shapeBlockSorted kernel)
      hrecipes input hsourceSupported factorNormalization hinputWeight

/--
Through cutoff four, the repaired aggregate-presentation residual-aware route
instantiates Claim 5 without an additional retained-recipe schedule hypothesis.
-/
theorem
    coordOccTrace
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hnUpper : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (kernel :
      CARecoll)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
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
  ECThree.TSInput.coordPolyOcc
    hn hnUpper H hH
      (kernel :=
        shapeAggregatedSorted kernel)
      input hsourceSupported factorNormalization hinputWeight

/--
Through cutoff four, the smaller per-grid-cancellation facade instantiates
Claim 5 without an additional retained-recipe schedule hypothesis.
-/
theorem
    sortedCollectedOccurrence
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hnUpper : n ≤ 4)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (kernel :
      OCSorted)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
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
  ECThree.TSInput.coordPolyOcc
    hn hnUpper H hH (kernel := shapeBlockSorted kernel)
      input hsourceSupported factorNormalization hinputWeight

end TSInput

end
  RCAdapt
end TCTex
end Towers


/-!
# Mirrored cutoff-aware occurrence runs for root-swap packet inversion

The cutoff-aware Hall collector inserts correction factors before a swapped
adjacent pair.  Reversing a factor list and inverting every factor transports
that operation to a genuinely different directed rule: the correction factors
occur after the swapped pair.

This file records that mirrored rule and proves that reverse-inverse transport
is involutive on factor lists, carries ordinary cutoff-aware runs to mirrored
runs, and agrees with reverse root-swap on signed-profile packet evaluation.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace
  TOMirror

open
  FRSwap
open
  CFSubsti
open
  PTOcc
open
  PCBridge

/-- Reverse a factor list and invert every factor. -/
def reverseInverseFactors
    {G : Type*}
    [Group G]
    (factors : List G) :
    List G :=
  factors.reverse.map Inv.inv

@[simp]
lemma reverse_factors_nil
    {G : Type*}
    [Group G] :
    reverseInverseFactors ([] : List G) = [] :=
  rfl

@[simp]
lemma reverse_factors_singleton
    {G : Type*}
    [Group G]
    (factor : G) :
    reverseInverseFactors [factor] = [factor⁻¹] :=
  rfl

@[simp]
lemma reverse_factors_append
    {G : Type*}
    [Group G]
    (left right : List G) :
    reverseInverseFactors (left ++ right) =
      reverseInverseFactors right ++ reverseInverseFactors left := by
  simp [reverseInverseFactors, List.reverse_append, List.map_append]

@[simp]
lemma reverse_inverse_factors
    {G : Type*}
    [Group G]
    (factors : List G) :
    reverseInverseFactors (reverseInverseFactors factors) = factors := by
  simp [reverseInverseFactors, List.map_reverse, List.map_map]

/-- Reverse-inverse transport computes the inverse ordered product. -/
lemma prod_reverse_factors
    {G : Type*}
    [Group G]
    (factors : List G) :
    (reverseInverseFactors factors).prod = factors.prod⁻¹ := by
  rw [reverseInverseFactors, List.map_reverse]
  exact (List.prod_inv_reverse factors).symm

/--
Mirrored adjacent-swap operation: correction factors are inserted after the
swapped pair.
-/
inductive TOStep
    {G : Type*}
    [Group G] :
    List G → List G → Prop where
  | obstruction
      (front back : List G)
      (left right : G)
      (corrections : List G)
      (swap_mul_corrections_eq :
        right * left * corrections.prod = left * right) :
      TOStep
        (front ++ [left, right] ++ back)
        (front ++ [right, left] ++ corrections ++ back)

namespace TOStep

/-- One mirrored adjacent-swap operation preserves its ordered product. -/
lemma list_prod_eq
    {G : Type*}
    [Group G]
    {source target : List G}
    (step :
      TOStep source target) :
    target.prod = source.prod := by
  cases step with
  | obstruction front back left right corrections hswap =>
      calc
        (front ++ [right, left] ++ corrections ++ back).prod =
            front.prod * (right * left * corrections.prod) *
              back.prod := by
          simp [List.prod_append, mul_assoc]
        _ = front.prod * (left * right) * back.prod := by
          rw [hswap]
        _ = (front ++ [left, right] ++ back).prod := by
          simp [List.prod_append, mul_assoc]

/-- Mirrored adjacent-swap operations remain valid in list contexts. -/
lemma context
    {G : Type*}
    [Group G]
    {source target : List G}
    (step :
      TOStep source target)
    (front back : List G) :
    TOStep
      (front ++ source ++ back)
      (front ++ target ++ back) := by
  cases step with
  | obstruction innerFront innerBack left right corrections hswap =>
      simpa [List.append_assoc] using
        (TOStep.obstruction
          (front ++ innerFront) (innerBack ++ back)
          left right corrections hswap)

end TOStep

/--
Mirrored cutoff-aware occurrence operation.  Identity erasure is unchanged;
only the adjacent-swap branch changes orientation.
-/
inductive TTOccur
    {G : Type*}
    [Group G] :
    List G → List G → Prop where
  | swap
      {source target : List G}
      (step :
        TOStep source target) :
      TTOccur source target
  | erase
      (front back : List G)
      (factor : G)
      (hfactor : factor = 1) :
      TTOccur
        (front ++ [factor] ++ back)
        (front ++ back)

/-- Finite mirrored cutoff-aware occurrence runs. -/
abbrev TORw
    {G : Type*}
    [Group G]
    (source target : List G) :
    Prop :=
  Relation.ReflTransGen
    (@TTOccur G _) source target

namespace TTOccur

/-- One mirrored cutoff-aware operation preserves its ordered product. -/
lemma list_prod_eq
    {G : Type*}
    [Group G]
    {source target : List G}
    (step : TTOccur source target) :
    target.prod = source.prod := by
  cases step with
  | swap step =>
      exact step.list_prod_eq
  | erase front back factor hfactor =>
      simp [List.prod_append, hfactor]

/-- Mirrored cutoff-aware operations remain valid in list contexts. -/
lemma context
    {G : Type*}
    [Group G]
    {source target : List G}
    (step : TTOccur source target)
    (front back : List G) :
    TTOccur
      (front ++ source ++ back)
      (front ++ target ++ back) := by
  cases step with
  | swap step =>
      exact TTOccur.swap (step.context front back)
  | erase innerFront innerBack factor hfactor =>
      simpa [List.append_assoc] using
        (TTOccur.erase
          (front ++ innerFront) (innerBack ++ back) factor hfactor)

end TTOccur

namespace TORw

/-- Every finite mirrored cutoff-aware run preserves its ordered product. -/
lemma list_prod_eq
    {G : Type*}
    [Group G]
    {source target : List G}
    (rewrites : TORw source target) :
    target.prod = source.prod := by
  induction rewrites with
  | refl =>
      rfl
  | tail _ step ih =>
      exact step.list_prod_eq.trans ih

/-- Finite mirrored cutoff-aware runs remain valid in list contexts. -/
lemma context
    {G : Type*}
    [Group G]
    {source target : List G}
    (rewrites : TORw source target)
    (front back : List G) :
    TORw
      (front ++ source ++ back)
      (front ++ target ++ back) := by
  induction rewrites with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ step ih =>
      exact Relation.ReflTransGen.tail ih (step.context front back)

end TORw

/--
Reverse-inverse transport turns a leading-correction adjacent swap into a
trailing-correction adjacent swap.
-/
lemma occurrence_trailing_reverse
    {G : Type*}
    [Group G]
    {source target : List G}
    (step :
      COStep source target) :
    TOStep
      (reverseInverseFactors source) (reverseInverseFactors target) := by
  cases step with
  | obstruction front back left right corrections hswap =>
      have hswap' :
          left⁻¹ * right⁻¹ * (reverseInverseFactors corrections).prod =
            right⁻¹ * left⁻¹ := by
        rw [prod_reverse_factors]
        calc
          left⁻¹ * right⁻¹ * corrections.prod⁻¹ =
              (corrections.prod * right * left)⁻¹ := by
            group
          _ = (left * right)⁻¹ :=
            congrArg Inv.inv hswap
          _ = right⁻¹ * left⁻¹ := by
            group
      simpa [reverseInverseFactors, List.append_assoc] using
        (TOStep.obstruction
          (reverseInverseFactors back) (reverseInverseFactors front)
          right⁻¹ left⁻¹ (reverseInverseFactors corrections) hswap')

/--
Reverse-inverse transport turns an ordinary cutoff-aware operation into a
mirrored cutoff-aware operation.
-/
lemma trailing_reverse_factors
    {G : Type*}
    [Group G]
    {source target : List G}
    (step : TOStepa source target) :
    TTOccur
      (reverseInverseFactors source) (reverseInverseFactors target) := by
  cases step with
  | swap step =>
      exact TTOccur.swap
        (occurrence_trailing_reverse
          step)
  | erase front back factor hfactor =>
      have hfactor' : factor⁻¹ = 1 := by
        simp [hfactor]
      simpa [reverseInverseFactors, List.append_assoc] using
        (TTOccur.erase
          (reverseInverseFactors back) (reverseInverseFactors front)
          factor⁻¹ hfactor')

/--
Reverse-inverse transport turns an ordinary cutoff-aware run into a mirrored
cutoff-aware run.
-/
lemma rewrites_trailing_reverse
    {G : Type*}
    [Group G]
    {source target : List G}
    (rewrites : TORwa source target) :
    TORw
      (reverseInverseFactors source) (reverseInverseFactors target) := by
  induction rewrites with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ step ih =>
      exact Relation.ReflTransGen.tail ih
        (trailing_reverse_factors step)

/--
Reverse-inverse transport turns a trailing-correction adjacent swap back into
a leading-correction adjacent swap.
-/
lemma trailing_leading_reverse
    {G : Type*}
    [Group G]
    {source target : List G}
    (step :
      TOStep source target) :
    COStep
      (reverseInverseFactors source) (reverseInverseFactors target) := by
  cases step with
  | obstruction front back left right corrections hswap =>
      have hswap' :
          (reverseInverseFactors corrections).prod * left⁻¹ * right⁻¹ =
            right⁻¹ * left⁻¹ := by
        rw [prod_reverse_factors]
        calc
          corrections.prod⁻¹ * left⁻¹ * right⁻¹ =
              (right * left * corrections.prod)⁻¹ := by
            group
          _ = (left * right)⁻¹ :=
            congrArg Inv.inv hswap
          _ = right⁻¹ * left⁻¹ := by
            group
      simpa [reverseInverseFactors, List.append_assoc] using
        (COStep.obstruction
          (reverseInverseFactors back) (reverseInverseFactors front)
          right⁻¹ left⁻¹ (reverseInverseFactors corrections) hswap')

/--
Reverse-inverse transport turns a mirrored cutoff-aware operation back into an
ordinary cutoff-aware operation.
-/
lemma trailing_occurrence_leading
    {G : Type*}
    [Group G]
    {source target : List G}
    (step : TTOccur source target) :
    TOStepa
      (reverseInverseFactors source) (reverseInverseFactors target) := by
  cases step with
  | swap step =>
      exact TOStepa.swap
        (trailing_leading_reverse
          step)
  | erase front back factor hfactor =>
      have hfactor' : factor⁻¹ = 1 := by
        simp [hfactor]
      simpa [reverseInverseFactors, List.append_assoc] using
        (TOStepa.erase
          (reverseInverseFactors back) (reverseInverseFactors front)
          factor⁻¹ hfactor')

/--
Reverse-inverse transport turns a finite mirrored cutoff-aware run back into
an ordinary cutoff-aware run.
-/
lemma trailing_rewrites_leading
    {G : Type*}
    [Group G]
    {source target : List G}
    (rewrites : TORw source target) :
    TORwa
      (reverseInverseFactors source) (reverseInverseFactors target) := by
  induction rewrites with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ step ih =>
      exact Relation.ReflTransGen.tail ih
        (trailing_occurrence_leading step)

/--
Ordinary cutoff-aware runs are exactly mirrored runs on reverse-inverse factor
lists.
-/
theorem trailing_rewrites_reverse
    {G : Type*}
    [Group G]
    {source target : List G} :
    TORw
        (reverseInverseFactors source) (reverseInverseFactors target) ↔
      TORwa source target := by
  constructor
  · intro rewrites
    simpa using
      trailing_rewrites_leading
        rewrites
  · exact rewrites_trailing_reverse

/-- Evaluate a list of signed-profile packets at a group pair and exponents. -/
def packetEvaluatedFactors
    {G : Type*}
    [Group G]
    (packets : List RFPkt)
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    List G :=
  packets.map fun packet =>
    packet.word.eval (HPAtom.eval left right) ^
      packet.profiles.value leftExponent rightExponent

/--
Reverse root-swap on packet lists evaluates as reverse-inverse transport on
their factor lists.
-/
lemma evaluated_swap_packets
    {G : Type*}
    [Group G]
    (packets : List RFPkt)
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    packetEvaluatedFactors (rootSwapPackets packets)
        left right leftExponent rightExponent =
      reverseInverseFactors
        (packetEvaluatedFactors packets
          left right leftExponent rightExponent) := by
  rw [packetEvaluatedFactors, rootSwapPackets, List.map_map,
    reverseInverseFactors, packetEvaluatedFactors, List.map_reverse]
  rw [List.map_reverse]
  apply congrArg List.reverse
  rw [List.map_map]
  apply List.map_congr_left
  intro packet _hpacket
  exact packet.eval_rootSwap left right leftExponent rightExponent

/--
Any cutoff-aware run between evaluated packet lists transports to a mirrored
run between the corresponding reverse root-swapped packet lists.
-/
lemma trailing_evaluated_packets
    {G : Type*}
    [Group G]
    {source target : List RFPkt}
    {left right : G}
    {leftExponent rightExponent : ℤ}
    (rewrites :
      TORwa
        (packetEvaluatedFactors source left right
          leftExponent rightExponent)
        (packetEvaluatedFactors target left right
          leftExponent rightExponent)) :
    TORw
      (packetEvaluatedFactors (rootSwapPackets source)
        left right leftExponent rightExponent)
      (packetEvaluatedFactors (rootSwapPackets target)
        left right leftExponent rightExponent) := by
  rw [evaluated_swap_packets,
    evaluated_swap_packets]
  exact
    rewrites_trailing_reverse rewrites

end
  TOMirror
end TCTex
end Towers
