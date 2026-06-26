import Towers.Group.Zassenhaus.InverseHistoryTruncation
import Towers.Group.Zassenhaus.PositiveDegreeRecipes
import Towers.Group.Zassenhaus.TruncatedRecipeInventories
import Towers.Group.Zassenhaus.PacketCompression
import Towers.Group.Zassenhaus.CompletePetrescoRecipe


-- Merged from InverseHistoryPolynomialPacket.lean

/-!
# Polynomial factors for retained inverse-oriented packet histories

The operational inverse-oriented Hall trace carries `PHistor` values.
After cutoff truncation, each surviving history still remembers a complete
independent-block recipe.  This file attaches those recipes to the signed
weighted-binomial factor language used by Claim 8.

This is the polynomial endpoint for the operational history model.  It is
intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace HPPkt

universe u

open HACoeff
open BRSpec
open HOPacket
open ITSched
open PHTrunc

/-- Retained recipes are exactly the recipes of the retained family packets. -/
lemma recipes_recipe_families
    {M N n leftWeight rightWeight : ℕ}
    (histories : List (PHistor M N)) :
    retainedRecipes n leftWeight rightWeight histories =
      (retainedFamilies n leftWeight rightWeight histories).map
        BFam.recipe :=
  rfl

/-- Every retained recipe comes from one surviving operational packet history. -/
lemma history_retained_recipes
    {M N n leftWeight rightWeight : ℕ}
    {histories : List (PHistor M N)}
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ retainedRecipes n leftWeight rightWeight histories) :
    ∃ history ∈ retainedHistories n leftWeight rightWeight histories,
      history.family.recipe = recipe := by
  unfold retainedRecipes historyRecipes historyFamilies at hrecipe
  rcases List.mem_map.mp hrecipe with ⟨family, hfamily, rfl⟩
  rcases List.mem_map.mp hfamily with ⟨history, hhistory, rfl⟩
  exact ⟨history, hhistory, rfl⟩

/-- Every retained operational recipe stays strictly below the cutoff. -/
lemma weighted_retained_recipes
    {M N n leftWeight rightWeight : ℕ}
    {histories : List (PHistor M N)}
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ retainedRecipes n leftWeight rightWeight histories) :
    weightedWordWeight leftWeight rightWeight recipe < n := by
  rcases history_retained_recipes hrecipe with
    ⟨history, hhistory, rfl⟩
  exact (mem_retainedHistories.mp hhistory).2

/-- Attach retained inverse-oriented histories to Claim 8 symbolic factors. -/
def symbolicFactors
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (histories : List (PHistor M N))
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    List (SPFactor H ι) :=
  BRSpec.symbolicFactors
    (retainedRecipes n leftAddress.1 rightAddress.1 histories)
    leftInput rightInput leftAddress rightAddress

/-- Every operational symbolic factor remembers one retained history recipe. -/
lemma recipe_factors
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {histories : List (PHistor M N)}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈ symbolicFactors (n := n) histories leftInput rightInput
        leftAddress rightAddress) :
    ∃ recipe ∈ retainedRecipes n leftAddress.1 rightAddress.1 histories,
      factor =
        BRSpec.symbolicFactor
          recipe leftInput rightInput leftAddress rightAddress := by
  exact
    BRSpec.recipe_factors
      hfactor

/-- Every operational symbolic correction factor remains below the cutoff. -/
lemma weight_symbolic_factors
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {histories : List (PHistor M N)}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈ symbolicFactors (n := n) histories leftInput rightInput
        leftAddress rightAddress) :
    factor.word.weight HEAddres.weight < n := by
  rcases recipe_factors hfactor with
    ⟨recipe, hrecipe, rfl⟩
  rw [word_symbolic_factor, ← weighted_word_weight]
  exact weighted_retained_recipes hrecipe

/-- Every operational symbolic correction factor lies above the left source. -/
lemma left_address_factors
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {histories : List (PHistor M N)}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈ symbolicFactors (n := n) histories leftInput rightInput
        leftAddress rightAddress) :
    leftAddress.1 < factor.word.weight HEAddres.weight := by
  rcases recipe_factors hfactor with
    ⟨recipe, _hrecipe, rfl⟩
  exact left_address_factor
    recipe leftInput rightInput leftAddress rightAddress

/-- Every operational symbolic correction factor lies above the right source. -/
lemma right_address_factors
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {histories : List (PHistor M N)}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈ symbolicFactors (n := n) histories leftInput rightInput
        leftAddress rightAddress) :
    rightAddress.1 < factor.word.weight HEAddres.weight := by
  rcases recipe_factors hfactor with
    ⟨recipe, _hrecipe, rfl⟩
  exact right_address_factor
    recipe leftInput rightInput leftAddress rightAddress

/-- Evaluate the ordered symbolic factor packet attached to retained histories. -/
lemma listSymbolicFactors
    {M N n d truncation : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (histories : List (PHistor M N))
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    SPFactor.listEval (n := truncation) e
        (symbolicFactors (n := n) histories leftInput rightInput
          leftAddress rightAddress) =
      ((retainedRecipes n leftAddress.1 rightAddress.1 histories).map fun recipe =>
        recipe.erasedShape.eval
            (HPAtom.eval
              (HEAddres.freeLowerTruncation leftAddress)
              (HEAddres.freeLowerTruncation rightAddress)) ^
          coefficientValue recipe
            (e leftInput leftAddress.1 leftAddress.2)
            (e rightInput rightAddress.1 rightAddress.2)).prod := by
  exact BRSpec.listSymbolicFactors
    e (retainedRecipes n leftAddress.1 rightAddress.1 histories)
      leftInput rightInput leftAddress rightAddress

namespace CHSched

/-- Polynomial factors retained from one packetized inverse-oriented trace. -/
def symbolicFactors
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (schedule : CHSched M N)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    List (SPFactor H ι) :=
  HPPkt.symbolicFactors
    (n := n) schedule.histories leftInput rightInput leftAddress rightAddress

/-- Every factor retained from a packetized trace remains below the cutoff. -/
lemma weight_symbolic_factors
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {schedule : CHSched M N}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈ symbolicFactors (n := n) schedule leftInput rightInput
        leftAddress rightAddress) :
    factor.word.weight HEAddres.weight < n := by
  exact
    HPPkt.weight_symbolic_factors
      hfactor

end CHSched

end HPPkt
end TCTex
end Towers

-- Merged from InverseUniversalRecipeVocabulary.lean

/-!
# Universal cutoff recipe vocabulary for inverse Hall-Petresco collection

The retained dummy raw trace supplies a finite multiplicity-independent list
of one-block source recipes.  Every pair of source recipes can then be fed
into the recipe-only operational recollector.  This file concatenates those
finite correction trees into one cutoff vocabulary.

The vocabulary is not yet an ordered collection schedule.  It is the finite
recipe universe in which such a schedule must live.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace URVocabu

open HACoeff
open BRSpec
open BRPkt
open RRVocabu

/-- Retained one-block source recipes from the cutoff-sized dummy raw trace. -/
noncomputable def sourceRecipes
    (n leftWeight rightWeight : ℕ) :
    List BRecipe :=
  (retainedInitialRecipes n n leftWeight rightWeight).map
    IRecipe.blockRecipe

/--
Operational corrections from one source pair, omitted when the pair has
already reached the cutoff.
-/
noncomputable def operationalRecipes
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : RObstru) :
    List BRecipe :=
  if _hroot : O.weight leftWeight rightWeight < n then
    O.retainedRecipes (n := n) hleftWeight hrightWeight
  else
    []

/-- All retained operational corrections generated by dummy source pairs. -/
noncomputable def operationalCorrectionRecipes
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List BRecipe :=
  (retainedInitialRecipes n n leftWeight rightWeight).flatMap fun left =>
    (retainedInitialRecipes n n leftWeight rightWeight).flatMap fun right =>
      operationalRecipes (n := n) hleftWeight hrightWeight {
        left := left.blockRecipe
        right := right.blockRecipe
      }

/-- Finite recipe universe for the retained raw source and its positive recollection. -/
noncomputable def recipes
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List BRecipe :=
  sourceRecipes n leftWeight rightWeight ++
    operationalCorrectionRecipes n leftWeight rightWeight
      hleftWeight hrightWeight

/--
The retained operational tree of any retained dummy source pair is included
in the universal correction vocabulary.
-/
lemma recipes_subset_operational
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {left right : IRecipe}
    (hleft :
      left ∈ retainedInitialRecipes n n leftWeight rightWeight)
    (hright :
      right ∈ retainedInitialRecipes n n leftWeight rightWeight)
    (hroot :
      (RObstru.mk left.blockRecipe right.blockRecipe).weight
          leftWeight rightWeight < n) :
    (RObstru.mk left.blockRecipe right.blockRecipe).retainedRecipes
        (n := n) hleftWeight hrightWeight ⊆
      operationalCorrectionRecipes n leftWeight rightWeight
        hleftWeight hrightWeight := by
  intro R hR
  unfold operationalCorrectionRecipes
  apply List.mem_flatMap.mpr
  refine ⟨left, hleft, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨right, hright, ?_⟩
  unfold operationalRecipes
  rw [dif_pos hroot]
  exact hR

/-- Every source recipe remembers a retained dummy raw representative. -/
lemma initial_recipe_recipes
    {n leftWeight rightWeight : ℕ}
    {R : BRecipe}
    (hR : R ∈ sourceRecipes n leftWeight rightWeight) :
    ∃ source ∈ retainedInitialRecipes n n leftWeight rightWeight,
      source.blockRecipe = R := by
  exact List.mem_map.mp hR

/-- Every retained dummy source recipe lies below the cutoff. -/
lemma weighted_cutoff_recipes
    {n leftWeight rightWeight : ℕ}
    {R : BRecipe}
    (hR : R ∈ sourceRecipes n leftWeight rightWeight) :
    weightedWordWeight leftWeight rightWeight R < n := by
  rcases initial_recipe_recipes hR with
    ⟨source, hsource, rfl⟩
  exact weight_initial_recipes hsource

/-- Every retained operational correction from one pair lies below the cutoff. -/
lemma weighted_operational_recipes
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : RObstru}
    {R : BRecipe}
    (hR :
      R ∈ operationalRecipes (n := n)
        hleftWeight hrightWeight O) :
    weightedWordWeight leftWeight rightWeight R < n := by
  unfold operationalRecipes at hR
  split at hR
  · exact O.retained_recipe_cutoff ‹_› hR
  · simp at hR

/-- Every operational correction from one pair is heavier than its left source. -/
lemma left_operational_recipes
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : RObstru}
    {R : BRecipe}
    (hR :
      R ∈ operationalRecipes (n := n)
        hleftWeight hrightWeight O) :
    weightedWordWeight leftWeight rightWeight O.left <
      weightedWordWeight leftWeight rightWeight R := by
  unfold operationalRecipes at hR
  split at hR
  · exact O.left_retained_recipes hR
  · simp at hR

/-- Every operational correction from one pair is heavier than its right source. -/
lemma right_operational_recipes
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : RObstru}
    {R : BRecipe}
    (hR :
      R ∈ operationalRecipes (n := n)
        hleftWeight hrightWeight O) :
    weightedWordWeight leftWeight rightWeight O.right <
      weightedWordWeight leftWeight rightWeight R := by
  unfold operationalRecipes at hR
  split at hR
  · exact O.right_retained_recipes hR
  · simp at hR

/-- Every universal operational correction lies below the cutoff. -/
lemma weighted_correction_recipes
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {R : BRecipe}
    (hR :
      R ∈ operationalCorrectionRecipes n leftWeight rightWeight
        hleftWeight hrightWeight) :
    weightedWordWeight leftWeight rightWeight R < n := by
  unfold operationalCorrectionRecipes at hR
  rcases List.mem_flatMap.mp hR with ⟨left, _hleft, hR⟩
  rcases List.mem_flatMap.mp hR with ⟨right, _hright, hR⟩
  exact weighted_operational_recipes hR

/--
Every universal operational correction is strictly heavier than the two
retained source recipes whose recollection tree emitted it.
-/
lemma recipes_operational_correction
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {R : BRecipe}
    (hR :
      R ∈ operationalCorrectionRecipes n leftWeight rightWeight
        hleftWeight hrightWeight) :
    ∃ left ∈ sourceRecipes n leftWeight rightWeight,
      ∃ right ∈ sourceRecipes n leftWeight rightWeight,
        weightedWordWeight leftWeight rightWeight left <
            weightedWordWeight leftWeight rightWeight R ∧
          weightedWordWeight leftWeight rightWeight right <
            weightedWordWeight leftWeight rightWeight R := by
  unfold operationalCorrectionRecipes at hR
  rcases List.mem_flatMap.mp hR with ⟨left, hleft, hR⟩
  rcases List.mem_flatMap.mp hR with ⟨right, hright, hR⟩
  refine
    ⟨left.blockRecipe, List.mem_map.mpr ⟨left, hleft, rfl⟩,
      right.blockRecipe, List.mem_map.mpr ⟨right, hright, rfl⟩, ?_, ?_⟩
  · exact left_operational_recipes hR
  · exact right_operational_recipes hR

/-- Every recipe in the universal inverse vocabulary lies below the cutoff. -/
lemma weighted_word_recipes
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {R : BRecipe}
    (hR : R ∈ recipes n leftWeight rightWeight hleftWeight hrightWeight) :
    weightedWordWeight leftWeight rightWeight R < n := by
  rcases List.mem_append.mp hR with hR | hR
  · exact weighted_cutoff_recipes hR
  · exact weighted_correction_recipes hR

end URVocabu
end TCTex
end Towers

-- Merged from InverseUniversalOperationalPacketCoverage.lean

/-!
# Universal coverage of inverse operational recipe packets

Every retained raw source factor is polynomial-equivalent to a member of the
cutoff-sized dummy vocabulary.  Operational recollection preserves that
equivalence pointwise.  This file combines those facts: each correction in an
arbitrary retained raw source-pair packet has a polynomial-equivalent
representative in the finite universal correction vocabulary.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace IPCovera

open HACoeff
open BRSpec
open BRPkt
open RHRecurs
open RHRecipe
open HHTrunc
open RRVocabu
open URVocabu

/--
Pointwise list equivalence lets a member on the right be pulled back to an
equivalent member on the left.
-/
lemma left_forall₂_of_mem_right
    {alpha beta : Type*}
    {r : alpha -> beta -> Prop}
    {left : List alpha}
    {right : List beta}
    (h : List.Forall₂ r left right)
    {b : beta}
    (hb : b ∈ right) :
    ∃ a ∈ left, r a b := by
  induction h with
  | nil =>
      simp at hb
  | cons hab _ ih =>
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ⟨_, List.mem_cons_self, hab⟩
      · rcases ih hb with ⟨a, ha, hab⟩
        exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

/--
Every correction in a polynomial-equivalent concrete source-pair packet has
a representative in the universal correction vocabulary.
-/
lemma equivalent_retained_recipes
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {dummyLeft dummyRight concreteLeft concreteRight : IRecipe}
    (hdummyLeft :
      dummyLeft ∈ retainedInitialRecipes n n leftWeight rightWeight)
    (hdummyRight :
      dummyRight ∈ retainedInitialRecipes n n leftWeight rightWeight)
    (hleft :
      IRecipe.PolynomialEquivalent dummyLeft concreteLeft)
    (hright :
      IRecipe.PolynomialEquivalent dummyRight concreteRight)
    (hroot :
      (RObstru.mk concreteLeft.blockRecipe concreteRight.blockRecipe).weight
          leftWeight rightWeight < n)
    {R : BRecipe}
    (hR :
      R ∈
        (RObstru.mk concreteLeft.blockRecipe concreteRight.blockRecipe).retainedRecipes
          (n := n) hleftWeight hrightWeight) :
    ∃ universalR ∈
        operationalCorrectionRecipes n leftWeight rightWeight
          hleftWeight hrightWeight,
      RPEquiv.BRecipe.PolynomialEquivalent
        universalR R := by
  let dummyO :=
    RObstru.mk dummyLeft.blockRecipe dummyRight.blockRecipe
  let concreteO :=
    RObstru.mk concreteLeft.blockRecipe concreteRight.blockRecipe
  have hO :
      ROEquiv.RObstru.PolynomialEquivalent
        dummyO concreteO :=
    ⟨IRecipe.block_recipe_equivalent
        hleft,
      IRecipe.block_recipe_equivalent
        hright⟩
  have hrootDummy :
      dummyO.weight leftWeight rightWeight < n := by
    rw [
      ROEquiv.RObstru.weight_poly_equivalent
        hO]
    exact hroot
  have hpackets :=
    ROEquiv.RObstru.retRecps_forall₂
      (n := n) hleftWeight hrightWeight dummyO concreteO hO
  rcases left_forall₂_of_mem_right hpackets hR with
    ⟨universalR, huniversalR, hequivalent⟩
  exact
    ⟨universalR,
      recipes_subset_operational
        hdummyLeft hdummyRight hrootDummy huniversalR,
      hequivalent⟩

namespace RHistor

/-- Recipe obstruction attached to a pair of actual inverse raw histories. -/
noncomputable def obstructionOfMem
    {M N : ℕ}
    (left right : RHistor M N)
    (hleft : left ∈ inverseRawHistories M N)
    (hright : right ∈ inverseRawHistories M N) :
    RObstru :=
  RObstru.mk
    (RRVocabu.RHistor.initialRecipe
      left hleft).blockRecipe
    (RRVocabu.RHistor.initialRecipe
      right hright).blockRecipe

end RHistor

/--
Every correction in the operational packet of an arbitrary retained raw
history pair has a representative in the universal correction vocabulary.
-/
lemma universal_equivalent_recipes
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {left right : RHistor M N}
    (hleftHistory :
      left ∈
        retainedHistories n leftWeight rightWeight
          (inverseRawHistories M N))
    (hrightHistory :
      right ∈
        retainedHistories n leftWeight rightWeight
          (inverseRawHistories M N))
    (hroot :
      (IPCovera.RHistor.obstructionOfMem
        left right
        (mem_retainedHistories.mp hleftHistory).1
        (mem_retainedHistories.mp hrightHistory).1).weight
          leftWeight rightWeight < n)
    {R : BRecipe}
    (hR :
      R ∈
        (IPCovera.RHistor.obstructionOfMem
          left right
          (mem_retainedHistories.mp hleftHistory).1
          (mem_retainedHistories.mp hrightHistory).1).retainedRecipes
            (n := n) hleftWeight hrightWeight) :
    ∃ universalR ∈
        operationalCorrectionRecipes n leftWeight rightWeight
          hleftWeight hrightWeight,
      RPEquiv.BRecipe.PolynomialEquivalent
        universalR R := by
  rcases polynomial_equivalent_histories
      hleftWeight hrightWeight hleftHistory with
    ⟨dummyLeft, hdummyLeft, hleft⟩
  rcases polynomial_equivalent_histories
      hleftWeight hrightWeight hrightHistory with
    ⟨dummyRight, hdummyRight, hright⟩
  exact
    equivalent_retained_recipes
      hleftWeight hrightWeight hdummyLeft hdummyRight hleft hright hroot hR

/--
The complete operational correction packet of an arbitrary retained raw
history pair has an ordered pointwise-equivalent representative packet drawn
from the finite universal vocabulary.
-/
lemma universal_packet_forall₂_of_mem_retainedHistories
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {left right : RHistor M N}
    (hleftHistory :
      left ∈
        retainedHistories n leftWeight rightWeight
          (inverseRawHistories M N))
    (hrightHistory :
      right ∈
        retainedHistories n leftWeight rightWeight
          (inverseRawHistories M N))
    (hroot :
      (IPCovera.RHistor.obstructionOfMem
        left right
        (mem_retainedHistories.mp hleftHistory).1
        (mem_retainedHistories.mp hrightHistory).1).weight
          leftWeight rightWeight < n) :
    ∃ universalPacket : List BRecipe,
      (∀ R ∈ universalPacket,
        R ∈ operationalCorrectionRecipes n leftWeight rightWeight
          hleftWeight hrightWeight) ∧
      List.Forall₂
        RPEquiv.BRecipe.PolynomialEquivalent
        universalPacket
        ((IPCovera.RHistor.obstructionOfMem
          left right
          (mem_retainedHistories.mp hleftHistory).1
          (mem_retainedHistories.mp hrightHistory).1).retainedRecipes
            (n := n) hleftWeight hrightWeight) := by
  rcases polynomial_equivalent_histories
      hleftWeight hrightWeight hleftHistory with
    ⟨dummyLeft, hdummyLeft, hleft⟩
  rcases polynomial_equivalent_histories
      hleftWeight hrightWeight hrightHistory with
    ⟨dummyRight, hdummyRight, hright⟩
  let dummyO :=
    RObstru.mk dummyLeft.blockRecipe dummyRight.blockRecipe
  let concreteO :=
    IPCovera.RHistor.obstructionOfMem
      left right
      (mem_retainedHistories.mp hleftHistory).1
      (mem_retainedHistories.mp hrightHistory).1
  have hO :
      ROEquiv.RObstru.PolynomialEquivalent
        dummyO concreteO :=
    ⟨IRecipe.block_recipe_equivalent
        hleft,
      IRecipe.block_recipe_equivalent
        hright⟩
  have hrootDummy :
      dummyO.weight leftWeight rightWeight < n := by
    rw [
      ROEquiv.RObstru.weight_poly_equivalent
        hO]
    exact hroot
  refine
    ⟨dummyO.retainedRecipes (n := n) hleftWeight hrightWeight, ?_, ?_⟩
  · intro R hR
    exact
      recipes_subset_operational
        hdummyLeft hdummyRight hrootDummy hR
  · exact
      ROEquiv.RObstru.retRecps_forall₂
        (n := n) hleftWeight hrightWeight dummyO concreteO hO

/--
The ordered universal representative packet has the same specialized
evaluation as the concrete raw-history operational packet.
-/
lemma universal_packet_histories
    {M N n leftWeight rightWeight d truncation : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {left right : RHistor M N}
    (hleftHistory :
      left ∈
        retainedHistories n leftWeight rightWeight
          (inverseRawHistories M N))
    (hrightHistory :
      right ∈
        retainedHistories n leftWeight rightWeight
          (inverseRawHistories M N))
    (hroot :
      (IPCovera.RHistor.obstructionOfMem
        left right
        (mem_retainedHistories.mp hleftHistory).1
        (mem_retainedHistories.mp hrightHistory).1).weight
          leftWeight rightWeight < n)
    (e : ι → HEFam H)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    ∃ universalPacket : List BRecipe,
      (∀ R ∈ universalPacket,
        R ∈ operationalCorrectionRecipes n leftWeight rightWeight
          hleftWeight hrightWeight) ∧
      SPFactor.listEval (n := truncation) e
          (BRSpec.symbolicFactors
            universalPacket leftInput rightInput leftAddress rightAddress) =
        SPFactor.listEval (n := truncation) e
          (BRSpec.symbolicFactors
            ((IPCovera.RHistor.obstructionOfMem
              left right
              (mem_retainedHistories.mp hleftHistory).1
              (mem_retainedHistories.mp hrightHistory).1).retainedRecipes
                (n := n) hleftWeight hrightWeight)
            leftInput rightInput leftAddress rightAddress) := by
  rcases universal_packet_forall₂_of_mem_retainedHistories
      hleftWeight hrightWeight hleftHistory hrightHistory hroot with
    ⟨universalPacket, huniversalPacket, hequivalent⟩
  exact
    ⟨universalPacket, huniversalPacket,
      RPEquiv.symbolic_factors_forall₂_polynomialEquivalent
        hequivalent e leftInput rightInput leftAddress rightAddress⟩

end IPCovera
end TCTex
end Towers

-- Merged from InverseUniversalRecipePrincipalSeparation.lean

/-!
# Separating the principal recipe from universal operational corrections

The universal inverse vocabulary contains retained raw source recipes followed
by recursively emitted operational corrections.  The correction region cannot
emit the principal `basic` recipe: every positive recipe has weighted degree
at least the basic degree, while each operational correction is strictly
heavier than its parents.

This isolates the principal-inventory fact needed when an ordered universal
packet is later constructed.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

open HACoeff

namespace BRSpec

/--
Every positive block recipe has weighted degree at least that of the principal
basic recipe.
-/
lemma weighted_weight_basic
    (leftWeight rightWeight : ℕ)
    (R : BRecipe) :
    weightedWordWeight leftWeight rightWeight hallPair ≤
      weightedWordWeight leftWeight rightWeight R := by
  rw [weighted_word_pair, weighted_word_weight]
  have hleft :
      leftWeight ≤ R.leftDegree * leftWeight :=
    Nat.le_mul_of_pos_left leftWeight (leftDegree_pos R)
  have hright :
      rightWeight ≤ R.rightDegree * rightWeight :=
    Nat.le_mul_of_pos_left rightWeight (rightDegree_pos R)
  omega

end BRSpec

namespace BRPkt
namespace RObstru

open BRSpec

/--
Every recursively emitted operational correction has bidegree different from
the principal bidegree `(1, 1)`.
-/
lemma bidegree_retained_recipes
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : RObstru}
    {R : BRecipe}
    (hR : R ∈ retainedRecipes (n := n) hleftWeight hrightWeight O) :
    R.leftDegree ≠ 1 ∨ R.rightDegree ≠ 1 := by
  by_contra hdegree
  push Not at hdegree
  have hmin :
      weightedWordWeight leftWeight rightWeight hallPair ≤
        weightedWordWeight leftWeight rightWeight O.left :=
    weighted_weight_basic leftWeight rightWeight O.left
  have hstrict :
      weightedWordWeight leftWeight rightWeight O.left <
        weightedWordWeight leftWeight rightWeight R :=
    left_retained_recipes hR
  have hRweight :
      weightedWordWeight leftWeight rightWeight R =
        weightedWordWeight leftWeight rightWeight hallPair := by
    simp [weighted_word_weight, hdegree.1, hdegree.2]
  omega

/-- No recursively emitted operational correction is the principal recipe. -/
lemma ne_retained_recipes
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : RObstru}
    {R : BRecipe}
    (hR : R ∈ retainedRecipes (n := n) hleftWeight hrightWeight O) :
    R ≠ hallPair := by
  intro hRbasic
  have hdegree := bidegree_retained_recipes hR
  rw [hRbasic] at hdegree
  exact hdegree.elim (fun h => h left_hall_pair) (fun h => h right_degree_pair)

end RObstru
end BRPkt

namespace URVocabu

open BRPkt
open BRSpec

/--
Every correction emitted for one retained source pair has bidegree different
from `(1, 1)`.
-/
lemma not_bidegree_recipes
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : RObstru}
    {R : BRecipe}
    (hR :
      R ∈ operationalRecipes (n := n)
        hleftWeight hrightWeight O) :
    R.leftDegree ≠ 1 ∨ R.rightDegree ≠ 1 := by
  unfold operationalRecipes at hR
  split at hR
  · exact O.bidegree_retained_recipes hR
  · simp at hR

/-- No correction emitted for one retained source pair is `basic`. -/
lemma ne_operational_recipes
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : RObstru}
    {R : BRecipe}
    (hR :
      R ∈ operationalRecipes (n := n)
        hleftWeight hrightWeight O) :
    R ≠ hallPair := by
  intro hRbasic
  have hdegree :=
    not_bidegree_recipes hR
  rw [hRbasic] at hdegree
  exact hdegree.elim (fun h => h left_hall_pair) (fun h => h right_degree_pair)

/--
The complete universal operational-correction vocabulary is a strict outer
tail: every member has bidegree different from `(1, 1)`.
-/
lemma bidegree_operational_recipes
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {R : BRecipe}
    (hR :
      R ∈ operationalCorrectionRecipes n leftWeight rightWeight
        hleftWeight hrightWeight) :
    R.leftDegree ≠ 1 ∨ R.rightDegree ≠ 1 := by
  unfold operationalCorrectionRecipes at hR
  rcases List.mem_flatMap.mp hR with ⟨left, _hleft, hR⟩
  rcases List.mem_flatMap.mp hR with ⟨right, _hright, hR⟩
  exact not_bidegree_recipes hR

/-- No member of the universal operational-correction vocabulary is `basic`. -/
lemma ne_basic_recipes
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {R : BRecipe}
    (hR :
      R ∈ operationalCorrectionRecipes n leftWeight rightWeight
        hleftWeight hrightWeight) :
    R ≠ hallPair := by
  intro hRbasic
  have hdegree :=
    bidegree_operational_recipes hR
  rw [hRbasic] at hdegree
  exact hdegree.elim (fun h => h left_hall_pair) (fun h => h right_degree_pair)

/-- The universal operational-correction vocabulary does not contain `basic`. -/
lemma basic_operational_recipes
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight} :
    hallPair ∉
      operationalCorrectionRecipes n leftWeight rightWeight
        hleftWeight hrightWeight := by
  intro hbasic
  exact ne_basic_recipes hbasic rfl

/--
If the retained raw-source vocabulary has one distinguished `basic`
occurrence, adjoining every recursively generated operational correction
preserves that unique occurrence.
-/
lemma unique_split_recipes
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (hsource :
      ∃ beforeBasic afterBasic : List BRecipe,
        sourceRecipes n leftWeight rightWeight =
            beforeBasic ++ hallPair :: afterBasic ∧
          hallPair ∉ beforeBasic ∧
            hallPair ∉ afterBasic) :
    ∃ beforeBasic afterBasic : List BRecipe,
      recipes n leftWeight rightWeight hleftWeight hrightWeight =
          beforeBasic ++ hallPair :: afterBasic ∧
        hallPair ∉ beforeBasic ∧
          hallPair ∉ afterBasic := by
  rcases hsource with
    ⟨beforeBasic, afterBasic, hsource, hbasicNotBefore, hbasicNotAfter⟩
  refine
    ⟨beforeBasic,
      afterBasic ++
        operationalCorrectionRecipes n leftWeight rightWeight
          hleftWeight hrightWeight,
      ?_, hbasicNotBefore, ?_⟩
  · rw [recipes, hsource, List.append_assoc]
    rfl
  · simp only [List.mem_append, not_or]
    exact
      ⟨hbasicNotAfter,
        basic_operational_recipes⟩

end URVocabu

end TCTex
end Towers

-- Merged from InverseUniversalRawPacketEnvelope.lean

/-!
# Universal envelopes for truncated inverse raw packets

The cutoff-sized dummy inverse trace supplies a finite source-recipe
vocabulary.  Every retained raw-history occurrence at arbitrary source
multiplicities has a polynomial-equivalent representative in that vocabulary.

This file chooses those representatives coherently across the complete
retained occurrence list.  It also applies the recipe-only operational
recollector to every pair of retained occurrences and proves that the
resulting universal correction envelope is supported in the finite universal
vocabulary and has the same ordered specialized evaluation as the concrete
envelope.

The envelope deliberately remains larger than the genuine support-compatible
collection schedule.  It is a finite-support reduction for the later uniform
normalization theorem, not a replacement for compatible-grid routing.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace RPEnvelo

universe u

open HACoeff
open ROEquiv
open BRPkt
open RPEquiv
open BRSpec
open RHRecurs
open RHRecipe
open HHTrunc
open RRVocabu
open URVocabu

/-- One retained raw-history occurrence at arbitrary source multiplicities. -/
abbrev RetainedRawHistory
    (M N n leftWeight rightWeight : ℕ) :=
  { history : RHistor M N //
    history ∈
      HHTrunc.retainedHistories
        n leftWeight rightWeight (inverseRawHistories M N) }

/-- The retained raw-history list with occurrence membership attached. -/
def rawHistoriesAttached
    (M N n leftWeight rightWeight : ℕ) :
    List (RetainedRawHistory M N n leftWeight rightWeight) :=
  (HHTrunc.retainedHistories
    n leftWeight rightWeight (inverseRawHistories M N)).attach

/-- Standardized concrete recipe carried by one retained raw occurrence. -/
noncomputable def initialRawHistory
    {M N n leftWeight rightWeight : ℕ}
    (history : RetainedRawHistory M N n leftWeight rightWeight) :
    IRecipe :=
  RRVocabu.RHistor.initialRecipe
    history.1
      (HHTrunc.mem_retainedHistories.mp
        history.2).1

/-- Choose one cutoff-vocabulary representative of a retained raw occurrence. -/
noncomputable def universalRawHistory
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (history : RetainedRawHistory M N n leftWeight rightWeight) :
    IRecipe :=
  Classical.choose
    (polynomial_equivalent_histories
      hleftWeight hrightWeight history.2)

/-- Every chosen source representative belongs to the finite dummy vocabulary. -/
lemma universal_raw_history
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (history : RetainedRawHistory M N n leftWeight rightWeight) :
    universalRawHistory
        hleftWeight hrightWeight history ∈
      retainedInitialRecipes n n leftWeight rightWeight :=
  (Classical.choose_spec
    (polynomial_equivalent_histories
      hleftWeight hrightWeight history.2)).1

/-- The chosen source recipe has the same symbolic polynomial data. -/
lemma universal_history_equivalent
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (history : RetainedRawHistory M N n leftWeight rightWeight) :
    IRecipe.PolynomialEquivalent
      (universalRawHistory
        hleftWeight hrightWeight history)
      (initialRawHistory history) :=
  (Classical.choose_spec
    (polynomial_equivalent_histories
      hleftWeight hrightWeight history.2)).2

/-- Chosen vocabulary-supported source packet for all retained occurrences. -/
noncomputable def universalSourcePacket
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List BRecipe :=
  (rawHistoriesAttached M N n leftWeight rightWeight).map
    fun history =>
      (universalRawHistory
        hleftWeight hrightWeight history).blockRecipe

/-- Concrete standardized source packet for all retained occurrences. -/
noncomputable def concreteSourcePacket
    (M N n leftWeight rightWeight : ℕ) :
    List BRecipe :=
  (rawHistoriesAttached M N n leftWeight rightWeight).map
    fun history =>
      (initialRawHistory history).blockRecipe

/-- The chosen source packet is supported in the finite universal vocabulary. -/
lemma recipes_universal_packet
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {R : BRecipe}
    (hR :
      R ∈ universalSourcePacket
        M N n leftWeight rightWeight hleftWeight hrightWeight) :
    R ∈ sourceRecipes n leftWeight rightWeight := by
  rcases List.mem_map.mp hR with ⟨history, _hhistory, rfl⟩
  exact
    List.mem_map.mpr
      ⟨universalRawHistory
          hleftWeight hrightWeight history,
        universal_raw_history
          hleftWeight hrightWeight history,
        rfl⟩

/-- The universal and concrete retained source packets are pointwise equivalent. -/
lemma universal_source_forall₂
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List.Forall₂
      RPEquiv.BRecipe.PolynomialEquivalent
      (universalSourcePacket
        M N n leftWeight rightWeight hleftWeight hrightWeight)
      (concreteSourcePacket M N n leftWeight rightWeight) := by
  unfold universalSourcePacket concreteSourcePacket
  induction rawHistoriesAttached M N n leftWeight rightWeight with
  | nil =>
      exact List.Forall₂.nil
  | cons history histories ih =>
      exact
        List.Forall₂.cons
          (IRecipe.block_recipe_equivalent
            (universal_history_equivalent
              hleftWeight hrightWeight history))
          ih

/-- The chosen source packet preserves every ordered symbolic specialization. -/
lemma list_universal_concrete
    {M N n leftWeight rightWeight d truncation : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (e : ι → HEFam H)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    SPFactor.listEval (n := truncation) e
        (symbolicFactors
          (universalSourcePacket
            M N n leftWeight rightWeight hleftWeight hrightWeight)
          leftInput rightInput leftAddress rightAddress) =
      SPFactor.listEval (n := truncation) e
        (symbolicFactors
          (concreteSourcePacket M N n leftWeight rightWeight)
          leftInput rightInput leftAddress rightAddress) := by
  exact
    symbolic_factors_forall₂_polynomialEquivalent
      (universal_source_forall₂
        M N n leftWeight rightWeight hleftWeight hrightWeight)
      e leftInput rightInput leftAddress rightAddress

/-- Concrete recipe obstruction attached to a pair of retained occurrences. -/
noncomputable def concreteObstruction
    {M N n leftWeight rightWeight : ℕ}
    (left right : RetainedRawHistory M N n leftWeight rightWeight) :
    RObstru where
  left := (initialRawHistory left).blockRecipe
  right := (initialRawHistory right).blockRecipe

/-- Universal recipe obstruction chosen for a pair of retained occurrences. -/
noncomputable def universalObstruction
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : RetainedRawHistory M N n leftWeight rightWeight) :
    RObstru where
  left :=
    (universalRawHistory
      hleftWeight hrightWeight left).blockRecipe
  right :=
    (universalRawHistory
      hleftWeight hrightWeight right).blockRecipe

/-- Chosen and concrete source-pair obstructions are polynomial-equivalent. -/
lemma universal_obstruction_equivalent
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : RetainedRawHistory M N n leftWeight rightWeight) :
    ROEquiv.RObstru.PolynomialEquivalent
      (universalObstruction hleftWeight hrightWeight left right)
      (concreteObstruction left right) :=
  ⟨IRecipe.block_recipe_equivalent
      (universal_history_equivalent
        hleftWeight hrightWeight left),
    IRecipe.block_recipe_equivalent
      (universal_history_equivalent
        hleftWeight hrightWeight right)⟩

/-- Universal operational correction packet for one retained source pair. -/
noncomputable def universalOperationalCorrection
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : RetainedRawHistory M N n leftWeight rightWeight) :
    List BRecipe :=
  operationalRecipes (n := n) hleftWeight hrightWeight
    (universalObstruction hleftWeight hrightWeight left right)

/-- Concrete operational correction packet for one retained source pair. -/
noncomputable def concreteOperationalPacket
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : RetainedRawHistory M N n leftWeight rightWeight) :
    List BRecipe :=
  operationalRecipes (n := n) hleftWeight hrightWeight
    (concreteObstruction left right)

/--
The chosen correction packet is supported in the universal correction
vocabulary.
-/
lemma operational_recipes_universal
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : RetainedRawHistory M N n leftWeight rightWeight)
    {R : BRecipe}
    (hR :
      R ∈ universalOperationalCorrection
        hleftWeight hrightWeight left right) :
    R ∈ operationalCorrectionRecipes
      n leftWeight rightWeight hleftWeight hrightWeight := by
  unfold universalOperationalCorrection at hR
  unfold operationalRecipes at hR
  split at hR
  · exact
      recipes_subset_operational
        (universal_raw_history
          hleftWeight hrightWeight left)
        (universal_raw_history
          hleftWeight hrightWeight right)
        ‹_› hR
  · simp at hR

/-- One chosen and concrete correction packet are pointwise equivalent. -/
lemma universal_operational_forall₂
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (left right : RetainedRawHistory M N n leftWeight rightWeight) :
    List.Forall₂
      RPEquiv.BRecipe.PolynomialEquivalent
      (universalOperationalCorrection
        hleftWeight hrightWeight left right)
      (concreteOperationalPacket
        hleftWeight hrightWeight left right) := by
  unfold universalOperationalCorrection
  unfold concreteOperationalPacket
  unfold operationalRecipes
  have hequivalent :=
    universal_obstruction_equivalent
      hleftWeight hrightWeight left right
  by_cases hroot :
      (universalObstruction hleftWeight hrightWeight left right).weight
        leftWeight rightWeight < n
  · have hrootConcrete :
        (concreteObstruction left right).weight leftWeight rightWeight < n := by
      rw [← RObstru.weight_poly_equivalent hequivalent]
      exact hroot
    rw [dif_pos hroot, dif_pos hrootConcrete]
    exact
      RObstru.retRecps_forall₂
        hleftWeight hrightWeight _ _ hequivalent
  · have hrootConcrete :
        ¬(concreteObstruction left right).weight leftWeight rightWeight < n := by
      intro h
      apply hroot
      rw [RObstru.weight_poly_equivalent hequivalent]
      exact h
    rw [dif_neg hroot, dif_neg hrootConcrete]
    exact List.Forall₂.nil

/-- `Forall₂` is preserved by applying two pointwise-related `flatMap`s. -/
lemma forall₂_flatMap_same
    {alpha beta : Type*}
    {relation : beta → beta → Prop}
    (items : List alpha)
    (left right : alpha → List beta)
    (h :
      ∀ item ∈ items,
        List.Forall₂ relation (left item) (right item)) :
    List.Forall₂ relation (items.flatMap left) (items.flatMap right) := by
  induction items with
  | nil =>
      exact List.Forall₂.nil
  | cons item items ih =>
      simp only [List.flatMap_cons]
      exact List.rel_append
        (h item List.mem_cons_self)
        (ih fun next hnext => h next (List.mem_cons_of_mem _ hnext))

/-- Universal correction envelope over every pair of retained occurrences. -/
noncomputable def universalCorrectionEnvelope
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List BRecipe :=
  (rawHistoriesAttached M N n leftWeight rightWeight).flatMap
    fun left =>
      (rawHistoriesAttached M N n leftWeight rightWeight).flatMap
        fun right =>
          universalOperationalCorrection
            hleftWeight hrightWeight left right

/-- Concrete correction envelope over every pair of retained occurrences. -/
noncomputable def concreteOperationalEnvelope
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List BRecipe :=
  (rawHistoriesAttached M N n leftWeight rightWeight).flatMap
    fun left =>
      (rawHistoriesAttached M N n leftWeight rightWeight).flatMap
        fun right =>
          concreteOperationalPacket
            hleftWeight hrightWeight left right

/-- The universal correction envelope is supported in the finite vocabulary. -/
lemma operational_recipes_envelope
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {R : BRecipe}
    (hR :
      R ∈ universalCorrectionEnvelope
        M N n leftWeight rightWeight hleftWeight hrightWeight) :
    R ∈ operationalCorrectionRecipes
      n leftWeight rightWeight hleftWeight hrightWeight := by
  rcases List.mem_flatMap.mp hR with ⟨left, _hleft, hR⟩
  rcases List.mem_flatMap.mp hR with ⟨right, _hright, hR⟩
  exact
    operational_recipes_universal
      hleftWeight hrightWeight left right hR

/-- Universal and concrete correction envelopes are pointwise equivalent. -/
lemma universal_envelope_forall₂
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List.Forall₂
      RPEquiv.BRecipe.PolynomialEquivalent
      (universalCorrectionEnvelope
        M N n leftWeight rightWeight hleftWeight hrightWeight)
      (concreteOperationalEnvelope
        M N n leftWeight rightWeight hleftWeight hrightWeight) := by
  unfold universalCorrectionEnvelope
  unfold concreteOperationalEnvelope
  apply forall₂_flatMap_same
  intro left _hleft
  apply forall₂_flatMap_same
  intro right _hright
  exact
    universal_operational_forall₂
      hleftWeight hrightWeight left right

/-- The universal correction envelope preserves every symbolic specialization. -/
lemma operational_envelope_concrete
    {M N n leftWeight rightWeight d truncation : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (e : ι → HEFam H)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    SPFactor.listEval (n := truncation) e
        (symbolicFactors
          (universalCorrectionEnvelope
            M N n leftWeight rightWeight hleftWeight hrightWeight)
          leftInput rightInput leftAddress rightAddress) =
      SPFactor.listEval (n := truncation) e
        (symbolicFactors
          (concreteOperationalEnvelope
            M N n leftWeight rightWeight hleftWeight hrightWeight)
          leftInput rightInput leftAddress rightAddress) := by
  exact
    symbolic_factors_forall₂_polynomialEquivalent
      (universal_envelope_forall₂
        M N n leftWeight rightWeight hleftWeight hrightWeight)
      e leftInput rightInput leftAddress rightAddress

/--
Finite universal envelope containing all chosen source representatives and
all chosen pairwise correction representatives.
-/
noncomputable def universalPacketEnvelope
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List BRecipe :=
  universalSourcePacket
      M N n leftWeight rightWeight hleftWeight hrightWeight ++
    universalCorrectionEnvelope
      M N n leftWeight rightWeight hleftWeight hrightWeight

/-- Concrete source-and-correction envelope before universal replacement. -/
noncomputable def concretePacketEnvelope
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List BRecipe :=
  concreteSourcePacket M N n leftWeight rightWeight ++
    concreteOperationalEnvelope
      M N n leftWeight rightWeight hleftWeight hrightWeight

/-- Every chosen recipe belongs to the finite universal cutoff vocabulary. -/
lemma recipes_universal_envelope
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {R : BRecipe}
    (hR :
      R ∈ universalPacketEnvelope
        M N n leftWeight rightWeight hleftWeight hrightWeight) :
    R ∈ recipes n leftWeight rightWeight hleftWeight hrightWeight := by
  rcases List.mem_append.mp hR with hR | hR
  · exact List.mem_append_left _
      (recipes_universal_packet
        hleftWeight hrightWeight hR)
  · exact List.mem_append_right _
      (operational_recipes_envelope
        hleftWeight hrightWeight hR)

/-- Every chosen recipe remains strictly below the cutoff. -/
lemma weighted_universal_envelope
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {R : BRecipe}
    (hR :
      R ∈ universalPacketEnvelope
        M N n leftWeight rightWeight hleftWeight hrightWeight) :
    weightedWordWeight leftWeight rightWeight R < n :=
  weighted_word_recipes
    (recipes_universal_envelope
      hleftWeight hrightWeight hR)

/-- Universal replacement preserves the complete source-and-correction envelope. -/
lemma packet_envelope_forall₂
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List.Forall₂
      RPEquiv.BRecipe.PolynomialEquivalent
      (universalPacketEnvelope
        M N n leftWeight rightWeight hleftWeight hrightWeight)
      (concretePacketEnvelope
        M N n leftWeight rightWeight hleftWeight hrightWeight) := by
  exact List.rel_append
    (universal_source_forall₂
      M N n leftWeight rightWeight hleftWeight hrightWeight)
    (universal_envelope_forall₂
      M N n leftWeight rightWeight hleftWeight hrightWeight)

/-- The complete finite universal envelope preserves symbolic specialization. -/
lemma list_envelope_concrete
    {M N n leftWeight rightWeight d truncation : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (e : ι → HEFam H)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    SPFactor.listEval (n := truncation) e
        (symbolicFactors
          (universalPacketEnvelope
            M N n leftWeight rightWeight hleftWeight hrightWeight)
          leftInput rightInput leftAddress rightAddress) =
      SPFactor.listEval (n := truncation) e
        (symbolicFactors
          (concretePacketEnvelope
            M N n leftWeight rightWeight hleftWeight hrightWeight)
          leftInput rightInput leftAddress rightAddress) := by
  exact
    symbolic_factors_forall₂_polynomialEquivalent
      (packet_envelope_forall₂
        M N n leftWeight rightWeight hleftWeight hrightWeight)
      e leftInput rightInput leftAddress rightAddress

end RPEnvelo
end TCTex
end Towers
