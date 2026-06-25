import Towers.Group.Zassenhaus.CompletePetrescoRecipe
import Towers.Group.Zassenhaus.TruncatedTraceEvaluation
import Towers.Group.Zassenhaus.BlockFamily
import Towers.Group.Zassenhaus.PositiveDegreeRecipes
import Towers.Group.Zassenhaus.SymbolicHallSteps


/-!
# Natural compression of Hall-Petresco block-family packets

A scheduled endpoint is an ordered list of complete counted block families.
At natural source multiplicities, forgetting the concrete realization slots
and retaining only their recipes preserves evaluation.  This is the exact
natural-multiplicity predecessor of the all-integral atomic packet law.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace RNCompre

universe u

open scoped commutatorElement

open HACoeff
open BFTrunc
open BRSpec
open ITEvalua

/--
Compress an ordered list of complete counted families into its symbolic recipe
evaluation at natural source multiplicities.
-/
lemma collapsed_realization_cast
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (x y : G) :
    ∀ families : List (BFam M N),
      collapsedList x y (BFam.realizationList families) =
        ((families.map BFam.recipe).map fun R =>
          R.erasedShape.eval (HPAtom.eval x y) ^
            coefficientValue R (M : ℤ) (N : ℤ)).prod
  | [] => by
      rfl
  | family :: families => by
      rw [BFam.realizationList_cons, collapsed_list_append,
        BFam.collli_eqera_coeva,
        collapsed_realization_cast x y families]
      rfl

namespace TFPkt

/--
The recipe list of a fixed natural-multiplicity scheduled endpoint satisfies
the atomic packet product law at its generating natural exponents.
-/
lemma recipe_cast_pow
    {M N n leftWeight rightWeight : ℕ}
    (packet : TFPkt.{u} M N n leftWeight rightWeight)
    {G : Type u}
    [Group G]
    (x y : G)
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥) :
    (((packet.families.map BFam.recipe).map fun R =>
      R.erasedShape.eval (HPAtom.eval x y) ^
        coefficientValue R (M : ℤ) (N : ℤ)).prod) =
      ⁅x ^ M, y ^ N⁆ := by
  rw [← collapsed_realization_cast x y]
  exact packet.collapsed_list_eval (G := G) x y hx hy hbot

end TFPkt
end RNCompre
end TCTex
end Towers

/-!
# Recipe-only operational recursive Hall-Petresco packets

The concrete operational obstruction tree is indexed by counted
`BFam`s, but its branch decisions and emitted recipes depend only on the
underlying `BRecipe`s and their weighted degrees.  This file records that
recipe-only recursion and proves that every concrete family packet projects to
it.

Unlike the initial inverse raw trace, this recursion starts after positive
block recipes already exist.  Raw source atoms remain outside this layer.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace BRPkt

open HACoeff
open BRSpec
open FRObstr

/-- One adjacent pair of positive recipes still requiring operational collection. -/
structure RObstru where
  left :
    BRecipe
  right :
    BRecipe

namespace RObstru

/-- Total weighted Hall degree of one recipe obstruction. -/
def weight
    (leftWeight rightWeight : ℕ)
    (O : RObstru) :
    ℕ :=
  weightedWordWeight leftWeight rightWeight O.left +
    weightedWordWeight leftWeight rightWeight O.right

/-- Leading correction recipe emitted by one recipe obstruction. -/
def correction
    (O : RObstru) :
    BRecipe :=
  O.left.correction O.right

/-- Operational child created when the left parent crosses the emitted correction. -/
def operationalNestedLeft
    (O : RObstru) :
    RObstru where
  left := O.left
  right := O.correction

/-- Operational child created when the right parent crosses the emitted correction. -/
def operationalNestedRight
    (O : RObstru) :
    RObstru where
  left := O.right
  right := O.correction

@[simp]
lemma weight_nested_left
    (leftWeight rightWeight : ℕ)
    (O : RObstru) :
    O.operationalNestedLeft.weight leftWeight rightWeight =
      2 * weightedWordWeight leftWeight rightWeight O.left +
        weightedWordWeight leftWeight rightWeight O.right := by
  change
    weightedWordWeight leftWeight rightWeight O.left +
          weightedWordWeight leftWeight rightWeight
            (O.left.correction O.right) =
      2 * weightedWordWeight leftWeight rightWeight O.left +
        weightedWordWeight leftWeight rightWeight O.right
  rw [weighted_weight_correction]
  omega

@[simp]
lemma weight_operational_right
    (leftWeight rightWeight : ℕ)
    (O : RObstru) :
    O.operationalNestedRight.weight leftWeight rightWeight =
      weightedWordWeight leftWeight rightWeight O.left +
        2 * weightedWordWeight leftWeight rightWeight O.right := by
  change
    weightedWordWeight leftWeight rightWeight O.right +
          weightedWordWeight leftWeight rightWeight
            (O.left.correction O.right) =
      weightedWordWeight leftWeight rightWeight O.left +
        2 * weightedWordWeight leftWeight rightWeight O.right
  rw [weighted_weight_correction]
  omega

/-- Every operational left child has strictly larger weighted degree. -/
lemma weight_operational_left
    {leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : RObstru) :
    O.weight leftWeight rightWeight <
      O.operationalNestedLeft.weight leftWeight rightWeight := by
  rw [weight_nested_left]
  unfold weight
  have hleft := weighted_weight_pos hleftWeight hrightWeight O.left
  omega

/-- Every operational right child has strictly larger weighted degree. -/
lemma weight_operational_nested
    {leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : RObstru) :
    O.weight leftWeight rightWeight <
      O.operationalNestedRight.weight leftWeight rightWeight := by
  rw [weight_operational_right]
  unfold weight
  have hright := weighted_weight_pos hleftWeight hrightWeight O.right
  omega

/-- Remaining room below the cutoff for one recipe obstruction. -/
def defect
    (n leftWeight rightWeight : ℕ)
    (O : RObstru) :
    ℕ :=
  n - O.weight leftWeight rightWeight

/-- Operational recipe obstructions descend when their cutoff defect decreases. -/
def Descends
    (n leftWeight rightWeight : ℕ)
    (child parent : RObstru) :
    Prop :=
  child.defect n leftWeight rightWeight <
    parent.defect n leftWeight rightWeight

/-- Recipe-obstruction descent is well-founded. -/
lemma descends_wellFounded
    (n leftWeight rightWeight : ℕ) :
    WellFounded (Descends n leftWeight rightWeight) := by
  unfold Descends
  exact InvImage.wf (defect n leftWeight rightWeight) Nat.lt_wfRel.wf

/-- Every surviving operational left child strictly descends in cutoff defect. -/
lemma nestedLeftDescends
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : RObstru)
    (hcutoff : O.operationalNestedLeft.weight leftWeight rightWeight < n) :
    Descends n leftWeight rightWeight O.operationalNestedLeft O := by
  unfold Descends defect
  have hweight := O.weight_operational_left hleftWeight hrightWeight
  omega

/-- Every surviving operational right child strictly descends in cutoff defect. -/
lemma nestedRightDescends
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : RObstru)
    (hcutoff : O.operationalNestedRight.weight leftWeight rightWeight < n) :
    Descends n leftWeight rightWeight O.operationalNestedRight O := by
  unfold Descends defect
  have hweight := O.weight_operational_nested hleftWeight hrightWeight
  omega

/--
Finite cutoff-specific list of recipes emitted by the operational recursion.
Its definition does not mention concrete source multiplicities.
-/
noncomputable def retainedRecipes
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : RObstru) :
    List BRecipe :=
  (descends_wellFounded n leftWeight rightWeight).fix
    (fun parent recurse =>
      parent.correction ::
        (if hleft :
            parent.operationalNestedLeft.weight leftWeight rightWeight < n then
          recurse parent.operationalNestedLeft
            (parent.nestedLeftDescends
              hleftWeight hrightWeight hleft)
        else []) ++
        (if hright :
            parent.operationalNestedRight.weight leftWeight rightWeight < n then
          recurse parent.operationalNestedRight
            (parent.nestedRightDescends
              hleftWeight hrightWeight hright)
        else []))
    O

/-- Recipe-only packets expose their root-and-operational-children recurrence. -/
lemma recipes_cons_append
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : RObstru) :
    retainedRecipes (n := n) hleftWeight hrightWeight O =
      O.correction ::
        (if _hleft :
            O.operationalNestedLeft.weight leftWeight rightWeight < n then
          retainedRecipes (n := n) hleftWeight hrightWeight
            O.operationalNestedLeft
        else []) ++
        (if _hright :
            O.operationalNestedRight.weight leftWeight rightWeight < n then
          retainedRecipes (n := n) hleftWeight hrightWeight
            O.operationalNestedRight
        else []) := by
  rw [retainedRecipes, WellFounded.fix_eq]
  split <;> split <;> rfl

/-- Forget concrete realization slots in a family obstruction. -/
def ofFamily
    {M N : ℕ}
    (O : FObstru M N) :
    RObstru where
  left := O.left.recipe
  right := O.right.recipe

@[simp]
lemma weight_ofFamily
    {M N leftWeight rightWeight : ℕ}
    (O : FObstru M N) :
    (ofFamily O).weight leftWeight rightWeight =
      O.weight leftWeight rightWeight :=
  rfl

@[simp]
lemma correction_ofFamily
    {M N : ℕ}
    (O : FObstru M N) :
    (ofFamily O).correction = O.correction.recipe :=
  rfl

@[simp]
lemma operational_left_family
    {M N : ℕ}
    (O : FObstru M N) :
    ofFamily
        (BFOrient.FObstru.operationalNestedLeft
          O) =
      (ofFamily O).operationalNestedLeft :=
  rfl

@[simp]
lemma operational_nested_family
    {M N : ℕ}
    (O : FObstru M N) :
    ofFamily
        (BFOrient.FObstru.operationalNestedRight
          O) =
      (ofFamily O).operationalNestedRight :=
  rfl

/--
Projecting the concrete operational family packet to recipes gives the
multiplicity-independent recipe-only packet.
-/
lemma retained_recipes_family
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    ∀ O : FObstru M N,
      ORPkt.retainedRecipes
          (n := n) hleftWeight hrightWeight O =
        retainedRecipes (n := n) hleftWeight hrightWeight (ofFamily O) := by
  intro O
  refine FObstru.descends_induction (n := n)
    (leftWeight := leftWeight) (rightWeight := rightWeight)
    (motive := fun O =>
      ORPkt.retainedRecipes
          (n := n) hleftWeight hrightWeight O =
        retainedRecipes (n := n) hleftWeight hrightWeight (ofFamily O)) ?_ O
  intro parent ih
  rw [
    ORPkt.recipes_cons_append,
    recipes_cons_append]
  simp only [correction_ofFamily]
  congr 1
  · by_cases hleft :
        (BFOrient.FObstru.operationalNestedLeft
          parent).weight leftWeight rightWeight < n
    · have hleft' :
          (ofFamily parent).operationalNestedLeft.weight
              leftWeight rightWeight < n := by
        simpa only [← operational_left_family, weight_ofFamily] using hleft
      rw [dif_pos hleft, dif_pos hleft']
      exact congrArg (List.cons parent.correction.recipe)
        (by
          simpa only [operational_left_family] using
            ih _
              (BFOrient.FObstru.nestedLeftDescends
                hleftWeight hrightWeight parent hleft))
    · have hleft' :
          ¬(ofFamily parent).operationalNestedLeft.weight
              leftWeight rightWeight < n := by
        intro h
        apply hleft
        simpa only [← operational_left_family, weight_ofFamily] using h
      rw [dif_neg hleft, dif_neg hleft']
  · by_cases hright :
        (BFOrient.FObstru.operationalNestedRight
          parent).weight leftWeight rightWeight < n
    · have hright' :
          (ofFamily parent).operationalNestedRight.weight
              leftWeight rightWeight < n := by
        simpa only [← operational_nested_family, weight_ofFamily] using hright
      rw [dif_pos hright, dif_pos hright']
      simpa only [operational_nested_family] using
        ih _
          (BFOrient.FObstru.nestedRightDescends
            hleftWeight hrightWeight parent hright)
    · have hright' :
          ¬(ofFamily parent).operationalNestedRight.weight
              leftWeight rightWeight < n := by
        intro h
        apply hright
        simpa only [← operational_nested_family, weight_ofFamily] using h
      rw [dif_neg hright, dif_neg hright']

/-- Canonically realize a recipe obstruction at arbitrary source multiplicities. -/
noncomputable def toFamily
    (M N : ℕ)
    (O : RObstru) :
    FObstru M N where
  left := BFam.ofRecipe M N O.left
  right := BFam.ofRecipe M N O.right

@[simp]
lemma of_to_family
    (M N : ℕ)
    (O : RObstru) :
    ofFamily (toFamily M N O) = O := by
  cases O
  rfl

/-- Concrete canonical realizations project back to the recipe-only packet. -/
lemma recipes_family
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (M N : ℕ)
    (O : RObstru) :
    ORPkt.retainedRecipes
        (n := n) hleftWeight hrightWeight (toFamily M N O) =
      retainedRecipes (n := n) hleftWeight hrightWeight O := by
  simpa using retained_recipes_family hleftWeight hrightWeight (toFamily M N O)

/-- Every recipe retained by the operational packet remains below the cutoff. -/
lemma retained_recipe_cutoff
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : RObstru}
    (hroot : O.weight leftWeight rightWeight < n)
    {R : BRecipe}
    (hR : R ∈ retainedRecipes (n := n) hleftWeight hrightWeight O) :
    weightedWordWeight leftWeight rightWeight R < n := by
  have hR' :
      R ∈
        ORPkt.retainedRecipes
          (n := n) hleftWeight hrightWeight (toFamily 0 0 O) := by
    rwa [recipes_family hleftWeight hrightWeight 0 0 O]
  exact
    ORPkt.retained_recipe_cutoff
      (by simpa using hroot) hR'

/-- Every retained recipe lies strictly above the root left parent. -/
lemma left_retained_recipes
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : RObstru}
    {R : BRecipe}
    (hR : R ∈ retainedRecipes (n := n) hleftWeight hrightWeight O) :
    weightedWordWeight leftWeight rightWeight O.left <
      weightedWordWeight leftWeight rightWeight R := by
  have hR' :
      R ∈
        ORPkt.retainedRecipes
          (n := n) hleftWeight hrightWeight (toFamily 0 0 O) := by
    rwa [recipes_family hleftWeight hrightWeight 0 0 O]
  exact
    ORPkt.left_retained_recipes
      hR'

/-- Every retained recipe lies strictly above the root right parent. -/
lemma right_retained_recipes
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : RObstru}
    {R : BRecipe}
    (hR : R ∈ retainedRecipes (n := n) hleftWeight hrightWeight O) :
    weightedWordWeight leftWeight rightWeight O.right <
      weightedWordWeight leftWeight rightWeight R := by
  have hR' :
      R ∈
        ORPkt.retainedRecipes
          (n := n) hleftWeight hrightWeight (toFamily 0 0 O) := by
    rwa [recipes_family hleftWeight hrightWeight 0 0 O]
  exact
    ORPkt.right_retained_recipes
      hR'

end RObstru
end BRPkt
end TCTex
end Towers

/-!
# Polynomial equivalence of operational recipe packets

The recipe-only operational recollector depends on block recipes through their
weighted degree and pairwise correction.  Both are invariant under symbolic
polynomial equivalence.  Consequently equivalent source obstructions follow
the same cutoff branches and emit pointwise equivalent finite packets.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace ROEquiv

open HACoeff
open BRSpec
open BRPkt
open BRPkt.RObstru
open RPEquiv

namespace RObstru

/-- Pointwise symbolic polynomial equivalence of recipe obstructions. -/
def PolynomialEquivalent
    (O P : RObstru) :
    Prop :=
  RPEquiv.BRecipe.PolynomialEquivalent
      O.left P.left ∧
    RPEquiv.BRecipe.PolynomialEquivalent
      O.right P.right

@[refl]
lemma polynomialEquivalent_refl
    (O : RObstru) :
    PolynomialEquivalent O O :=
  ⟨RPEquiv.BRecipe.polynomialEquivalent_refl
      O.left,
    RPEquiv.BRecipe.polynomialEquivalent_refl
      O.right⟩

/-- Polynomial-equivalent obstructions have equal total weighted degree. -/
lemma weight_poly_equivalent
    {leftWeight rightWeight : ℕ}
    {O P : RObstru}
    (h : PolynomialEquivalent O P) :
    O.weight leftWeight rightWeight =
      P.weight leftWeight rightWeight := by
  unfold BRPkt.RObstru.weight
  rw [
    RPEquiv.BRecipe.weighted_poly_equivalent
      h.1,
    RPEquiv.BRecipe.weighted_poly_equivalent
      h.2]

/-- Polynomial-equivalent obstructions emit equivalent leading corrections. -/
lemma correctio_polynomi
    {O P : RObstru}
    (h : PolynomialEquivalent O P) :
    RPEquiv.BRecipe.PolynomialEquivalent
      O.correction P.correction :=
  RPEquiv.BRecipe.polynomia_correcti
    h.1 h.2

/-- The oriented left children of equivalent obstructions remain equivalent. -/
lemma operational_left_equivalent
    {O P : RObstru}
    (h : PolynomialEquivalent O P) :
    PolynomialEquivalent O.operationalNestedLeft P.operationalNestedLeft :=
  ⟨h.1, correctio_polynomi h⟩

/-- The oriented right children of equivalent obstructions remain equivalent. -/
lemma operational_nested_equivalent
    {O P : RObstru}
    (h : PolynomialEquivalent O P) :
    PolynomialEquivalent O.operationalNestedRight P.operationalNestedRight :=
  ⟨h.2, correctio_polynomi h⟩

/--
Polynomial-equivalent source obstructions emit pointwise equivalent finite
operational packets.
-/
lemma retRecps_forall₂
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    ∀ O P : RObstru,
      PolynomialEquivalent O P →
        List.Forall₂
          RPEquiv.BRecipe.PolynomialEquivalent
          (O.retainedRecipes (n := n) hleftWeight hrightWeight)
          (P.retainedRecipes (n := n) hleftWeight hrightWeight) := by
  intro O
  refine
    (descends_wellFounded n leftWeight rightWeight).induction
      (C := fun O =>
        ∀ P : RObstru,
          PolynomialEquivalent O P →
            List.Forall₂
              RPEquiv.BRecipe.PolynomialEquivalent
              (O.retainedRecipes (n := n) hleftWeight hrightWeight)
              (P.retainedRecipes (n := n) hleftWeight hrightWeight))
      O ?_
  intro O ih P hOP
  rw [recipes_cons_append hleftWeight hrightWeight O,
    recipes_cons_append hleftWeight hrightWeight P]
  refine List.Forall₂.cons (correctio_polynomi hOP) ?_
  refine List.rel_append ?_ ?_
  · by_cases hleft :
        O.operationalNestedLeft.weight leftWeight rightWeight < n
    · have hleftP :
          P.operationalNestedLeft.weight leftWeight rightWeight < n := by
        rw [← weight_poly_equivalent
          (operational_left_equivalent hOP)]
        exact hleft
      rw [dif_pos hleft, dif_pos hleftP]
      exact
        ih O.operationalNestedLeft
          (O.nestedLeftDescends
            hleftWeight hrightWeight hleft)
          P.operationalNestedLeft
          (operational_left_equivalent hOP)
    · have hleftP :
          ¬ P.operationalNestedLeft.weight leftWeight rightWeight < n := by
        intro h
        apply hleft
        rw [weight_poly_equivalent
          (operational_left_equivalent hOP)]
        exact h
      rw [dif_neg hleft, dif_neg hleftP]
      exact List.Forall₂.nil
  · by_cases hright :
        O.operationalNestedRight.weight leftWeight rightWeight < n
    · have hrightP :
          P.operationalNestedRight.weight leftWeight rightWeight < n := by
        rw [← weight_poly_equivalent
          (operational_nested_equivalent hOP)]
        exact hright
      rw [dif_pos hright, dif_pos hrightP]
      exact
        ih O.operationalNestedRight
          (O.nestedRightDescends
            hleftWeight hrightWeight hright)
          P.operationalNestedRight
          (operational_nested_equivalent hOP)
    · have hrightP :
          ¬ P.operationalNestedRight.weight leftWeight rightWeight < n := by
        intro h
        apply hright
        rw [weight_poly_equivalent
          (operational_nested_equivalent hOP)]
        exact h
      rw [dif_neg hright, dif_neg hrightP]
      exact List.Forall₂.nil

end RObstru
end ROEquiv
end TCTex
end Towers

/-!
# Polynomial factors from recipe-only operational packets

The recipe-only operational tree is already independent of concrete source
multiplicities.  This file specializes its finite retained recipe list to
signed Claim 8 polynomial factors and records the cutoff and strict
higher-weight bounds needed by the nonterminal collector.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace RORec

universe u

open HACoeff
open BRPkt
open BRPkt.RObstru
open BRSpec

/-- Attach one recipe-only operational packet to signed Claim 8 factors. -/
noncomputable def symbolicFactors
    {n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (O : RObstru)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    List (SPFactor H ι) :=
  BRSpec.symbolicFactors
    (O.retainedRecipes (n := n)
      (HEAddres.weight_pos leftAddress)
      (HEAddres.weight_pos rightAddress))
    leftInput rightInput leftAddress rightAddress

/-- Every symbolic factor remembers one retained operational recipe. -/
lemma recipe_factors
    {n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {O : RObstru}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈ symbolicFactors (n := n) O leftInput rightInput
        leftAddress rightAddress) :
    ∃ R ∈ O.retainedRecipes (n := n)
        (HEAddres.weight_pos leftAddress)
        (HEAddres.weight_pos rightAddress),
      factor =
        BRSpec.symbolicFactor
          R leftInput rightInput leftAddress rightAddress := by
  exact BRSpec.recipe_factors
    hfactor

/-- Every symbolic correction factor remains below the quotient cutoff. -/
lemma weight_symbolic_factors
    {n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {O : RObstru}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    (hroot : O.weight leftAddress.weight rightAddress.weight < n)
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈ symbolicFactors (n := n) O leftInput rightInput
        leftAddress rightAddress) :
    factor.word.weight HEAddres.weight < n := by
  rcases recipe_factors hfactor with
    ⟨R, hR, rfl⟩
  rw [word_symbolic_factor, ← weighted_word_weight]
  exact retained_recipe_cutoff hroot hR

/-- Every symbolic correction factor lies above the root left parent. -/
lemma left_symbolic_factors
    {n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {O : RObstru}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈ symbolicFactors (n := n) O leftInput rightInput
        leftAddress rightAddress) :
    weightedWordWeight leftAddress.weight rightAddress.weight O.left <
      factor.word.weight HEAddres.weight := by
  rcases recipe_factors hfactor with
    ⟨R, hR, rfl⟩
  rw [word_symbolic_factor, ← weighted_word_weight]
  exact left_retained_recipes hR

/-- Every symbolic correction factor lies above the root right parent. -/
lemma right_symbolic_factors
    {n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {O : RObstru}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈ symbolicFactors (n := n) O leftInput rightInput
        leftAddress rightAddress) :
    weightedWordWeight leftAddress.weight rightAddress.weight O.right <
      factor.word.weight HEAddres.weight := by
  rcases recipe_factors hfactor with
    ⟨R, hR, rfl⟩
  rw [word_symbolic_factor, ← weighted_word_weight]
  exact right_retained_recipes hR

/-- Specialized factors expose the root-and-operational-branches recurrence. -/
lemma symbolic_cons_append
    {n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (O : RObstru)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    symbolicFactors (n := n) O leftInput rightInput leftAddress rightAddress =
      BRSpec.symbolicFactor
          O.correction leftInput rightInput leftAddress rightAddress ::
        (if _hleft :
            O.operationalNestedLeft.weight
                leftAddress.weight rightAddress.weight < n then
          symbolicFactors (n := n) O.operationalNestedLeft
            leftInput rightInput leftAddress rightAddress
        else []) ++
        (if _hright :
            O.operationalNestedRight.weight
                leftAddress.weight rightAddress.weight < n then
          symbolicFactors (n := n) O.operationalNestedRight
            leftInput rightInput leftAddress rightAddress
        else []) := by
  rw [symbolicFactors, recipes_cons_append]
  simp only [BRSpec.symbolicFactors,
    List.map_cons, List.map_append]
  split <;> split <;>
    simp_all [symbolicFactors,
      BRSpec.symbolicFactors]

/--
Evaluation of a recipe-only symbolic packet is its root correction followed
by the two surviving oriented branch packets.
-/
lemma list_factors_branches
    {n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (O : RObstru)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    SPFactor.listEval (n := n) e
        (symbolicFactors (n := n) O leftInput rightInput
          leftAddress rightAddress) =
      (BRSpec.symbolicFactor
          O.correction leftInput rightInput leftAddress rightAddress).eval e *
        (SPFactor.listEval e
            (if _hleft :
                O.operationalNestedLeft.weight
                    leftAddress.weight rightAddress.weight < n then
              symbolicFactors (n := n) O.operationalNestedLeft
                leftInput rightInput leftAddress rightAddress
            else []) *
          SPFactor.listEval e
            (if _hright :
                O.operationalNestedRight.weight
                    leftAddress.weight rightAddress.weight < n then
              symbolicFactors (n := n) O.operationalNestedRight
                leftInput rightInput leftAddress rightAddress
            else [])) := by
  rw [symbolic_cons_append]
  simp only [SPFactor.listEval_cons,
    SPFactor.listEval_append]
  rw [mul_assoc]

end RORec
end TCTex
end Towers

/-!
# Specializing polynomial-equivalent operational recipe packets

Equivalent recipe obstructions emit pointwise equivalent operational packets.
After specialization, those finite ordered packets have identical evaluation.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace ROEquiv

universe u

open HACoeff
open BRPkt
open RORec
open RPEquiv
open BRSpec

namespace RObstru

/--
Polynomial-equivalent source obstructions emit operational recipe packets
with identical ordered specialized evaluation.
-/
lemma symbolic_recipes_equivalent
    {n leftWeight rightWeight d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {O P : RObstru}
    (h : PolynomialEquivalent O P)
    (e : ι → HEFam H)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    SPFactor.listEval (n := n) e
        (symbolicFactors
          (O.retainedRecipes (n := n) hleftWeight hrightWeight)
          leftInput rightInput leftAddress rightAddress) =
      SPFactor.listEval (n := n) e
        (symbolicFactors
          (P.retainedRecipes (n := n) hleftWeight hrightWeight)
          leftInput rightInput leftAddress rightAddress) := by
  exact
    symbolic_factors_forall₂_polynomialEquivalent
      (retRecps_forall₂ (n := n) hleftWeight hrightWeight O P h)
      e leftInput rightInput leftAddress rightAddress

/--
The multiplicity-independent recipe-only polynomial packets of equivalent
obstructions have identical ordered evaluation.
-/
lemma operat_symbo_equiv
    {n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {O P : RObstru}
    (h : PolynomialEquivalent O P)
    (e : ι → HEFam H)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    SPFactor.listEval (n := n) e
        (RORec.symbolicFactors
          (n := n) O leftInput rightInput leftAddress rightAddress) =
      SPFactor.listEval (n := n) e
        (RORec.symbolicFactors
          (n := n) P leftInput rightInput leftAddress rightAddress) := by
  exact
    symbolic_recipes_equivalent
      (n := n)
      (HEAddres.weight_pos leftAddress)
      (HEAddres.weight_pos rightAddress)
      h e leftInput rightInput leftAddress rightAddress

end RObstru
end ROEquiv
end TCTex
end Towers

/-!
# Exact interface for recipe-only operational polynomial packets

The recipe-only operational tree constructs a finite list of signed
Hall-Petresco correction factors and proves every structural bound required by
the nonterminal collector.  The remaining group-theoretic obligation is one
all-integral evaluation identity.  This file isolates that obligation and
turns any proof of it into the exact correction-packet interface consumed by
the symbolic collection scheduler.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace RORec

universe u

open scoped commutatorElement

open HACoeff
open BRPkt
open BRPkt.RObstru
open BRSpec

/--
All-integral semantic law for one multiplicity-independent recipe-only
operational packet.
-/
structure SELaw
    {n d : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (O : RObstru)
    {ι : Type}
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) : Prop where
  listEval_eq :
    ∀ e : ι → HEFam H,
      SPFactor.listEval (n := n) e
          (symbolicFactors (n := n) O leftInput rightInput
            leftAddress rightAddress) =
        ⁅(symbolicFactor O.left leftInput rightInput
              leftAddress rightAddress).eval (n := n) e,
          (symbolicFactor O.right leftInput rightInput
              leftAddress rightAddress).eval (n := n) e⁆

namespace SELaw

/--
The all-integral semantic law and the already-proved structural bounds produce
the exact correction packet required by one adjacent nonterminal swap.
-/
noncomputable def toCorrectionPacket
    {n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {O : RObstru}
    {ι : Type}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    (law :
      SELaw (n := n) H O
        leftInput rightInput leftAddress rightAddress)
    (hroot : O.weight leftAddress.weight rightAddress.weight < n) :
    TSPkt n
      (symbolicFactor O.left leftInput rightInput leftAddress rightAddress)
      (symbolicFactor O.right leftInput rightInput leftAddress rightAddress) where
  factors :=
    symbolicFactors (n := n) O leftInput rightInput leftAddress rightAddress
  listEval_eq :=
    law.listEval_eq
  word_weight_left := by
    intro factor hfactor
    rw [word_symbolic_factor, ← weighted_word_weight]
    exact left_symbolic_factors hfactor
  word_weight_right := by
    intro factor hfactor
    rw [word_symbolic_factor, ← weighted_word_weight]
    exact right_symbolic_factors hfactor
  word_weight_cutoff := by
    intro factor hfactor
    exact weight_symbolic_factors hroot hfactor

end SELaw
end RORec
end TCTex
end Towers
