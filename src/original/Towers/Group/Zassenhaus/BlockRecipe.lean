import Towers.Group.Zassenhaus.CorrectionClosureVocabulary
import Towers.Group.Zassenhaus.PacketCompression


/-!
# Finite correction-closure support for ordered operational recipe packets

The finite correction closure is deliberately larger than any one operational
recollection trace.  This file proves the forward containment needed by a
semantic scheduler: every recipe emitted by an ordered recipe-only operational
tree rooted at source recipes belongs to the retained finite correction
closure.

The proof keeps the operational recipe list in its original order.  The
closure is used only as a pointwise finite support envelope.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace RCSuppor

open HACoeff
open BRPkt
open BRPkt.RObstru
open BRSpec
open UCVocabu
open URVocabu

namespace RObstru

/--
If both parents occur by their weighted-degree closure layers, then their
correction occurs by its own weighted-degree closure layer.
-/
lemma correction_closure_weight
    {source : List BRecipe}
    {leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : RObstru)
    (hleft :
      O.left ∈ correctionClosure source
        (weightedWordWeight leftWeight rightWeight O.left))
    (hright :
      O.right ∈ correctionClosure source
        (weightedWordWeight leftWeight rightWeight O.right)) :
    O.correction ∈ correctionClosure source
      (weightedWordWeight leftWeight rightWeight O.correction) := by
  apply correction_closure
    (correction_mem_closure hleft hright)
  change
    max (weightedWordWeight leftWeight rightWeight O.left)
          (weightedWordWeight leftWeight rightWeight O.right) + 1 ≤
      weightedWordWeight leftWeight rightWeight
        (O.left.correction O.right)
  rw [weighted_weight_correction]
  have hleftPos :=
    weighted_weight_pos hleftWeight hrightWeight O.left
  have hrightPos :=
    weighted_weight_pos hleftWeight hrightWeight O.right
  omega

/--
Every recipe in an ordered operational packet occurs by its weighted-degree
closure layer, provided both root parents do.
-/
lemma correction_closure_recipes
    {source : List BRecipe}
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    ∀ (O : RObstru),
      O.left ∈ correctionClosure source
          (weightedWordWeight leftWeight rightWeight O.left) →
        O.right ∈ correctionClosure source
            (weightedWordWeight leftWeight rightWeight O.right) →
          ∀ {recipe : BRecipe},
            recipe ∈ O.retainedRecipes (n := n)
                hleftWeight hrightWeight →
              recipe ∈ correctionClosure source
                (weightedWordWeight leftWeight rightWeight recipe) := by
  intro O
  refine
    (descends_wellFounded n leftWeight rightWeight).induction
      (C := fun parent =>
        parent.left ∈ correctionClosure source
            (weightedWordWeight leftWeight rightWeight parent.left) →
          parent.right ∈ correctionClosure source
              (weightedWordWeight leftWeight rightWeight parent.right) →
            ∀ {recipe : BRecipe},
              recipe ∈ parent.retainedRecipes (n := n)
                  hleftWeight hrightWeight →
                recipe ∈ correctionClosure source
                  (weightedWordWeight leftWeight rightWeight recipe))
      O ?_
  intro parent ih hleft hright recipe hrecipe
  have hcorrection :
      parent.correction ∈ correctionClosure source
        (weightedWordWeight leftWeight rightWeight parent.correction) :=
    correction_closure_weight
      hleftWeight hrightWeight parent hleft hright
  rw [recipes_cons_append hleftWeight hrightWeight parent] at hrecipe
  rcases List.mem_cons.mp hrecipe with hrecipe | hrecipe
  · subst recipe
    exact hcorrection
  · rcases List.mem_append.mp hrecipe with hrecipe | hrecipe
    · by_cases hcutoff :
          parent.operationalNestedLeft.weight leftWeight rightWeight < n
      · rw [dif_pos hcutoff] at hrecipe
        exact
          ih parent.operationalNestedLeft
            (parent.nestedLeftDescends
              hleftWeight hrightWeight hcutoff)
            hleft hcorrection hrecipe
      · rw [dif_neg hcutoff] at hrecipe
        simp at hrecipe
    · by_cases hcutoff :
          parent.operationalNestedRight.weight leftWeight rightWeight < n
      · rw [dif_pos hcutoff] at hrecipe
        exact
          ih parent.operationalNestedRight
            (parent.nestedRightDescends
              hleftWeight hrightWeight hcutoff)
            hright hcorrection hrecipe
      · rw [dif_neg hcutoff] at hrecipe
        simp at hrecipe

/--
Every ordered operational recipe packet rooted at retained source recipes is
pointwise supported by the retained finite correction closure.
-/
lemma retained_closure_recipes
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : RObstru)
    (hleft : O.left ∈ sourceRecipes n leftWeight rightWeight)
    (hright : O.right ∈ sourceRecipes n leftWeight rightWeight)
    (hroot : O.weight leftWeight rightWeight < n)
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ O.retainedRecipes (n := n) hleftWeight hrightWeight) :
    recipe ∈ correctionClosureRecipes n leftWeight rightWeight := by
  apply retained_correction_closure.mpr
  constructor
  · apply correction_closure
      (correction_closure_recipes
        hleftWeight hrightWeight O
        (correction_closure
          (show O.left ∈
              correctionClosure (sourceRecipes n leftWeight rightWeight) 0 by
            exact hleft)
          (Nat.zero_le _))
        (correction_closure
          (show O.right ∈
              correctionClosure (sourceRecipes n leftWeight rightWeight) 0 by
            exact hright)
          (Nat.zero_le _))
        hrecipe)
    exact Nat.le_of_lt
      (retained_recipe_cutoff hroot hrecipe)
  · exact retained_recipe_cutoff hroot hrecipe

end RObstru

/--
Every recipe emitted by the universal ordered operational source-pair trees
belongs to the retained finite correction closure.
-/
lemma closure_recipes_operational
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ operationalCorrectionRecipes n leftWeight rightWeight
        hleftWeight hrightWeight) :
    recipe ∈ correctionClosureRecipes n leftWeight rightWeight := by
  unfold operationalCorrectionRecipes at hrecipe
  rcases List.mem_flatMap.mp hrecipe with ⟨left, hleft, hrecipe⟩
  rcases List.mem_flatMap.mp hrecipe with ⟨right, hright, hrecipe⟩
  unfold operationalRecipes at hrecipe
  split at hrecipe
  · apply
      RObstru.retained_closure_recipes
        hleftWeight hrightWeight
        (RObstru.mk left.blockRecipe right.blockRecipe)
    · exact List.mem_map.mpr ⟨left, hleft, rfl⟩
    · exact List.mem_map.mpr ⟨right, hright, rfl⟩
    · assumption
    · exact hrecipe
  · simp at hrecipe

/--
The earlier universal source-and-operational vocabulary is pointwise included
in the retained finite correction closure.
-/
lemma retained_correction_recipes
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ recipes n leftWeight rightWeight
        hleftWeight hrightWeight) :
    recipe ∈ correctionClosureRecipes n leftWeight rightWeight := by
  rcases List.mem_append.mp hrecipe with hrecipe | hrecipe
  · apply retained_correction_closure.mpr
    exact
      ⟨correction_closure
          (show recipe ∈
              correctionClosure (sourceRecipes n leftWeight rightWeight) 0 by
            exact hrecipe)
          (Nat.zero_le _),
        weighted_cutoff_recipes hrecipe⟩
  · exact
      closure_recipes_operational
        hrecipe

end RCSuppor
end TCTex
end Towers

/-!
# Polynomial-orbit aggregation for Hall-Petresco block recipes

The finite correction closure is deliberately conservative: it may retain
several recipes carrying the same symbolic polynomial factor.  This file
records the exact multiplicity-independent orbit key of a recipe, partitions
an arbitrary finite recipe inventory by that key, and proves the coefficient
aggregation formula for each orbit.

The orbit key is strictly finer than the erased Hall word.  It remembers the
left and right source-block degrees as well, so equality of orbit keys is
exactly `BRecipe.PolynomialEquivalent`.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace ROAggreg

open RPEquiv

open HACoeff
open BRSpec
open OCPartit
open UCVocabu

/--
The complete multiplicity-independent polynomial data carried by one block
recipe.
-/
structure POKey where
  leftBlocks :
    List ℕ
  rightBlocks :
    List ℕ
  erasedShape :
    CWord HPAtom
  deriving DecidableEq

/-- Forget dependent recipe labels while retaining its symbolic polynomial data. -/
def polynomialOrbitKey
    (recipe : BRecipe) :
    POKey where
  leftBlocks :=
    recipe.leftBlocks
  rightBlocks :=
    recipe.rightBlocks
  erasedShape :=
    recipe.erasedShape

/-- Equality of polynomial orbit keys is exactly recipe polynomial equivalence. -/
lemma polynomial_orbit_key
    {left right : BRecipe} :
    polynomialOrbitKey left = polynomialOrbitKey right ↔
      RPEquiv.BRecipe.PolynomialEquivalent
        left right := by
  constructor
  · intro h
    have hleft :
        left.leftBlocks = right.leftBlocks := by
      simpa only [polynomialOrbitKey] using
        congrArg POKey.leftBlocks h
    have hright :
        left.rightBlocks = right.rightBlocks := by
      simpa only [polynomialOrbitKey] using
        congrArg POKey.rightBlocks h
    have hshape :
        left.erasedShape = right.erasedShape := by
      simpa only [polynomialOrbitKey] using
        congrArg POKey.erasedShape h
    exact ⟨hleft, hright, hshape⟩
  · intro h
    simp only [polynomialOrbitKey]
    rw [h.1, h.2.1, h.2.2]

/-- Deduplicated polynomial-orbit keys occurring in one finite recipe list. -/
noncomputable def polynomialOrbitVocabulary
    (recipes : List BRecipe) :
    List POKey :=
  (recipes.map polynomialOrbitKey).dedup

/-- The recipes belonging to one fixed polynomial orbit. -/
noncomputable def recipesPolynomialOrbit
    (recipes : List BRecipe)
    (key : POKey) :
    List BRecipe := by
  classical
  exact recipes.filter fun recipe =>
    polynomialOrbitKey recipe = key

/-- Polynomial-orbit chunks, ordered by first appearance of their keys. -/
noncomputable def polynomialOrbitChunks
    (recipes : List BRecipe) :
    List (List BRecipe) :=
  (polynomialOrbitVocabulary recipes).map fun key =>
    recipesPolynomialOrbit recipes key

/-- Flatten the polynomial-orbit chunks back into one recipe inventory. -/
noncomputable def polynomialOrbitRecipes
    (recipes : List BRecipe) :
    List BRecipe :=
  (polynomialOrbitChunks recipes).flatten

/-- Every recipe in a polynomial-orbit chunk has the requested key. -/
lemma polynomial_key_recipes
    {recipes : List BRecipe}
    {key : POKey}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ recipesPolynomialOrbit recipes key) :
    polynomialOrbitKey recipe = key := by
  classical
  exact of_decide_eq_true (List.mem_filter.mp hrecipe).2

/-- Every member of a polynomial-orbit chunk came from the input inventory. -/
lemma recipes_polynomial_orbit
    {recipes : List BRecipe}
    {key : POKey}
    {recipe : BRecipe}
    (hrecipe : recipe ∈ recipesPolynomialOrbit recipes key) :
    recipe ∈ recipes := by
  classical
  exact List.mem_of_mem_filter hrecipe

/-- Any two recipes in one polynomial-orbit chunk are polynomial equivalent. -/
lemma equivalent_recipes_orbit
    {recipes : List BRecipe}
    {key : POKey}
    {left right : BRecipe}
    (hleft : left ∈ recipesPolynomialOrbit recipes key)
    (hright : right ∈ recipesPolynomialOrbit recipes key) :
    RPEquiv.BRecipe.PolynomialEquivalent
      left right := by
  rw [← polynomial_orbit_key]
  exact
    (polynomial_key_recipes hleft).trans
      (polynomial_key_recipes hright).symm

/-- Polynomial-orbit peers have the same erased Hall word. -/
lemma erased_recipes_orbit
    {recipes : List BRecipe}
    {key : POKey}
    {left right : BRecipe}
    (hleft : left ∈ recipesPolynomialOrbit recipes key)
    (hright : right ∈ recipesPolynomialOrbit recipes key) :
    left.erasedShape = right.erasedShape :=
  (equivalent_recipes_orbit hleft hright).2.2

/-- Polynomial-orbit peers have the same generalized-binomial coefficient. -/
lemma coefficient_recipes_orbit
    {recipes : List BRecipe}
    {key : POKey}
    {left right : BRecipe}
    (hleft : left ∈ recipesPolynomialOrbit recipes key)
    (hright : right ∈ recipesPolynomialOrbit recipes key)
    (leftExponent rightExponent : ℤ) :
    coefficientValue left leftExponent rightExponent =
      coefficientValue right leftExponent rightExponent :=
  BRecipe.coeff_poly_equivalent
    (equivalent_recipes_orbit hleft hright)
    leftExponent rightExponent

private lemma flat_key_perm
    {α β : Type*}
    [DecidableEq β]
    (key : α → β) :
    ∀ (keys : List β) (values : List α),
      keys.Nodup →
        (∀ value ∈ values, key value ∈ keys) →
          List.Perm
            (keys.flatMap fun target =>
              values.filter fun value => key value = target)
            values
  | [], values, _hnodup, hcover => by
      have hvalues : values = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro value hvalue
        simpa using hcover value hvalue
      subst values
      exact .nil
  | target :: keys, values, hnodup, hcover => by
      let matching :=
        values.filter fun value => key value = target
      let rest :=
        values.filter fun value => key value ≠ target
      have hrestCover :
          ∀ value ∈ rest, key value ∈ keys := by
        intro value hvalue
        have hvalueMem : value ∈ values :=
          List.mem_of_mem_filter hvalue
        have hvalueNe : key value ≠ target :=
          of_decide_eq_true (List.mem_filter.mp hvalue).2
        have hkeyMem :=
          hcover value hvalueMem
        simpa [hvalueNe] using hkeyMem
      have hfilter :
          ∀ nextTarget ∈ keys,
            values.filter (fun value => key value = nextTarget) =
              rest.filter (fun value => key value = nextTarget) := by
        intro nextTarget hnextTarget
        simp only [rest, List.filter_filter]
        apply List.filter_congr
        intro value _hvalue
        have htargetNotMem : target ∉ keys :=
          (List.nodup_cons.mp hnodup).1
        have hnextNe : nextTarget ≠ target := by
          intro hnextEq
          subst nextTarget
          exact htargetNotMem hnextTarget
        by_cases hvalueEq : key value = nextTarget
        · simp [hvalueEq, hnextNe]
        · simp [hvalueEq]
      have htail :
          List.Perm
            (keys.flatMap fun nextTarget =>
              rest.filter fun value => key value = nextTarget)
            rest :=
        flat_key_perm key keys rest
          (List.nodup_cons.mp hnodup).2 hrestCover
      have htailEq :
          (keys.flatMap fun nextTarget =>
              values.filter fun value => key value = nextTarget) =
            keys.flatMap fun nextTarget =>
              rest.filter fun value => key value = nextTarget := by
        apply List.flatMap_congr
        exact hfilter
      simp only [List.flatMap_cons]
      rw [htailEq]
      exact
        (List.Perm.append_left matching htail).trans
          (by
            simpa [matching, rest] using
              (List.perm_filterappend_filternot
                (fun value => decide (key value = target)) values).symm)

/--
Flattening polynomial-orbit chunks preserves the complete finite recipe
inventory, including repeated polynomially equivalent recipes.
-/
lemma orbit_recipes_perm
    (recipes : List BRecipe) :
    List.Perm (polynomialOrbitRecipes recipes) recipes := by
  classical
  unfold polynomialOrbitRecipes polynomialOrbitChunks
  unfold polynomialOrbitVocabulary recipesPolynomialOrbit
  change
    List.Perm
      (((recipes.map polynomialOrbitKey).dedup.flatMap fun target =>
        recipes.filter fun recipe => polynomialOrbitKey recipe = target))
      recipes
  exact
    flat_key_perm polynomialOrbitKey
      ((recipes.map polynomialOrbitKey).dedup)
      recipes
      (List.nodup_dedup _)
      (fun recipe hrecipe => by
        rw [List.mem_dedup]
        exact List.mem_map.mpr ⟨recipe, hrecipe, rfl⟩)

/-- Polynomial-orbit flattening retains exactly the original recipe members. -/
lemma orbit_recipes
    {recipes : List BRecipe}
    {recipe : BRecipe} :
    recipe ∈ polynomialOrbitRecipes recipes ↔
      recipe ∈ recipes :=
  (orbit_recipes_perm recipes).mem_iff

private lemma sum_length_forall
    {α : Type*}
    (values : List α)
    (f : α → ℤ)
    (constant : ℤ)
    (hconstant : ∀ value ∈ values, f value = constant) :
    (values.map f).sum = (values.length : ℤ) * constant := by
  induction values with
  | nil =>
      simp
  | cons value values ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      rw [hconstant value (by simp)]
      rw [ih (fun nextValue hnextValue =>
        hconstant nextValue (by simp [hnextValue]))]
      ring

/--
The coefficient sum of one polynomial orbit is its multiplicity times any
representative coefficient formula.
-/
lemma sum_recipes_length
    {recipes : List BRecipe}
    {key : POKey}
    {representative : BRecipe}
    (hrepresentative :
      representative ∈ recipesPolynomialOrbit recipes key)
    (leftExponent rightExponent : ℤ) :
    ((recipesPolynomialOrbit recipes key).map fun recipe =>
      coefficientValue recipe leftExponent rightExponent).sum =
        ((recipesPolynomialOrbit recipes key).length : ℤ) *
          coefficientValue representative leftExponent rightExponent := by
  apply sum_length_forall
  intro recipe hrecipe
  exact
    coefficient_recipes_orbit
      hrecipe hrepresentative leftExponent rightExponent

/--
The retained universal finite correction closure admits an exact
multiplicity-independent polynomial-orbit partition.
-/
lemma closure_recipes_perm
    (n leftWeight rightWeight : ℕ) :
    List.Perm
      (polynomialOrbitRecipes
        (correctionClosureRecipes n leftWeight rightWeight))
      (correctionClosureRecipes n leftWeight rightWeight) :=
  orbit_recipes_perm _

end ROAggreg
end TCTex
end Towers

/-!
# Polynomial-orbit transitions for Hall-Petresco block recipes

The symbolic correction transition of a complete block recipe depends only on
its polynomial orbit key.  This file records the recipe-free transition,
constructs the corresponding finite orbit closure, and proves that mapping
recipe closure layers to keys is exact.

The final section applies the same observation to the operational obstruction
tree: polynomial-equivalent source obstructions emit literally equal ordered
key traces, even when their dependent recipe labels differ.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace ROTransi

open HACoeff
open ROEquiv
open ROEquiv.RObstru
open BRPkt
open ROAggreg
open BRSpec
open UCVocabu
open URVocabu

/-- Recipe-free polynomial-orbit transition induced by pairwise correction. -/
def orbitCorrection
    (left right : POKey) :
    POKey where
  leftBlocks :=
    left.leftBlocks ++ right.leftBlocks
  rightBlocks :=
    left.rightBlocks ++ right.rightBlocks
  erasedShape :=
    .commutator left.erasedShape right.erasedShape

/-- Weighted Hall degree of one polynomial orbit key. -/
def orbitWeight
    (leftWeight rightWeight : ℕ)
    (key : POKey) :
    ℕ :=
  key.erasedShape.weight (HPAtom.weight leftWeight rightWeight)

@[simp]
lemma weight_correction
    (leftWeight rightWeight : ℕ)
    (left right : POKey) :
    orbitWeight leftWeight rightWeight (orbitCorrection left right) =
      orbitWeight leftWeight rightWeight left +
        orbitWeight leftWeight rightWeight right := by
  simp [orbitWeight, orbitCorrection]

/-- Mapping a concrete recipe correction to its key is the recipe-free transition. -/
@[simp]
lemma orbit_key_correction
    (left right : BRecipe) :
    polynomialOrbitKey (left.correction right) =
      orbitCorrection (polynomialOrbitKey left) (polynomialOrbitKey right) := by
  unfold polynomialOrbitKey orbitCorrection
  rw [BRecipe.erasedShape_corr]
  rfl

/-- Mapping a concrete recipe weight to its orbit key preserves weighted degree. -/
@[simp]
lemma weight_orbit_key
    (leftWeight rightWeight : ℕ)
    (recipe : BRecipe) :
    orbitWeight leftWeight rightWeight (polynomialOrbitKey recipe) =
      weightedWordWeight leftWeight rightWeight recipe :=
  rfl

/-- All pairwise recipe-free correction transitions from one finite key list. -/
def pairwiseOrbitCorrections
    (keys : List POKey) :
    List POKey :=
  keys.flatMap fun left =>
    keys.map fun right =>
      orbitCorrection left right

/-- Finite recipe-free iterated polynomial-orbit closure. -/
def orbitCorrectionClosure
    (source : List POKey) :
    ℕ → List POKey
  | 0 =>
      source
  | depth + 1 =>
      orbitCorrectionClosure source depth ++
        pairwiseOrbitCorrections (orbitCorrectionClosure source depth)

/-- Mapping pairwise concrete recipe corrections to keys is exact. -/
lemma key_pairwise_corrections
    (recipes : List BRecipe) :
    (pairwiseCorrections recipes).map polynomialOrbitKey =
      pairwiseOrbitCorrections (recipes.map polynomialOrbitKey) := by
  unfold pairwiseCorrections pairwiseOrbitCorrections
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro left _hleft
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro right _hright
  exact orbit_key_correction left right

/-- Mapping every concrete closure layer to keys gives the recipe-free closure. -/
lemma orbit_key_closure
    (source : List BRecipe) :
    ∀ depth : ℕ,
      (correctionClosure source depth).map polynomialOrbitKey =
        orbitCorrectionClosure (source.map polynomialOrbitKey) depth
  | 0 =>
      rfl
  | depth + 1 => by
      simp only [correctionClosure, orbitCorrectionClosure, List.map_append,
        key_pairwise_corrections,
        orbit_key_closure source depth]

private lemma map_filter_decide
    {α β : Type*}
    (f : α → β)
    (leftPredicate : α → Prop)
    (rightPredicate : β → Prop)
    [DecidablePred leftPredicate]
    [DecidablePred rightPredicate]
    (hpredicate :
      ∀ value, leftPredicate value ↔ rightPredicate (f value)) :
    ∀ values : List α,
      (values.filter fun value => decide (leftPredicate value)).map f =
        (values.map f).filter fun value => decide (rightPredicate value)
  | [] =>
      rfl
  | value :: values => by
      by_cases hvalue : leftPredicate value
      · have hvalue' :
            rightPredicate (f value) :=
          (hpredicate value).mp hvalue
        simp [hvalue, hvalue',
          map_filter_decide f leftPredicate rightPredicate hpredicate values]
      · have hvalue' :
            ¬rightPredicate (f value) := by
          intro h
          exact hvalue ((hpredicate value).mpr h)
        simp [hvalue, hvalue',
          map_filter_decide f leftPredicate rightPredicate hpredicate values]

/-- Retain precisely the recipe-free orbit keys lying below one cutoff. -/
noncomputable def retainedOrbitClosure
    (n leftWeight rightWeight : ℕ) :
    List POKey :=
  (orbitCorrectionClosure
      ((sourceRecipes n leftWeight rightWeight).map polynomialOrbitKey) n).filter
    fun key =>
      decide (orbitWeight leftWeight rightWeight key < n)

/--
Mapping the concrete retained closure to keys is exactly the filtered
recipe-free orbit closure.
-/
lemma key_closure_recipes
    (n leftWeight rightWeight : ℕ) :
    (correctionClosureRecipes n leftWeight rightWeight).map
        polynomialOrbitKey =
      retainedOrbitClosure n leftWeight rightWeight := by
  unfold correctionClosureRecipes retainedOrbitClosure
  rw [map_filter_decide polynomialOrbitKey
    (fun recipe => weightedWordWeight leftWeight rightWeight recipe < n)
    (fun key => orbitWeight leftWeight rightWeight key < n)
    (fun recipe => by
      change
        weightedWordWeight leftWeight rightWeight recipe < n ↔
          orbitWeight leftWeight rightWeight (polynomialOrbitKey recipe) < n
      rw [weight_orbit_key])]
  rw [orbit_key_closure]

/-- Deduplicated retained orbit vocabulary computed without dependent recipes. -/
noncomputable def retainedOrbitVocabulary
    (n leftWeight rightWeight : ℕ) :
    List POKey :=
  (retainedOrbitClosure n leftWeight rightWeight).dedup

/--
The recipe-free retained orbit vocabulary is exactly the polynomial-orbit
vocabulary of the concrete finite correction closure.
-/
lemma retained_orbit_vocabulary
    (n leftWeight rightWeight : ℕ) :
    retainedOrbitVocabulary n leftWeight rightWeight =
      polynomialOrbitVocabulary
        (correctionClosureRecipes n leftWeight rightWeight) := by
  unfold retainedOrbitVocabulary polynomialOrbitVocabulary
  rw [key_closure_recipes]

private lemma map_map_of₂
    {α β γ : Type*}
    {relation : α → β → Prop}
    (f : α → γ)
    (g : β → γ)
    (hfg : ∀ left right, relation left right → f left = g right) :
    ∀ {left : List α} {right : List β},
      List.Forall₂ relation left right →
        left.map f = right.map g
  | [], [], .nil =>
      rfl
  | _ :: _, _ :: _, .cons head tail => by
      simp only [List.map_cons]
      rw [hfg _ _ head, map_map_of₂ f g hfg tail]

/-- Ordered multiplicity-independent orbit-key trace emitted by one obstruction. -/
noncomputable def retainedOrbitKeys
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (obstruction : RObstru) :
    List POKey :=
  (obstruction.retainedRecipes (n := n) hleftWeight hrightWeight).map
    polynomialOrbitKey

/--
Polynomial-equivalent source obstructions emit literally equal ordered
polynomial-orbit key traces.
-/
lemma retained_keys_equivalent
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {left right : RObstru}
    (h : PolynomialEquivalent left right) :
    retainedOrbitKeys (n := n) hleftWeight hrightWeight left =
      retainedOrbitKeys (n := n) hleftWeight hrightWeight right := by
  unfold retainedOrbitKeys
  exact
    map_map_of₂ polynomialOrbitKey polynomialOrbitKey
      (fun leftRecipe rightRecipe hrecipe =>
        polynomial_orbit_key.mpr hrecipe)
      (retRecps_forall₂
        (n := n) hleftWeight hrightWeight left right h)

end ROTransi
end TCTex
end Towers

/-!
# Recipe-free operational recursion for Hall-Petresco polynomial orbits

The recipe-level operational recollector retains dependent placeholder
alphabets even though its branch decisions and emitted polynomial factors
depend only on polynomial orbit keys.  This file defines the same ordered
recursion directly on recipe-free keys and proves that mapping a recipe trace
to keys gives exactly this recursion.

No positivity subtype is needed: every orbit key carries a nonempty
`CWord`, so positive source weights make its weighted Hall degree
positive.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace RRPkt

open HACoeff
open BRPkt
open ROAggreg
open ROTransi
open BRSpec

/-- One adjacent pair of recipe-free polynomial orbit keys still requiring collection. -/
structure POObstru where
  left :
    POKey
  right :
    POKey

namespace POObstru

/-- Total weighted Hall degree of one recipe-free orbit obstruction. -/
def weight
    (leftWeight rightWeight : ℕ)
    (O : POObstru) :
    ℕ :=
  orbitWeight leftWeight rightWeight O.left +
    orbitWeight leftWeight rightWeight O.right

/-- Leading recipe-free correction key emitted by one orbit obstruction. -/
def correction
    (O : POObstru) :
    POKey :=
  orbitCorrection O.left O.right

/-- Operational child created when the left parent crosses the emitted correction. -/
def operationalNestedLeft
    (O : POObstru) :
    POObstru where
  left :=
    O.left
  right :=
    O.correction

/-- Operational child created when the right parent crosses the emitted correction. -/
def operationalNestedRight
    (O : POObstru) :
    POObstru where
  left :=
    O.right
  right :=
    O.correction

@[simp]
lemma weight_nested_left
    (leftWeight rightWeight : ℕ)
    (O : POObstru) :
    O.operationalNestedLeft.weight leftWeight rightWeight =
      2 * orbitWeight leftWeight rightWeight O.left +
        orbitWeight leftWeight rightWeight O.right := by
  change
    orbitWeight leftWeight rightWeight O.left +
          orbitWeight leftWeight rightWeight
            (orbitCorrection O.left O.right) =
      2 * orbitWeight leftWeight rightWeight O.left +
        orbitWeight leftWeight rightWeight O.right
  rw [weight_correction]
  omega

@[simp]
lemma weight_operational_right
    (leftWeight rightWeight : ℕ)
    (O : POObstru) :
    O.operationalNestedRight.weight leftWeight rightWeight =
      orbitWeight leftWeight rightWeight O.left +
        2 * orbitWeight leftWeight rightWeight O.right := by
  change
    orbitWeight leftWeight rightWeight O.right +
          orbitWeight leftWeight rightWeight
            (orbitCorrection O.left O.right) =
      orbitWeight leftWeight rightWeight O.left +
        2 * orbitWeight leftWeight rightWeight O.right
  rw [weight_correction]
  omega

/-- Every recipe-free operational left child has strictly larger weighted degree. -/
lemma weight_operational_left
    {leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru) :
    O.weight leftWeight rightWeight <
      O.operationalNestedLeft.weight leftWeight rightWeight := by
  rw [weight_nested_left]
  unfold weight
  have hleft :
      0 < orbitWeight leftWeight rightWeight O.left := by
    unfold orbitWeight
    exact
      CWord.weight_pos
        (HPAtom.weight leftWeight rightWeight)
        (HPAtom.weight_pos hleftWeight hrightWeight)
        O.left.erasedShape
  omega

/-- Every recipe-free operational right child has strictly larger weighted degree. -/
lemma weight_operational_nested
    {leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru) :
    O.weight leftWeight rightWeight <
      O.operationalNestedRight.weight leftWeight rightWeight := by
  rw [weight_operational_right]
  unfold weight
  have hright :
      0 < orbitWeight leftWeight rightWeight O.right := by
    unfold orbitWeight
    exact
      CWord.weight_pos
        (HPAtom.weight leftWeight rightWeight)
        (HPAtom.weight_pos hleftWeight hrightWeight)
        O.right.erasedShape
  omega

/-- Remaining room below the cutoff for one recipe-free orbit obstruction. -/
def defect
    (n leftWeight rightWeight : ℕ)
    (O : POObstru) :
    ℕ :=
  n - O.weight leftWeight rightWeight

/-- Recipe-free orbit obstructions descend when their cutoff defect decreases. -/
def Descends
    (n leftWeight rightWeight : ℕ)
    (child parent : POObstru) :
    Prop :=
  child.defect n leftWeight rightWeight <
    parent.defect n leftWeight rightWeight

/-- Recipe-free orbit-obstruction descent is well-founded. -/
lemma descends_wellFounded
    (n leftWeight rightWeight : ℕ) :
    WellFounded (Descends n leftWeight rightWeight) := by
  unfold Descends
  exact InvImage.wf (defect n leftWeight rightWeight) Nat.lt_wfRel.wf

/-- Every surviving recipe-free operational left child strictly descends. -/
lemma nestedLeftDescends
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hcutoff : O.operationalNestedLeft.weight leftWeight rightWeight < n) :
    Descends n leftWeight rightWeight O.operationalNestedLeft O := by
  unfold Descends defect
  have hweight := O.weight_operational_left hleftWeight hrightWeight
  omega

/-- Every surviving recipe-free operational right child strictly descends. -/
lemma nestedRightDescends
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    (hcutoff : O.operationalNestedRight.weight leftWeight rightWeight < n) :
    Descends n leftWeight rightWeight O.operationalNestedRight O := by
  unfold Descends defect
  have hweight := O.weight_operational_nested hleftWeight hrightWeight
  omega

/--
Finite cutoff-specific list of recipe-free keys emitted by the operational
recursion.
-/
noncomputable def retainedKeys
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru) :
    List POKey :=
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

/-- Recipe-free packets expose their root-and-operational-children recurrence. -/
lemma keys_cons_append
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru) :
    retainedKeys (n := n) hleftWeight hrightWeight O =
      O.correction ::
        (if _hleft :
            O.operationalNestedLeft.weight leftWeight rightWeight < n then
          retainedKeys (n := n) hleftWeight hrightWeight
            O.operationalNestedLeft
        else []) ++
        (if _hright :
            O.operationalNestedRight.weight leftWeight rightWeight < n then
          retainedKeys (n := n) hleftWeight hrightWeight
            O.operationalNestedRight
        else []) := by
  rw [retainedKeys, WellFounded.fix_eq]
  split <;> split <;> rfl

end POObstru

/-- Forget dependent recipe labels in one operational recipe obstruction. -/
def polynomialOrbitObstruction
    (O : RObstru) :
    POObstru where
  left :=
    polynomialOrbitKey O.left
  right :=
    polynomialOrbitKey O.right

@[simp]
lemma weight_orbit_obstruction
    (leftWeight rightWeight : ℕ)
    (O : RObstru) :
    (polynomialOrbitObstruction O).weight leftWeight rightWeight =
      O.weight leftWeight rightWeight := by
  simp [polynomialOrbitObstruction, POObstru.weight,
    RObstru.weight]

@[simp]
lemma correction_orbit_obstruction
    (O : RObstru) :
    (polynomialOrbitObstruction O).correction =
      polynomialOrbitKey O.correction := by
  simp [polynomialOrbitObstruction, POObstru.correction,
    RObstru.correction]

@[simp]
lemma operational_left_obstruction
    (O : RObstru) :
    (polynomialOrbitObstruction O).operationalNestedLeft =
      polynomialOrbitObstruction O.operationalNestedLeft := by
  simp [polynomialOrbitObstruction,
    POObstru.operationalNestedLeft,
    RObstru.operationalNestedLeft,
    POObstru.correction,
    RObstru.correction]

@[simp]
lemma operational_orbit_obstruction
    (O : RObstru) :
    (polynomialOrbitObstruction O).operationalNestedRight =
      polynomialOrbitObstruction O.operationalNestedRight := by
  simp [polynomialOrbitObstruction,
    POObstru.operationalNestedRight,
    RObstru.operationalNestedRight,
    POObstru.correction,
    RObstru.correction]

/--
Mapping an ordered operational recipe trace to polynomial orbit keys gives
exactly the recipe-free operational recursion.
-/
lemma retained_orbit_keys
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : RObstru) :
    retainedOrbitKeys (n := n) hleftWeight hrightWeight O =
      (polynomialOrbitObstruction O).retainedKeys
        (n := n) hleftWeight hrightWeight := by
  unfold retainedOrbitKeys
  refine
    (RObstru.descends_wellFounded n leftWeight rightWeight).induction
      (C := fun O =>
        (O.retainedRecipes (n := n) hleftWeight hrightWeight).map
            polynomialOrbitKey =
          (polynomialOrbitObstruction O).retainedKeys
            (n := n) hleftWeight hrightWeight)
      O ?_
  intro parent ih
  rw [RObstru.recipes_cons_append
      hleftWeight hrightWeight parent,
    POObstru.keys_cons_append
      hleftWeight hrightWeight (polynomialOrbitObstruction parent),
    List.map_append, List.map_cons,
    correction_orbit_obstruction]
  apply congrArg₂ (· ++ ·)
  · by_cases hleft :
        parent.operationalNestedLeft.weight leftWeight rightWeight < n
    · have horbit :
          (polynomialOrbitObstruction parent).operationalNestedLeft.weight
              leftWeight rightWeight < n := by
        simpa using hleft
      rw [dif_pos hleft, dif_pos horbit,
        operational_left_obstruction]
      exact
        congrArg (List.cons (polynomialOrbitKey parent.correction))
          (ih parent.operationalNestedLeft
            (parent.nestedLeftDescends
              hleftWeight hrightWeight hleft))
    · have horbit :
          ¬(polynomialOrbitObstruction parent).operationalNestedLeft.weight
              leftWeight rightWeight < n := by
        simpa using hleft
      rw [dif_neg hleft, dif_neg horbit]
      rfl
  · by_cases hright :
        parent.operationalNestedRight.weight leftWeight rightWeight < n
    · have horbit :
          (polynomialOrbitObstruction parent).operationalNestedRight.weight
              leftWeight rightWeight < n := by
        simpa using hright
      rw [dif_pos hright, dif_pos horbit,
        operational_orbit_obstruction]
      exact
        ih parent.operationalNestedRight
          (parent.nestedRightDescends
            hleftWeight hrightWeight hright)
    · have horbit :
          ¬(polynomialOrbitObstruction parent).operationalNestedRight.weight
              leftWeight rightWeight < n := by
        simpa using hright
      rw [dif_neg hright, dif_neg horbit]
      rfl

end RRPkt
end TCTex
end Towers

/-!
# Polynomial-orbit support for ordered operational recipe packets

Ordered operational recipe traces are multiplicity-independent before any
deduplication or regrouping.  The finite correction closure supports each
recipe occurrence pointwise.  This file transfers that support statement to
the recipe-free polynomial-orbit vocabulary.

The resulting key list retains the operational order and may contain repeated
keys.  The vocabulary on the right is deduplicated and is used only as a
finite support set.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace ROSuppor

open HACoeff
open RCSuppor
open BRPkt
open BRPkt.RObstru
open ROAggreg
open ROTransi
open UCVocabu
open URVocabu

/--
Every retained concrete closure recipe maps into the deduplicated recipe-free
orbit vocabulary.
-/
lemma
    key_vocabulary_recipes
    {n leftWeight rightWeight : ℕ}
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ correctionClosureRecipes n leftWeight rightWeight) :
    polynomialOrbitKey recipe ∈
      retainedOrbitVocabulary n leftWeight rightWeight := by
  rw [retained_orbit_vocabulary]
  unfold polynomialOrbitVocabulary
  rw [List.mem_dedup]
  exact List.mem_map.mpr ⟨recipe, hrecipe, rfl⟩

/--
Every key occurrence in an ordered operational trace rooted at source recipes
belongs to the deduplicated retained orbit vocabulary.
-/
lemma orbit_vocabulary_keys
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : RObstru)
    (hleft : O.left ∈ sourceRecipes n leftWeight rightWeight)
    (hright : O.right ∈ sourceRecipes n leftWeight rightWeight)
    (hroot : O.weight leftWeight rightWeight < n)
    {key : POKey}
    (hkey :
      key ∈ retainedOrbitKeys (n := n)
        hleftWeight hrightWeight O) :
    key ∈ retainedOrbitVocabulary
      n leftWeight rightWeight := by
  unfold retainedOrbitKeys at hkey
  rcases List.mem_map.mp hkey with ⟨recipe, hrecipe, rfl⟩
  apply
    key_vocabulary_recipes
  exact
    RObstru.retained_closure_recipes
      hleftWeight hrightWeight O hleft hright hroot hrecipe

/--
The complete ordered key trace of a source-rooted operational packet is
pointwise supported by the finite recipe-free orbit vocabulary.
-/
lemma keys_subset_vocabulary
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : RObstru)
    (hleft : O.left ∈ sourceRecipes n leftWeight rightWeight)
    (hright : O.right ∈ sourceRecipes n leftWeight rightWeight)
    (hroot : O.weight leftWeight rightWeight < n) :
    retainedOrbitKeys (n := n)
        hleftWeight hrightWeight O ⊆
      retainedOrbitVocabulary n leftWeight rightWeight := by
  intro key hkey
  exact
    orbit_vocabulary_keys
      hleftWeight hrightWeight O hleft hright hroot hkey

/--
Every recipe in the earlier universal source-and-operational vocabulary maps
into the retained recipe-free orbit vocabulary.
-/
lemma
    orbit_key_recipes
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ recipes n leftWeight rightWeight
        hleftWeight hrightWeight) :
    polynomialOrbitKey recipe ∈
      retainedOrbitVocabulary n leftWeight rightWeight := by
  apply
    key_vocabulary_recipes
  exact retained_correction_recipes hrecipe

end ROSuppor
end TCTex
end Towers

/-!
# Recipe-free evaluation of ordered operational polynomial-orbit traces

Polynomial orbit keys remember exactly the multiplicity-independent data
needed to evaluate one Hall-Petresco recipe factor: its erased Hall word and
its two generalized-binomial source-block lists.  This file evaluates ordered
operational key traces directly and proves that forgetting dependent recipe
labels does not change their noncommutative product.

As a consequence, polynomial-equivalent source obstructions emit local
operational packets with literally equal ordered evaluations.  This is a safe
orbit-level compression statement: it does not permute factors inside a
packet.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace ROEvalua

open HACoeff
open ROEquiv
open ROEquiv.RObstru
open BRPkt
open BRPkt.RObstru
open ROAggreg
open ROTransi
open BRSpec

/-- Generalized-binomial coefficient carried by one recipe-free orbit key. -/
def orbitCoefficientValue
    (key : POKey)
    (leftExponent rightExponent : ℤ) :
    ℤ :=
  (key.leftBlocks.map fun degree => Ring.choose leftExponent degree).prod *
    (key.rightBlocks.map fun degree => Ring.choose rightExponent degree).prod

/-- Evaluate one recipe-free orbit key as a Hall-word power. -/
def orbitFactorValue
    {G : Type*}
    [Group G]
    (key : POKey)
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    G :=
  key.erasedShape.eval (HPAtom.eval left right) ^
    orbitCoefficientValue key leftExponent rightExponent

@[simp]
lemma coefficient_value_key
    (recipe : BRecipe)
    (leftExponent rightExponent : ℤ) :
    orbitCoefficientValue (polynomialOrbitKey recipe)
        leftExponent rightExponent =
      BRSpec.coefficientValue
        recipe leftExponent rightExponent :=
  rfl

@[simp]
lemma orbit_value_key
    {G : Type*}
    [Group G]
    (recipe : BRecipe)
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    orbitFactorValue (polynomialOrbitKey recipe)
        left right leftExponent rightExponent =
      recipe.erasedShape.eval (HPAtom.eval left right) ^
        BRSpec.coefficientValue
          recipe leftExponent rightExponent :=
  rfl

/--
Evaluating the ordered operational key trace is exactly the original ordered
recipe-factor product.
-/
lemma orbit_keys_recipes
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : RObstru)
    {G : Type*}
    [Group G]
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    ((retainedOrbitKeys (n := n)
        hleftWeight hrightWeight O).map fun key =>
      orbitFactorValue key
        left right leftExponent rightExponent).prod =
        ((O.retainedRecipes (n := n) hleftWeight hrightWeight).map
          fun recipe =>
            recipe.erasedShape.eval (HPAtom.eval left right) ^
              BRSpec.coefficientValue
                recipe leftExponent rightExponent).prod := by
  unfold retainedOrbitKeys
  rw [List.map_map]
  rfl

/--
Polynomial-equivalent source obstructions have equal recipe-free ordered
operational evaluations.
-/
lemma orbit_keys_equivalent
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {O P : RObstru}
    (h : PolynomialEquivalent O P)
    {G : Type*}
    [Group G]
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    ((retainedOrbitKeys (n := n)
        hleftWeight hrightWeight O).map fun key =>
      orbitFactorValue key
        left right leftExponent rightExponent).prod =
        ((retainedOrbitKeys (n := n)
          hleftWeight hrightWeight P).map fun key =>
            orbitFactorValue key
              left right leftExponent rightExponent).prod := by
  rw [retained_keys_equivalent
    hleftWeight hrightWeight h]

/--
Polynomial-equivalent source obstructions have equal ordered recipe-factor
products at every group pair and integral exponent pair.
-/
lemma list_recipes_equivalent
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {O P : RObstru}
    (h : PolynomialEquivalent O P)
    {G : Type*}
    [Group G]
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    ((O.retainedRecipes (n := n) hleftWeight hrightWeight).map
      fun recipe =>
        recipe.erasedShape.eval (HPAtom.eval left right) ^
          BRSpec.coefficientValue
            recipe leftExponent rightExponent).prod =
      ((P.retainedRecipes (n := n) hleftWeight hrightWeight).map
        fun recipe =>
          recipe.erasedShape.eval (HPAtom.eval left right) ^
            BRSpec.coefficientValue
              recipe leftExponent rightExponent).prod := by
  rw [←
    orbit_keys_recipes
      hleftWeight hrightWeight O left right leftExponent rightExponent]
  rw [←
    orbit_keys_recipes
      hleftWeight hrightWeight P left right leftExponent rightExponent]
  exact
    orbit_keys_equivalent
      hleftWeight hrightWeight h left right leftExponent rightExponent

end ROEvalua
end TCTex
end Towers

/-!
# Evaluation of recipe-free operational Hall-Petresco orbit recursions

The recipe-free operational recurrence carries enough information to evaluate
its ordered trace directly.  This file records the root-and-two-branches
evaluation equation and identifies the resulting product with the original
ordered recipe-factor product.

The theorem is local: it preserves the operational order inside one
obstruction packet and does not regroup unrelated packets.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace RREvalua

open ROEvalua
open RRPkt
open
  RRPkt.POObstru
open BRPkt
open ROAggreg
open ROTransi
open BRSpec

/-- Evaluate the recipe-free ordered trace emitted by one orbit obstruction. -/
noncomputable def listEval
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    {G : Type*}
    [Group G]
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    G :=
  ((O.retainedKeys (n := n) hleftWeight hrightWeight).map fun key =>
    orbitFactorValue key
      left right leftExponent rightExponent).prod

/--
The recipe-free ordered evaluation is its leading correction factor followed
by the two surviving operational branch evaluations.
-/
lemma list_root_branches
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : POObstru)
    {G : Type*}
    [Group G]
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    listEval (n := n) hleftWeight hrightWeight O
        left right leftExponent rightExponent =
      orbitFactorValue O.correction
          left right leftExponent rightExponent *
        (((if _hleft :
              O.operationalNestedLeft.weight leftWeight rightWeight < n then
            O.operationalNestedLeft.retainedKeys
              (n := n) hleftWeight hrightWeight
          else []).map fun key =>
            orbitFactorValue key
              left right leftExponent rightExponent).prod *
          ((if _hright :
              O.operationalNestedRight.weight leftWeight rightWeight < n then
            O.operationalNestedRight.retainedKeys
              (n := n) hleftWeight hrightWeight
          else []).map fun key =>
            orbitFactorValue key
              left right leftExponent rightExponent).prod) := by
  unfold listEval
  rw [keys_cons_append]
  simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  rw [mul_assoc]

/--
Evaluating the recipe-free recurrence rooted at a recipe obstruction is
exactly the original ordered recipe-factor product.
-/
lemma orbit_obstruction_recipes
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : RObstru)
    {G : Type*}
    [Group G]
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    listEval (n := n) hleftWeight hrightWeight
        (polynomialOrbitObstruction O)
        left right leftExponent rightExponent =
      ((O.retainedRecipes (n := n) hleftWeight hrightWeight).map
        fun recipe =>
          recipe.erasedShape.eval (HPAtom.eval left right) ^
            BRSpec.coefficientValue
              recipe leftExponent rightExponent).prod := by
  unfold listEval
  rw [← retained_orbit_keys
    hleftWeight hrightWeight O]
  exact
    orbit_keys_recipes
      hleftWeight hrightWeight O left right leftExponent rightExponent

end RREvalua
end TCTex
end Towers

/-!
# Signed-profile packets for polynomial orbits of block recipes

Polynomial-orbit aggregation is finer than erased-word aggregation: distinct
coefficient formulas may still evaluate the same Hall word.  This file keeps
that distinction and attaches one homogeneous signed-profile packet to each
polynomial orbit of a finite recipe inventory.

Each orbit packet evaluates as its orbit multiplicity times one representative
coefficient formula.  The ordered orbit packets remain aligned with the full
recipe inventory up to the exact permutation proved by the orbit partition.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace RFPacket

open HACoeff
open ROAggreg
open BRSpec
open
  CFSubsti
open
  ACAlign
open UCVocabu

/-- Every retained polynomial-orbit key has a recipe representative. -/
lemma recipe_recipes_orbit
    {recipes : List BRecipe}
    {key : POKey}
    (hkey : key ∈ polynomialOrbitVocabulary recipes) :
    ∃ recipe : BRecipe,
      recipe ∈ recipesPolynomialOrbit recipes key := by
  classical
  unfold polynomialOrbitVocabulary at hkey
  rw [List.mem_dedup] at hkey
  rcases List.mem_map.mp hkey with
    ⟨recipe, hrecipe, hrecipeKey⟩
  refine ⟨recipe, ?_⟩
  unfold recipesPolynomialOrbit
  rw [List.mem_filter]
  exact ⟨hrecipe, by simpa using hrecipeKey⟩

/-- Choose one concrete recipe representative of a retained polynomial orbit. -/
noncomputable def recipePolynomialOrbit
    (recipes : List BRecipe)
    (key : { key // key ∈ polynomialOrbitVocabulary recipes }) :
    BRecipe :=
  Classical.choose
    (recipe_recipes_orbit key.2)

/-- The selected orbit representative belongs to its orbit chunk. -/
lemma recipe_polynomial_orbit
    (recipes : List BRecipe)
    (key : { key // key ∈ polynomialOrbitVocabulary recipes }) :
    recipePolynomialOrbit recipes key ∈
      recipesPolynomialOrbit recipes key.1 :=
  Classical.choose_spec
    (recipe_recipes_orbit key.2)

/--
Attach the aggregate same-orbit coefficient profile to one polynomial-orbit
representative.
-/
noncomputable def packetPolynomialOrbit
    (recipes : List BRecipe)
    (key : { key // key ∈ polynomialOrbitVocabulary recipes }) :
    RFPkt :=
  let representative :=
    recipePolynomialOrbit recipes key
  RFPkt.ofRecipeChunk
    representative.erasedShape
    representative.positive
    (recipesPolynomialOrbit recipes key.1)
    (fun _recipe hrecipe =>
      erased_recipes_orbit
        hrecipe (recipe_polynomial_orbit recipes key))

/-- Ordered signed-profile packet list, one packet for each polynomial orbit. -/
noncomputable def polynomialOrbitPackets
    (recipes : List BRecipe) :
    List RFPkt :=
  (polynomialOrbitVocabulary recipes).attach.map fun key =>
    packetPolynomialOrbit recipes key

/-- Orbit chunks indexed in the same attached-key order as the packet list. -/
noncomputable def attachedOrbitChunks
    (recipes : List BRecipe) :
    List (List BRecipe) :=
  (polynomialOrbitVocabulary recipes).attach.map fun key =>
    recipesPolynomialOrbit recipes key.1

/-- Attaching subtype membership proofs does not change the orbit chunks. -/
lemma attached_orbit_chunks
    (recipes : List BRecipe) :
    attachedOrbitChunks recipes =
      polynomialOrbitChunks recipes := by
  unfold attachedOrbitChunks polynomialOrbitChunks
  simpa only [List.map_map, Function.comp_apply] using
    congrArg
      (fun keys => keys.map (recipesPolynomialOrbit recipes))
      (List.attach_map_subtype_val (polynomialOrbitVocabulary recipes))

/-- The attached orbit chunks still flatten to a permutation of the input list. -/
lemma flatten_attached_chunks
    (recipes : List BRecipe) :
    List.Perm (attachedOrbitChunks recipes).flatten recipes := by
  rw [attached_orbit_chunks]
  exact orbit_recipes_perm recipes

/-- Each orbit packet is aligned with its complete same-orbit recipe chunk. -/
noncomputable def packetChunkAlignment
    (recipes : List BRecipe)
    (key : { key // key ∈ polynomialOrbitVocabulary recipes }) :
    RFPkt.RCAlign
      (packetPolynomialOrbit recipes key)
      (recipesPolynomialOrbit recipes key.1) :=
  RFPkt.recipe_chunk_alignment
    (recipePolynomialOrbit recipes key).erasedShape
    (recipePolynomialOrbit recipes key).positive
    (recipesPolynomialOrbit recipes key.1)
    (fun _recipe hrecipe =>
      erased_recipes_orbit
        hrecipe (recipe_polynomial_orbit recipes key))

/-- The ordered polynomial-orbit packet list is aligned chunk by chunk. -/
lemma orbit_packets_forall₂_attachedPolynomialOrbitChunks
    (recipes : List BRecipe) :
    List.Forall₂
      RFPkt.RCAlign
      (polynomialOrbitPackets recipes)
      (attachedOrbitChunks recipes) := by
  unfold polynomialOrbitPackets attachedOrbitChunks
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff,
    List.forall₂_same]
  intro key _hkey
  exact packetChunkAlignment recipes key

/--
Each orbit packet value is its orbit multiplicity times the coefficient of its
selected representative.
-/
lemma value_orbit_length
    (recipes : List BRecipe)
    (key : { key // key ∈ polynomialOrbitVocabulary recipes })
    (leftExponent rightExponent : ℤ) :
    (packetPolynomialOrbit recipes key).profiles.value
        leftExponent rightExponent =
      ((recipesPolynomialOrbit recipes key.1).length : ℤ) *
        coefficientValue (recipePolynomialOrbit recipes key)
          leftExponent rightExponent := by
  rw [
    show
      (packetPolynomialOrbit recipes key).profiles.value
          leftExponent rightExponent =
        ((recipesPolynomialOrbit recipes key.1).map fun recipe =>
          coefficientValue recipe leftExponent rightExponent).sum by
        exact
          (packetChunkAlignment recipes key)
            |>.profiles_value_sum leftExponent rightExponent]
  exact
    sum_recipes_length
      (recipe_polynomial_orbit recipes key)
      leftExponent rightExponent

private lemma flatten_recipe_factors
    {G : Type*}
    [Group G]
    {packets : List RFPkt}
    {chunks : List (List BRecipe)}
    (alignment :
      List.Forall₂
        RFPkt.RCAlign
        packets chunks)
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    (packets.map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value leftExponent rightExponent).prod =
      (chunks.flatten.map fun recipe =>
        recipe.erasedShape.eval (HPAtom.eval left right) ^
          coefficientValue recipe leftExponent rightExponent).prod := by
  induction alignment with
  | nil =>
      simp
  | cons headAlignment _tailAlignment ih =>
      simp only [List.map_cons, List.prod_cons, List.flatten_cons,
        List.map_append, List.prod_append]
      rw [headAlignment.eval_recipe_factors, ih]

/--
The orbit packet product is the full recipe product after the exact orbit
permutation.  This is valid in arbitrary groups because permutation is used
only to describe the retained inventory, not to commute its factors.
-/
lemma packets_flattened_factors
    {G : Type*}
    [Group G]
    (recipes : List BRecipe)
    (left right : G)
    (leftExponent rightExponent : ℤ) :
    ((polynomialOrbitPackets recipes).map fun packet =>
      packet.word.eval (HPAtom.eval left right) ^
        packet.profiles.value leftExponent rightExponent).prod =
      ((attachedOrbitChunks recipes).flatten.map fun recipe =>
        recipe.erasedShape.eval (HPAtom.eval left right) ^
          coefficientValue recipe leftExponent rightExponent).prod :=
  flatten_recipe_factors
    (orbit_packets_forall₂_attachedPolynomialOrbitChunks recipes)
    left right leftExponent rightExponent

/-- Orbit packets specialize to the retained universal finite correction closure. -/
noncomputable def closureOrbitPackets
    (n leftWeight rightWeight : ℕ) :
    List RFPkt :=
  polynomialOrbitPackets
    (correctionClosureRecipes n leftWeight rightWeight)

end RFPacket
end TCTex
end Towers
