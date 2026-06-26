import Towers.Group.Zassenhaus.SchedulingContracts
import Towers.Group.Zassenhaus.PartialCollapsedAccounting
import Towers.Group.Zassenhaus.PositiveDegreeRecipes


/-!
# Recursive Hall-Petresco family obstructions

Outside the class-two terminal zone, collecting the leading correction packet
creates two possible nested adjacent obstructions.  Their total weights are
`2 * wt(B) + wt(A)` and `wt(B) + 2 * wt(A)`.  Both strictly exceed the parent
obstruction weight, so cutoff-minus-weight is a well-founded recursion measure.

This file packages that recursion skeleton and connects one obstruction to its
exact Cartesian correction-slot ledger.  It is intentionally not imported by
the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace FRObstr

universe u

open HACoeff
open BRSpec

/-- One adjacent pair of complete block families still requiring collection. -/
structure FObstru
    (M N : ℕ) where
  left :
    BFam M N
  right :
    BFam M N

namespace FObstru

/-- Total weighted Hall degree of an adjacent family obstruction. -/
def weight
    {M N : ℕ}
    (leftWeight rightWeight : ℕ)
    (O : FObstru M N) :
    ℕ :=
  weightedWordWeight leftWeight rightWeight O.left.recipe +
    weightedWordWeight leftWeight rightWeight O.right.recipe

/-- The leading Cartesian correction family emitted by one obstruction. -/
def correction
    {M N : ℕ}
    (O : FObstru M N) :
    BFam M N :=
  O.left.correction O.right

/-- Nested obstruction produced when the correction packet crosses the left parent. -/
def nestedLeft
    {M N : ℕ}
    (O : FObstru M N) :
    FObstru M N where
  left := O.correction
  right := O.left

/-- Nested obstruction produced when the correction packet crosses the right parent. -/
def nestedRight
    {M N : ℕ}
    (O : FObstru M N) :
    FObstru M N where
  left := O.correction
  right := O.right

@[simp]
lemma recipe_correction
    {M N : ℕ}
    (O : FObstru M N) :
    O.correction.recipe = O.left.recipe.correction O.right.recipe :=
  rfl

@[simp]
lemma weight_nestedLeft
    {M N : ℕ}
    (leftWeight rightWeight : ℕ)
    (O : FObstru M N) :
    O.nestedLeft.weight leftWeight rightWeight =
      2 * weightedWordWeight leftWeight rightWeight O.left.recipe +
        weightedWordWeight leftWeight rightWeight O.right.recipe := by
  change
    weightedWordWeight leftWeight rightWeight
          (O.left.correction O.right).recipe +
        weightedWordWeight leftWeight rightWeight O.left.recipe =
      2 * weightedWordWeight leftWeight rightWeight O.left.recipe +
        weightedWordWeight leftWeight rightWeight O.right.recipe
  rw [BFam.recipe_correction, weighted_weight_correction]
  omega

@[simp]
lemma weight_nestedRight
    {M N : ℕ}
    (leftWeight rightWeight : ℕ)
    (O : FObstru M N) :
    O.nestedRight.weight leftWeight rightWeight =
      weightedWordWeight leftWeight rightWeight O.left.recipe +
        2 * weightedWordWeight leftWeight rightWeight O.right.recipe := by
  change
    weightedWordWeight leftWeight rightWeight
          (O.left.correction O.right).recipe +
        weightedWordWeight leftWeight rightWeight O.right.recipe =
      weightedWordWeight leftWeight rightWeight O.left.recipe +
        2 * weightedWordWeight leftWeight rightWeight O.right.recipe
  rw [BFam.recipe_correction, weighted_weight_correction]
  omega

/-- Both nested corrections have reached the quotient cutoff. -/
def Terminal
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (O : FObstru M N) :
    Prop :=
  n ≤ O.nestedLeft.weight leftWeight rightWeight ∧
    n ≤ O.nestedRight.weight leftWeight rightWeight

/-- Remaining room below the cutoff for one adjacent family obstruction. -/
def defect
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (O : FObstru M N) :
    ℕ :=
  n - O.weight leftWeight rightWeight

/-- A nested obstruction descends when its cutoff defect decreases. -/
def Descends
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (child parent : FObstru M N) :
    Prop :=
  child.defect n leftWeight rightWeight <
    parent.defect n leftWeight rightWeight

/-- Obstruction descent is well-founded because it is inverse image of `Nat.lt`. -/
lemma descends_wellFounded
    (M N n leftWeight rightWeight : ℕ) :
    WellFounded
      (@Descends M N n leftWeight rightWeight) := by
  unfold Descends
  exact InvImage.wf (defect n leftWeight rightWeight) Nat.lt_wfRel.wf

/-- The left nested obstruction has strictly larger weight than its parent. -/
lemma nested_left
    {M N leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) :
    O.weight leftWeight rightWeight <
      O.nestedLeft.weight leftWeight rightWeight := by
  rw [weight_nestedLeft]
  unfold weight
  have hleft :=
    weighted_weight_pos hleftWeight hrightWeight O.left.recipe
  omega

/-- The right nested obstruction has strictly larger weight than its parent. -/
lemma weight_nested_right
    {M N leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) :
    O.weight leftWeight rightWeight <
      O.nestedRight.weight leftWeight rightWeight := by
  rw [weight_nestedRight]
  unfold weight
  have hright :=
    weighted_weight_pos hleftWeight hrightWeight O.right.recipe
  omega

/-- A surviving left nested obstruction strictly descends in cutoff defect. -/
lemma nestedLeft_descends
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N)
    (hcutoff : O.nestedLeft.weight leftWeight rightWeight < n) :
    Descends n leftWeight rightWeight O.nestedLeft O := by
  unfold Descends defect
  have hweight := O.nested_left hleftWeight hrightWeight
  omega

/-- A surviving right nested obstruction strictly descends in cutoff defect. -/
lemma nestedRight_descends
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N)
    (hcutoff : O.nestedRight.weight leftWeight rightWeight < n) :
    Descends n leftWeight rightWeight O.nestedRight O := by
  unfold Descends defect
  have hweight := O.weight_nested_right hleftWeight hrightWeight
  omega

/-- Well-founded induction principle for recursive adjacent-obstruction builders. -/
theorem descends_induction
    {M N n leftWeight rightWeight : ℕ}
    {motive : FObstru M N → Prop}
    (step :
      ∀ parent,
        (∀ child,
          Descends n leftWeight rightWeight child parent →
            motive child) →
          motive parent)
    (O : FObstru M N) :
    motive O :=
  (descends_wellFounded M N n leftWeight rightWeight).induction O step

/-- Canonical parent realizations form closed collapsed packets. -/
lemma realizations_packet_left
    {M N : ℕ}
    (O : FObstru M N) :
    PCCounti.CPFor
      O.left O.left.realizations :=
  PCCounti.CPFor.realizations O.left

/-- Canonical parent realizations form closed collapsed packets. -/
lemma realizations_packet_right
    {M N : ℕ}
    (O : FObstru M N) :
    PCCounti.CPFor
      O.right O.right.realizations :=
  PCCounti.CPFor.realizations O.right

/-- Exact concrete slot ledger for the leading Cartesian correction family. -/
def initialCorrectionLedger
    {M N : ℕ}
    (O : FObstru M N) :
    HPCollap.CSLedger
      O.left O.right O.left.realizations O.right.realizations :=
  HPCollap.CSLedger.initial
    O.left O.right O.left.realizations O.right.realizations

/-- Exhausting the initial correction ledger closes to the leading family packet. -/
lemma correctionPacket
    {M N : ℕ}
    (O : FObstru M N) :
    PCCounti.CPFor O.correction
      (PCCounti.correctionWords
        O.left.realizations O.right.realizations) := by
  exact (O.realizations_packet_left).correctionWords O.realizations_packet_right

/--
At a terminal obstruction, the previously proved class-two constructor supplies
the quotient-aware adjacent family swap.
-/
def terminalSwap
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N)
    (hterminal : O.Terminal n leftWeight rightWeight) :
    BFTrunc.STSwap.{u}
      n leftWeight rightWeight O.left O.right :=
  CTPacketa.STSwap.of_classTwo
    hleftWeight hrightWeight O.left O.right
      (by simpa [Terminal] using hterminal.1)
      (by simpa [Terminal] using hterminal.2)

/-- If an obstruction itself reaches the cutoff, it swaps with no retained packet. -/
def cutoffSwap
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N)
    (hcutoff : n ≤ O.weight leftWeight rightWeight) :
    BFTrunc.STSwap.{u}
      n leftWeight rightWeight O.left O.right :=
  BFTrunc.STSwap.empty_n_add
    hleftWeight hrightWeight O.left O.right hcutoff

mutual

  /--
  Finite recursive call tree for one retained family obstruction.  Its two
  children record the only nested obstruction weights needed by the
  Hall-Petresco collector.
  -/
  inductive ROTree
      {M N : ℕ}
      (n leftWeight rightWeight : ℕ) :
      FObstru M N → Type
    | node
        (O : FObstru M N)
        (left :
          NOTree n leftWeight rightWeight O.nestedLeft)
        (right :
          NOTree n leftWeight rightWeight O.nestedRight) :
        ROTree n leftWeight rightWeight O

  /-- One nested branch is either erased at the cutoff or recursively retained. -/
  inductive NOTree
      {M N : ℕ}
      (n leftWeight rightWeight : ℕ) :
      FObstru M N → Type
    | cutoff
        (O : FObstru M N)
        (hcutoff : n ≤ O.weight leftWeight rightWeight) :
        NOTree n leftWeight rightWeight O
    | retained
        (O : FObstru M N)
        (hcutoff : O.weight leftWeight rightWeight < n)
        (tree : ROTree n leftWeight rightWeight O) :
        NOTree n leftWeight rightWeight O

end

/--
Construct the finite recursive obstruction tree by well-founded induction on
cutoff defect.  Every retained edge carries the strict descent proof.
-/
noncomputable def recursiveObstructionTree
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) :
    ROTree n leftWeight rightWeight O :=
  (descends_wellFounded M N n leftWeight rightWeight).fix
    (fun parent recurse =>
      ROTree.node parent
        (if hleft :
            parent.nestedLeft.weight leftWeight rightWeight < n then
          NOTree.retained parent.nestedLeft hleft
            (recurse parent.nestedLeft
              (parent.nestedLeft_descends hleftWeight hrightWeight hleft))
        else
          NOTree.cutoff parent.nestedLeft
            (Nat.le_of_not_gt hleft))
        (if hright :
            parent.nestedRight.weight leftWeight rightWeight < n then
          NOTree.retained parent.nestedRight hright
            (recurse parent.nestedRight
              (parent.nestedRight_descends hleftWeight hrightWeight hright))
        else
          NOTree.cutoff parent.nestedRight
            (Nat.le_of_not_gt hright)))
    O

@[simp]
lemma weight_correction
    {M N leftWeight rightWeight : ℕ}
    (O : FObstru M N) :
    weightedWordWeight leftWeight rightWeight O.correction.recipe =
      O.weight leftWeight rightWeight := by
  rw [recipe_correction, weighted_weight_correction]
  rfl

/-- Each original left parent lies strictly below its obstruction weight. -/
lemma left_weight
    {M N leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) :
    weightedWordWeight leftWeight rightWeight O.left.recipe <
      O.weight leftWeight rightWeight := by
  unfold weight
  exact Nat.lt_add_of_pos_right
    (weighted_weight_pos hleftWeight hrightWeight O.right.recipe)

/-- Each original right parent lies strictly below its obstruction weight. -/
lemma right_weight
    {M N leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) :
    weightedWordWeight leftWeight rightWeight O.right.recipe <
      O.weight leftWeight rightWeight := by
  unfold weight
  rw [Nat.add_comm]
  exact Nat.lt_add_of_pos_right
    (weighted_weight_pos hleftWeight hrightWeight O.left.recipe)

mutual

  /-- Flatten the leading family emitted at each retained obstruction-tree node. -/
  def ROTree.correctionFamilies
      {M N n leftWeight rightWeight : ℕ}
      {O : FObstru M N} :
      ROTree n leftWeight rightWeight O →
        List (BFam M N)
    | .node O left right =>
        O.correction :: left.correctionFamilies ++ right.correctionFamilies

  /-- Cutoff branches emit nothing; retained branches emit their recursive packets. -/
  def NOTree.correctionFamilies
      {M N n leftWeight rightWeight : ℕ}
      {O : FObstru M N} :
      NOTree n leftWeight rightWeight O →
        List (BFam M N)
    | .cutoff _ _ =>
        []
    | .retained _ _ tree =>
        tree.correctionFamilies

end

/-- Every flattened recursive correction family remains below the cutoff. -/
lemma ROTree.corr_famsweight_ltcutoff
    {M N n leftWeight rightWeight : ℕ}
    {O : FObstru M N}
    (tree : ROTree n leftWeight rightWeight O)
    (hcutoff : O.weight leftWeight rightWeight < n) :
    ∀ C ∈ tree.correctionFamilies,
      weightedWordWeight leftWeight rightWeight C.recipe < n := by
  refine ROTree.recOn
    (motive_1 := fun O tree =>
      O.weight leftWeight rightWeight < n →
        ∀ C ∈ tree.correctionFamilies,
          weightedWordWeight leftWeight rightWeight C.recipe < n)
    (motive_2 := fun _ tree =>
      ∀ C ∈ tree.correctionFamilies,
        weightedWordWeight leftWeight rightWeight C.recipe < n)
    tree ?_ ?_ ?_ hcutoff
  · intro O left right hleft hright hcutoff C hC
    simp only [ROTree.correctionFamilies,
      List.mem_cons, List.mem_append] at hC
    rcases hC with (rfl | hC) | hC
    · rw [weight_correction]
      exact hcutoff
    · exact hleft C hC
    · exact hright C hC
  · intro O hcutoff
    simp [NOTree.correctionFamilies]
  · intro O hcutoff tree htree
    exact htree hcutoff

/-- Every family emitted below a retained nested branch remains below cutoff. -/
lemma NOTree.corr_famsweight_ltcutoff
    {M N n leftWeight rightWeight : ℕ}
    {O : FObstru M N}
    (tree : NOTree n leftWeight rightWeight O) :
    ∀ C ∈ tree.correctionFamilies,
      weightedWordWeight leftWeight rightWeight C.recipe < n := by
  refine NOTree.recOn
    (motive_1 := fun O tree =>
      O.weight leftWeight rightWeight < n →
        ∀ C ∈ tree.correctionFamilies,
          weightedWordWeight leftWeight rightWeight C.recipe < n)
    (motive_2 := fun _ tree =>
      ∀ C ∈ tree.correctionFamilies,
        weightedWordWeight leftWeight rightWeight C.recipe < n)
    tree ?_ ?_ ?_
  · intro O left right hleft hright hcutoff C hC
    simp only [ROTree.correctionFamilies,
      List.mem_cons, List.mem_append] at hC
    rcases hC with (rfl | hC) | hC
    · rw [weight_correction]
      exact hcutoff
    · exact hleft C hC
    · exact hright C hC
  · intro O hcutoff
    simp [NOTree.correctionFamilies]
  · intro O hcutoff tree htree
    exact htree hcutoff

/-- Flattened correction families lie at or above the root obstruction weight. -/
lemma ROTree.weight_lecorr_fammem
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {O : FObstru M N}
    (tree : ROTree n leftWeight rightWeight O) :
    ∀ C ∈ tree.correctionFamilies,
      O.weight leftWeight rightWeight ≤
        weightedWordWeight leftWeight rightWeight C.recipe := by
  refine ROTree.recOn
    (motive_1 := fun O tree =>
      ∀ C ∈ tree.correctionFamilies,
        O.weight leftWeight rightWeight ≤
          weightedWordWeight leftWeight rightWeight C.recipe)
    (motive_2 := fun O tree =>
      ∀ C ∈ tree.correctionFamilies,
        O.weight leftWeight rightWeight ≤
          weightedWordWeight leftWeight rightWeight C.recipe)
    tree ?_ ?_ ?_
  · intro O left right hleft hright C hC
    simp only [ROTree.correctionFamilies,
      List.mem_cons, List.mem_append] at hC
    rcases hC with (rfl | hC) | hC
    · rw [weight_correction]
    · exact le_trans
        (O.nested_left hleftWeight hrightWeight).le
        (hleft C hC)
    · exact le_trans
        (O.weight_nested_right hleftWeight hrightWeight).le
        (hright C hC)
  · intro O hcutoff
    simp [NOTree.correctionFamilies]
  · intro O hcutoff tree htree
    exact htree

/-- Nested flattened packets lie at or above their branch obstruction weight. -/
lemma NOTree.weight_lecorr_fammem
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {O : FObstru M N}
    (tree : NOTree n leftWeight rightWeight O) :
    ∀ C ∈ tree.correctionFamilies,
      O.weight leftWeight rightWeight ≤
        weightedWordWeight leftWeight rightWeight C.recipe := by
  refine NOTree.recOn
    (motive_1 := fun O tree =>
      ∀ C ∈ tree.correctionFamilies,
        O.weight leftWeight rightWeight ≤
          weightedWordWeight leftWeight rightWeight C.recipe)
    (motive_2 := fun O tree =>
      ∀ C ∈ tree.correctionFamilies,
        O.weight leftWeight rightWeight ≤
          weightedWordWeight leftWeight rightWeight C.recipe)
    tree ?_ ?_ ?_
  · intro O left right hleft hright C hC
    simp only [ROTree.correctionFamilies,
      List.mem_cons, List.mem_append] at hC
    rcases hC with (rfl | hC) | hC
    · rw [weight_correction]
    · exact le_trans
        (O.nested_left hleftWeight hrightWeight).le
        (hleft C hC)
    · exact le_trans
        (O.weight_nested_right hleftWeight hrightWeight).le
        (hright C hC)
  · intro O hcutoff
    simp [NOTree.correctionFamilies]
  · intro O hcutoff tree htree
    exact htree

/-- Every flattened recursive family lies strictly above the original left parent. -/
lemma ROTree.leftweight_ltcorr_fammem
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {O : FObstru M N}
    (tree : ROTree n leftWeight rightWeight O)
    {C : BFam M N}
    (hC : C ∈ tree.correctionFamilies) :
    weightedWordWeight leftWeight rightWeight O.left.recipe <
      weightedWordWeight leftWeight rightWeight C.recipe :=
  lt_of_lt_of_le
    (O.left_weight hleftWeight hrightWeight)
    (tree.weight_lecorr_fammem hleftWeight hrightWeight C hC)

/-- Every flattened recursive family lies strictly above the original right parent. -/
lemma ROTree.rightweight_ltcorr_fammem
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {O : FObstru M N}
    (tree : ROTree n leftWeight rightWeight O)
    {C : BFam M N}
    (hC : C ∈ tree.correctionFamilies) :
    weightedWordWeight leftWeight rightWeight O.right.recipe <
      weightedWordWeight leftWeight rightWeight C.recipe :=
  lt_of_lt_of_le
    (O.right_weight hleftWeight hrightWeight)
    (tree.weight_lecorr_fammem hleftWeight hrightWeight C hC)

/-- Concrete finite packet of all correction families retained by the recursive tree. -/
noncomputable def retainedCorrectionFamilies
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) :
    List (BFam M N) :=
  (recursiveObstructionTree (n := n) hleftWeight hrightWeight O).correctionFamilies

end FObstru

end FRObstr
end TCTex
end Towers

/-!
# Polynomial endpoint for recursive Hall-Petresco family packets

The finite obstruction tree retains complete higher-weight block families.
This file forgets their concrete realization slots only at the endpoint and
attaches the raw independent-block recipes to Claim 8 symbolic polynomial
factors.  The semantic collection identity for the nonterminal tree is a
separate remaining obligation.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace RPPkt

universe u

open HACoeff
open BRSpec
open FRObstr

/-- Raw-history recipes retained by one finite recursive obstruction tree. -/
noncomputable def retainedRecipes
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) :
    List BRecipe :=
  (O.retainedCorrectionFamilies (n := n) hleftWeight hrightWeight).map
    BFam.recipe

/-- Every retained raw recipe comes from one concrete family in the tree packet. -/
lemma family_retained_recipes
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    {R : BRecipe}
    (hR : R ∈ retainedRecipes (n := n) hleftWeight hrightWeight O) :
    ∃ C ∈ O.retainedCorrectionFamilies (n := n) hleftWeight hrightWeight,
      C.recipe = R := by
  rcases List.mem_map.mp hR with ⟨C, hC, rfl⟩
  exact ⟨C, hC, rfl⟩

/-- Every retained raw recipe remains below the quotient cutoff. -/
lemma weighted_retained_recipes
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    (hroot : O.weight leftWeight rightWeight < n)
    {R : BRecipe}
    (hR : R ∈ retainedRecipes (n := n) hleftWeight hrightWeight O) :
    weightedWordWeight leftWeight rightWeight R < n := by
  rcases family_retained_recipes hR with ⟨C, hC, rfl⟩
  exact
    (O.recursiveObstructionTree
      (n := n) hleftWeight hrightWeight).corr_famsweight_ltcutoff
      hroot C hC

/-- Every retained raw recipe lies strictly above the original left parent. -/
lemma left_retained_recipes
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    {R : BRecipe}
    (hR : R ∈ retainedRecipes (n := n) hleftWeight hrightWeight O) :
    weightedWordWeight leftWeight rightWeight O.left.recipe <
      weightedWordWeight leftWeight rightWeight R := by
  rcases family_retained_recipes hR with ⟨C, hC, rfl⟩
  exact
    (O.recursiveObstructionTree
      (n := n) hleftWeight hrightWeight).leftweight_ltcorr_fammem
      hleftWeight hrightWeight hC

/-- Every retained raw recipe lies strictly above the original right parent. -/
lemma right_retained_recipes
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    {R : BRecipe}
    (hR : R ∈ retainedRecipes (n := n) hleftWeight hrightWeight O) :
    weightedWordWeight leftWeight rightWeight O.right.recipe <
      weightedWordWeight leftWeight rightWeight R := by
  rcases family_retained_recipes hR with ⟨C, hC, rfl⟩
  exact
    (O.recursiveObstructionTree
      (n := n) hleftWeight hrightWeight).rightweight_ltcorr_fammem
      hleftWeight hrightWeight hC

/-- Attach the retained raw-history recipes to Claim 8 symbolic factors. -/
noncomputable def symbolicFactors
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (O : FObstru M N)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    List (SPFactor H ι) :=
  BRSpec.symbolicFactors
    (retainedRecipes (n := n)
      (HEAddres.weight_pos leftAddress)
      (HEAddres.weight_pos rightAddress) O)
    leftInput rightInput leftAddress rightAddress

/-- Every recursive symbolic factor remembers one retained raw-history recipe. -/
lemma recipe_factors
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {O : FObstru M N}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈ symbolicFactors (n := n) O leftInput rightInput
        leftAddress rightAddress) :
    ∃ R ∈ retainedRecipes (n := n)
        (HEAddres.weight_pos leftAddress)
        (HEAddres.weight_pos rightAddress) O,
      factor =
        BRSpec.symbolicFactor
          R leftInput rightInput leftAddress rightAddress := by
  exact BRSpec.recipe_factors
    hfactor

/-- Every recursive symbolic correction factor remains below the quotient cutoff. -/
lemma weight_symbolic_factors
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {O : FObstru M N}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    (hroot : O.weight leftAddress.1 rightAddress.1 < n)
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈ symbolicFactors (n := n) O leftInput rightInput
        leftAddress rightAddress) :
    factor.word.weight HEAddres.weight < n := by
  rcases recipe_factors hfactor with ⟨R, hR, rfl⟩
  rw [word_symbolic_factor, ← weighted_word_weight]
  exact weighted_retained_recipes hroot hR

/-- Every recursive symbolic correction factor lies above the original left parent. -/
lemma left_parent_factors
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {O : FObstru M N}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈ symbolicFactors (n := n) O leftInput rightInput
        leftAddress rightAddress) :
    weightedWordWeight leftAddress.1 rightAddress.1 O.left.recipe <
      factor.word.weight HEAddres.weight := by
  rcases recipe_factors hfactor with ⟨R, hR, rfl⟩
  rw [word_symbolic_factor, ← weighted_word_weight]
  exact left_retained_recipes hR

/-- Every recursive symbolic correction factor lies above the original right parent. -/
lemma right_parent_factors
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {O : FObstru M N}
    {leftInput rightInput : ι}
    {leftAddress rightAddress : HEAddres H}
    {factor : SPFactor H ι}
    (hfactor :
      factor ∈ symbolicFactors (n := n) O leftInput rightInput
        leftAddress rightAddress) :
    weightedWordWeight leftAddress.1 rightAddress.1 O.right.recipe <
      factor.word.weight HEAddres.weight := by
  rcases recipe_factors hfactor with ⟨R, hR, rfl⟩
  rw [word_symbolic_factor, ← weighted_word_weight]
  exact right_retained_recipes hR

end RPPkt
end TCTex
end Towers

/-!
# Recursive decomposition of retained Hall-Petresco packets

The obstruction-tree endpoint is useful to polynomial consumers, but recursive
semantic proofs also need its one-step equation.  This file exposes the root
correction packet followed by the two surviving nested packets, with cutoff
branches erased.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace RPDecomp

open HACoeff
open FRObstr
open RPPkt

namespace FObstru

/--
The retained concrete packet consists of the leading correction family and the
two recursively retained nested packets.  A nested packet contributes nothing
once its obstruction weight reaches the cutoff.
-/
lemma retained_families_cons
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) :
    O.retainedCorrectionFamilies (n := n) hleftWeight hrightWeight =
      O.correction ::
        (if _hleft :
            O.nestedLeft.weight leftWeight rightWeight < n then
          O.nestedLeft.retainedCorrectionFamilies
            (n := n) hleftWeight hrightWeight
        else []) ++
        (if _hright :
            O.nestedRight.weight leftWeight rightWeight < n then
          O.nestedRight.retainedCorrectionFamilies
            (n := n) hleftWeight hrightWeight
        else []) := by
  rw [FObstru.retainedCorrectionFamilies,
    FObstru.recursiveObstructionTree, WellFounded.fix_eq]
  simp only [FObstru.ROTree.correctionFamilies]
  split <;> split <;>
    simp [FObstru.NOTree.correctionFamilies,
      FObstru.retainedCorrectionFamilies,
      FObstru.recursiveObstructionTree]

end FObstru

/--
The retained raw recipes satisfy the same root-and-two-branches recursion as
their concrete block families.
-/
lemma recipes_cons_append
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) :
    retainedRecipes (n := n) hleftWeight hrightWeight O =
      O.correction.recipe ::
        (if _hleft :
            O.nestedLeft.weight leftWeight rightWeight < n then
          retainedRecipes (n := n) hleftWeight hrightWeight O.nestedLeft
        else []) ++
        (if _hright :
            O.nestedRight.weight leftWeight rightWeight < n then
          retainedRecipes (n := n) hleftWeight hrightWeight O.nestedRight
        else []) := by
  rw [retainedRecipes,
    FObstru.retained_families_cons
    hleftWeight hrightWeight]
  simp only [List.map_cons, List.map_append]
  split <;> split <;> rfl

/--
The specialized symbolic factor packet has an explicit recursive equation:
the leading correction factor is followed by the two surviving nested factor
packets.
-/
lemma symbolic_cons_append
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (O : FObstru M N)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    RPPkt.symbolicFactors
        (n := n) O leftInput rightInput leftAddress rightAddress =
      BRSpec.symbolicFactor
          O.correction.recipe leftInput rightInput leftAddress rightAddress ::
        (if _hleft :
            O.nestedLeft.weight leftAddress.weight rightAddress.weight < n then
          RPPkt.symbolicFactors
            (n := n) O.nestedLeft leftInput rightInput
              leftAddress rightAddress
        else []) ++
        (if _hright :
            O.nestedRight.weight leftAddress.weight rightAddress.weight < n then
          RPPkt.symbolicFactors
            (n := n) O.nestedRight leftInput rightInput
              leftAddress rightAddress
        else []) := by
  rw [RPPkt.symbolicFactors,
    recipes_cons_append]
  simp only [BRSpec.symbolicFactors,
    List.map_cons, List.map_append]
  split <;> split <;>
    simp_all [RPPkt.symbolicFactors,
      BRSpec.symbolicFactors]

/--
Evaluation of the recursive symbolic packet follows the same root-and-branches
equation.  This is the polynomial recurrence consumed by a semantic induction.
-/
lemma list_factors_branches
    {M N n d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (e : ι → HEFam H)
    (O : FObstru M N)
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H) :
    SPFactor.listEval (n := n) e
        (RPPkt.symbolicFactors
          (n := n) O leftInput rightInput leftAddress rightAddress) =
      (BRSpec.symbolicFactor
          O.correction.recipe leftInput rightInput
            leftAddress rightAddress).eval e *
        (SPFactor.listEval e
            (if _hleft :
                O.nestedLeft.weight leftAddress.weight rightAddress.weight < n then
              RPPkt.symbolicFactors
                (n := n) O.nestedLeft leftInput rightInput
                  leftAddress rightAddress
            else []) *
          SPFactor.listEval e
            (if _hright :
                O.nestedRight.weight leftAddress.weight rightAddress.weight < n then
              RPPkt.symbolicFactors
                (n := n) O.nestedRight leftInput rightInput
                  leftAddress rightAddress
            else [])) := by
  rw [symbolic_cons_append]
  simp only [SPFactor.listEval_cons,
    SPFactor.listEval_append]
  rw [mul_assoc]

end RPDecomp
end TCTex
end Towers

/-!
# Semantic interface for recursive Hall-Petresco family packets

The recursive obstruction tree already constructs the finite list of retained
higher-weight raw-history packets.  One theorem remains before that list can be
used as a complete adjacent-family swap: its ordered realization list must have
the expected value in every matching nilpotent quotient.

This file isolates exactly that semantic certificate.  Once supplied, the
existing truncated-family consumer and scheduler step follow automa.
This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace RSInterf

universe u

open HACoeff
open BRSpec
open FRObstr
open BFTrunc
open CTPacketa.STSwap

/--
The single semantic theorem still required for one nonterminal recursive
family packet.
-/
structure RSCert
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N)
    (hroot : O.weight leftWeight rightWeight < n) :
    Prop where
  collapsed_list_eval :
    ∀ {G : Type u} [Group G]
      (x y : G),
      x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1) →
      y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1) →
      Subgroup.lowerCentralSeries G (n - 1) = ⊥ →
      collapsedList x y
          (BFam.realizationList
              (O.retainedCorrectionFamilies (n := n)
                hleftWeight hrightWeight) ++
            O.right.realizations ++ O.left.realizations) =
        collapsedList x y
          (O.left.realizations ++ O.right.realizations)

/--
In the class-two terminal zone, the recursive tree retains exactly the leading
correction family.
-/
lemma families_singleton_terminal
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N)
    (hterminal : O.Terminal n leftWeight rightWeight) :
    O.retainedCorrectionFamilies (n := n) hleftWeight hrightWeight =
      [O.correction] := by
  rw [FObstru.retainedCorrectionFamilies,
    FObstru.recursiveObstructionTree, WellFounded.fix_eq]
  simp only [dif_neg (Nat.not_lt_of_ge hterminal.1),
    dif_neg (Nat.not_lt_of_ge hterminal.2),
    FObstru.ROTree.correctionFamilies,
    FObstru.NOTree.correctionFamilies,
    List.append_nil]

namespace RSCert

/--
The class-two terminal constructor supplies the semantic certificate for a
surviving leading correction family.
-/
def of_terminal
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N)
    (hroot : O.weight leftWeight rightWeight < n)
    (hterminal : O.Terminal n leftWeight rightWeight) :
    RSCert n leftWeight rightWeight
      hleftWeight hrightWeight O hroot where
  collapsed_list_eval := by
    intro G _ x y hx hy hbot
    rw [families_singleton_terminal
      hleftWeight hrightWeight O hterminal]
    exact
      (singleton_correction_two
        hleftWeight hrightWeight O.left O.right hroot
          (by simpa [FObstru.Terminal] using hterminal.1)
          (by simpa [FObstru.Terminal] using hterminal.2)).collapsed_list_eval
        x y hx hy hbot

/--
Turn the isolated semantic theorem into the quotient-aware family-swap
consumer.  Weight ascent and cutoff bounds are discharged by the recursive
tree.
-/
noncomputable def semanticallyCompleteSwap
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    {hroot : O.weight leftWeight rightWeight < n}
    (certificate :
      RSCert n leftWeight rightWeight
        hleftWeight hrightWeight O hroot) :
    STSwap.{u}
      n leftWeight rightWeight O.left O.right where
  correctionFamilies :=
    O.retainedCorrectionFamilies (n := n) hleftWeight hrightWeight
  collapsed_list_eval :=
    certificate.collapsed_list_eval
  weighted_weight_left := by
    intro C hC
    exact
      (O.recursiveObstructionTree
        (n := n) hleftWeight hrightWeight).leftweight_ltcorr_fammem
          hleftWeight hrightWeight hC
  weighted_weight_right := by
    intro C hC
    exact
      (O.recursiveObstructionTree
        (n := n) hleftWeight hrightWeight).rightweight_ltcorr_fammem
          hleftWeight hrightWeight hC
  weighted_weight_cutoff := by
    intro C hC
    exact
      (O.recursiveObstructionTree
        (n := n) hleftWeight hrightWeight).corr_famsweight_ltcutoff
          hroot C hC

/-- Place one certified recursive swap into an adjacent family-list context. -/
noncomputable def semanticallyCompleteStep
    {M N n leftWeight rightWeight : ℕ}
    {G : Type u}
    [Group G]
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    {hroot : O.weight leftWeight rightWeight < n}
    (certificate :
      RSCert n leftWeight rightWeight
        hleftWeight hrightWeight O hroot)
    (x y : G)
    (P S : List (BFam M N)) :
    let swap :
        STSwap.{u}
          n leftWeight rightWeight O.left O.right :=
      RSCert.semanticallyCompleteSwap.{u}
        certificate
    BTSteps.SCStep
      x y n leftWeight rightWeight
      (P ++ [O.left, O.right] ++ S)
      (P ++ swap.correctionFamilies ++ [O.right, O.left] ++ S) := by
  let swap :
      STSwap.{u}
        n leftWeight rightWeight O.left O.right :=
    RSCert.semanticallyCompleteSwap.{u}
      certificate
  exact
    BTSteps.SCStep.obstruction
      (x := x) (y := y) P S O.left O.right swap

end RSCert

end RSInterf
end TCTex
end Towers

/-!
# Resolving recursive Hall-Petresco semantic certificates

The obstruction tree has two strictly smaller nested branches outside its
class-two terminal zone.  This file packages the remaining local algebra law as
a kernel: if one nonterminal obstruction can be certified from certificates for
its two surviving nested branches, well-founded recursion certifies every
obstruction below the cutoff.

The kernel constructor itself is the remaining Hall-polynomial collection
theorem.  This file is intentionally not imported by the existing collection
proof.
-/

namespace Towers
namespace TCTex
namespace RSResolu

universe u

open HACoeff
open FRObstr
open RSInterf

/--
Local nonterminal algebra law.  Both nested certificates are exposed as
functions because a branch at or above the cutoff requires no recursive proof.
-/
structure RSKern
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    Prop where
  resolve_nonterminal :
    ∀ (O : FObstru M N)
      (hroot : O.weight leftWeight rightWeight < n),
      ¬ O.Terminal n leftWeight rightWeight →
      (∀ hleft :
          O.nestedLeft.weight leftWeight rightWeight < n,
        RSCert.{u} n leftWeight rightWeight
          hleftWeight hrightWeight O.nestedLeft hleft) →
      (∀ hright :
          O.nestedRight.weight leftWeight rightWeight < n,
        RSCert.{u} n leftWeight rightWeight
          hleftWeight hrightWeight O.nestedRight hright) →
      RSCert.{u} n leftWeight rightWeight
        hleftWeight hrightWeight O hroot

namespace RSKern

/--
Resolve every below-cutoff obstruction by well-founded induction on cutoff
defect.  Terminal nodes use the checked class-two constructor; nonterminal
nodes invoke the local kernel on their two smaller branches.
-/
noncomputable def resolve
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      RSKern.{u} (M := M) (N := N)
        n leftWeight rightWeight
        hleftWeight hrightWeight)
    (O : FObstru M N)
    (hroot : O.weight leftWeight rightWeight < n) :
    RSCert.{u} n leftWeight rightWeight
      hleftWeight hrightWeight O hroot := by
  classical
  exact FObstru.descends_induction
    (motive := fun parent =>
      ∀ hparent : parent.weight leftWeight rightWeight < n,
        RSCert.{u} n leftWeight rightWeight
          hleftWeight hrightWeight parent hparent)
    (fun parent recurse hparent =>
      if hterminal : parent.Terminal n leftWeight rightWeight then
        RSCert.of_terminal
          hleftWeight hrightWeight parent hparent hterminal
      else
        kernel.resolve_nonterminal parent hparent hterminal
          (fun hleft =>
            recurse parent.nestedLeft
              (parent.nestedLeft_descends hleftWeight hrightWeight hleft)
              hleft)
          (fun hright =>
            recurse parent.nestedRight
              (parent.nestedRight_descends hleftWeight hrightWeight hright)
              hright))
    O hroot

/-- Every resolved recursive certificate becomes a quotient-aware family swap. -/
noncomputable def resolveSwap
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      RSKern.{u} (M := M) (N := N)
        n leftWeight rightWeight
        hleftWeight hrightWeight)
    (O : FObstru M N)
    (hroot : O.weight leftWeight rightWeight < n) :
    BFTrunc.STSwap.{u}
      n leftWeight rightWeight O.left O.right :=
  RSCert.semanticallyCompleteSwap.{u}
    (kernel.resolve O hroot)

/-- Every resolved recursive certificate becomes one contextual scheduler step. -/
noncomputable def resolveStep
    {M N n leftWeight rightWeight : ℕ}
    {G : Type u}
    [Group G]
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      RSKern.{u} (M := M) (N := N)
        n leftWeight rightWeight
        hleftWeight hrightWeight)
    (O : FObstru M N)
    (hroot : O.weight leftWeight rightWeight < n)
    (x y : G)
    (P S : List (BFam M N)) :
    let swap :
        BFTrunc.STSwap.{u}
          n leftWeight rightWeight O.left O.right :=
      kernel.resolveSwap O hroot
    BTSteps.SCStep
      x y n leftWeight rightWeight
      (P ++ [O.left, O.right] ++ S)
      (P ++ swap.correctionFamilies ++ [O.right, O.left] ++ S) := by
  exact
    (kernel.resolve O hroot).semanticallyCompleteStep
      x y P S

end RSKern

end RSResolu
end TCTex
end Towers

/-!
# Exact scheduler interface for recursive Hall-Petresco family packets

The recursive obstruction tree records the finite list of retained complete
correction families.  Its semantic interface asks for equality after
evaluation in every matching nilpotent quotient.  A concrete finite scheduler
can discharge that obligation more strongly: it may provide an exact sequence
of labelled-word swaps from the two parent realization lists to the flattened
tree endpoint.

This file packages that exact boundary and feeds it into the already checked
well-founded semantic resolver.
-/

namespace Towers
namespace TCTex
namespace REInterf

universe u

open HACoeff
open BBSched
open FRObstr
open RSInterf
open RSResolu

/--
An exact labelled-word schedule for the flattened endpoint retained by one
recursive obstruction tree.
-/
def RESched
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) :
    Prop :=
  BBSched.LWRw
    (O.left.realizations ++ O.right.realizations)
    (BFam.realizationList
        (O.retainedCorrectionFamilies (n := n)
          hleftWeight hrightWeight) ++
      O.right.realizations ++ O.left.realizations)

namespace RESched

/--
An exact complete-family swap supplies the recursive-tree schedule once its
emitted correction families are identified with the flattened tree packet.
-/
def completeFamilySwap
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    (swap :
      BBSched.CFSwap
        O.left O.right)
    (hcorrectionFamilies :
      swap.correctionFamilies =
        O.retainedCorrectionFamilies (n := n)
          hleftWeight hrightWeight) :
    RESched n leftWeight rightWeight
      hleftWeight hrightWeight O := by
  simpa [RESched, hcorrectionFamilies] using swap.rewrites

/-- Package one recursive-tree schedule as the existing exact family-swap carrier. -/
noncomputable def completeSwap
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    (schedule :
      RESched n leftWeight rightWeight
        hleftWeight hrightWeight O) :
    BBSched.CFSwap
      O.left O.right where
  correctionFamilies :=
    O.retainedCorrectionFamilies (n := n) hleftWeight hrightWeight
  rewrites := schedule

/--
The obstruction tree discharges every weight invariant required by the exact
truncated-family consumer.
-/
noncomputable def truncatedCompleteSwap
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    (hroot : O.weight leftWeight rightWeight < n)
    (schedule :
      RESched n leftWeight rightWeight
        hleftWeight hrightWeight O) :
    BBSched.TCSwap
      n leftWeight rightWeight O.left O.right where
  correctionFamilies :=
    O.retainedCorrectionFamilies (n := n) hleftWeight hrightWeight
  rewrites := schedule
  weighted_weight_left := by
    intro C hC
    exact
      (O.recursiveObstructionTree
        (n := n) hleftWeight hrightWeight).leftweight_ltcorr_fammem
          hleftWeight hrightWeight hC
  weighted_weight_right := by
    intro C hC
    exact
      (O.recursiveObstructionTree
        (n := n) hleftWeight hrightWeight).rightweight_ltcorr_fammem
          hleftWeight hrightWeight hC
  weighted_weight_cutoff := by
    intro C hC
    exact
      (O.recursiveObstructionTree
        (n := n) hleftWeight hrightWeight).corr_famsweight_ltcutoff
          hroot C hC

/--
An exact labelled-word schedule is stronger than the quotient-aware semantic
certificate consumed by the recursive family collector.
-/
def recursiveSemanticCertificate
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    {hroot : O.weight leftWeight rightWeight < n}
    (schedule :
      RESched n leftWeight rightWeight
        hleftWeight hrightWeight O) :
    RSCert.{u} n leftWeight rightWeight
      hleftWeight hrightWeight O hroot where
  collapsed_list_eval := by
    intro G _ x y _hx _hy _hbot
    exact
      BFTrunc.collapsed_labelled_rewrites
        x y schedule

/-- An exact recursive schedule directly supplies a quotient-aware family swap. -/
noncomputable def semanticallyCompleteSwap
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    {hroot : O.weight leftWeight rightWeight < n}
    (schedule :
      RESched n leftWeight rightWeight
        hleftWeight hrightWeight O) :
    BFTrunc.STSwap.{u}
      n leftWeight rightWeight O.left O.right :=
  RSCert.semanticallyCompleteSwap.{u}
    (schedule.recursiveSemanticCertificate (hroot := hroot))

end RESched

/--
Local nonterminal exact scheduler law.  Constructing this kernel is now the
remaining finite collection problem: no quotient semantics or polynomial
packaging remains inside the obligation.
-/
structure REKern
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    Prop where
  resolve_nonterminal :
    ∀ (O : FObstru M N)
      (_hroot : O.weight leftWeight rightWeight < n),
      ¬ O.Terminal n leftWeight rightWeight →
      RESched n leftWeight rightWeight
        hleftWeight hrightWeight O

/--
A batch scheduler may work directly with the existing exact
`CFSwap` carrier.  It only needs to prove that its emitted packet is
the flattened packet retained by the recursive obstruction tree.
-/
structure RCSwap
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    Prop where
  resolve_nonterminal :
    ∀ (O : FObstru M N)
      (_hroot : O.weight leftWeight rightWeight < n),
      ¬ O.Terminal n leftWeight rightWeight →
      ∃ swap :
          BBSched.CFSwap
            O.left O.right,
        swap.correctionFamilies =
          O.retainedCorrectionFamilies (n := n)
            hleftWeight hrightWeight

namespace RCSwap

/--
Every complete-family batch scheduler is an exact recursive scheduler after
forgetting its packaged family-swap witness.
-/
def recursiveExactKernel
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      RCSwap (M := M) (N := N)
        n leftWeight rightWeight hleftWeight hrightWeight) :
    REKern (M := M) (N := N)
      n leftWeight rightWeight hleftWeight hrightWeight where
  resolve_nonterminal := by
    intro O hroot hterminal
    obtain ⟨swap, hcorrectionFamilies⟩ :=
      kernel.resolve_nonterminal O hroot hterminal
    exact
      RESched.completeFamilySwap
        swap hcorrectionFamilies

end RCSwap

namespace REKern

/-- Every exact scheduler kernel is automa a semantic resolver kernel. -/
def recursiveSemanticKernel
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      REKern (M := M) (N := N)
        n leftWeight rightWeight hleftWeight hrightWeight) :
    RSKern.{u} (M := M) (N := N)
      n leftWeight rightWeight
      hleftWeight hrightWeight where
  resolve_nonterminal := by
    intro O hroot hterminal _hleft _hright
    exact
      (kernel.resolve_nonterminal O hroot hterminal).recursiveSemanticCertificate

/--
Resolve every below-cutoff family obstruction from a concrete exact scheduler
kernel.  Terminal nodes still use the checked class-two constructor.
-/
noncomputable def resolve
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      REKern (M := M) (N := N)
        n leftWeight rightWeight hleftWeight hrightWeight)
    (O : FObstru M N)
    (hroot : O.weight leftWeight rightWeight < n) :
    RSCert.{u} n leftWeight rightWeight
      hleftWeight hrightWeight O hroot :=
  kernel.recursiveSemanticKernel.resolve O hroot

/-- Every resolved exact kernel supplies the quotient-aware family swap. -/
noncomputable def resolveSwap
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      REKern (M := M) (N := N)
        n leftWeight rightWeight hleftWeight hrightWeight)
    (O : FObstru M N)
    (hroot : O.weight leftWeight rightWeight < n) :
    BFTrunc.STSwap.{u}
      n leftWeight rightWeight O.left O.right :=
  kernel.recursiveSemanticKernel.resolveSwap O hroot

/-- Every resolved exact kernel supplies one contextual quotient-aware step. -/
noncomputable def resolveStep
    {M N n leftWeight rightWeight : ℕ}
    {G : Type u}
    [Group G]
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      REKern (M := M) (N := N)
        n leftWeight rightWeight hleftWeight hrightWeight)
    (O : FObstru M N)
    (hroot : O.weight leftWeight rightWeight < n)
    (x y : G)
    (P S : List (BFam M N)) :
    let swap :
        BFTrunc.STSwap.{u}
          n leftWeight rightWeight O.left O.right :=
      kernel.resolveSwap O hroot
    BTSteps.SCStep
      x y n leftWeight rightWeight
      (P ++ [O.left, O.right] ++ S)
      (P ++ swap.correctionFamilies ++ [O.right, O.left] ++ S) := by
  exact kernel.recursiveSemanticKernel.resolveStep O hroot x y P S

end REKern

end REInterf
end TCTex
end Towers

/-!
# Residual-aware scheduling for truncated Hall-Petresco packets

An exact labelled-word collector cannot erase corrections in the free group.
At a fixed nilpotent cutoff it should instead retain an explicit residual word
list and prove that every residual word has reached the cutoff.  Those residual
words evaluate trivially only after passing to the matching nilpotent quotient.

This file packages that stronger operational boundary and feeds it into the
existing semantic recursive resolver.  It is intentionally not imported by the
existing collection proof.
-/

namespace Towers
namespace TCTex
namespace BRScheda

universe u

open HACoeff
open BRSpec
open BBSched
open BFTrunc
open FRObstr
open RSInterf
open RSResolu
open REInterf

/-- A concrete labelled word has reached the nilpotent cutoff after collapse. -/
def CollapsedWeightLeast
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (w : BBSched.LabelledWord M N) :
    Prop :=
  n ≤ (collapseWord w).weight (HPAtom.weight leftWeight rightWeight)

/-- Every collapsed word in a residual list has reached the nilpotent cutoff. -/
def WordsAboveCutoff
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (residualWords :
      List (BBSched.LabelledWord M N)) :
    Prop :=
  ∀ w ∈ residualWords, CollapsedWeightLeast n leftWeight rightWeight w

/-- One collapsed labelled word above the cutoff evaluates trivially. -/
lemma collapsed_weight_least
    {M N n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    (w : BBSched.LabelledWord M N)
    (hweight : CollapsedWeightLeast n leftWeight rightWeight w) :
    (collapseWord w).eval (HPAtom.eval x y) = 1 := by
  apply eq_bot_iff.mp hbot
  exact Subgroup.lowerCentralSeries_antitone (Nat.sub_le_sub_right hweight 1)
    (CWord.eval_lower_series
      (HPAtom.eval x y)
      (HPAtom.weight leftWeight rightWeight)
      (HPAtom.weight_pos hleftWeight hrightWeight)
      (fun a => by
        cases a with
        | left =>
            simpa [HPAtom.eval, HPAtom.weight] using hx
        | right =>
            simpa [HPAtom.eval, HPAtom.weight] using hy)
      (collapseWord w))

/-- A residual list above the cutoff has trivial collapsed evaluation. -/
lemma collapsed_words_above
    {M N n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    (residualWords :
      List (BBSched.LabelledWord M N))
    (hresidual :
      WordsAboveCutoff n leftWeight rightWeight residualWords) :
    collapsedList x y residualWords = 1 := by
  induction residualWords with
  | nil =>
      rfl
  | cons w residualWords ih =>
      simp only [collapsedList, List.map_cons, List.prod_cons]
      rw [collapsed_weight_least
        hleftWeight hrightWeight hx hy hbot w (hresidual w (by simp))]
      simpa [collapsedList] using
        ih (fun z hz => hresidual z (by simp [hz]))

/--
Exact operational family swap with an explicit above-cutoff residual list.
Only the below-cutoff correction families are retained by polynomial consumers.
-/
structure ECSwap
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (B A : BFam M N) where
  correctionFamilies :
    List (BFam M N)
  residualWords :
    List (BBSched.LabelledWord M N)
  rewrites :
    BBSched.LWRw
      (B.realizations ++ A.realizations)
      (BFam.realizationList correctionFamilies ++
        residualWords ++ A.realizations ++ B.realizations)
  wordsAboveCutoff :
    WordsAboveCutoff n leftWeight rightWeight residualWords
  weighted_weight_left :
    ∀ C ∈ correctionFamilies,
      weightedWordWeight leftWeight rightWeight B.recipe <
        weightedWordWeight leftWeight rightWeight C.recipe
  weighted_weight_right :
    ∀ C ∈ correctionFamilies,
      weightedWordWeight leftWeight rightWeight A.recipe <
        weightedWordWeight leftWeight rightWeight C.recipe
  weighted_weight_cutoff :
    ∀ C ∈ correctionFamilies,
      weightedWordWeight leftWeight rightWeight C.recipe < n

namespace ECSwap

/--
Residual-aware exact schedules supply quotient-aware swaps: the exact rewrite
preserves evaluation and the residual prefix disappears at the cutoff.
-/
def semanticallyCompleteSwap
    {M N n leftWeight rightWeight : ℕ}
    {B A : BFam M N}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (swap :
      ECSwap n leftWeight rightWeight B A) :
    STSwap.{u}
      n leftWeight rightWeight B A where
  correctionFamilies := swap.correctionFamilies
  collapsed_list_eval := by
    intro G _ x y hx hy hbot
    have hresidual :
        collapsedList x y swap.residualWords = 1 :=
      collapsed_words_above
        hleftWeight hrightWeight hx hy hbot
          swap.residualWords swap.wordsAboveCutoff
    have hrewrites :=
      collapsed_labelled_rewrites x y swap.rewrites
    simpa [collapsed_list_append, hresidual] using hrewrites
  weighted_weight_left := swap.weighted_weight_left
  weighted_weight_right := swap.weighted_weight_right
  weighted_weight_cutoff := swap.weighted_weight_cutoff

end ECSwap

/--
Residual-aware exact schedule for the flattened packet retained by one
recursive obstruction tree.
-/
structure RRSched
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (O : FObstru M N) where
  residualWords :
    List (BBSched.LabelledWord M N)
  rewrites :
    BBSched.LWRw
      (O.left.realizations ++ O.right.realizations)
      (BFam.realizationList
          (O.retainedCorrectionFamilies (n := n)
            hleftWeight hrightWeight) ++
        residualWords ++ O.right.realizations ++ O.left.realizations)
  wordsAboveCutoff :
    WordsAboveCutoff n leftWeight rightWeight residualWords

namespace RRSched

/-- An exact recursive schedule is the special case with no residual words. -/
def recursiveExactSchedule
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    (schedule :
      REInterf.RESched
        n leftWeight rightWeight hleftWeight hrightWeight O) :
    RRSched n leftWeight rightWeight
      hleftWeight hrightWeight O where
  residualWords := []
  rewrites := by
    simpa [REInterf.RESched,
      List.append_assoc] using schedule
  wordsAboveCutoff := by
    intro w hw
    simp at hw

/-- Package one recursive residual schedule as a general residual family swap. -/
noncomputable def exactCompleteSwap
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    (hroot : O.weight leftWeight rightWeight < n)
    (schedule :
      RRSched n leftWeight rightWeight
        hleftWeight hrightWeight O) :
    ECSwap n leftWeight rightWeight
      O.left O.right where
  correctionFamilies :=
    O.retainedCorrectionFamilies (n := n) hleftWeight hrightWeight
  residualWords := schedule.residualWords
  rewrites := schedule.rewrites
  wordsAboveCutoff := schedule.wordsAboveCutoff
  weighted_weight_left := by
    intro C hC
    exact
      (O.recursiveObstructionTree
        (n := n) hleftWeight hrightWeight).leftweight_ltcorr_fammem
          hleftWeight hrightWeight hC
  weighted_weight_right := by
    intro C hC
    exact
      (O.recursiveObstructionTree
        (n := n) hleftWeight hrightWeight).rightweight_ltcorr_fammem
          hleftWeight hrightWeight hC
  weighted_weight_cutoff := by
    intro C hC
    exact
      (O.recursiveObstructionTree
        (n := n) hleftWeight hrightWeight).corr_famsweight_ltcutoff
          hroot C hC

/-- A residual-aware recursive schedule supplies the required semantic endpoint. -/
def recursiveSemanticCertificate
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {O : FObstru M N}
    (hroot : O.weight leftWeight rightWeight < n)
    (schedule :
      RRSched n leftWeight rightWeight
        hleftWeight hrightWeight O) :
    RSCert.{u} n leftWeight rightWeight
      hleftWeight hrightWeight O hroot where
  collapsed_list_eval := by
    intro G _ x y hx hy hbot
    exact
      (schedule.exactCompleteSwap hroot
        |>.semanticallyCompleteSwap
          hleftWeight hrightWeight).collapsed_list_eval
            x y hx hy hbot

end RRSched

/--
Local operational kernel with explicit high-weight residual words.  This is the
appropriate exact target for a cutoff-aware concrete collector.
-/
structure RRExact
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    Prop where
  resolve_nonterminal :
    ∀ (O : FObstru M N)
      (_hroot : O.weight leftWeight rightWeight < n),
      ¬ O.Terminal n leftWeight rightWeight →
        Nonempty
          (RRSched n leftWeight rightWeight
            hleftWeight hrightWeight O)

namespace RRExact

/-- Every residual-aware operational kernel supplies the semantic recursion kernel. -/
noncomputable def recursiveSemanticKernel
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      RRExact (M := M) (N := N)
        n leftWeight rightWeight hleftWeight hrightWeight) :
    RSKern.{u} (M := M) (N := N)
      n leftWeight rightWeight hleftWeight hrightWeight where
  resolve_nonterminal := by
    intro O hroot hterminal _hleft _hright
    exact
      (Classical.choice
        (kernel.resolve_nonterminal O hroot hterminal)).recursiveSemanticCertificate
          hroot

/-- Resolve every below-cutoff obstruction from one residual-aware exact kernel. -/
noncomputable def resolve
    {M N n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      RRExact (M := M) (N := N)
        n leftWeight rightWeight hleftWeight hrightWeight)
    (O : FObstru M N)
    (hroot : O.weight leftWeight rightWeight < n) :
    RSCert.{u} n leftWeight rightWeight
      hleftWeight hrightWeight O hroot :=
  kernel.recursiveSemanticKernel.resolve O hroot

end RRExact

end BRScheda
end TCTex
end Towers
