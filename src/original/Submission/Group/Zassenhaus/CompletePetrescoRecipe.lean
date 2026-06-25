import Submission.Group.Zassenhaus.AtomicPacketInterface
import Submission.Group.Zassenhaus.PositiveDegreeRecipes
import Submission.Group.Zassenhaus.SchedulingContracts

/-!
# Basic complete Hall-Petresco block recipe

The first retained correction in a Hall-Petresco packet is the hallPair
commutator.  It selects one raw left block and one raw right block.  This file
records that complete recipe and proves the simplifications needed by the
class-two terminal packet constructor.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

open HACoeff

namespace BRSpec

/-- The unique label in a singleton block of degree one. -/
def singletonOneLabel :
    BlockLabel [1] :=
  ⟨0, ⟨0, by simp⟩⟩

/-- Complete independent-block recipe for the hallPair Hall commutator. -/
def hallPair :
    BRecipe where
  leftBlocks := [1]
  rightBlocks := [1]
  word :=
    .commutator
      (.atom (.inl singletonOneLabel))
      (.atom (.inr singletonOneLabel))
  positive := by
    simp [collapseBlockRecipe, collapseRecipeLabel,
      CWord.PBPos]
  left_degree_eq := by
    simp [collapseBlockRecipe, collapseRecipeLabel]
  right_degree_eq := by
    simp [collapseBlockRecipe, collapseRecipeLabel]

/-- The hallPair recipe erases to the hallPair Hall-pair commutator. -/
@[simp]
lemma erased_shape_pair :
    hallPair.erasedShape = CWord.hallPairBase := by
  rfl

/-- The hallPair recipe selects one left source block. -/
@[simp]
lemma left_hall_pair :
    hallPair.leftDegree = 1 := by
  rfl

/-- The hallPair recipe selects one right source block. -/
@[simp]
lemma right_degree_pair :
    hallPair.rightDegree = 1 := by
  rfl

/-- The hallPair recipe coefficient is the product of the two source exponents. -/
@[simp]
lemma coefficient_value_pair
    (leftExponent rightExponent : ℤ) :
    coefficientValue hallPair leftExponent rightExponent =
      leftExponent * rightExponent := by
  simp [coefficientValue, hallPair]

/-- Substituting the hallPair recipe gives the bracket of the two raw atoms. -/
@[simp]
lemma bound_word_pair
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta d r}
    (leftAddress rightAddress : HEAddres H) :
    boundWord hallPair leftAddress rightAddress =
      .commutator (.atom leftAddress) (.atom rightAddress) := by
  rfl

/-- The hallPair recipe weight is the sum of the two raw Hall weights. -/
@[simp]
lemma weighted_word_pair
    (leftWeight rightWeight : ℕ) :
    weightedWordWeight leftWeight rightWeight hallPair =
      leftWeight + rightWeight := by
  simp

end BRSpec
end TCTex
end Submission

/-!
# Natural specialization of Hall-Petresco block recipes

A concrete complete `BFam` records one realization for each independent
choice of order embeddings.  The symbolic Claim 8 coefficient attached to its
recipe records the same count using generalized binomial coefficients.  This
file identifies the two descriptions at natural source multiplicities.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace BRSpec

open HACoeff
open BFTrunc

/--
At natural source multiplicities, the generalized-binomial coefficient of one
block recipe is the cardinality of its independent realization space.
-/
lemma coefficient_cast_embeddings
    (R : BRecipe)
    (M N : ℕ) :
    coefficientValue R (M : ℤ) (N : ℤ) =
      (Fintype.card (BRecipe.OrderEmbeddings R.leftBlocks M) : ℤ) *
        (Fintype.card (BRecipe.OrderEmbeddings R.rightBlocks N) : ℤ) := by
  simp only [coefficientValue, Ring.choose_natCast]
  rw [BRecipe.card_orderEmbeddings, BRecipe.card_orderEmbeddings]
  norm_num [Function.comp_def]

/--
At natural source multiplicities, the symbolic coefficient of a counted
family is its concrete number of labelled realizations.
-/
lemma BFam.coeffvalue_natcast_eqlength
    {M N : ℕ}
    (F : BFam M N) :
    coefficientValue F.recipe (M : ℤ) (N : ℤ) =
      (F.realizations.length : ℤ) := by
  rw [coefficient_cast_embeddings, F.length_eq]
  norm_num

/--
The concrete realization list of a counted family evaluates as the symbolic
recipe power specialized to natural source multiplicities.
-/
lemma BFam.collli_eqera_coeva
    {M N : ℕ}
    {G : Type*}
    [Group G]
    (x y : G)
    (F : BFam M N) :
    collapsedList x y F.realizations =
      F.recipe.erasedShape.eval (HPAtom.eval x y) ^
        coefficientValue F.recipe (M : ℤ) (N : ℤ) := by
  rw [collapsedList]
  have hmap :
      F.realizations.map
          (fun w => (collapseWord w).eval (HPAtom.eval x y)) =
        List.replicate F.realizations.length
          (F.recipe.erasedShape.eval (HPAtom.eval x y)) := by
    simpa using
      (List.eq_replicate_of_mem
        (a := F.recipe.erasedShape.eval (HPAtom.eval x y))
        (l := F.realizations.map
          fun w => (collapseWord w).eval (HPAtom.eval x y))
        (by
          intro z hz
          rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
          rw [F.collapse_word w hw]))
  rw [hmap, List.prod_replicate, coeffvalue_natcast_eqlength F,
    zpow_natCast]

end BRSpec
end TCTex
end Submission
