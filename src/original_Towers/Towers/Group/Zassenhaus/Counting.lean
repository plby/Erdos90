import Towers.Group.Zassenhaus.Recipes

/-!
# Counting independent repeated-block selections

The binomial monomials used by the power collector are literal cardinalities.
For each recorded block size `k`, choose an order-preserving embedding
`Fin k ↪o Fin q`; choices for distinct blocks are independent.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

/--
Independent order-preserving selections from `q` repeated input blocks, one
selection for every recorded block size.
-/
abbrev BlockOrderEmbeddings
    (indices : List ℕ)
    (q : ℕ) :=
  ∀ block : Fin indices.length, Fin (indices.get block) ↪o Fin q

/--
The number of independent order-preserving selections is the product of the
corresponding binomial coefficients.
-/
lemma card_order_embeddings
    (indices : List ℕ)
    (q : ℕ) :
    Fintype.card (BlockOrderEmbeddings indices q) =
      (indices.map fun k => Nat.choose q k).prod := by
  simp [BlockOrderEmbeddings,
    HACoeff.LRecipe.card_embedding_fin]

/-- Appending independent block histories multiplies their realization counts. -/
lemma card_embeddings_append
    (left right : List ℕ)
    (q : ℕ) :
    Fintype.card (BlockOrderEmbeddings (left ++ right) q) =
      Fintype.card (BlockOrderEmbeddings left q) *
        Fintype.card (BlockOrderEmbeddings right q) := by
  rw [card_order_embeddings, card_order_embeddings,
    card_order_embeddings]
  simp [List.map_append, List.prod_append]

/-- The polynomial attached to a block list evaluates to its realization count. -/
lemma nat_choose_card
    (indices : List ℕ)
    (q : ℕ) :
    (natChooseProduct indices).eval (q : ℚ) =
      Fintype.card (BlockOrderEmbeddings indices q) := by
  rw [nat_choose_product, card_order_embeddings]
  norm_num [Function.comp_def]

namespace PBRecipe

/-- A recipe evaluates to the signed realization count of its block history. -/
lemma eval_card_embeddings
    {inputWeight : ℕ}
    (recipe : PBRecipe inputWeight)
    (q : ℕ) :
    recipe.eval q =
      Fintype.card (BlockOrderEmbeddings recipe.indices q) := by
  rw [card_order_embeddings]
  norm_num [eval, Function.comp_def]

/--
Recipe composition multiplies realization counts because appended histories
make their block selections independently.
-/
lemma order_embeddings_append
    {inputWeight : ℕ}
    (left right : PBRecipe inputWeight)
    (q : ℕ) :
    Fintype.card (BlockOrderEmbeddings (left.append right).indices q) =
      Fintype.card (BlockOrderEmbeddings left.indices q) *
        Fintype.card (BlockOrderEmbeddings right.indices q) := by
  exact card_embeddings_append left.indices right.indices q

end PBRecipe

end TCTex
end Towers
