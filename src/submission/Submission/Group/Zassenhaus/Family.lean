import Submission.Group.Zassenhaus.FamilyOperationalEndpoint

-- Merged from FamilyShapeBlockEndpoint.lean

/-!
# Same-shape block endpoints for the operational family collector

More3 collection is organized by erased Hall shape.  A maximal same-shape
block may contain several counted families in an interleaved concrete order;
requiring a consecutive sublist for every individual family is stronger than
the polynomial consumer needs.

The correct endpoint invariant is block-local exact realization-slot coverage:
inside every maximal same-shape block, each slot of each represented family
occurs exactly once.  This file proves that such blocks compress to canonical
block-family recipes and that a collected output satisfying the invariant
yields the desired factor expansion.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace SBEnd

open scoped commutatorElement
open HACoeff
open HOCollec
open PPColl
open PPColl.RCColl.RPAggreg

/-- Canonical represented families of every same-shape block, in block order. -/
noncomputable def shapeBlockFamilies
    {M N K : ℕ}
    (blocks : List (List (DFTerm M N K))) :
    List (BFam M N) :=
  blocks.flatMap distinctBlockFamilies

/-- Concrete words of a same-shape decorated block have that collapsed shape. -/
lemma same_collapsed_decorated
    {M N K : ℕ}
    {block : List (DFTerm M N K)}
    {word : CWord HPAtom}
    (hsame : ∀ T ∈ block, T.erasedShape = word) :
    HACoeff.SCShape word
      (decoratedFamilyList block) := by
  intro labelled hlabelled
  rcases List.mem_map.mp hlabelled with ⟨T, hT, rfl⟩
  exact hsame T hT

/--
The canonical realization lists of all families represented in a same-shape
block also have that collapsed shape.
-/
lemma same_distinct_families
    {M N K : ℕ}
    (block : List (DFTerm M N K))
    (word : CWord HPAtom)
    (hsame : ∀ T ∈ block, T.erasedShape = word) :
    HACoeff.SCShape word
      (BFam.realizationList (distinctBlockFamilies block)) := by
  intro labelled hlabelled
  rw [BFam.realizationList] at hlabelled
  rcases List.mem_flatMap.mp hlabelled with ⟨F, hF, hlabelled⟩
  rw [F.collapse_word labelled hlabelled,
    recipe_distinct_families block word hsame F hF]

/--
One same-shape block with exact realization-token coverage has the same
collapsed evaluation as its canonical represented family lists.
-/
lemma collapsed_distinct_families
    {M N K : ℕ}
    (block : List (DFTerm M N K))
    (word : CWord HPAtom)
    (hsame : ∀ T ∈ block, T.erasedShape = word)
    (hindexed : RealizationIndexedBlock block) :
    collapsedListEval
        (BFam.realizationList (distinctBlockFamilies block)) =
      collapsedListEval (decoratedFamilyList block) := by
  rw [collapsed_length_same
      (same_distinct_families
        block word hsame),
    collapsed_length_same
      (same_collapsed_decorated hsame)]
  rw [realization_distinct_counted
    block (counted_realization_indexed block hindexed)]
  simp [decoratedFamilyList]

/--
Compress a finite ordered list of same-shape blocks whose token inventories
are all complete.
-/
lemma collapsed_block_families
    {M N K : ℕ}
    (blocks : List (List (DFTerm M N K)))
    (hsame :
      ∀ block ∈ blocks, SameErasedBlock block)
    (hindexed :
      ∀ block ∈ blocks, RealizationIndexedBlock block) :
    collapsedListEval
        (BFam.realizationList (shapeBlockFamilies blocks)) =
      collapsedListEval (decoratedFamilyList blocks.flatten) := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      rcases hsame block (by simp) with ⟨word, hword⟩
      have hblock :=
        collapsed_distinct_families
          block word hword (hindexed block (by simp))
      have htail :=
        ih
          (fun next hnext => hsame next (by simp [hnext]))
          (fun next hnext => hindexed next (by simp [hnext]))
      rw [show
          shapeBlockFamilies (block :: blocks) =
            distinctBlockFamilies block ++ shapeBlockFamilies blocks by
          rfl]
      rw [show
          BFam.realizationList
              (distinctBlockFamilies block ++ shapeBlockFamilies blocks) =
            BFam.realizationList (distinctBlockFamilies block) ++
              BFam.realizationList (shapeBlockFamilies blocks) by
          simp [BFam.realizationList, List.flatMap_append]]
      rw [show
          decoratedFamilyList (block :: blocks).flatten =
            decoratedFamilyList block ++
              decoratedFamilyList blocks.flatten by
          simp [decoratedFamilyList]]
      rw [BRecipe.collapsed_eval_append,
        BRecipe.collapsed_eval_append, hblock, htail]

/--
Operational More3 output together with exact token coverage in every maximal
same-shape block.
-/
structure SREnd
    (M N : ℕ) where
  collected :
    ODTerms M N
  realizationIndexed :
    ∀ block ∈ sameErasedBlocks collected.factors,
      RealizationIndexedBlock block

namespace SREnd

/-- Canonical block families retained by the shape-block endpoint. -/
noncomputable def families
    {M N : ℕ}
    (E : SREnd M N) :
    List (BFam M N) :=
  shapeBlockFamilies (sameErasedBlocks E.collected.factors)

/-- Compress a block-local exact-slot endpoint to canonical block families. -/
noncomputable def blockExpansion
    {M N : ℕ}
    (E : SREnd M N) :
    BFam.Expansion M N where
  families := E.families
  collapsed_eval_eq := by
    calc
      collapsedListEval (BFam.realizationList E.families) =
          collapsedListEval
            (decoratedFamilyList
              (sameErasedBlocks E.collected.factors).flatten) := by
        exact collapsed_block_families
          (sameErasedBlocks E.collected.factors)
          (same_erased_blocks
            E.collected.factors)
          E.realizationIndexed
      _ = collapsedListEval
            (decoratedFamilyList E.collected.factors) := by
        rw [flatten_same_blocks]
      _ = collapseHom M N
            (labelledListEval
              (decoratedFamilyList E.collected.factors)) :=
        (collapse_labelled_eval _).symm
      _ = collapseHom M N
            (DFTerm.listEval E.collected.factors) := by
        rw [labelled_decorated_family]
      _ = collapseHom M N ⁅labelledLeft M N, labelledRight M N⁆ := by
        rw [E.collected.eval_eq]
      _ = ⁅universalLeft ^ M, universalRight ^ N⁆ := by
        rw [map_commutatorElement, collapse_labelled_left,
          collapse_labelled_right]

/-- Polynomial-ready factors of the compressed shape-block endpoint. -/
noncomputable def factors
    {M N : ℕ}
    (E : SREnd M N) :
    List (Factor M N) :=
  E.blockExpansion.factors

/-- The compressed factors evaluate to the universal power commutator. -/
lemma listEval_factors
    {M N : ℕ}
    (E : SREnd M N) :
    listEval universalLeft universalRight E.factors =
      ⁅universalLeft ^ M, universalRight ^ N⁆ :=
  E.blockExpansion.listEval_factors

end SREnd

/--
Correct remaining propagation law: every maximal same-shape block in every
terminating operational More3 output has complete exact realization slots.
-/
structure SCKern : Prop where
  realizationIndexed :
    ∀ {M N : ℕ}
      (collected : ODTerms M N)
      (block : List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)),
      block ∈ sameErasedBlocks collected.factors →
        RealizationIndexedBlock block

namespace SCKern

/-- Resolve one operational output from the block-local propagation law. -/
def endpoint
    (kernel : SCKern)
    {M N : ℕ}
    (collected : ODTerms M N) :
    SREnd M N where
  collected := collected
  realizationIndexed := kernel.realizationIndexed collected

/-- Resolve the canonical block-family expansion from stable collection. -/
noncomputable def expansion
    (kernel : SCKern)
    (M N : ℕ) :
    BFam.Expansion M N :=
  let collected :=
    Classical.choice
      (nonempty_decorated_terms M N)
  (kernel.endpoint collected).blockExpansion

end SCKern

end SBEnd
end TCTex
end Submission

-- Merged from FamilySlotInventories.lean

/-!
# Unordered multi-family realization-slot inventories

A maximal More3 shape block may interleave terms from several counted block
families.  Compression needs exact slot coverage, not consecutive singleton
packets.  This file generalizes `RPFor` to an unordered finite
inventory of represented families and proves the closure operations used when
packet fragments are merged into one same-shape block.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace HSInvent

open HACoeff
open HSPacket
open BRSpec

/-- Exact realization slots of several represented families in arbitrary order. -/
def RIFor
    {M N K : ℕ}
    (families : List (BFam M N))
    (terms : List (DFTerm M N K)) :
    Prop :=
  List.Perm
    (BFam.realizationTokenList families)
    (terms.map DFTerm.realizationToken)

@[simp]
lemma BFam.realization_token_listappend
    {M N : ℕ}
    (left right : List (BFam M N)) :
    BFam.realizationTokenList (left ++ right) =
      BFam.realizationTokenList left ++
        BFam.realizationTokenList right := by
  simp [BFam.realizationTokenList, List.sigma, List.flatMap_append]

/-- Cartesian correction families generated by two represented family lists. -/
def BFam.correctionGrid
    {M N : ℕ}
    (left right : List (BFam M N)) :
    List (BFam M N) :=
  left.flatMap fun B =>
    right.map fun A => B.correction A

@[simp]
lemma BFam.mem_correctionGrid
    {M N : ℕ}
    {left right : List (BFam M N)}
    {C : BFam M N} :
    C ∈ BFam.correctionGrid left right ↔
      ∃ B ∈ left, ∃ A ∈ right, C = B.correction A := by
  simp [BFam.correctionGrid, eq_comm]

/-- Every family in a Cartesian correction grid has pairwise parent provenance. -/
lemma BFam.exists_parentsmem_corrgrid
    {M N : ℕ}
    {left right : List (BFam M N)}
    {C : BFam M N}
    (hC : C ∈ BFam.correctionGrid left right) :
    ∃ B ∈ left, ∃ A ∈ right, C = B.correction A :=
  BFam.mem_correctionGrid.mp hC

/-- Every family in a correction grid has the sum of its parent weights. -/
lemma BFam.weight_weigh_memco
    {M N leftWeight rightWeight : ℕ}
    {left right : List (BFam M N)}
    {C : BFam M N}
    (hC : C ∈ BFam.correctionGrid left right) :
    ∃ B ∈ left, ∃ A ∈ right,
      weightedWordWeight leftWeight rightWeight C.recipe =
        weightedWordWeight leftWeight rightWeight B.recipe +
          weightedWordWeight leftWeight rightWeight A.recipe := by
  rcases BFam.mem_correctionGrid.mp hC with
    ⟨B, hB, A, hA, rfl⟩
  refine ⟨B, hB, A, hA, ?_⟩
  rw [BFam.recipe_correction, weighted_weight_correction]

/-- Every generated correction family lies strictly above its left parent. -/
lemma BFam.weight_weigh_memca
    {M N leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {left right : List (BFam M N)}
    {C : BFam M N}
    (hC : C ∈ BFam.correctionGrid left right) :
    ∃ B ∈ left,
      weightedWordWeight leftWeight rightWeight B.recipe <
        weightedWordWeight leftWeight rightWeight C.recipe := by
  rcases BFam.mem_correctionGrid.mp hC with
    ⟨B, hB, A, _hA, rfl⟩
  exact ⟨B, hB, by
    rw [BFam.recipe_correction]
    exact weighted_correction_left
      hleftWeight hrightWeight B.recipe A.recipe⟩

/-- Every generated correction family lies strictly above its right parent. -/
lemma BFam.weight_weigh_memcb
    {M N leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {left right : List (BFam M N)}
    {C : BFam M N}
    (hC : C ∈ BFam.correctionGrid left right) :
    ∃ A ∈ right,
      weightedWordWeight leftWeight rightWeight A.recipe <
        weightedWordWeight leftWeight rightWeight C.recipe := by
  rcases BFam.mem_correctionGrid.mp hC with
    ⟨B, _hB, A, hA, rfl⟩
  exact ⟨A, hA, by
    rw [BFam.recipe_correction]
    exact weighted_correction_right
      hleftWeight hrightWeight B.recipe A.recipe⟩

/--
If each parent inventory has one erased shape, every generated correction
family has the corresponding commutator shape.
-/
lemma BFam.recipeshape_eqmem_corrgrid
    {M N : ℕ}
    {left right : List (BFam M N)}
    {leftShape rightShape : CWord HPAtom}
    (hleft :
      ∀ B ∈ left, B.recipe.erasedShape = leftShape)
    (hright :
      ∀ A ∈ right, A.recipe.erasedShape = rightShape)
    {C : BFam M N}
    (hC : C ∈ BFam.correctionGrid left right) :
    C.recipe.erasedShape =
      CWord.commutator leftShape rightShape := by
  rcases BFam.mem_correctionGrid.mp hC with
    ⟨B, hB, A, hA, rfl⟩
  rw [BFam.recipe_correction, BRecipe.erasedShape_corr,
    hleft B hB, hright A hA]

/-- Reorder two nested finite Cartesian traversals. -/
lemma List.flat_map_swapperm
    {α β γ : Type*}
    (left : List α)
    (right : List β)
    (f : α → β → List γ) :
    List.Perm
      (left.flatMap fun a => right.flatMap fun b => f a b)
      (right.flatMap fun b => left.flatMap fun a => f a b) := by
  induction left with
  | nil =>
      simp
  | cons a left ih =>
      simp only [List.flatMap_cons]
      exact
        (List.Perm.append_left (right.flatMap (f a)) ih).trans
          (List.flatMap_append_perm right (f a)
            (fun b => left.flatMap fun a => f a b))

/--
Exact tokens of one family-correction row are the Cartesian corrections of
the left family slots with every right-family slot.
-/
lemma BFam.realizatoken_listcorr_rowperm
    {M N : ℕ}
    (B : BFam M N)
    (right : List (BFam M N)) :
    List.Perm
      (BFam.realizationTokenList
        (right.map fun A => B.correction A))
      ((BFam.realizationTokenList [B]).flatMap fun b =>
        (BFam.realizationTokenList right).map
          (BFam.RToken.correction b)) := by
  rw [show
      BFam.realizationTokenList
          (right.map fun A => B.correction A) =
        (right.flatMap fun A =>
          BFam.realizationTokenList [B.correction A]) by
    simp [BFam.realizationTokenList, List.sigma,
      List.flatMap_map]]
  apply
    (List.Perm.flatMap_left right fun A _hA =>
      BFam.realizatoken_listsingleton_corrperm B A).trans
  apply
    (List.flat_map_swapperm right
      (BFam.realizationTokenList [B])
      (fun A b =>
        (BFam.realizationTokenList [A]).map
          (BFam.RToken.correction b))).trans
  simp [BFam.realizationTokenList, List.sigma,
    List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def]

/--
Exact tokens of a multi-family correction grid are the Cartesian pairwise
corrections of all parent inventory tokens.
-/
lemma BFam.realizatoken_listcorr_gridperm
    {M N : ℕ}
    (left right : List (BFam M N)) :
    List.Perm
      (BFam.realizationTokenList
        (BFam.correctionGrid left right))
      ((BFam.realizationTokenList left).flatMap fun b =>
        (BFam.realizationTokenList right).map
          (BFam.RToken.correction b)) := by
  rw [show
      BFam.realizationTokenList
          (BFam.correctionGrid left right) =
        (left.flatMap fun B =>
          BFam.realizationTokenList
            (right.map fun A => B.correction A)) by
    simp [BFam.correctionGrid,
      BFam.realizationTokenList, List.sigma,
      List.flatMap_map, List.flatMap_assoc]]
  apply
    (List.Perm.flatMap_left left fun B _hB =>
      BFam.realizatoken_listcorr_rowperm B right).trans
  simp [BFam.realizationTokenList, List.sigma,
    List.flatMap_assoc]

namespace RIFor

/-- A singleton-family inventory is exactly an exact realization packet. -/
lemma singleton_iff
    {M N K : ℕ}
    {F : BFam M N}
    {terms : List (DFTerm M N K)} :
    RIFor [F] terms ↔
      RPFor F terms :=
  Iff.rfl

/-- The empty term list carries the empty family inventory. -/
lemma nil
    {M N K : ℕ} :
    RIFor
      ([] : List (BFam M N))
      ([] : List (DFTerm M N K)) := by
  simp [RIFor, BFam.realizationTokenList]

/-- Concatenate two exact inventories. -/
lemma append
    {M N K : ℕ}
    {leftFamilies rightFamilies : List (BFam M N)}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (hleft : RIFor leftFamilies leftTerms)
    (hright : RIFor rightFamilies rightTerms) :
    RIFor
      (leftFamilies ++ rightFamilies)
      (leftTerms ++ rightTerms) := by
  simpa [RIFor, List.map_append] using
    List.Perm.append hleft hright

/-- Reorder represented families without changing the concrete inventory. -/
lemma perm_families
    {M N K : ℕ}
    {families families' : List (BFam M N)}
    {terms : List (DFTerm M N K)}
    (hinventory : RIFor families terms)
    (hfamilies : List.Perm families' families) :
    RIFor families' terms := by
  apply (show
      List.Perm
        (BFam.realizationTokenList families')
        (BFam.realizationTokenList families) by
    simpa [BFam.realizationTokenList, List.sigma] using
      hfamilies.flatMap_right fun F =>
        (List.finRange F.realizations.length).map (Sigma.mk F)).trans
  exact hinventory

/-- Reorder concrete terms without changing their represented slot inventory. -/
lemma perm_terms
    {M N K : ℕ}
    {families : List (BFam M N)}
    {terms terms' : List (DFTerm M N K)}
    (hinventory : RIFor families terms)
    (hterms : List.Perm terms terms') :
    RIFor families terms' := by
  exact hinventory.trans
    (hterms.map DFTerm.realizationToken)

/-- Every complete singleton packet is a singleton multi-family inventory. -/
lemma ofPacket
    {M N K : ℕ}
    {F : BFam M N}
    {terms : List (DFTerm M N K)}
    (hpacket : RPFor F terms) :
    RIFor [F] terms :=
  hpacket

/-- Pairwise correction of two packets supplies one exact correction inventory. -/
lemma correctionGrid
    {M N K : ℕ}
    {B A : BFam M N}
    {left right : List (DFTerm M N K)}
    (hleft : RPFor B left)
    (hright : RPFor A right) :
    RIFor [B.correction A]
      (DFTerm.correctionGrid left right) :=
  hleft.correctionGrid hright

/--
Cartesian correction of two unordered multi-family inventories again yields
an exact unordered inventory for the Cartesian grid of correction families.
-/
lemma correctionGrid_inventory
    {M N K : ℕ}
    {leftFamilies rightFamilies : List (BFam M N)}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (hleft : RIFor leftFamilies leftTerms)
    (hright : RIFor rightFamilies rightTerms) :
    RIFor
      (BFam.correctionGrid leftFamilies rightFamilies)
      (DFTerm.correctionGrid leftTerms rightTerms) := by
  apply
    (BFam.realizatoken_listcorr_gridperm
      leftFamilies rightFamilies).trans
  rw [DFTerm.realization_token_grid]
  exact hleft.flatMap fun b _hb =>
    hright.map (BFam.RToken.correction b)

/--
An inventory whose family list is a permutation of the represented distinct
families is exactly the block-local realization-indexed invariant.
-/
lemma realization_distinct_families
    {M N K : ℕ}
    {families : List (BFam M N)}
    {terms : List (DFTerm M N K)}
    (hinventory : RIFor families terms)
    (hfamilies :
      List.Perm (distinctBlockFamilies terms) families) :
    RealizationIndexedBlock terms := by
  exact hinventory.perm_families hfamilies

/--
Under a complete inventory, represented distinct-family membership is exactly
membership in the inventory family list, provided empty families are omitted.
-/
lemma distinct_block_families
    {M N K : ℕ}
    {families : List (BFam M N)}
    {terms : List (DFTerm M N K)}
    (hinventory : RIFor families terms)
    (hnonempty :
      ∀ F ∈ families, F.realizations ≠ [])
    (F : BFam M N) :
    F ∈ distinctBlockFamilies terms ↔ F ∈ families := by
  constructor
  · intro hF
    rcases HACoeff.distinct_block_families.mp hF with
      ⟨T, hT, rfl⟩
    have htokenActual :
        T.realizationToken ∈
          terms.map DFTerm.realizationToken :=
      List.mem_map.mpr ⟨T, hT, rfl⟩
    have htokenCanonical :=
      hinventory.symm.subset htokenActual
    exact (List.mem_sigma.mp htokenCanonical).1
  · intro hF
    let index : Fin F.realizations.length :=
      ⟨0, List.length_pos_of_ne_nil (hnonempty F hF)⟩
    have htokenCanonical :
        (⟨F, index⟩ : BFam.RToken M N) ∈
          BFam.realizationTokenList families :=
      List.mem_sigma.mpr ⟨hF, List.mem_finRange index⟩
    have htokenActual :=
      hinventory.subset htokenCanonical
    rcases List.mem_map.mp htokenActual with ⟨T, hT, htoken⟩
    exact
      HACoeff.distinct_block_families.mpr
        ⟨T, hT, congrArg Sigma.fst htoken⟩

/--
A duplicate-free, nonempty represented-family inventory is precisely a
realization-indexed shape block.
-/
lemma realizationIndexedBlock
    {M N K : ℕ}
    {families : List (BFam M N)}
    {terms : List (DFTerm M N K)}
    (hinventory : RIFor families terms)
    (hnodup : families.Nodup)
    (hnonempty :
      ∀ F ∈ families, F.realizations ≠ []) :
    RealizationIndexedBlock terms := by
  apply hinventory.realization_distinct_families
  apply (List.perm_ext_iff_of_nodup
    (distinct_families_nodup terms) hnodup).2
  intro F
  exact hinventory.distinct_block_families hnonempty F

/-- The block-local invariant is the canonical represented-family inventory. -/
lemma realization_indexed
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (hindexed : RealizationIndexedBlock terms) :
    RIFor (distinctBlockFamilies terms) terms :=
  hindexed

end RIFor

end HSInvent
end TCTex
end Submission

-- Merged from FamilySlotInventoryNormalization.lean

/-!
# Normalizing unordered realization-slot inventories

The operational family collector emits same-shape correction slots in an
order chosen by adjacent rewrites.  `RIFor` deliberately
forgets that order.  This file proves the normalization step needed by the
shape-block endpoint: an exact inventory of distinct nonempty families is the
canonical `RealizationIndexedBlock` inventory of its concrete terms.

It also applies that normalization to Cartesian correction grids.  The only
remaining local side condition is duplicate-freeness of the represented
correction-family grid.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace SINorm

open HACoeff
open HSPacket
open HSInvent

/-- Every family represented by a concrete block has a nonempty realization list. -/
lemma realizations_distinct_families
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    {F : BFam M N}
    (hF : F ∈ distinctBlockFamilies terms) :
    F.realizations ≠ [] := by
  rcases distinct_block_families.mp hF with ⟨T, _hT, rfl⟩
  exact List.ne_nil_of_mem T.word_mem

/-- Pairwise correction of two nonempty families again has realizations. -/
lemma BFam.realizations_ne_nilcorr
    {M N : ℕ}
    (B A : BFam M N)
    (hB : B.realizations ≠ [])
    (hA : A.realizations ≠ []) :
    (B.correction A).realizations ≠ [] := by
  rw [List.ne_nil_iff_length_pos] at hB hA ⊢
  simpa [BFam.correction, List.length_flatMap] using
    Nat.mul_pos hB hA

/-- Every family in a nonempty Cartesian correction grid has realizations. -/
lemma BFam.realizationsne_nilmem_corrgrid
    {M N : ℕ}
    {leftFamilies rightFamilies : List (BFam M N)}
    (hleft : ∀ B ∈ leftFamilies, B.realizations ≠ [])
    (hright : ∀ A ∈ rightFamilies, A.realizations ≠ [])
    {F : BFam M N}
    (hF : F ∈ BFam.correctionGrid leftFamilies rightFamilies) :
    F.realizations ≠ [] := by
  rcases List.mem_flatMap.mp hF with ⟨B, hB, hF⟩
  rcases List.mem_map.mp hF with ⟨A, hA, rfl⟩
  exact BFam.realizations_ne_nilcorr
    B A (hleft B hB) (hright A hA)

/--
Cartesian correction of exact inventories is a canonical indexed block when
its represented correction-family grid has no duplicate families.
-/
lemma realization_indexed_inventories
    {M N K : ℕ}
    {leftFamilies rightFamilies : List (BFam M N)}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (hleft : RIFor leftFamilies leftTerms)
    (hright : RIFor rightFamilies rightTerms)
    (hleftNonempty : ∀ B ∈ leftFamilies, B.realizations ≠ [])
    (hrightNonempty : ∀ A ∈ rightFamilies, A.realizations ≠ [])
    (hnodup :
      (BFam.correctionGrid leftFamilies rightFamilies).Nodup) :
    RealizationIndexedBlock
      (DFTerm.correctionGrid leftTerms rightTerms) := by
  apply RIFor.realizationIndexedBlock
    (HSInvent.RIFor.correctionGrid_inventory
      hleft hright) hnodup
  exact fun _F hF =>
    BFam.realizationsne_nilmem_corrgrid
      hleftNonempty hrightNonempty hF

/--
Canonical indexed parent blocks close under Cartesian correction once the
finite correction-family grid is duplicate-free.
-/
lemma realization_indexed_grid
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (hleft : RealizationIndexedBlock leftTerms)
    (hright : RealizationIndexedBlock rightTerms)
    (hnodup :
      (BFam.correctionGrid
        (distinctBlockFamilies leftTerms)
        (distinctBlockFamilies rightTerms)).Nodup) :
    RealizationIndexedBlock
      (DFTerm.correctionGrid leftTerms rightTerms) := by
  apply realization_indexed_inventories
    (RIFor.realization_indexed hleft)
    (RIFor.realization_indexed hright)
  · exact fun _F hF => realizations_distinct_families hF
  · exact fun _F hF => realizations_distinct_families hF
  · exact hnodup

end SINorm
end TCTex
end Submission

-- Merged from FamilySlotInventoryDistinctness.lean

/-!
# Distinct correction-family inventories

Normalizing a Cartesian correction inventory requires its represented family
grid to contain no duplicate families.  Equality of proof-carrying
`BFam` values is deliberately left abstract here.  This file isolates
the exact injectivity criterion needed by the operational collector and proves
that it implies duplicate-free grids and indexed correction closure.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace SIDistin

open HACoeff
open HSPacket
open HSInvent
open SINorm

/--
Pairwise family correction is injective on two finite represented-family
lists.  The hypothesis is intentionally local to the inventories in use.
-/
def BFam.CorrectionInjectiveOn
    {M N : ℕ}
    (left right : List (BFam M N)) :
    Prop :=
  ∀ ⦃B B' : BFam M N⦄,
    B ∈ left →
      B' ∈ left →
        ∀ ⦃A A' : BFam M N⦄,
          A ∈ right →
            A' ∈ right →
              B.correction A = B'.correction A' →
                B = B' ∧ A = A'

/--
Injective pairwise family correction sends duplicate-free parent lists to a
duplicate-free Cartesian correction grid.
-/
lemma BFam.correctionGrid_nodup
    {M N : ℕ}
    {left right : List (BFam M N)}
    (hleft : left.Nodup)
    (hright : right.Nodup)
    (hinjective : BFam.CorrectionInjectiveOn left right) :
    (BFam.correctionGrid left right).Nodup := by
  rw [BFam.correctionGrid, List.nodup_flatMap]
  constructor
  · intro B hB
    exact hright.map_on fun A hA A' hA' hcorrection =>
      (hinjective hB hB hA hA' hcorrection).2
  · apply hleft.imp_of_mem
    intro B B' hB hB' hne
    change List.Disjoint
      (right.map fun A => B.correction A)
      (right.map fun A => B'.correction A)
    rw [List.disjoint_left]
    intro correction hcorrection hcorrection'
    rcases List.mem_map.mp hcorrection with ⟨A, hA, rfl⟩
    rcases List.mem_map.mp hcorrection' with ⟨A', hA', hEq⟩
    exact hne (hinjective hB hB' hA hA' hEq.symm).1

/--
Canonical indexed parent blocks therefore close under Cartesian correction
whenever family correction is injective on their represented families.
-/
lemma realization_indexed_injective
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (hleft : RealizationIndexedBlock leftTerms)
    (hright : RealizationIndexedBlock rightTerms)
    (hinjective :
      BFam.CorrectionInjectiveOn
        (distinctBlockFamilies leftTerms)
        (distinctBlockFamilies rightTerms)) :
    RealizationIndexedBlock
      (DFTerm.correctionGrid leftTerms rightTerms) := by
  apply realization_indexed_grid hleft hright
  exact BFam.correctionGrid_nodup
    (distinct_families_nodup leftTerms)
    (distinct_families_nodup rightTerms)
    hinjective

end SIDistin
end TCTex
end Submission

-- Merged from FamilySlotInventoryPropagation.lean

/-!
# Propagating exact realization-slot inventories

The term-level More3 collector emits corrections one concrete slot at a time.
Closed batches are easier to reason about: they carry an unordered exact slot
inventory, omit empty families, and do not repeat represented families.

This file packages that block-local invariant.  It is closed under reordering,
concatenation of disjoint family inventories, and Cartesian correction grids
whenever pairwise family correction is injective on the represented parent
lists.  It then turns a block-local operational propagation certificate into
the shape-block kernel consumed by the canonical recipe endpoint.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace SIPropaga

open HACoeff
open HOCollec
open SBEnd
open HSPacket
open HSInvent
open SINorm
open SIDistin
open RSCovera

namespace BFam

/-- Equal correction families have equal parent correction recipes. -/
lemma recipe_eq_eq
    {M N : ℕ}
    {B A B' A' : BFam M N}
    (hcorrection : B.correction A = B'.correction A') :
    B.recipe.correction A.recipe =
      B'.recipe.correction A'.recipe := by
  exact congrArg BFam.recipe hcorrection

/-- Equal correction families already force equality of both parent shapes. -/
lemma parent_shapes_correction
    {M N : ℕ}
    {B A B' A' : BFam M N}
    (hcorrection : B.correction A = B'.correction A') :
    B.recipe.erasedShape = B'.recipe.erasedShape ∧
      A.recipe.erasedShape = A'.recipe.erasedShape := by
  have hshape :=
    congrArg (fun F : BFam M N => F.recipe.erasedShape) hcorrection
  simp only [BFam.recipe_correction,
    BRecipe.erasedShape_corr] at hshape
  injection hshape with hleft hright
  exact ⟨hleft, hright⟩

end BFam

/--
One finite same-shape candidate block with an exact unordered inventory of
distinct nonempty realization families.
-/
structure EIBlock
    {M N K : ℕ}
    (terms : List (DFTerm M N K)) where
  families :
    List (BFam M N)
  inventory :
    RIFor families terms
  families_nodup :
    families.Nodup
  realizations_ne_nil :
    ∀ F ∈ families, F.realizations ≠ []

namespace EIBlock

/-- Exact inventory blocks normalize to the canonical block-local invariant. -/
lemma realizationIndexedBlock
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (block : EIBlock terms) :
    RealizationIndexedBlock terms :=
  block.inventory.realizationIndexedBlock
    block.families_nodup block.realizations_ne_nil

/-- A canonical realization-indexed block is already an exact inventory block. -/
noncomputable def realization_indexed
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (hindexed : RealizationIndexedBlock terms) :
    EIBlock terms where
  families := distinctBlockFamilies terms
  inventory := RIFor.realization_indexed hindexed
  families_nodup := distinct_families_nodup terms
  realizations_ne_nil := fun _F hF =>
    realizations_distinct_families hF

/-- The raw inverse More3 source starts as one exact finite inventory block. -/
noncomputable def inverseRaw
    (M N : ℕ) :
    EIBlock (inverseDecoratedTerms M N) :=
  realization_indexed
    (realization_indexed_decorated M N)

/-- A complete singleton realization packet is an exact inventory block. -/
def ofPacket
    {M N K : ℕ}
    {F : BFam M N}
    {terms : List (DFTerm M N K)}
    (hpacket : HSPacket.RPFor F terms)
    (hnonempty : F.realizations ≠ []) :
    EIBlock terms where
  families := [F]
  inventory := RIFor.ofPacket hpacket
  families_nodup := by simp
  realizations_ne_nil := by
    intro family hfamily
    rcases List.mem_singleton.mp hfamily with rfl
    exact hnonempty

/-- Reordering concrete terms preserves their exact unordered inventory. -/
def permTerms
    {M N K : ℕ}
    {terms terms' : List (DFTerm M N K)}
    (block : EIBlock terms)
    (hterms : List.Perm terms terms') :
    EIBlock terms' where
  families := block.families
  inventory := block.inventory.perm_terms hterms
  families_nodup := block.families_nodup
  realizations_ne_nil := block.realizations_ne_nil

/--
Concatenate two exact inventory blocks whose represented family lists are
disjoint.
-/
def append
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : EIBlock leftTerms)
    (right : EIBlock rightTerms)
    (hdisjoint : List.Disjoint left.families right.families) :
    EIBlock (leftTerms ++ rightTerms) where
  families := left.families ++ right.families
  inventory := left.inventory.append right.inventory
  families_nodup :=
    left.families_nodup.append right.families_nodup hdisjoint
  realizations_ne_nil := by
    intro F hF
    rcases List.mem_append.mp hF with hF | hF
    · exact left.realizations_ne_nil F hF
    · exact right.realizations_ne_nil F hF

/--
Cartesian correction of two exact blocks is exact once represented-family
correction is injective on the two finite parent lists.
-/
def correctionGrid
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : EIBlock leftTerms)
    (right : EIBlock rightTerms)
    (hinjective :
      BFam.CorrectionInjectiveOn left.families right.families) :
    EIBlock
      (DFTerm.correctionGrid leftTerms rightTerms) where
  families := BFam.correctionGrid left.families right.families
  inventory :=
    RIFor.correctionGrid_inventory
      left.inventory right.inventory
  families_nodup :=
    BFam.correctionGrid_nodup
      left.families_nodup right.families_nodup hinjective
  realizations_ne_nil := fun _F hF =>
    BFam.realizationsne_nilmem_corrgrid
      left.realizations_ne_nil right.realizations_ne_nil hF

/--
The correction-grid constructor immediately yields the canonical local
coverage invariant expected by shape-block compression.
-/
lemma realization_indexed_grid
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : EIBlock leftTerms)
    (right : EIBlock rightTerms)
    (hinjective :
      BFam.CorrectionInjectiveOn left.families right.families) :
    RealizationIndexedBlock
      (DFTerm.correctionGrid leftTerms rightTerms) :=
  (left.correctionGrid right hinjective).realizationIndexedBlock

end EIBlock

/--
Operational propagation law in its compositional form: each maximal
same-shape block emitted by More3 carries one exact finite inventory block.
-/
structure SEInv : Prop where
  exactInventory :
    ∀ {M N : ℕ}
      (collected : ODTerms M N)
      (block : List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)),
      block ∈ sameErasedBlocks collected.factors →
        Nonempty (EIBlock block)

namespace SEInv

/--
Exact finite inventory propagation resolves the shape-block packet closure
law consumed by the canonical recipe endpoint.
-/
def shapeClosureKernel
    (kernel : SEInv) :
    SCKern where
  realizationIndexed collected block hblock :=
    (Classical.choice
      (kernel.exactInventory collected block hblock)).realizationIndexedBlock

/--
Stable More3 collection plus compositional exact-inventory propagation yields
the canonical finite block-family expansion.
-/
noncomputable def expansion
    (kernel : SEInv)
    (M N : ℕ) :
    BFam.Expansion M N :=
  kernel.shapeClosureKernel.expansion M N

end SEInv

end SIPropaga
end TCTex
end Submission
