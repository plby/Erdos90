import Submission.Group.Zassenhaus.Family


/-!
# Inventory endpoints for operational product and inverse collection

The local exact-slot collector composes unordered family inventories.  The
polynomial endpoint only needs exact inventories inside maximal same-shape
blocks.  This file joins those two interfaces.

It records that the inverse raw trace is an exact inventory, forgets ordered
packet endpoints to inventories, and packages a compositional inventory
closure kernel whose normalization immediately resolves the shape-block
endpoint kernel.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace FIEnd

open HACoeff
open HSPacket
open HSInvent
open SIDistin
open SIPropaga
open HOCollec
open SBEnd
open RSCovera

namespace RIFor

/-- Ordered consecutive packet endpoints forget to unordered inventories. -/
lemma ofPacketedBy
    {M N K : ℕ}
    {families : List (BFam M N)}
    {terms : List (DFTerm M N K)}
    (hpacketed : RPBy families terms) :
    RIFor families terms := by
  induction hpacketed with
  | nil =>
      exact RIFor.nil
  | cons F families packet rest hpacket hrest ih =>
      simpa using (RIFor.ofPacket hpacket).append ih

end RIFor

/--
The inverse raw source trace is an exact inventory of its represented initial
families before operational collection begins.
-/
lemma realization_inventory_decorated
    (M N : ℕ) :
    RIFor
      (distinctBlockFamilies (inverseDecoratedTerms M N))
      (inverseDecoratedTerms M N) :=
  RIFor.realization_indexed
    (realization_indexed_decorated M N)

/--
Compositional endpoint kernel: every collected same-shape block can be
assembled as an exact unordered inventory, and its assembled family list
normalizes to the canonical represented distinct families.
-/
structure SIClos : Prop where
  inventory :
    ∀ {M N : ℕ}
      (collected : ODTerms M N)
      (block : List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)),
      block ∈ sameErasedBlocks collected.factors →
        ∃ families : List (BFam M N),
          RIFor families block ∧
            List.Perm (distinctBlockFamilies block) families

namespace SIClos

/--
Normalizing every block-local inventory resolves the exact shape-block
coverage law consumed by the polynomial endpoint.
-/
def shapeClosureKernel
    (kernel : SIClos) :
    SCKern where
  realizationIndexed collected block hblock := by
    rcases kernel.inventory collected block hblock with
      ⟨families, hinventory, hfamilies⟩
    exact
      hinventory.realization_distinct_families
        hfamilies

/--
The stable terminating collector and one compositional inventory kernel
produce the canonical block-family expansion.
-/
noncomputable def expansion
    (kernel : SIClos)
    (M N : ℕ) :
    BFam.Expansion M N :=
  kernel.shapeClosureKernel.expansion M N

end SIClos

end FIEnd
end TCTex
end Submission

/-!
# Multiplicity-preserving inventory shape endpoints

Exact realization-slot inventories do not need represented families to be
duplicate-free.  If two operational histories produce equal `BFam`
values, the endpoint may retain both copies: their multiplicity contributes
twice to the final polynomial coefficient.

This file compresses arbitrary unordered inventories one same-shape block at
a time.  Unlike the canonical `distinctBlockFamilies` endpoint, it never
deduplicates represented families.  Cartesian correction grids therefore
compose without any injectivity hypothesis on proof-carrying family values.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace ISEnd

open scoped commutatorElement
open HACoeff
open HOCollec
open HSInvent
open SINorm
open HSPacket
open PPColl
open PPColl.RCColl.RPAggreg

/--
The realization-token list and the concrete realization-word list of a finite
family inventory have the same length.
-/
lemma BFam.realizatoken_listlength_eqreallist
    {M N : ℕ}
    (families : List (BFam M N)) :
    (BFam.realizationTokenList families).length =
      (BFam.realizationList families).length := by
  induction families with
  | nil =>
      rfl
  | cons F families ih =>
      simp [BFam.realizationTokenList, BFam.realizationList,
        List.sigma, List.length_flatMap]

/--
An unordered realization inventory has exactly as many canonical realization
words as concrete decorated terms.
-/
lemma RIFor.realization_list_lengtheq
    {M N K : ℕ}
    {families : List (BFam M N)}
    {terms : List (DFTerm M N K)}
    (hinventory : RIFor families terms) :
    (BFam.realizationList families).length = terms.length := by
  calc
    (BFam.realizationList families).length =
        (BFam.realizationTokenList families).length :=
      (BFam.realizatoken_listlength_eqreallist families).symm
    _ = (terms.map DFTerm.realizationToken).length :=
      hinventory.length_eq
    _ = terms.length := by simp

/--
Every nonempty family retained by an exact same-shape inventory has the same
recipe shape as its concrete block.
-/
lemma RIFor.recipe_shape_eqmem
    {M N K : ℕ}
    {families : List (BFam M N)}
    {terms : List (DFTerm M N K)}
    {shape : CWord HPAtom}
    (hinventory : RIFor families terms)
    (hnonempty : ∀ F ∈ families, F.realizations ≠ [])
    (hterms : ∀ T ∈ terms, T.erasedShape = shape)
    {F : BFam M N}
    (hF : F ∈ families) :
    F.recipe.erasedShape = shape := by
  let index : Fin F.realizations.length :=
    ⟨0, List.length_pos_of_ne_nil (hnonempty F hF)⟩
  have htokenCanonical :
      (⟨F, index⟩ : BFam.RToken M N) ∈
        BFam.realizationTokenList families :=
    List.mem_sigma.mpr ⟨hF, List.mem_finRange index⟩
  have htokenActual := hinventory.subset htokenCanonical
  rcases List.mem_map.mp htokenActual with ⟨T, hT, htoken⟩
  have hfamily : T.family = F :=
    congrArg Sigma.fst htoken
  rw [← hfamily, ← T.erased_shape_family, hterms T hT]

/--
One multiplicity-preserving block: its concrete decorated terms and retained
family list share one erased Hall shape and carry exactly the same slots.
-/
structure ISBlock
    (M N K : ℕ) where
  shape :
    CWord HPAtom
  terms :
    List (DFTerm M N K)
  families :
    List (BFam M N)
  inventory :
    RIFor families terms
  terms_shape :
    ∀ T ∈ terms, T.erasedShape = shape
  families_shape :
    ∀ F ∈ families, F.recipe.erasedShape = shape

namespace ISBlock

/--
Build one multiplicity-preserving shape block from a nonempty exact inventory
and a common concrete erased shape.
-/
def ofInventory
    {M N K : ℕ}
    {shape : CWord HPAtom}
    {terms : List (DFTerm M N K)}
    {families : List (BFam M N)}
    (hinventory : RIFor families terms)
    (hnonempty : ∀ F ∈ families, F.realizations ≠ [])
    (hterms : ∀ T ∈ terms, T.erasedShape = shape) :
    ISBlock M N K where
  shape := shape
  terms := terms
  families := families
  inventory := hinventory
  terms_shape := hterms
  families_shape := fun _F hF =>
    RIFor.recipe_shape_eqmem
      hinventory hnonempty hterms hF

/-- Reordering concrete terms preserves one multiplicity-preserving block. -/
def permTerms
    {M N K : ℕ}
    (block : ISBlock M N K)
    {terms' : List (DFTerm M N K)}
    (hterms : List.Perm block.terms terms') :
    ISBlock M N K where
  shape := block.shape
  terms := terms'
  families := block.families
  inventory := block.inventory.perm_terms hterms
  terms_shape := by
    intro T hT
    exact block.terms_shape T (hterms.symm.subset hT)
  families_shape := block.families_shape

/-- Concatenate two inventory blocks carrying the same erased Hall shape. -/
def append
    {M N K : ℕ}
    (left right : ISBlock M N K)
    (hshape : right.shape = left.shape) :
    ISBlock M N K where
  shape := left.shape
  terms := left.terms ++ right.terms
  families := left.families ++ right.families
  inventory := left.inventory.append right.inventory
  terms_shape := by
    intro T hT
    rcases List.mem_append.mp hT with hT | hT
    · exact left.terms_shape T hT
    · rw [right.terms_shape T hT, hshape]
  families_shape := by
    intro F hF
    rcases List.mem_append.mp hF with hF | hF
    · exact left.families_shape F hF
    · rw [right.families_shape F hF, hshape]

/--
Cartesian correction of two inventory shape blocks is another exact block.
No family distinctness assumption is needed: equal correction histories retain
their multiplicity as repeated entries of the output family list.
-/
noncomputable def correctionGrid
    {M N K : ℕ}
    (left right : ISBlock M N K) :
    ISBlock M N K where
  shape := .commutator left.shape right.shape
  terms := DFTerm.correctionGrid left.terms right.terms
  families := BFam.correctionGrid left.families right.families
  inventory :=
    RIFor.correctionGrid_inventory
      left.inventory right.inventory
  terms_shape := by
    intro T hT
    rcases List.mem_flatMap.mp hT with ⟨B, hB, hT⟩
    rcases List.mem_map.mp hT with ⟨A, hA, rfl⟩
    change
      (DTerm.correction B.decorated A.decorated).erasedShape =
        .commutator left.shape right.shape
    rw [DTerm.erasedShape_corr]
    change B.erasedShape.commutator A.erasedShape =
      left.shape.commutator right.shape
    rw [left.terms_shape B hB, right.terms_shape A hA]
  families_shape := by
    intro F hF
    exact BFam.recipeshape_eqmem_corrgrid
      left.families_shape right.families_shape hF

/-- Canonical realization words retained by one inventory block share its shape. -/
lemma same_collapsed_realization
    {M N K : ℕ}
    (block : ISBlock M N K) :
    SCShape block.shape
      (BFam.realizationList block.families) := by
  intro word hword
  rw [BFam.realizationList] at hword
  rcases List.mem_flatMap.mp hword with ⟨F, hF, hword⟩
  rw [F.collapse_word word hword, block.families_shape F hF]

/-- Concrete decorated words retained by one inventory block share its shape. -/
lemma same_collapsed_decorated
    {M N K : ℕ}
    (block : ISBlock M N K) :
    SCShape block.shape (decoratedFamilyList block.terms) := by
  intro word hword
  rcases List.mem_map.mp hword with ⟨T, hT, rfl⟩
  exact block.terms_shape T hT

/--
One unordered multiplicity-preserving inventory block compresses to its
canonical family realization lists.
-/
lemma collapsed_realization
    {M N K : ℕ}
    (block : ISBlock M N K) :
    collapsedListEval (BFam.realizationList block.families) =
      collapsedListEval (decoratedFamilyList block.terms) := by
  rw [collapsed_length_same
      block.same_collapsed_realization,
    collapsed_length_same
      block.same_collapsed_decorated,
    RIFor.realization_list_lengtheq block.inventory]
  simp [decoratedFamilyList]

end ISBlock

/-- Ordered endpoint families retained by a finite list of inventory blocks. -/
def inventoriedShapeFamilies
    {M N K : ℕ}
    (blocks : List (ISBlock M N K)) :
    List (BFam M N) :=
  blocks.flatMap ISBlock.families

/-- Ordered concrete terms retained by a finite list of inventory blocks. -/
def inventoriedShapeTerms
    {M N K : ℕ}
    (blocks : List (ISBlock M N K)) :
    List (DFTerm M N K) :=
  blocks.flatMap ISBlock.terms

/--
Compress an ordered finite list of multiplicity-preserving inventory blocks.
-/
lemma collapsed_inventoried_families
    {M N K : ℕ}
    (blocks : List (ISBlock M N K)) :
    collapsedListEval
        (BFam.realizationList
          (inventoriedShapeFamilies blocks)) =
      collapsedListEval
        (decoratedFamilyList (inventoriedShapeTerms blocks)) := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      rw [show
          inventoriedShapeFamilies (block :: blocks) =
            block.families ++ inventoriedShapeFamilies blocks by
          rfl]
      rw [show
          BFam.realizationList
              (block.families ++ inventoriedShapeFamilies blocks) =
            BFam.realizationList block.families ++
              BFam.realizationList
                (inventoriedShapeFamilies blocks) by
          simp [BFam.realizationList, List.flatMap_append]]
      rw [show
          inventoriedShapeTerms (block :: blocks) =
            block.terms ++ inventoriedShapeTerms blocks by
          rfl]
      rw [show
          decoratedFamilyList
              (block.terms ++ inventoriedShapeTerms blocks) =
            decoratedFamilyList block.terms ++
              decoratedFamilyList (inventoriedShapeTerms blocks) by
          simp [decoratedFamilyList]]
      rw [BRecipe.collapsed_eval_append,
        BRecipe.collapsed_eval_append,
        block.collapsed_realization, ih]

/--
Operational More3 output decomposed into multiplicity-preserving exact
same-shape inventories.
-/
structure IREnd
    (M N : ℕ) where
  collected :
    ODTerms M N
  blocks :
    List (ISBlock M N
      (inverseLabelledCollection M N).factors.length)
  terms_eq :
    inventoriedShapeTerms blocks = collected.factors

namespace IREnd

/-- Ordered endpoint families, retaining every operational multiplicity. -/
def families
    {M N : ℕ}
    (endpoint : IREnd M N) :
    List (BFam M N) :=
  inventoriedShapeFamilies endpoint.blocks

/--
Compress a multiplicity-preserving inventory endpoint to canonical admissible
block-family factors.
-/
noncomputable def blockExpansion
    {M N : ℕ}
    (endpoint : IREnd M N) :
    BFam.Expansion M N where
  families := endpoint.families
  collapsed_eval_eq := by
    calc
      collapsedListEval (BFam.realizationList endpoint.families) =
          collapsedListEval
            (decoratedFamilyList
              (inventoriedShapeTerms endpoint.blocks)) :=
        collapsed_inventoried_families endpoint.blocks
      _ = collapsedListEval
            (decoratedFamilyList endpoint.collected.factors) := by
        rw [endpoint.terms_eq]
      _ = collapseHom M N
            (labelledListEval
              (decoratedFamilyList endpoint.collected.factors)) :=
        (collapse_labelled_eval _).symm
      _ = collapseHom M N
            (DFTerm.listEval endpoint.collected.factors) := by
        rw [labelled_decorated_family]
      _ = collapseHom M N ⁅labelledLeft M N, labelledRight M N⁆ := by
        rw [endpoint.collected.eval_eq]
      _ = ⁅universalLeft ^ M, universalRight ^ N⁆ := by
        rw [map_commutatorElement, collapse_labelled_left,
          collapse_labelled_right]

/-- Polynomial-ready factors retained by the inventory endpoint. -/
noncomputable def factors
    {M N : ℕ}
    (endpoint : IREnd M N) :
    List (Factor M N) :=
  endpoint.blockExpansion.factors

/-- Retained factors evaluate to the universal powered commutator. -/
lemma listEval_factors
    {M N : ℕ}
    (endpoint : IREnd M N) :
    listEval universalLeft universalRight endpoint.factors =
      ⁅universalLeft ^ M, universalRight ^ N⁆ :=
  endpoint.blockExpansion.listEval_factors

end IREnd

/--
Remaining multiplicity-preserving propagation law: every stable operational
More3 output can be partitioned into exact same-shape inventory blocks.
-/
structure ISClosa : Prop where
  endpoint :
    ∀ {M N : ℕ},
      ODTerms M N →
        Nonempty (IREnd M N)

namespace ISClosa

/--
Stable terminating More3 collection and multiplicity-preserving inventory
propagation produce the canonical finite block-family expansion.
-/
noncomputable def expansion
    (kernel : ISClosa)
    (M N : ℕ) :
    BFam.Expansion M N :=
  let collected :=
    Classical.choice
      (nonempty_decorated_terms M N)
  (Classical.choice (kernel.endpoint collected)).blockExpansion

end ISClosa

end ISEnd
end TCTex
end Submission

/-!
# More3 shape-block propagation without family deduplication

The stable More3 collector ends in maximal adjacent blocks of equal erased
Hall shape.  To compress such a block, it is enough to exhibit an exact
unordered realization inventory whose retained families are nonempty.
Repeated equal families are allowed and retain their coefficient
multiplicity.

This file packages that reduced propagation law and builds the
multiplicity-preserving recipe endpoint automa from the canonical
`sameErasedBlocks` partition.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace ISPropag

open HACoeff
open FIEnd
open ISEnd
open HOCollec
open SBEnd
open HSInvent
open SINorm

/--
Reduced global propagation law: every maximal same-shape block in every
stable operational output is an exact unordered inventory of nonempty
families.  No family distinctness or correction injectivity is required.
-/
structure SIPropag : Prop where
  inventory :
    ∀ {M N : ℕ}
      (collected : ODTerms M N)
      (block : List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)),
      block ∈ sameErasedBlocks collected.factors →
        ∃ families : List (BFam M N),
          RIFor families block ∧
            ∀ F ∈ families, F.realizations ≠ []

namespace SIPropag

/--
Turn one canonical maximal same-shape block into a multiplicity-preserving
inventory block.
-/
noncomputable def inventoriedBlock
    (kernel : SIPropag)
    {M N : ℕ}
    (collected : ODTerms M N)
    (block :
      { block : List (DFTerm M N
          (inverseLabelledCollection M N).factors.length) //
        block ∈ sameErasedBlocks collected.factors }) :
    ISBlock M N
      (inverseLabelledCollection M N).factors.length := by
  let hsame :=
    same_erased_blocks
      collected.factors block.1 block.2
  let shape := Classical.choose hsame
  let hterms := Classical.choose_spec hsame
  let hinventory := kernel.inventory collected block.1 block.2
  let families := Classical.choose hinventory
  let hinventorySpec := Classical.choose_spec hinventory
  exact ISBlock.ofInventory
    hinventorySpec.1 hinventorySpec.2 hterms

@[simp]
lemma inventoried_block_terms
    (kernel : SIPropag)
    {M N : ℕ}
    (collected : ODTerms M N)
    (block :
      { block : List (DFTerm M N
          (inverseLabelledCollection M N).factors.length) //
        block ∈ sameErasedBlocks collected.factors }) :
    (kernel.inventoriedBlock collected block).terms = block.1 := by
  simp [inventoriedBlock, ISBlock.ofInventory]

/-- Inventory blocks attached to the canonical maximal same-shape partition. -/
noncomputable def blocks
    (kernel : SIPropag)
    {M N : ℕ}
    (collected : ODTerms M N) :
    List (ISBlock M N
      (inverseLabelledCollection M N).factors.length) :=
  (sameErasedBlocks collected.factors).attach.map
    (kernel.inventoriedBlock collected)

/-- Forgetting attached inventory certificates recovers the collected terms. -/
lemma inventoried_terms_blocks
    (kernel : SIPropag)
    {M N : ℕ}
    (collected : ODTerms M N) :
    inventoriedShapeTerms (kernel.blocks collected) =
      collected.factors := by
  rw [← flatten_same_blocks collected.factors]
  rw [blocks, inventoriedShapeTerms, List.flatMap_map]
  simp only [inventoried_block_terms]
  change
    ((sameErasedBlocks collected.factors).attach.map Subtype.val).flatten =
      (sameErasedBlocks collected.factors).flatten
  rw [List.attach_map_subtype_val]

/-- Resolve one stable operational output to a multiplicity-preserving endpoint. -/
noncomputable def endpoint
    (kernel : SIPropag)
    {M N : ℕ}
    (collected : ODTerms M N) :
    IREnd M N where
  collected := collected
  blocks := kernel.blocks collected
  terms_eq := kernel.inventoried_terms_blocks collected

/-- Resolve the endpoint kernel consumed by multiplicity-preserving compression. -/
def inventoryShapeClosure
    (kernel : SIPropag) :
    ISClosa where
  endpoint collected :=
    ⟨kernel.endpoint collected⟩

/--
Stable terminating More3 collection plus reduced inventory propagation yields
the canonical finite block-family expansion.
-/
noncomputable def expansion
    (kernel : SIPropag)
    (M N : ℕ) :
    BFam.Expansion M N :=
  kernel.inventoryShapeClosure.expansion M N

end SIPropag

/--
The older canonical distinct-family inventory kernel implies the reduced
multiplicity-preserving propagation law.
-/
def canonicalInventoryClosure
    (kernel : SIClos) :
    SIPropag where
  inventory collected block hblock := by
    rcases kernel.inventory collected block hblock with
      ⟨families, hinventory, hfamilies⟩
    refine ⟨families, hinventory, ?_⟩
    intro F hF
    exact realizations_distinct_families
      (hfamilies.symm.subset hF)

/--
The older canonical realization-indexed closure kernel also implies the
reduced multiplicity-preserving propagation law.
-/
def canonicalPacketClosure
    (kernel : SCKern) :
    SIPropag where
  inventory collected block hblock := by
    let families := distinctBlockFamilies block
    refine ⟨families, ?_, ?_⟩
    · exact RIFor.realization_indexed
        (kernel.realizationIndexed collected block hblock)
    · intro F hF
      exact realizations_distinct_families hF

end ISPropag
end TCTex
end Submission

/-!
# Multiplicity-preserving family inventory propagation

Operational More3 collection may retain repeated equal `BFam` values.
The correct closed-batch invariant therefore remembers a list of families
with multiplicity, an exact unordered realization-slot inventory, and
nonemptiness of every retained family.

This invariant starts at the inverse raw source and is closed under concrete
term reordering, concatenation, and Cartesian correction grids.  In
particular, correction-grid closure has no family distinctness or injectivity
side condition.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace IMPropag

open HACoeff
open ISPropag
open ISEnd
open HOCollec
open HSInvent
open SINorm
open HSPacket
open RSCovera

/--
One finite concrete block carrying an exact unordered inventory of nonempty
families.  Repeated equal family entries retain multiplicity.
-/
structure MIBlock
    {M N K : ℕ}
    (terms : List (DFTerm M N K)) where
  families :
    List (BFam M N)
  inventory :
    RIFor families terms
  realizations_ne_nil :
    ∀ F ∈ families, F.realizations ≠ []

namespace MIBlock

/-- Every concrete term in a multiplicity block belongs to a retained family. -/
lemma family_mem
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (block : MIBlock terms)
    {T : DFTerm M N K}
    (hT : T ∈ terms) :
    T.family ∈ block.families := by
  have htokenActual :
      T.realizationToken ∈
        terms.map DFTerm.realizationToken :=
    List.mem_map.mpr ⟨T, hT, rfl⟩
  have htokenCanonical := block.inventory.symm.subset htokenActual
  exact (List.mem_sigma.mp htokenCanonical).1

/-- The empty concrete block carries the empty family inventory. -/
def nil
    {M N K : ℕ} :
    MIBlock
      ([] : List (DFTerm M N K)) where
  families := []
  inventory := RIFor.nil
  realizations_ne_nil := by simp

/-- Canonical indexed blocks forget to multiplicity-preserving inventories. -/
noncomputable def realization_indexed
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (hindexed : RealizationIndexedBlock terms) :
    MIBlock terms where
  families := distinctBlockFamilies terms
  inventory := RIFor.realization_indexed hindexed
  realizations_ne_nil := fun _F hF =>
    realizations_distinct_families hF

/-- The inverse raw More3 source starts with exact nonempty slot inventory. -/
noncomputable def inverseRaw
    (M N : ℕ) :
    MIBlock (inverseDecoratedTerms M N) :=
  realization_indexed
    (realization_indexed_decorated M N)

/-- A complete singleton realization packet is one multiplicity block. -/
def ofPacket
    {M N K : ℕ}
    {F : BFam M N}
    {terms : List (DFTerm M N K)}
    (hpacket : RPFor F terms)
    (hnonempty : F.realizations ≠ []) :
    MIBlock terms where
  families := [F]
  inventory := RIFor.ofPacket hpacket
  realizations_ne_nil := by
    intro family hfamily
    rcases List.mem_singleton.mp hfamily with rfl
    exact hnonempty

/-- Reordering concrete terms preserves multiplicity-preserving inventory. -/
def permTerms
    {M N K : ℕ}
    {terms terms' : List (DFTerm M N K)}
    (block : MIBlock terms)
    (hterms : List.Perm terms terms') :
    MIBlock terms' where
  families := block.families
  inventory := block.inventory.perm_terms hterms
  realizations_ne_nil := block.realizations_ne_nil

/-- Concatenate two exact inventories, retaining every family multiplicity. -/
def append
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : MIBlock leftTerms)
    (right : MIBlock rightTerms) :
    MIBlock (leftTerms ++ rightTerms) where
  families := left.families ++ right.families
  inventory := left.inventory.append right.inventory
  realizations_ne_nil := by
    intro F hF
    rcases List.mem_append.mp hF with hF | hF
    · exact left.realizations_ne_nil F hF
    · exact right.realizations_ne_nil F hF

/--
Cartesian correction of two exact multiplicity inventories is exact and
nonempty.  Equal correction families remain repeated list entries.
-/
noncomputable def correctionGrid
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : MIBlock leftTerms)
    (right : MIBlock rightTerms) :
    MIBlock
      (DFTerm.correctionGrid leftTerms rightTerms) where
  families := BFam.correctionGrid left.families right.families
  inventory :=
    RIFor.correctionGrid_inventory
      left.inventory right.inventory
  realizations_ne_nil := fun _F hF =>
    BFam.realizationsne_nilmem_corrgrid
      left.realizations_ne_nil right.realizations_ne_nil hF

/--
Attach one common erased shape to a multiplicity-preserving inventory block.
-/
def inventoriedShapeBlock
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    {shape : CWord HPAtom}
    (block : MIBlock terms)
    (hterms : ∀ T ∈ terms, T.erasedShape = shape) :
    ISBlock M N K :=
  ISBlock.ofInventory
    block.inventory block.realizations_ne_nil hterms

end MIBlock

/--
Primitive remaining propagation law: each canonical maximal More3 shape block
admits one multiplicity-preserving exact inventory.
-/
structure SMInv : Prop where
  inventory :
    ∀ {M N : ℕ}
      (collected : ODTerms M N)
      (block : List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)),
      block ∈ sameErasedBlocks collected.factors →
        Nonempty (MIBlock block)

namespace SMInv

/-- Forget block packaging and resolve the reduced shape-block inventory law. -/
def shapeInventoryPropagation
    (kernel : SMInv) :
    SIPropag where
  inventory collected block hblock := by
    let exact := Classical.choice (kernel.inventory collected block hblock)
    exact ⟨exact.families, exact.inventory, exact.realizations_ne_nil⟩

/--
Stable More3 collection plus primitive multiplicity propagation yields the
canonical finite block-family expansion.
-/
noncomputable def expansion
    (kernel : SMInv)
    (M N : ℕ) :
    BFam.Expansion M N :=
  kernel.shapeInventoryPropagation.expansion M N

end SMInv

end IMPropag
end TCTex
end Submission

/-!
# Filtering multiplicity-preserving family inventories

A closed operational endpoint first supplies one global realization-token
inventory.  Polynomial compression works shape block by shape block.  This
file provides the reusable bridge: restricting represented families and
concrete terms by any family predicate preserves exact token inventory.

Filtering by erased Hall shape is an immediate specialization.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace FIFilter

open HACoeff
open IMPropag
open ISEnd
open HSInvent

/-- Filtering families filters their exact realization tokens by family. -/
lemma BFam.realization_token_listfilter
    {M N : ℕ}
    (predicate : BFam M N → Prop)
    [DecidablePred predicate]
    (families : List (BFam M N)) :
    BFam.realizationTokenList (families.filter predicate) =
      (BFam.realizationTokenList families).filter
        fun token => predicate token.1 := by
  induction families with
  | nil =>
      rfl
  | cons family families ih =>
      have ih' :
          (families.filter predicate).sigma
              (fun F => List.finRange F.realizations.length) =
            (families.sigma
              (fun F => List.finRange F.realizations.length)).filter
                (fun token => predicate token.1) := by
        simpa [BFam.realizationTokenList] using ih
      by_cases hfamily : predicate family
      · have hfamily' : decide (predicate family) = true := by
          simp [hfamily]
        have hfilterCons :
            (family :: families).filter predicate =
              family :: families.filter predicate :=
          List.filter_cons_of_pos hfamily'
        rw [hfilterCons]
        simp only [BFam.realizationTokenList, List.sigma_cons,
          List.filter_append]
        rw [ih']
        congr 1
        symm
        apply List.filter_eq_self.2
        intro token htoken
        rcases List.mem_map.mp htoken with ⟨index, _hindex, rfl⟩
        simp [hfamily]
      · have hfamily' : ¬ decide (predicate family) = true := by
          simp [hfamily]
        have hfilterCons :
            (family :: families).filter predicate =
              families.filter predicate :=
          List.filter_cons_of_neg hfamily'
        rw [hfilterCons]
        simp only [BFam.realizationTokenList, List.sigma_cons,
          List.filter_append]
        rw [ih']
        have hfilter :
            (List.map
              (fun index =>
                (⟨family, index⟩ : BFam.RToken M N))
              (List.finRange family.realizations.length)).filter
                (fun token => predicate token.1) = [] := by
          simp [hfamily]
        rw [hfilter, List.nil_append]

/-- Filtering concrete terms by family commutes with realization-token projection. -/
lemma DFTerm.map_realizatoken_filterfam
    {M N K : ℕ}
    (predicate : BFam M N → Prop)
    [DecidablePred predicate]
    (terms : List (DFTerm M N K)) :
    (terms.filter fun T => predicate T.family).map
        DFTerm.realizationToken =
      (terms.map DFTerm.realizationToken).filter
        fun token => predicate token.1 := by
  induction terms with
  | nil =>
      rfl
  | cons term terms ih =>
      by_cases hterm : predicate term.family
      · simp [hterm, ih]
      · simp [hterm, ih]

namespace MIBlock

/--
Restrict one exact multiplicity inventory by an arbitrary predicate on its
represented family values.
-/
noncomputable def filterFamilies
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (block : MIBlock terms)
    (predicate : BFam M N → Prop)
    [DecidablePred predicate] :
    MIBlock
      (terms.filter fun T => predicate T.family) where
  families := block.families.filter predicate
  inventory := by
    rw [RIFor,
      BFam.realization_token_listfilter,
      DFTerm.map_realizatoken_filterfam]
    exact block.inventory.filter fun token => predicate token.1
  realizations_ne_nil := by
    intro family hfamily
    exact block.realizations_ne_nil family (List.mem_of_mem_filter hfamily)

/-- The retained represented families are exactly the family-filtered list. -/
@[simp]
lemma filterFamilies_families
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (block : MIBlock terms)
    (predicate : BFam M N → Prop)
    [DecidablePred predicate] :
    (filterFamilies block predicate).families =
      block.families.filter predicate :=
  rfl

/-- Restrict one exact inventory to a single erased Hall shape. -/
noncomputable def filterShape
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (block : MIBlock terms)
    (shape : CWord HPAtom) :
    MIBlock
      (terms.filter fun T => T.family.recipe.erasedShape = shape) :=
  filterFamilies block fun family => family.recipe.erasedShape = shape

/-- Every concrete term retained by shape filtering has the selected shape. -/
lemma filter_shape_terms
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (_block : MIBlock terms)
    (shape : CWord HPAtom) :
    ∀ T ∈ (terms.filter fun T => T.family.recipe.erasedShape = shape),
      T.erasedShape = shape := by
  intro T hT
  rw [T.erased_shape_family]
  simpa using (List.mem_filter.mp hT).2

/-- Every represented family retained by shape filtering has the selected shape. -/
lemma filter_shape_families
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (block : MIBlock terms)
    (shape : CWord HPAtom) :
    ∀ F ∈ (filterShape block shape).families,
      F.recipe.erasedShape = shape := by
  intro family hfamily
  have hfamily' :
      family ∈ block.families.filter
        (fun family => family.recipe.erasedShape = shape) :=
    hfamily
  simpa using (List.mem_filter.mp hfamily').2

/-- Shape filtering immediately supplies a polynomial-compressible shape block. -/
noncomputable def filterInventoriedBlock
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (block : MIBlock terms)
    (shape : CWord HPAtom) :
    ISBlock M N K :=
  (filterShape block shape).inventoriedShapeBlock
    (filter_shape_terms block shape)

end MIBlock

end FIFilter
end TCTex
end Submission

/-!
# Concrete witnesses for multiplicity-preserving family inventories

An exact nonempty realization-token inventory records represented families
with multiplicity.  Every listed family therefore has at least one concrete
decorated-family term carrying that family value.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace IMWitnes

open HACoeff
open IMPropag
open HSInvent

namespace MIBlock

/-- Every represented nonempty family has a concrete realization in the block. -/
lemma term_family
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (block : MIBlock terms)
    {family : BFam M N}
    (hfamily : family ∈ block.families) :
    ∃ term ∈ terms, term.family = family := by
  let index : Fin family.realizations.length :=
    ⟨0, List.length_pos_of_ne_nil
      (block.realizations_ne_nil family hfamily)⟩
  have htokenCanonical :
      (⟨family, index⟩ : BFam.RToken M N) ∈
        BFam.realizationTokenList block.families :=
    List.mem_sigma.mpr ⟨hfamily, List.mem_finRange index⟩
  have htokenActual := block.inventory.subset htokenCanonical
  rcases List.mem_map.mp htokenActual with ⟨term, hterm, htoken⟩
  exact ⟨term, hterm, congrArg Sigma.fst htoken⟩

end MIBlock

end IMWitnes
end TCTex
end Submission

/-!
# Multiplicity-preserving correction worklists

The singleton-family decorated ledger is useful for one closed packet, but a
maximal More3 shape block may interleave several families.  This file lifts
the same arithmetic to multiplicity-preserving parent inventories.

An open ledger remembers all Cartesian correction terms, permits actual More3
obstructions to consume them in arbitrary order, and closes to the exact
multiplicity inventory supplied by `MIBlock.correctionGrid`.
The only remaining global scheduler obligation is to show that the stable
More3 insertion trace encounters every opened pending slot.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace FIWork

open HACoeff
open BBSched
open BRSpec
open IMPropag
open HSInvent
open HSPacket

/--
Permutation-aware open Cartesian correction batch for two arbitrary
multiplicity-preserving parent inventories.
-/
structure MTLedger
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : MIBlock leftTerms)
    (right : MIBlock rightTerms) where
  emitted :
    List (DFTerm M N K)
  pending :
    List (DFTerm M N K)
  accounting :
    List.Perm (emitted ++ pending)
      (DFTerm.correctionGrid leftTerms rightTerms)

namespace MTLedger

/-- Open one batch with every Cartesian correction term still pending. -/
noncomputable def initial
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : MIBlock leftTerms)
    (right : MIBlock rightTerms) :
    MTLedger left right where
  emitted := []
  pending := DFTerm.correctionGrid leftTerms rightTerms
  accounting := by simp

/--
Consume any selected pending correction term, retaining emitted operational
order and forgetting it only through a permutation certificate.
-/
def emit
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger : MTLedger left right)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : ledger.pending = before ++ term :: after) :
    MTLedger left right where
  emitted := ledger.emitted ++ [term]
  pending := before ++ after
  accounting := by
    apply List.Perm.trans _ ledger.accounting
    rw [hpending]
    simp only [List.append_assoc]
    apply List.Perm.append_left
    have hcomm :
        List.Perm
          (([term] : List (DFTerm M N K)) ++ before)
          (before ++ [term]) :=
      List.perm_append_comm
    simpa [List.append_assoc] using hcomm.append_right after

/-- Emitting one selected term removes exactly one pending slot. -/
lemma pending_length_emit
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger : MTLedger left right)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : ledger.pending = before ++ term :: after) :
    (ledger.emit before term after hpending).pending.length + 1 =
      ledger.pending.length := by
  simp [emit, hpending]
  omega

/-- Every selected pending term can be consumed. -/
lemma emit_pending
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger : MTLedger left right)
    {term : DFTerm M N K}
    (hterm : term ∈ ledger.pending) :
    ∃ before after,
      ledger.pending = before ++ term :: after :=
  List.mem_iff_append.mp hterm

/-- Every pending term comes from one concrete Cartesian pair of parents. -/
lemma parent_terms_pending
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger : MTLedger left right)
    {term : DFTerm M N K}
    (hterm : term ∈ ledger.pending) :
    ∃ leftTerm ∈ leftTerms, ∃ rightTerm ∈ rightTerms,
      term = leftTerm.correction rightTerm := by
  have hgrid :
      term ∈ DFTerm.correctionGrid leftTerms rightTerms :=
    ledger.accounting.subset (List.mem_append_right ledger.emitted hterm)
  rcases List.mem_flatMap.mp hgrid with ⟨leftTerm, hleft, hterm⟩
  rcases List.mem_map.mp hterm with ⟨rightTerm, hright, rfl⟩
  exact ⟨leftTerm, hleft, rightTerm, hright, rfl⟩

/-- Every pending concrete term belongs to the represented correction-family grid. -/
lemma family_grid_pending
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger : MTLedger left right)
    {term : DFTerm M N K}
    (hterm : term ∈ ledger.pending) :
    term.family ∈
      BFam.correctionGrid left.families right.families := by
  rcases ledger.parent_terms_pending hterm with
    ⟨leftTerm, hleft, rightTerm, hright, rfl⟩
  exact BFam.mem_correctionGrid.mpr
    ⟨leftTerm.family, left.family_mem hleft,
      rightTerm.family, right.family_mem hright, rfl⟩

/-- Every pending correction term lies strictly above one left-parent family. -/
lemma left_family_pending
    {M N K leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger : MTLedger left right)
    {term : DFTerm M N K}
    (hterm : term ∈ ledger.pending) :
    ∃ family ∈ left.families,
      weightedWordWeight leftWeight rightWeight family.recipe <
        weightedWordWeight leftWeight rightWeight term.family.recipe :=
  BFam.weight_weigh_memca
    hleftWeight hrightWeight
      (ledger.family_grid_pending hterm)

/-- Every pending correction term lies strictly above one right-parent family. -/
lemma right_family_pending
    {M N K leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger : MTLedger left right)
    {term : DFTerm M N K}
    (hterm : term ∈ ledger.pending) :
    ∃ family ∈ right.families,
      weightedWordWeight leftWeight rightWeight family.recipe <
        weightedWordWeight leftWeight rightWeight term.family.recipe :=
  BFam.weight_weigh_memcb
    hleftWeight hrightWeight
      (ledger.family_grid_pending hterm)

/-- A closed ledger emits one complete multiplicity-preserving correction block. -/
noncomputable def closedInventoryBlock
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger : MTLedger left right)
    (hpending : ledger.pending = []) :
    MIBlock ledger.emitted := by
  apply (left.correctionGrid right).permTerms
  simpa [hpending] using ledger.accounting.symm

/-- One exact decorated-slot consumption transition. -/
inductive Step
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms} :
    MTLedger left right →
      MTLedger left right →
        Prop where
  | emit
      (ledger : MTLedger left right)
      (before : List (DFTerm M N K))
      (term : DFTerm M N K)
      (after : List (DFTerm M N K))
      (hpending : ledger.pending = before ++ term :: after) :
      Step ledger (ledger.emit before term after hpending)

/-- Finite arithmetic drain for one open multiplicity batch. -/
abbrev Rewrites
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger final : MTLedger left right) :
    Prop :=
  Relation.ReflTransGen Step ledger final

/--
Every finite multiplicity ledger can be drained arithmetically.  The global
scheduler still has to realize these selected consumptions by its actual
adjacent obstruction trace.
-/
lemma rewrites_pending_nil
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger : MTLedger left right) :
    ∃ final, Rewrites ledger final ∧ final.pending = [] := by
  generalize hpending : ledger.pending = pending
  induction pending generalizing ledger with
  | nil =>
      exact ⟨ledger, Relation.ReflTransGen.refl, hpending⟩
  | cons term pending ih =>
      let next := ledger.emit [] term pending (by simpa using hpending)
      rcases ih next rfl with ⟨final, hrewrites, hclosed⟩
      exact ⟨final, hrewrites.head
        (Step.emit ledger [] term pending (by simpa using hpending)), hclosed⟩

end MTLedger

/-- One concrete More3 obstruction selected from an open multiplicity batch. -/
structure CMEmissi
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger : MTLedger left right) where
  leftTerm :
    DFTerm M N K
  rightTerm :
    DFTerm M N K
  left_mem :
    leftTerm ∈ leftTerms
  right_mem :
    rightTerm ∈ rightTerms
  pendingPrefix :
    List (DFTerm M N K)
  pendingSuffix :
    List (DFTerm M N K)
  pending_eq :
    ledger.pending =
      pendingPrefix ++ leftTerm.correction rightTerm :: pendingSuffix

namespace CMEmissi

/-- Consume the selected concrete correction term in its open batch. -/
noncomputable def emitLedger
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    {ledger : MTLedger left right}
    (emission : CMEmissi ledger) :
    MTLedger left right :=
  ledger.emit emission.pendingPrefix
    (emission.leftTerm.correction emission.rightTerm)
    emission.pendingSuffix emission.pending_eq

/-- The selected term belongs to the canonical Cartesian correction grid. -/
lemma correction_mem
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    {ledger : MTLedger left right}
    (emission : CMEmissi ledger) :
    emission.leftTerm.correction emission.rightTerm ∈
      DFTerm.correctionGrid leftTerms rightTerms := by
  apply List.mem_flatMap.mpr
  refine ⟨emission.leftTerm, emission.left_mem, ?_⟩
  exact List.mem_map.mpr
    ⟨emission.rightTerm, emission.right_mem, rfl⟩

/-- The selected More3 obstruction is one explicit adjacent labelled-word step. -/
def labelledWordStep
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    {ledger : MTLedger left right}
    (emission : CMEmissi ledger)
    (pre post :
      List (CWord (LabelledAtom M N))) :
    BBSched.LWStep
      (pre ++
        [emission.leftTerm.decorated.word,
          emission.rightTerm.decorated.word] ++ post)
      (pre ++
        [(emission.leftTerm.correction emission.rightTerm).decorated.word,
          emission.rightTerm.decorated.word,
          emission.leftTerm.decorated.word] ++ post) := by
  simpa [DTerm.correction] using
    (BBSched.LWStep.obstruction pre post
      emission.leftTerm.decorated.word
      emission.rightTerm.decorated.word)

end CMEmissi

end FIWork
end TCTex
end Submission
