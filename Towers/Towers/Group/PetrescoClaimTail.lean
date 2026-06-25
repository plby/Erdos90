import Towers.Group.HallPetrescoClaim

open scoped commutatorElement

namespace Towers
namespace HACoeff

open PPColl
open PPColl.RCColl.RPAggreg

/--
The concrete inverse raw family terms have nonempty singleton support, so
More3's finite independent-history family collector can run.
-/
lemma decorated_collect_ready
    (M N : ℕ) :
    DFTerm.CollectReady (inverseDecoratedTerms M N) := by
  have hinputSupport :
      SupportNonemptyList
        ((inverseDecoratedTerms M N).map DFTerm.decorated) := by
    rw [decorated_inverse_terms]
    exact (inverseDecoratedCollection M N).factors_support_nonempty
  exact
    DFTerm.collect_ready_independent
      (DFTerm.independentCollectReady
        (inverseDecoratedTerms M N) hinputSupport)

lemma nonempty_collected_decorated
    (M N : ℕ) :
    Nonempty
      (CDTerms M N) :=
  nonempty_decorated_ready M N
    (decorated_collect_ready M N)

namespace DTerm

/-- The inverse-oriented interchange term in `BA = A [A⁻¹, B] B`. -/
def inverseCorrection
    {M N K : ℕ}
    (B A : DTerm M N K) :
    DTerm M N K where
  word := .commutator (rootSwapWord A.word) B.word
  support := B.support ∪ A.support

@[simp]
lemma support_inverseCorrection
    {M N K : ℕ}
    (B A : DTerm M N K) :
    (inverseCorrection B A).support = B.support ∪ A.support :=
  rfl

@[simp]
lemma erased_shape_correction
    {M N K : ℕ}
    (B A : DTerm M N K) :
    (inverseCorrection B A).erasedShape =
      .commutator (rootSwapWord A.erasedShape) B.erasedShape := by
  change
    collapseWord (.commutator (rootSwapWord A.word) B.word) =
      .commutator (rootSwapWord (collapseWord A.word)) (collapseWord B.word)
  change
    CWord.commutator (collapseWord (rootSwapWord A.word)) (collapseWord B.word) =
      CWord.commutator (rootSwapWord (collapseWord A.word)) (collapseWord B.word)
  rw [collapse_root_swap]

lemma eval_inverseCorrection
    {M N K : ℕ}
    (B A : DTerm M N K)
    (hA : A.erasedShape.PBPos) :
    (inverseCorrection B A).eval = ⁅A.eval⁻¹, B.eval⁆ := by
  simp [eval, inverseCorrection,
    swap_collapse_positive FreeGroup.of hA]

/-- The low-degree local collector rewrite is exact in the labelled free group. -/
lemma eval_inverse_correction
    {M N K : ℕ}
    (B A : DTerm M N K)
    (hA : A.erasedShape.PBPos) :
    A.eval * (inverseCorrection B A).eval * B.eval =
      B.eval * A.eval := by
  rw [eval_inverseCorrection B A hA]
  simp [commutatorElement_def, mul_assoc]

lemma inverseCorrection_positive
    {M N K : ℕ}
    {B A : DTerm M N K}
    (hB : B.erasedShape.PBPos)
    (hA : A.erasedShape.PBPos) :
    (inverseCorrection B A).erasedShape.PBPos := by
  have hroot : (rootSwapWord A.erasedShape).PBPos :=
    rootSwap_positive hA
  rw [erased_shape_correction]
  simp only [CWord.PBPos,
    CWord.pair_left_commutator,
    CWord.pair_degree_commutator] at hroot hB ⊢
  omega

end DTerm

/-- Reorient a certified commutator factor without changing its group value. -/
def Factor.rootSwap
    {M N : ℕ}
    (F : Factor M N) :
    Factor M N where
  word := rootSwapWord F.word
  coefficient := -F.coefficient
  positive := rootSwap_positive F.positive
  coefficient_admissible := by
    rw [root_swap_positive F.positive,
      pair_swap_positive F.positive]
    exact
      (submodule M N F.word.pairLeftDegree F.word.pairRightDegree).neg_mem
        F.coefficient_admissible

@[simp]
lemma Factor.eval_rootSwap
    {M N : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    (F : Factor M N) :
    F.rootSwap.eval x y = F.eval x y := by
  rw [Factor.eval, Factor.rootSwap, swap_bidegree_positive
    (HPAtom.eval x y) F.positive]
  simp [Factor.eval]

/-- Invert one certified factor by negating only its outer coefficient. -/
def Factor.inv
    {M N : ℕ}
    (F : Factor M N) :
    Factor M N where
  word := F.word
  coefficient := -F.coefficient
  positive := F.positive
  coefficient_admissible :=
    (submodule M N F.word.pairLeftDegree F.word.pairRightDegree).neg_mem
      F.coefficient_admissible

@[simp]
lemma Factor.eval_inv
    {M N : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    (F : Factor M N) :
    F.inv.eval x y = (F.eval x y)⁻¹ := by
  simp [Factor.inv, Factor.eval]

/-- Reverse and invert a bare certified factor list. -/
def factorListInv
    {M N : ℕ}
    (factors : List (Factor M N)) :
    List (Factor M N) :=
  factors.reverse.map Factor.inv

lemma list_factor_inv
    {M N : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    (factors : List (Factor M N)) :
    listEval x y (factorListInv factors) =
      (listEval x y factors)⁻¹ := by
  rw [factorListInv, listEval, List.map_map, List.map_reverse]
  simpa [Function.comp_def, Factor.eval_inv] using
    (List.prod_inv_reverse (factors.map (Factor.eval x y))).symm

/--
Universal elements admitting one exact ordered bare certified factor list.

The collector can now target this subgroup directly; once membership of the
block commutator is known, the required `List (Factor M N)` is just the
membership witness.
-/
def canonicalFactorSubgroup
    (M N : ℕ) :
    Subgroup UniversalGroup where
  carrier :=
    { g |
      ∃ factors : List (Factor M N),
        listEval universalLeft universalRight factors = g }
  mul_mem' := by
    rintro g h ⟨gFactors, rfl⟩ ⟨hFactors, rfl⟩
    refine ⟨gFactors ++ hFactors, ?_⟩
    simp [listEval, List.prod_append]
  one_mem' := by
    exact ⟨[], rfl⟩
  inv_mem' := by
    rintro g ⟨factors, rfl⟩
    exact ⟨factorListInv factors,
      list_factor_inv universalLeft universalRight factors⟩

lemma factors_canonical_subgroup
    {M N : ℕ}
    {g : UniversalGroup}
    (hg : g ∈ canonicalFactorSubgroup M N) :
    ∃ factors : List (Factor M N),
      listEval universalLeft universalRight factors = g :=
  hg

/--
The collapsed inverse-oriented labelled trace evaluates to the universal
commutator `[X^M, Y^N]`.
-/
lemma collapsed_labelled_atoms
    (M N : ℕ) :
    collapsedListEval
        (inverseLeftTrace
          (labelledLeftAtoms M N)
          (labelledRightAtoms M N)) =
      ⁅universalLeft ^ M, universalRight ^ N⁆ := by
  calc
    collapsedListEval
        (inverseLeftTrace
          (labelledLeftAtoms M N)
          (labelledRightAtoms M N)) =
        collapseHom M N
          (labelledListEval
            (inverseLeftTrace
              (labelledLeftAtoms M N)
              (labelledRightAtoms M N))) := by
      exact (collapse_labelled_eval _).symm
    _ =
        collapseHom M N
          ⁅labelledAtomList (labelledLeftAtoms M N),
            labelledAtomList (labelledRightAtoms M N)⁆ := by
      rw [labelled_right_trace]
      · intro x hx
        exact collapse_label_atoms hx
      · intro y hy
        exact collapse_labelled_atoms hy
    _ =
        collapseHom M N ⁅labelledLeft M N, labelledRight M N⁆ := by
      rw [labelled_left_atoms,
        labelled_atom_atoms]
    _ = ⁅universalLeft ^ M, universalRight ^ N⁆ := by
      rw [map_commutatorElement, collapse_labelled_left,
        collapse_labelled_right]

/--
The inverse-trace subgroup target is equivalent to the canonical-factor
theorem.  In particular, it is not a smaller upstream subgoal.
-/
lemma canonical_factors_subgroup
    (M N : ℕ) :
    (∃ factors : List (Factor M N),
      listEval universalLeft universalRight factors =
        ⁅universalLeft ^ M, universalRight ^ N⁆) ↔
    collapsedListEval
        (inverseLeftTrace
          (labelledLeftAtoms M N)
          (labelledRightAtoms M N)) ∈
      canonicalFactorSubgroup M N := by
  constructor
  · rintro ⟨factors, hfactors⟩
    rw [collapsed_labelled_atoms M N]
    exact ⟨factors, hfactors⟩
  · intro hmem
    rcases factors_canonical_subgroup hmem with
      ⟨factors, hfactors⟩
    refine ⟨factors, ?_⟩
    rw [← collapsed_labelled_atoms M N]
    exact hfactors

lemma factor_canonical_subgroup
    {M N : ℕ}
    (F : Factor M N) :
    F.eval universalLeft universalRight ∈ canonicalFactorSubgroup M N := by
  exact ⟨[F], by simp [listEval]⟩

lemma list_factor_subgroup
    {M N : ℕ}
    (factors : List (Factor M N)) :
    listEval universalLeft universalRight factors ∈
      canonicalFactorSubgroup M N := by
  exact ⟨factors, rfl⟩

lemma BFam.collapsedlist_evalmem_canofactsubg
    {M N : ℕ}
    (F : BFam M N) :
    collapsedListEval F.realizations ∈
      canonicalFactorSubgroup M N := by
  rw [F.collapsed_list_factor]
  exact factor_canonical_subgroup F.factor

lemma BFam.colllisteval_reallistmem_canofactsubg
    {M N : ℕ}
    (families : List (BFam M N)) :
    collapsedListEval (BFam.realizationList families) ∈
      canonicalFactorSubgroup M N := by
  rw [BFam.collapsed_realization_factor]
  exact list_factor_subgroup (BFam.factorList families)

/-- A finite collected block whose decorated terms erase to one Hall word. -/
def SameErasedBlock
    {M N K : ℕ}
    (block : List (DFTerm M N K)) :
    Prop :=
  ∃ word : CWord HPAtom,
    ∀ T ∈ block, T.erasedShape = word

/-- Canonical maximal adjacent runs of equal erased Hall shape. -/
def sameErasedBlocks
    {M N K : ℕ}
    (terms : List (DFTerm M N K)) :
    List (List (DFTerm M N K)) :=
  terms.splitBy fun T U => decide (T.erasedShape = U.erasedShape)

lemma flatten_same_blocks
    {M N K : ℕ}
    (terms : List (DFTerm M N K)) :
    (sameErasedBlocks terms).flatten = terms := by
  exact List.flatten_splitBy _ _

lemma same_erased_blocks
    {M N K : ℕ}
    (terms : List (DFTerm M N K))
    (block : List (DFTerm M N K))
    (hblock : block ∈ sameErasedBlocks terms) :
    SameErasedBlock block := by
  have hblock' :
      block ∈ terms.splitBy fun T U => decide (T.erasedShape = U.erasedShape) := by
    simpa [sameErasedBlocks] using hblock
  have hchainBool :
      block.IsChain fun T U => decide (T.erasedShape = U.erasedShape) :=
    List.isChain_of_mem_splitBy hblock'
  have hchain :
      block.IsChain fun T U => T.erasedShape = U.erasedShape :=
    hchainBool.imp (by
      intro T U hTU
      simpa using hTU)
  cases block with
  | nil =>
      exact False.elim (List.ne_nil_of_mem_splitBy hblock' rfl)
  | cons head tail =>
      letI : Trans
          (fun T U : DFTerm M N K => T.erasedShape = U.erasedShape)
          (fun T U : DFTerm M N K => T.erasedShape = U.erasedShape)
          (fun T U : DFTerm M N K => T.erasedShape = U.erasedShape) :=
        ⟨fun hTU hUV => hTU.trans hUV⟩
      have hpairwise :
          (head :: tail).Pairwise fun T U => T.erasedShape = U.erasedShape :=
        hchain.pairwise
      rw [List.pairwise_cons] at hpairwise
      refine ⟨head.erasedShape, ?_⟩
      intro T hT
      simp only [List.mem_cons] at hT
      rcases hT with rfl | hT
      · rfl
      · exact (hpairwise.1 T hT).symm

/-- Collapsing one same-shape decorated block gives the corresponding power. -/
lemma decorated_collapsed_same
    {M N K : ℕ}
    (block : List (DFTerm M N K))
    (word : CWord HPAtom)
    (hsame : ∀ T ∈ block, T.erasedShape = word) :
    decoratedCollapsedEval (block.map DFTerm.decorated) =
      word.eval (HPAtom.eval universalLeft universalRight) ^ block.length := by
  rw [decoratedCollapsedEval, List.map_map, Function.comp_def]
  have hmap :
      block.map (fun T => T.decorated.collapsedEval) =
        List.replicate block.length
          (word.eval (HPAtom.eval universalLeft universalRight)) := by
    simpa using
      (List.eq_replicate_of_mem
        (a := word.eval (HPAtom.eval universalLeft universalRight))
        (l := block.map fun T => T.decorated.collapsedEval)
        (by
          intro z hz
          rcases List.mem_map.mp hz with ⟨T, hT, rfl⟩
          change T.erasedShape.eval (HPAtom.eval universalLeft universalRight) =
            word.eval (HPAtom.eval universalLeft universalRight)
          rw [hsame T hT]))
  rw [hmap, List.prod_replicate]

/--
One counted block family already carries exactly the admissible coefficient
needed for the length of its realization list.
-/
lemma BFam.realizations_length_memsubmodule
    {M N : ℕ}
    (F : BFam M N) :
    (F.realizations.length : ℤ) ∈
      submodule M N F.recipe.erasedShape.pairLeftDegree
        F.recipe.erasedShape.pairRightDegree := by
  simpa [BFam.factor, F.length_eq,
    F.recipe.factor_coefficient_embeddings M N] using
    F.factor.coefficient_admissible

/--
If a concrete same-shape block is exactly one counted block family, its
concrete length has the family coefficient's admissibility.
-/
lemma length_submodule_realizations
    {M N K : ℕ}
    (F : BFam M N)
    (block : List (DFTerm M N K))
    (word : CWord HPAtom)
    (hrealizations : F.realizations = decoratedFamilyList block)
    (hword : F.recipe.erasedShape = word) :
    (block.length : ℤ) ∈
      submodule M N word.pairLeftDegree word.pairRightDegree := by
  have hlen : block.length = F.realizations.length := by
    rw [hrealizations, decoratedFamilyList, List.length_map]
  simpa [hword, hlen] using F.realizations_length_memsubmodule

/--
A finite list of counted families with one erased shape contributes an
admissible total realization count at that shape.
-/
lemma BFam.realiz_lengm_recip
    {M N : ℕ}
    (families : List (BFam M N))
    (word : CWord HPAtom)
    (hfamilies : ∀ F ∈ families, F.recipe.erasedShape = word) :
    ((BFam.realizationList families).length : ℤ) ∈
      submodule M N word.pairLeftDegree word.pairRightDegree := by
  induction families with
  | nil =>
      simp [BFam.realizationList]
  | cons F families ih =>
      have hF :
          (F.realizations.length : ℤ) ∈
            submodule M N word.pairLeftDegree word.pairRightDegree := by
        simpa [hfamilies F (by simp)] using F.realizations_length_memsubmodule
      have htail :
          ((BFam.realizationList families).length : ℤ) ∈
            submodule M N word.pairLeftDegree word.pairRightDegree :=
        ih (fun G hG => hfamilies G (by simp [hG]))
      simpa [BFam.realizationList, Int.natCast_add] using
        (submodule M N word.pairLeftDegree word.pairRightDegree).add_mem
          hF htail

/--
Once a concrete block has the same length as complete counted families with
one erased shape, its concrete length has admissible provenance.
-/
lemma length_submodule_realization
    {M N K : ℕ}
    (families : List (BFam M N))
    (block : List (DFTerm M N K))
    (word : CWord HPAtom)
    (hlength : (BFam.realizationList families).length = block.length)
    (hfamilies : ∀ F ∈ families, F.recipe.erasedShape = word) :
    (block.length : ℤ) ∈
      submodule M N word.pairLeftDegree word.pairRightDegree := by
  simpa [hlength] using
    BFam.realiz_lengm_recip
      families word hfamilies

/-- Distinct counted recipe families represented in one concrete block. -/
noncomputable def distinctBlockFamilies
    {M N K : ℕ}
    (block : List (DFTerm M N K)) :
    List (BFam M N) := by
  classical
  exact (block.map DFTerm.family).dedup

lemma distinct_block_families
    {M N K : ℕ}
    {block : List (DFTerm M N K)}
    {F : BFam M N} :
    F ∈ distinctBlockFamilies block ↔
      ∃ T ∈ block, T.family = F := by
  classical
  simp [distinctBlockFamilies]

lemma recipe_distinct_families
    {M N K : ℕ}
    (block : List (DFTerm M N K))
    (word : CWord HPAtom)
    (hsame : ∀ T ∈ block, T.erasedShape = word)
    (F : BFam M N)
    (hF : F ∈ distinctBlockFamilies block) :
    F.recipe.erasedShape = word := by
  rcases distinct_block_families.mp hF with ⟨T, hT, rfl⟩
  rw [← T.erased_shape_family, hsame T hT]

/--
Every concrete labelled word in a block is one realization of a distinct
counted family represented by that block.
-/
lemma decorated_distinct_families
    {M N K : ℕ}
    (block : List (DFTerm M N K)) :
    decoratedFamilyList block ⊆
      BFam.realizationList (distinctBlockFamilies block) := by
  intro word hword
  rcases List.mem_map.mp hword with ⟨T, hT, rfl⟩
  rw [BFam.realizationList]
  exact List.mem_flatMap.mpr
    ⟨T.family, distinct_block_families.mpr ⟨T, hT, rfl⟩, T.word_mem⟩

/--
The raw inverse family input is saturated at the level of selected labelled
words: every realization of a represented raw family occurs as another raw
family term.
-/
lemma inverse_decorated_realizations
    {M N : ℕ}
    {T : DFTerm M N (inverseLabelledCollection M N).factors.length}
    (hT : T ∈ inverseDecoratedTerms M N)
    {word : CWord (LabelledAtom M N)}
    (hword : word ∈ T.family.realizations) :
    ∃ U ∈ inverseDecoratedTerms M N, U.decorated.word = word := by
  rcases List.mem_ofFn.mp hT with ⟨index, rfl⟩
  have hinst :
      word ∈
        (LRecipe.ofLabelLinear
          ((inverseLabelledCollection M N).factors.get index)
          ((inverseLabelledCollection M N).factors_positive
            ((inverseLabelledCollection M N).factors.get index)
            (List.get_mem _ index))
          (inverse_labelled_linear M N
            ((inverseLabelledCollection M N).factors.get index)
            (List.get_mem _ index))).instantiations M N := by
    simpa [inverseDecoratedTerms, DFTerm.ofLabelLinear,
      BFam.ofLinear] using hword
  have hwordRaw :
      word ∈ (inverseLabelledCollection M N).factors :=
    LRecipe.labellin_instantimem_invlabecoll
      ((inverseLabelledCollection M N).factors.get index)
      (List.get_mem _ index) word hinst
  rcases List.mem_iff_get.mp hwordRaw with ⟨wordIndex, rfl⟩
  let familyIndex : Fin (inverseDecoratedTerms M N).length :=
    ⟨wordIndex, by simp [inverseDecoratedTerms]⟩
  refine ⟨(inverseDecoratedTerms M N).get familyIndex, List.get_mem _ _, ?_⟩
  simp [familyIndex, inverseDecoratedTerms, DFTerm.ofLabelLinear,
    DTerm.raw]

/--
The distinct raw counted families do not introduce labelled words outside the
actual raw inverse family input.
-/
lemma realization_distinct_words
    (M N : ℕ) :
    BFam.realizationList
        (distinctBlockFamilies (inverseDecoratedTerms M N)) ⊆
      decoratedFamilyList (inverseDecoratedTerms M N) := by
  intro word hword
  rw [BFam.realizationList] at hword
  rcases List.mem_flatMap.mp hword with ⟨F, hF, hwordF⟩
  rcases distinct_block_families.mp hF with ⟨T, hT, rfl⟩
  rcases inverse_decorated_realizations
      hT hwordF with ⟨U, hU, rfl⟩
  exact List.mem_map.mpr ⟨U, hU, rfl⟩

/-- Repeat each represented family once for every concrete realization it carries. -/
def BFam.realizationFamilyList
    {M N : ℕ}
    (families : List (BFam M N)) :
    List (BFam M N) :=
  families.flatMap fun F => List.replicate F.realizations.length F

/-- One concrete realization slot of one counted family. -/
abbrev BFam.RToken
    (M N : ℕ) :=
  Σ F : BFam M N, Fin F.realizations.length

/-- List the concrete realization slots carried by a finite family list. -/
def BFam.realizationTokenList
    {M N : ℕ}
    (families : List (BFam M N)) :
    List (BFam.RToken M N) :=
  families.sigma fun F => List.finRange F.realizations.length

lemma BFam.realization_tokenlist_nodupnodup
    {M N : ℕ}
    {families : List (BFam M N)}
    (hfamilies : families.Nodup) :
    (BFam.realizationTokenList families).Nodup := by
  exact hfamilies.sigma fun F => List.nodup_finRange F.realizations.length

lemma distinct_families_nodup
    {M N K : ℕ}
    (block : List (DFTerm M N K)) :
    (distinctBlockFamilies block).Nodup := by
  classical
  exact List.nodup_dedup _

def DFTerm.realizationIndex
    {M N K : ℕ}
    (T : DFTerm M N K) :
    Fin T.family.realizations.length :=
  T.word_index

lemma DFTerm.realizationIndex_get
    {M N K : ℕ}
    (T : DFTerm M N K) :
    T.family.realizations.get T.realizationIndex = T.decorated.word :=
  T.word_get

noncomputable def DFTerm.realizationToken
    {M N K : ℕ}
    (T : DFTerm M N K) :
    BFam.RToken M N :=
  ⟨T.family, T.realizationIndex⟩

@[simp]
lemma DFTerm.realizationToken_family
    {M N K : ℕ}
    (T : DFTerm M N K) :
    T.realizationToken.1 = T.family :=
  rfl

@[simp]
lemma DFTerm.realizationToken_correction
    {M N K : ℕ}
    (B A : DFTerm M N K) :
    (B.correction A).realizationToken =
      ⟨B.family.correction A.family,
        B.family.correctionIndex A.family B.word_index A.word_index⟩ :=
  rfl

@[simp]
lemma DFTerm.realization_token_rootswap
    {M N K : ℕ}
    (T : DFTerm M N K) :
    T.rootSwap.realizationToken =
      ⟨T.family.rootSwap, T.family.rootSwapIndex T.word_index⟩ :=
  rfl

/-- Pairwise correction of two concrete realization slots. -/
def BFam.RToken.correction
    {M N : ℕ}
    (B A : BFam.RToken M N) :
    BFam.RToken M N :=
  ⟨B.1.correction A.1, B.1.correctionIndex A.1 B.2 A.2⟩

lemma BFam.realizatoken_listsingleton_corrperm
    {M N : ℕ}
    (B A : BFam M N) :
    List.Perm (BFam.realizationTokenList [B.correction A])
      ((BFam.realizationTokenList [B]).flatMap fun b =>
        (BFam.realizationTokenList [A]).map
          (BFam.RToken.correction b)) := by
  let indices :
      List (Σ _ : Fin B.realizations.length, Fin A.realizations.length) :=
    (List.finRange B.realizations.length).sigma fun _ =>
      List.finRange A.realizations.length
  let correctionOfIndices :
      (Σ _ : Fin B.realizations.length, Fin A.realizations.length) →
        BFam.RToken M N :=
    fun index =>
      ⟨B.correction A, B.correctionIndex A index.1 index.2⟩
  have hindices : indices.Nodup := by
    exact (List.nodup_finRange B.realizations.length).sigma fun _ =>
      List.nodup_finRange A.realizations.length
  have hcorrectionOfIndices : Function.Injective correctionOfIndices := by
    intro index index' hindex
    rcases index with ⟨b, a⟩
    rcases index' with ⟨b', a'⟩
    have hslot :
        B.correctionIndex A b a = B.correctionIndex A b' a' := by
      exact eq_of_heq (Sigma.mk.inj hindex).2
    have hslotVal := congrArg Fin.val hslot
    have hmkDivMod : b.mkDivMod a = b'.mkDivMod a' := by
      apply Fin.ext
      simpa [BFam.correctionIndex, List.flat_map_mapindex, Fin.mkDivMod,
        Nat.mul_comm] using hslotVal
    have hb : b = b' := by
      simpa using congrArg Fin.divNat hmkDivMod
    have ha : a = a' := by
      simpa using congrArg Fin.modNat hmkDivMod
    cases hb
    cases ha
    rfl
  have hright :
      ((BFam.realizationTokenList [B]).flatMap fun b =>
          (BFam.realizationTokenList [A]).map
            (BFam.RToken.correction b)) =
        indices.map correctionOfIndices := by
    dsimp [indices]
    simp only [List.sigma]
    rw [List.map_flatMap]
    simp [BFam.realizationTokenList, correctionOfIndices,
      BFam.RToken.correction, List.sigma,
      List.flatMap_map, List.map_map, Function.comp_def]
  apply (List.perm_ext_iff_of_nodup
    (BFam.realization_tokenlist_nodupnodup (by simp))
    (by rw [hright]; exact hindices.map hcorrectionOfIndices)).2
  · intro token
    constructor
    · intro htoken
      rcases token with ⟨F, index⟩
      have htoken' :
          B.correction A = F ∧
            ∃ index' : Fin (B.correction A).realizations.length,
              index' ≍ index := by
        simpa [BFam.realizationTokenList] using htoken
      rcases htoken' with ⟨rfl, ⟨index, hindex⟩⟩
      cases hindex
      let index' : Fin (B.realizations.length * A.realizations.length) :=
        ⟨index, by simpa [BFam.correction, List.length_flatMap] using index.isLt⟩
      have hindex' :
          B.correctionIndex A index'.divNat index'.modNat =
            index := by
        apply Fin.ext
        simp [BFam.correctionIndex, List.flat_map_mapindex,
          index', Nat.mul_comm, Nat.div_add_mod]
      rw [← hindex']
      apply List.mem_flatMap.mpr
      refine ⟨⟨B, index'.divNat⟩, ?_, ?_⟩
      · simp [BFam.realizationTokenList]
      · exact List.mem_map.mpr
          ⟨⟨A, index'.modNat⟩, by
            simp [BFam.realizationTokenList], rfl⟩
    · intro htoken
      rcases List.mem_flatMap.mp htoken with ⟨b, hb, htoken⟩
      rcases List.mem_map.mp htoken with ⟨a, ha, rfl⟩
      rcases b with ⟨F, b⟩
      rcases a with ⟨G, a⟩
      have hb' : B = F ∧ ∃ b' : Fin B.realizations.length, b' ≍ b := by
        simpa [BFam.realizationTokenList] using hb
      have ha' : A = G ∧ ∃ a' : Fin A.realizations.length, a' ≍ a := by
        simpa [BFam.realizationTokenList] using ha
      rcases hb' with ⟨rfl, ⟨b', rfl⟩⟩
      rcases ha' with ⟨rfl, ⟨a', rfl⟩⟩
      exact List.mem_sigma.mpr ⟨by simp, List.mem_finRange _⟩

lemma BFam.realization_tokenlist_fammap
    {M N : ℕ}
    (families : List (BFam M N)) :
    (BFam.realizationTokenList families).map Sigma.fst =
      BFam.realizationFamilyList families := by
  induction families with
  | nil =>
      simp [BFam.realizationTokenList, BFam.realizationFamilyList]
  | cons F families ih =>
      simpa [BFam.realizationTokenList,
        BFam.realizationFamilyList, List.sigma_cons,
        List.map_append, List.map_map, Function.comp_def] using
        congrArg (List.append (List.replicate F.realizations.length F)) ih

lemma BFam.realization_fam_listlength
    {M N : ℕ}
    (families : List (BFam M N)) :
    (BFam.realizationFamilyList families).length =
      (BFam.realizationList families).length := by
  induction families with
  | nil =>
      simp [BFam.realizationFamilyList, BFam.realizationList]
  | cons F families _ih =>
      simp [BFam.realizationFamilyList, BFam.realizationList]

/--
One concrete same-shape block is family-counted when its family labels are
exactly one realization-sized packet for every distinct represented family.
-/
def FamilyCountedBlock
    {M N K : ℕ}
    (block : List (DFTerm M N K)) :
    Prop :=
  List.Perm
    (BFam.realizationFamilyList (distinctBlockFamilies block))
    (block.map DFTerm.family)

/--
The precise packet invariant: each represented family realization slot occurs
once in the concrete block.
-/
def RealizationIndexedBlock
    {M N K : ℕ}
    (block : List (DFTerm M N K)) :
    Prop :=
  List.Perm
    (BFam.realizationTokenList (distinctBlockFamilies block))
    (block.map DFTerm.realizationToken)

lemma counted_realization_indexed
    {M N K : ℕ}
    (block : List (DFTerm M N K))
    (hindexed : RealizationIndexedBlock block) :
    FamilyCountedBlock block := by
  have hfamilies := hindexed.map Sigma.fst
  simpa [RealizationIndexedBlock, FamilyCountedBlock,
    BFam.realization_tokenlist_fammap, List.map_map] using hfamilies

lemma realization_distinct_counted
    {M N K : ℕ}
    (block : List (DFTerm M N K))
    (hcounted : FamilyCountedBlock block) :
    (BFam.realizationList (distinctBlockFamilies block)).length =
      block.length := by
  rw [← BFam.realization_fam_listlength]
  calc
    (BFam.realizationFamilyList (distinctBlockFamilies block)).length =
        (block.map DFTerm.family).length :=
      hcounted.length_eq
    _ = block.length := by simp

lemma decorated_collapsed_append
    {M N K : ℕ}
    (L R : List (DTerm M N K)) :
    decoratedCollapsedEval (L ++ R) =
      decoratedCollapsedEval L * decoratedCollapsedEval R := by
  simp [decoratedCollapsedEval, List.prod_append]

lemma CDTerms.collapsed_evaleq_commpow
    {M N : ℕ}
    (C : CDTerms M N) :
    decoratedCollapsedEval (C.factors.map DFTerm.decorated) =
      ⁅universalLeft ^ M, universalRight ^ N⁆ := by
  calc
    decoratedCollapsedEval (C.factors.map DFTerm.decorated) =
        collapseHom M N
          (decoratedListEval (C.factors.map DFTerm.decorated)) :=
      (collapse_decorated_eval _).symm
    _ = collapseHom M N (DFTerm.listEval C.factors) := by
      rw [DFTerm.list_eval_decorated]
    _ = collapseHom M N ⁅labelledLeft M N, labelledRight M N⁆ := by
      rw [C.eval_eq]
    _ = ⁅universalLeft ^ M, universalRight ^ N⁆ := by
      rw [map_commutatorElement, collapse_labelled_left,
        collapse_labelled_right]

/--
For a collected decorated-family output, membership in the canonical factor
subgroup is independent of the particular collector output: the output evaluates
to the universal commutator.

Thus this target is exactly the global canonical-factor theorem.
-/
lemma CDTerms.memcanon_factsubgiff_exisfactlist
    {M N : ℕ}
    (C : CDTerms M N) :
    decoratedCollapsedEval
        (C.factors.map DFTerm.decorated) ∈
      canonicalFactorSubgroup M N ↔
    ∃ factors : List (Factor M N),
      listEval universalLeft universalRight factors =
        ⁅universalLeft ^ M, universalRight ^ N⁆ := by
  constructor
  · intro hmem
    rcases factors_canonical_subgroup hmem with
      ⟨factors, hfactors⟩
    exact ⟨factors, by
      rw [← C.collapsed_evaleq_commpow]
      exact hfactors⟩
  · rintro ⟨factors, hfactors⟩
    rw [C.collapsed_evaleq_commpow]
    exact ⟨factors, hfactors⟩

/-- A labelled formal commutator word. -/
abbrev LabelledWord (M N : ℕ) :=
  CWord (LabelledAtom M N)

/-- The concrete correction inserted when moving `A` left across `B`. -/
def labelledWordCorrection
    {M N : ℕ}
    (B A : LabelledWord M N) :
    LabelledWord M N :=
  .commutator B A

lemma labelled_correction_mul
    {M N : ℕ}
    (B A : LabelledWord M N) :
    (labelledWordCorrection B A).eval FreeGroup.of *
        A.eval FreeGroup.of * B.eval FreeGroup.of =
      B.eval FreeGroup.of * A.eval FreeGroup.of := by
  simp [labelledWordCorrection, CWord.eval_commutator,
    commutatorElement_def]

/--
One sound local rewrite in a labelled word list.

`B A` may be replaced by `[B,A] A B`. This is exactly the concrete
collection move, but stated without support/termination side conditions.
The side conditions are needed only to prove existence of a terminating
scheduler, not soundness.
-/
inductive LWStep
    {M N : ℕ} :
    List (LabelledWord M N) → List (LabelledWord M N) → Prop where
  | obstruction
      (P S : List (LabelledWord M N))
      (B A : LabelledWord M N) :
      LWStep
        (P ++ [B, A] ++ S)
        (P ++ [labelledWordCorrection B A, A, B] ++ S)

/-- Finite sequence of concrete collection rewrites. -/
abbrev LWRw
    {M N : ℕ}
    (L R : List (LabelledWord M N)) : Prop :=
  Relation.ReflTransGen (@LWStep M N) L R

lemma labelled_list_step
    {M N : ℕ}
    {L R : List (LabelledWord M N)}
    (h : LWStep L R) :
    labelledListEval R = labelledListEval L := by
  cases h with
  | obstruction P S B A =>
      simp [labelledListEval, List.prod_append, labelledWordCorrection,
        CWord.eval_commutator, commutatorElement_def]
      group

lemma labelled_list_rewrites
    {M N : ℕ}
    {L R : List (LabelledWord M N)}
    (h : LWRw L R) :
    labelledListEval R = labelledListEval L := by
  induction h with
  | refl => rfl
  | tail hLR hstep ih =>
      exact (labelled_list_step hstep).trans ih

lemma LWStep.context
    {M N : ℕ}
    {L R : List (LabelledWord M N)}
    (h : LWStep L R)
    (P S : List (LabelledWord M N)) :
    LWStep (P ++ L ++ S) (P ++ R ++ S) := by
  cases h with
  | obstruction P0 S0 B A =>
      simpa [List.append_assoc] using
        (LWStep.obstruction
          (P ++ P0) (S0 ++ S) B A)

lemma LWRw.context
    {M N : ℕ}
    {L R : List (LabelledWord M N)}
    (h : LWRw L R)
    (P S : List (LabelledWord M N)) :
    LWRw (P ++ L ++ S) (P ++ R ++ S) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hLR hstep ih =>
      exact Relation.ReflTransGen.tail ih (hstep.context P S)

lemma LWRw.append
    {M N : ℕ}
    {L₁ R₁ L₂ R₂ : List (LabelledWord M N)}
    (h₁ : LWRw L₁ R₁)
    (h₂ : LWRw L₂ R₂) :
    LWRw (L₁ ++ L₂) (R₁ ++ R₂) := by
  have hleft :
      LWRw (L₁ ++ L₂) (R₁ ++ L₂) := by
    simpa [List.append_assoc] using h₁.context [] L₂
  have hright :
      LWRw (R₁ ++ L₂) (R₁ ++ R₂) := by
    simpa [List.append_assoc] using h₂.context R₁ []
  exact hleft.trans hright

lemma LWRw.single_step
    {M N : ℕ}
    (P S : List (LabelledWord M N))
    (B A : LabelledWord M N) :
    LWRw
      (P ++ [B, A] ++ S)
      (P ++ [labelledWordCorrection B A, A, B] ++ S) := by
  exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl
    (LWStep.obstruction P S B A)

/-- A word list is packeted if it is exactly a concatenation of complete families. -/
def PWList
    (M N : ℕ)
    (words : List (LabelledWord M N)) : Prop :=
  ∃ families : List (BFam M N),
    BFam.realizationList families = words

namespace PWList

lemma of_families
    {M N : ℕ}
    (families : List (BFam M N)) :
    PWList M N (BFam.realizationList families) := by
  exact ⟨families, rfl⟩

lemma nil
    (M N : ℕ) :
    PWList M N [] := by
  exact ⟨[], by simp [BFam.realizationList]⟩

lemma append
    {M N : ℕ}
    {L R : List (LabelledWord M N)}
    (hL : PWList M N L)
    (hR : PWList M N R) :
    PWList M N (L ++ R) := by
  rcases hL with ⟨familiesL, rfl⟩
  rcases hR with ⟨familiesR, rfl⟩
  refine ⟨familiesL ++ familiesR, ?_⟩
  simp [BFam.realizationList, List.flatMap_append]

/-- Convert a packed labelled word identity into a `BFam.Expansion`. -/
lemma nonempty_block_expansion
    {M N : ℕ}
    {words : List (LabelledWord M N)}
    (hpacked : PWList M N words)
    (heval : labelledListEval words =
      ⁅labelledLeft M N, labelledRight M N⁆) :
    Nonempty (BFam.Expansion M N) := by
  rcases hpacked with ⟨families, hfamilies⟩
  refine ⟨{
    families := families
    collapsed_eval_eq := ?_ }⟩
  calc
    collapsedListEval (BFam.realizationList families) =
        collapseHom M N
          (labelledListEval (BFam.realizationList families)) := by
      exact (collapse_labelled_eval _).symm
    _ = collapseHom M N (labelledListEval words) := by
      rw [hfamilies]
    _ = collapseHom M N ⁅labelledLeft M N, labelledRight M N⁆ := by
      rw [heval]
    _ = ⁅universalLeft ^ M, universalRight ^ N⁆ := by
      rw [map_commutatorElement, collapse_labelled_left,
        collapse_labelled_right]

end PWList

/--
A concrete packetization certificate for the inverse trace.

This is the non-circular target to prove: starting from the already-proved
labelled inverse trace, a finite sequence of explicit word-collection rewrites
lands on a concatenation of complete `BFam` realization packets.
-/
def InversePacketReachable
    (M N : ℕ) : Prop :=
  ∃ families : List (BFam M N),
    LWRw
      (inverseLeftTrace
        (labelledLeftAtoms M N)
        (labelledRightAtoms M N))
      (BFam.realizationList families)

lemma inverse_trace_commutator
    (M N : ℕ) :
    labelledListEval
        (inverseLeftTrace
          (labelledLeftAtoms M N)
          (labelledRightAtoms M N)) =
      ⁅labelledLeft M N, labelledRight M N⁆ := by
  simpa [labelled_left_atoms,
    labelled_atom_atoms] using
    (labelled_right_trace
      (labelledLeftAtoms M N)
      (labelledRightAtoms M N)
      (fun x hx => collapse_label_atoms hx)
      (fun y hy => collapse_labelled_atoms hy))

/-- Convert a packet-rewrite scheduler certificate into a block-family expansion. -/
theorem nonempty_expansion_reachable
    {M N : ℕ}
    (hreachable : InversePacketReachable M N) :
    Nonempty (BFam.Expansion M N) := by
  rcases hreachable with ⟨families, hrewrite⟩
  have heval :
      labelledListEval (BFam.realizationList families) =
        ⁅labelledLeft M N, labelledRight M N⁆ := by
    calc
      labelledListEval (BFam.realizationList families) =
          labelledListEval
            (inverseLeftTrace
              (labelledLeftAtoms M N)
              (labelledRightAtoms M N)) :=
        labelled_list_rewrites hrewrite
      _ = ⁅labelledLeft M N, labelledRight M N⁆ :=
        inverse_trace_commutator M N
  exact PWList.nonempty_block_expansion
    (PWList.of_families families) heval

/-- The right-labelled inverse trace is empty when the right input list is empty. -/
lemma inverse_left_nil
    {M N : ℕ}
    (xs : List (LabelledAtom M N)) :
    inverseLeftTrace xs [] = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [inverseLeftTrace, inverseRightTrace, inverseTraceList, ih]

/-- The packet scheduler is already solved when there are no left labels. -/
lemma inverse_reachable_left
    (N : ℕ) :
    InversePacketReachable 0 N := by
  refine ⟨[], ?_⟩
  simpa [labelledLeftAtoms, BFam.realizationList, inverseLeftTrace] using
    (Relation.ReflTransGen.refl :
      LWRw ([] : List (LabelledWord 0 N)) [])

/-- The packet scheduler is already solved when there are no right labels. -/
lemma inverse_reachable_right
    (M : ℕ) :
    InversePacketReachable M 0 := by
  refine ⟨[], ?_⟩
  simpa [labelledRightAtoms, BFam.realizationList,
    inverse_left_nil (labelledLeftAtoms M 0)] using
    (Relation.ReflTransGen.refl :
      LWRw ([] : List (LabelledWord M 0)) [])

namespace BFam

/--
The collapsed value of the realizations of one family is just the erased shape
raised to the number of realizations. This version avoids `Factor`; it is the
right tool for comparing with an arbitrary block of words that merely has the
same erased shape and the same length.
-/
lemma collapsed_shape_length
    {M N : ℕ}
    (F : BFam M N) :
    collapsedListEval F.realizations =
      (F.recipe.erasedShape.eval
        (HPAtom.eval universalLeft universalRight)) ^ F.realizations.length := by
  rw [collapsedListEval]
  have hmap :
      List.map
          (fun w =>
            (collapseWord w).eval
              (HPAtom.eval universalLeft universalRight))
          F.realizations =
        List.replicate F.realizations.length
          (F.recipe.erasedShape.eval
            (HPAtom.eval universalLeft universalRight)) := by
    simpa using
      (List.eq_replicate_of_mem
        (a := F.recipe.erasedShape.eval
          (HPAtom.eval universalLeft universalRight))
        (l := List.map
          (fun w =>
            (collapseWord w).eval
              (HPAtom.eval universalLeft universalRight))
          F.realizations)
        (by
          intro z hz
          rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
          rw [F.collapse_word w hw]))
  rw [hmap, List.prod_replicate]

end BFam

/-- A plain list of labelled words all collapses to one erased Hall-pair word. -/
def SCShape
    {M N : ℕ}
    (shape : CWord HPAtom)
    (words : List (LabelledWord M N)) : Prop :=
  ∀ w ∈ words, collapseWord w = shape

lemma collapsed_length_same
    {M N : ℕ}
    {shape : CWord HPAtom}
    {words : List (LabelledWord M N)}
    (hsame : SCShape shape words) :
    collapsedListEval words =
      (shape.eval (HPAtom.eval universalLeft universalRight)) ^ words.length := by
  rw [collapsedListEval]
  have hmap :
      List.map
          (fun w =>
            (collapseWord w).eval
              (HPAtom.eval universalLeft universalRight))
          words =
        List.replicate words.length
          (shape.eval (HPAtom.eval universalLeft universalRight)) := by
    simpa using
      (List.eq_replicate_of_mem
        (a := shape.eval (HPAtom.eval universalLeft universalRight))
        (l := List.map
          (fun w =>
            (collapseWord w).eval
              (HPAtom.eval universalLeft universalRight))
          words)
        (by
          intro z hz
          rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
          rw [hsame w hw]))
  rw [hmap, List.prod_replicate]

/--
A final concrete block of words represents the collapsed value of one complete
`BFam` packet if it has the packet's erased shape and the packet's
length. Notice that this deliberately forgets the individual labels: after
collapse, label order inside such a block is irrelevant because every term has
exactly the same collapsed value.
-/
def CPFor
    {M N : ℕ}
    (F : BFam M N)
    (words : List (LabelledWord M N)) : Prop :=
  SCShape F.recipe.erasedShape words ∧
    words.length = F.realizations.length

namespace CPFor

lemma collapsed_list_family
    {M N : ℕ}
    {F : BFam M N}
    {words : List (LabelledWord M N)}
    (hpacket : CPFor F words) :
    collapsedListEval words = collapsedListEval F.realizations := by
  rcases hpacket with ⟨hsame, hlength⟩
  rw [collapsed_length_same hsame,
    BFam.collapsed_shape_length F,
    hlength]

end CPFor

/--
A word list is packeted, for collapsed evaluation purposes, by a family list if
it splits into consecutive blocks, one block for each family, and each block has
the erased shape and length of that family.

This is intentionally weaker than exact equality with
`BFam.realizationList families`; it is exactly the amount of information
needed to build a `BFam.Expansion`.
-/
inductive CPBy
    {M N : ℕ} :
    List (BFam M N) → List (LabelledWord M N) → Prop where
  | nil :
      CPBy [] []
  | cons
      (F : BFam M N)
      (families : List (BFam M N))
      (packet rest : List (LabelledWord M N))
      (hpacket : CPFor F packet)
      (hrest : CPBy families rest) :
      CPBy (F :: families) (packet ++ rest)

namespace CPBy

lemma collapsed_eval_realization
    {M N : ℕ}
    {families : List (BFam M N)}
    {words : List (LabelledWord M N)}
    (hpacketed : CPBy families words) :
    collapsedListEval words =
      collapsedListEval (BFam.realizationList families) := by
  induction hpacketed with
  | nil =>
      simp [BFam.realizationList, collapsedListEval]
  | cons F families packet rest hpacket hrest ih =>
      rw [BFam.realizationList_cons]
      rw [BRecipe.collapsed_eval_append, BRecipe.collapsed_eval_append]
      rw [CPFor.collapsed_list_family hpacket]
      rw [ih]

end CPBy

/--
The corrected reachable target. The final list need not be literally
`BFam.realizationList families`. It only needs a consecutive collapsed
packet decomposition. This avoids the false one-swap family theorem.
-/
def InverseCollapsedReachable
    (M N : ℕ) : Prop :=
  ∃ families : List (BFam M N),
  ∃ words : List (LabelledWord M N),
    LWRw
      (inverseLeftTrace
        (labelledLeftAtoms M N)
        (labelledRightAtoms M N))
      words ∧
    CPBy families words

lemma collapsed_list_rewrites
    {M N : ℕ}
    {L R : List (LabelledWord M N)}
    (h : LWRw L R) :
    collapsedListEval R = collapsedListEval L := by
  calc
    collapsedListEval R = collapseHom M N (labelledListEval R) := by
      exact (collapse_labelled_eval R).symm
    _ = collapseHom M N (labelledListEval L) := by
      rw [labelled_list_rewrites h]
    _ = collapsedListEval L := by
      exact collapse_labelled_eval L

/-- The main soundness theorem for the corrected scheduler target. -/
theorem nonempty_collapsed_reachable
    {M N : ℕ}
    (hreachable : InverseCollapsedReachable M N) :
    Nonempty (BFam.Expansion M N) := by
  rcases hreachable with ⟨families, words, hrewrite, hpacketed⟩
  refine ⟨{
    families := families
    collapsed_eval_eq := ?_ }⟩
  calc
    collapsedListEval (BFam.realizationList families) =
        collapsedListEval words := by
      exact (CPBy.collapsed_eval_realization hpacketed).symm
    _ = collapsedListEval
        (inverseLeftTrace
          (labelledLeftAtoms M N)
          (labelledRightAtoms M N)) := by
      exact collapsed_list_rewrites hrewrite
    _ = ⁅universalLeft ^ M, universalRight ^ N⁆ := by
      exact collapsed_labelled_atoms M N

/-- Zero-left case for the corrected scheduler target. -/
lemma collapsed_reachable_left
    (N : ℕ) :
    InverseCollapsedReachable 0 N := by
  refine ⟨[], [], ?_, ?_⟩
  · simpa [labelledLeftAtoms, inverseLeftTrace] using
      (Relation.ReflTransGen.refl :
        LWRw ([] : List (LabelledWord 0 N)) [])
  · exact CPBy.nil

/-- Zero-right case for the corrected scheduler target. -/
lemma inverse_collapsed_reachable
    (M : ℕ) :
    InverseCollapsedReachable M 0 := by
  refine ⟨[], [], ?_, ?_⟩
  · simpa [labelledRightAtoms,
      inverse_left_nil (labelledLeftAtoms M 0)] using
      (Relation.ReflTransGen.refl :
        LWRw ([] : List (LabelledWord M 0)) [])
  · exact CPBy.nil

/-- A not-yet-closed packet of words of one target family shape. -/
structure PCPkt
    (M N : ℕ) where
  family : BFam M N
  words : List (LabelledWord M N)
  same_shape : SCShape family.recipe.erasedShape words
  length_le : words.length ≤ family.realizations.length

namespace PCPkt

/-- A partial packet is closed exactly when its length has reached the family size. -/
def Closed
    {M N : ℕ}
    (P : PCPkt M N) : Prop :=
  P.words.length = P.family.realizations.length

/-- A closed partial packet is a genuine collapsed packet. -/
lemma collapsed_packet_closed
    {M N : ℕ}
    (P : PCPkt M N)
    (hclosed : P.Closed) :
    CPFor P.family P.words := by
  exact ⟨P.same_shape, hclosed⟩

/-- Append one word of the right erased shape, provided the target length is not exceeded. -/
def push
    {M N : ℕ}
    (P : PCPkt M N)
    (w : LabelledWord M N)
    (hwshape : collapseWord w = P.family.recipe.erasedShape)
    (hlen : P.words.length + 1 ≤ P.family.realizations.length) :
    PCPkt M N where
  family := P.family
  words := P.words ++ [w]
  same_shape := by
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact P.same_shape u hu
    · rw [List.mem_singleton] at hu
      subst u
      exact hwshape
  length_le := by
    simpa using hlen

@[simp]
lemma push_words
    {M N : ℕ}
    (P : PCPkt M N)
    (w : LabelledWord M N)
    (hwshape hlen) :
    (P.push w hwshape hlen).words = P.words ++ [w] :=
  rfl

end PCPkt

/-- A list of partial packets; closed packets may be emitted as final packets. -/
abbrev PartialCollapsedState (M N : ℕ) :=
  List (PCPkt M N)

/--
Find-or-create update operation for a correction word.

The intended implementation is:
* the family is `B.family.correction A.family` at the appropriate history level;
* the word is `labelledWordCorrection b a`;
* if a partial packet for that family is already open, push the word there;
* otherwise create a new partial packet of that family with one word.

The two obligations that replace the false theorem are just shape and length:
no complete packet is claimed after a single swap.
-/
structure CorrectionSlotUpdate
    {M N : ℕ}
    (state state' : PartialCollapsedState M N)
    (F : BFam M N)
    (w : LabelledWord M N) : Prop where
  same_shape : collapseWord w = F.recipe.erasedShape
  length_accounting : True

/--
Close all partial packets. This is the finite arithmetic endpoint of the
scheduler: every opened packet has received exactly the family length many
correction words.
-/
def PartialPacketsClosed
    {M N : ℕ}
    (state : PartialCollapsedState M N) : Prop :=
  ∀ P ∈ state, P.Closed

/-- Convert a fully closed partial state to a collapsed packet decomposition. -/
lemma CPBy.closed_partial_state
    {M N : ℕ}
    (state : PartialCollapsedState M N)
    (hclosed : PartialPacketsClosed state) :
    CPBy
      (state.map PCPkt.family)
      (state.flatMap PCPkt.words) := by
  induction state with
  | nil =>
      simpa [PartialPacketsClosed] using
        (CPBy.nil :
          CPBy ([] : List (BFam M N)) [])
  | cons P state ih =>
      have hP : P.Closed := hclosed P (by simp)
      have hstate : PartialPacketsClosed state := by
        intro Q hQ
        exact hclosed Q (by simp [hQ])
      simpa [List.map_cons, List.flatMap_cons] using
        CPBy.cons P.family (state.map PCPkt.family)
          P.words (state.flatMap PCPkt.words)
          (P.collapsed_packet_closed hP)
          (ih hstate)

lemma support_val_congr
    {K : ℕ}
    {support support' : Finset (Fin K)}
    (h : support = support')
    (hsupport : support.Nonempty)
    (hsupport' : support'.Nonempty)
    (i : Fin K) :
    (supportRank support hsupport i).val =
      (supportRank support' hsupport' i).val := by
  subst support'
  rfl

lemma relabelWord_heq
    {M N M' N' M'' N'' : ℕ}
    (hM : M' = M'')
    (hN : N' = N'')
    (left : Fin M → Fin M')
    (right : Fin N → Fin N')
    (left' : Fin M → Fin M'')
    (right' : Fin N → Fin N'')
    (hleft : ∀ i, HEq (left i) (left' i))
    (hright : ∀ j, HEq (right j) (right' j))
    (w : CWord (LabelledAtom M N)) :
    HEq (relabelWord left right w) (relabelWord left' right' w) := by
  subst M''
  subst N''
  have hleft' : left = left' := by
    funext i
    exact eq_of_heq (hleft i)
  have hright' : right = right' := by
    funext j
    exact eq_of_heq (hright j)
  rw [hleft', hright']

lemma LRecipe.label_lin_instantiate
    {M N : ℕ}
    (R : LRecipe)
    (left : Fin R.leftDegree ↪o Fin M)
    (right : Fin R.rightDegree ↪o Fin N) :
    LRecipe.ofLabelLinear
        (R.instantiate left right)
        (by simpa using R.positive)
        (label_linear_relabel left.toEmbedding right.toEmbedding R.linear) =
      R := by
  have hleftSupport :
      leftLabelSupport (R.instantiate left right) =
        Finset.univ.map left.toEmbedding := by
    change
      leftLabelSupport (relabelWord left.toEmbedding right.toEmbedding R.word) =
        Finset.univ.map left.toEmbedding
    rw [left_label_relabel, R.left_support_full]
  have hrightSupport :
      rightLabelSupport (R.instantiate left right) =
        Finset.univ.map right.toEmbedding := by
    change
      rightLabelSupport (relabelWord left.toEmbedding right.toEmbedding R.word) =
        Finset.univ.map right.toEmbedding
    rw [right_label_relabel, R.right_support_full]
  have hleftDegree : 0 < R.leftDegree := by
    rw [← R.erased_left_degree]
    exact R.positive.left
  have hrightDegree : 0 < R.rightDegree := by
    rw [← R.erased_shape_degree]
    exact R.positive.right
  let leftImage := Finset.univ.map left.toEmbedding
  let rightImage := Finset.univ.map right.toEmbedding
  have hleftImageNonempty : leftImage.Nonempty := by
    exact Finset.Nonempty.map (f := left.toEmbedding)
      (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hleftDegree))
  have hrightImageNonempty : rightImage.Nonempty := by
    exact Finset.Nonempty.map (f := right.toEmbedding)
      (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hrightDegree))
  let leftBack : Fin M → Fin R.leftDegree :=
    fun i => Fin.cast (by simp [leftImage]) (supportRank leftImage hleftImageNonempty i)
  let rightBack : Fin N → Fin R.rightDegree :=
    fun j => Fin.cast (by simp [rightImage]) (supportRank rightImage hrightImageNonempty j)
  have hleft :
      left = leftImage.orderEmbOfFin (by simp [leftImage]) := by
    apply Finset.orderEmbOfFin_unique'
    intro index
    simp [leftImage]
  have hright :
      right = rightImage.orderEmbOfFin (by simp [rightImage]) := by
    apply Finset.orderEmbOfFin_unique'
    intro index
    simp [rightImage]
  have hleftBack (i : Fin R.leftDegree) :
      leftBack (left i) = i := by
    simp only [leftBack]
    have happ :
        left i = leftImage.orderEmbOfFin (by simp [leftImage]) i :=
      DFunLike.congr_fun hleft i
    rw [happ]
    apply Fin.ext
    simpa using congrArg Fin.val
      (support_emb_fin leftImage hleftImageNonempty
        (Fin.cast (by simp [leftImage]) i))
  have hrightBack (j : Fin R.rightDegree) :
      rightBack (right j) = j := by
    simp only [rightBack]
    have happ :
        right j = rightImage.orderEmbOfFin (by simp [rightImage]) j :=
      DFunLike.congr_fun hright j
    rw [happ]
    apply Fin.ext
    simpa using congrArg Fin.val
      (support_emb_fin rightImage hrightImageNonempty
        (Fin.cast (by simp [rightImage]) j))
  have hword :
      relabelWord leftBack rightBack (R.instantiate left right) = R.word := by
    exact relabel_inverse_support
      left right leftBack rightBack R.word
      (fun i _hi => hleftBack i) (fun j _hj => hrightBack j)
  have hDpositive :
      (collapseWord (R.instantiate left right)).PBPos := by
    simpa using R.positive
  have hDlinear : LabelLinear (R.instantiate left right) :=
    label_linear_relabel left.toEmbedding right.toEmbedding R.linear
  have hleftNonempty :
      (leftLabelSupport (R.instantiate left right)).Nonempty :=
    label_support_positive hDlinear hDpositive
  have hrightNonempty :
      (rightLabelSupport (R.instantiate left right)).Nonempty :=
    label_nonempty_positive hDlinear hDpositive
  have hleftCard :
      (leftLabelSupport (R.instantiate left right)).card = R.leftDegree := by
    simp [hleftSupport]
  have hrightCard :
      (rightLabelSupport (R.instantiate left right)).card = R.rightDegree := by
    simp [hrightSupport]
  have hleftRank (i : Fin M) :
      HEq (supportRank (leftLabelSupport (R.instantiate left right)) hleftNonempty i)
        (leftBack i) := by
    apply (Fin.heq_ext_iff hleftCard).2
    simpa only [leftBack, Fin.val_cast] using
      support_val_congr hleftSupport hleftNonempty hleftImageNonempty i
  have hrightRank (j : Fin N) :
      HEq (supportRank (rightLabelSupport (R.instantiate left right)) hrightNonempty j)
        (rightBack j) := by
    apply (Fin.heq_ext_iff hrightCard).2
    simpa only [rightBack, Fin.val_cast] using
      support_val_congr hrightSupport hrightNonempty hrightImageNonempty j
  have hnormalized :
      HEq
        (relabelWord
          (supportRank (leftLabelSupport (R.instantiate left right)) hleftNonempty)
          (supportRank (rightLabelSupport (R.instantiate left right)) hrightNonempty)
          (R.instantiate left right))
        (relabelWord leftBack rightBack (R.instantiate left right)) := by
    exact relabelWord_heq hleftCard hrightCard _ _ _ _
      hleftRank hrightRank (R.instantiate left right)
  simp only [LRecipe.ofLabelLinear]
  rw [LRecipe.mk.injEq]
  simp only [hleftSupport, hrightSupport, Finset.card_map, Finset.card_univ,
    Fintype.card_fin]
  refine ⟨trivial, trivial, ?_⟩
  exact hnormalized.trans (heq_of_eq hword)

lemma order_embedding_univ
    {r M : ℕ}
    {left left' : Fin r ↪o Fin M}
    (h :
      Finset.univ.map left.toEmbedding =
        Finset.univ.map left'.toEmbedding) :
    left = left' := by
  apply Set.powersetCard.ofFinEmbEquiv.injective
  apply Subtype.ext
  simpa [Set.powersetCard.ofFinEmbEquiv_apply,
    Set.powersetCard.val_ofFinEmb] using h

lemma LRecipe.instantiate_injective
    {M N : ℕ}
    (R : LRecipe) :
    Function.Injective
      (fun pair : (Fin R.leftDegree ↪o Fin M) ×
          (Fin R.rightDegree ↪o Fin N) =>
        R.instantiate pair.1 pair.2) := by
  rintro ⟨left, right⟩ ⟨left', right'⟩ hword
  apply Prod.ext
  · apply order_embedding_univ
    have hsupport := congrArg leftLabelSupport hword
    calc
      Finset.univ.map left.toEmbedding =
          leftLabelSupport (R.instantiate left right) := by
        change
          Finset.univ.map left.toEmbedding =
            leftLabelSupport (relabelWord left.toEmbedding right.toEmbedding R.word)
        rw [left_label_relabel, R.left_support_full]
      _ = leftLabelSupport (R.instantiate left' right') := hsupport
      _ = Finset.univ.map left'.toEmbedding := by
        change
          leftLabelSupport (relabelWord left'.toEmbedding right'.toEmbedding R.word) =
            Finset.univ.map left'.toEmbedding
        rw [left_label_relabel, R.left_support_full]
  · apply order_embedding_univ
    have hsupport := congrArg rightLabelSupport hword
    calc
      Finset.univ.map right.toEmbedding =
          rightLabelSupport (R.instantiate left right) := by
        change
          Finset.univ.map right.toEmbedding =
            rightLabelSupport (relabelWord left.toEmbedding right.toEmbedding R.word)
        rw [right_label_relabel, R.right_support_full]
      _ = rightLabelSupport (R.instantiate left' right') := hsupport
      _ = Finset.univ.map right'.toEmbedding := by
        change
          rightLabelSupport (relabelWord left'.toEmbedding right'.toEmbedding R.word) =
            Finset.univ.map right'.toEmbedding
        rw [right_label_relabel, R.right_support_full]

lemma LRecipe.instantiations_nodup
    {M N : ℕ}
    (R : LRecipe) :
    (R.instantiations M N).Nodup := by
  rw [LRecipe.instantiations]
  let lefts : List (Fin R.leftDegree → Fin M) := do
    let left ← (Finset.univ : Finset (Fin R.leftDegree ↪o Fin M)).toList
    pure left
  let rights : List (Fin R.rightDegree → Fin N) := do
    let right ← (Finset.univ : Finset (Fin R.rightDegree ↪o Fin N)).toList
    pure right
  change (lefts.flatMap fun left => rights.map fun right =>
    R.instantiate left right).Nodup
  have hlefts : lefts.Nodup := by
    dsimp [lefts]
    rw [← List.map_eq_flatMap]
    exact
      (Finset.nodup_toList
        (Finset.univ : Finset (Fin R.leftDegree ↪o Fin M))).map
          (fun _ _ h => DFunLike.coe_injective h)
  have hrights : rights.Nodup := by
    dsimp [rights]
    rw [← List.map_eq_flatMap]
    exact
      (Finset.nodup_toList
        (Finset.univ : Finset (Fin R.rightDegree ↪o Fin N))).map
          (fun _ _ h => DFunLike.coe_injective h)
  have hleft_mem :
      ∀ {left}, left ∈ lefts →
        ∃ left' : Fin R.leftDegree ↪o Fin M, (left' : Fin R.leftDegree → Fin M) = left := by
    intro left hleft
    simpa [lefts, eq_comm] using hleft
  have hright_mem :
      ∀ {right}, right ∈ rights →
        ∃ right' : Fin R.rightDegree ↪o Fin N,
          (right' : Fin R.rightDegree → Fin N) = right := by
    intro right hright
    simpa [rights, eq_comm] using hright
  have hinjective_on :
      ∀ {left left' right right'},
        left ∈ lefts → left' ∈ lefts →
          right ∈ rights → right' ∈ rights →
            R.instantiate left right = R.instantiate left' right' →
              left = left' ∧ right = right' := by
    intro left left' right right' hleft hleft' hright hright' hword
    rcases hleft_mem hleft with ⟨leftEmb, rfl⟩
    rcases hleft_mem hleft' with ⟨leftEmb', rfl⟩
    rcases hright_mem hright with ⟨rightEmb, rfl⟩
    rcases hright_mem hright' with ⟨rightEmb', rfl⟩
    have hpairs : (leftEmb, rightEmb) = (leftEmb', rightEmb') := by
      apply R.instantiate_injective
      exact hword
    exact ⟨congrArg (fun pair => (pair.1 : Fin R.leftDegree → Fin M)) hpairs,
      congrArg (fun pair => (pair.2 : Fin R.rightDegree → Fin N)) hpairs⟩
  rw [List.nodup_flatMap]
  constructor
  · intro left hleft
    exact hrights.map_on
      (fun _right hright _right' hright' hword =>
        (hinjective_on hleft hleft hright hright' hword).2)
  · exact hlefts.imp_of_mem fun hleft hleft' hne => by
      change List.Disjoint _ _
      rw [List.disjoint_left]
      intro word hword hword'
      rcases List.mem_map.mp hword with ⟨right, hright, rfl⟩
      rcases List.mem_map.mp hword' with ⟨right', hright', hwords⟩
      exact hne (hinjective_on hleft hleft' hright hright' hwords.symm).1

lemma BFam.linlabel_lineq_meminstanti
    {M N : ℕ}
    (w : CWord (LabelledAtom M N))
    (hpositive : (collapseWord w).PBPos)
    (hlinear : LabelLinear w)
    {D : CWord (LabelledAtom M N)}
    (hD :
      D ∈ (LRecipe.ofLabelLinear w hpositive hlinear).instantiations M N)
    (hDpositive : (collapseWord D).PBPos)
    (hDlinear : LabelLinear D) :
    BFam.ofLinear M N
        (LRecipe.ofLabelLinear D hDpositive hDlinear) =
      BFam.ofLinear M N
        (LRecipe.ofLabelLinear w hpositive hlinear) := by
  rw [LRecipe.mem_instantiations_iff] at hD
  rcases hD with ⟨left, right, rfl⟩
  congr 1
  exact LRecipe.label_lin_instantiate
    (LRecipe.ofLabelLinear w hpositive hlinear) left right

lemma family_label_raw
    {M N : ℕ}
    {T : DFTerm M N (inverseLabelledCollection M N).factors.length}
    (hT : T ∈ inverseDecoratedTerms M N) :
    ∃ hpositive : T.erasedShape.PBPos,
      ∃ hlinear : LabelLinear T.decorated.word,
        T.family =
          BFam.ofLinear M N
            (LRecipe.ofLabelLinear T.decorated.word hpositive hlinear) := by
  rcases List.mem_ofFn.mp hT with ⟨index, rfl⟩
  refine ⟨?_, ?_, rfl⟩
  · exact
      (inverseLabelledCollection M N).factors_positive
        ((inverseLabelledCollection M N).factors.get index)
        (List.get_mem _ index)
  · exact
      inverse_labelled_linear M N
        ((inverseLabelledCollection M N).factors.get index)
        (List.get_mem _ index)

lemma family_raw_realizations
    {M N : ℕ}
    {T U : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hT : T ∈ inverseDecoratedTerms M N)
    (hU : U ∈ inverseDecoratedTerms M N)
    (hword : U.decorated.word ∈ T.family.realizations) :
    T.family = U.family := by
  rcases family_label_raw hT with
    ⟨hTpositive, hTlinear, hTfamily⟩
  rcases family_label_raw hU with
    ⟨hUpositive, hUlinear, hUfamily⟩
  rw [hTfamily] at hword ⊢
  rw [hUfamily]
  exact
    (BFam.linlabel_lineq_meminstanti
      T.decorated.word hTpositive hTlinear hword hUpositive hUlinear).symm

lemma realizations_nodup_raw
    {M N : ℕ}
    {T : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hT : T ∈ inverseDecoratedTerms M N) :
    T.family.realizations.Nodup := by
  rcases family_label_raw hT with
    ⟨hpositive, hlinear, hfamily⟩
  rw [hfamily]
  exact
    (LRecipe.ofLabelLinear T.decorated.word hpositive hlinear).instantiations_nodup

lemma family_realizations_overlap
    {M N : ℕ}
    {T U : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hT : T ∈ inverseDecoratedTerms M N)
    (hU : U ∈ inverseDecoratedTerms M N)
    {word : CWord (LabelledAtom M N)}
    (hwordT : word ∈ T.family.realizations)
    (hwordU : word ∈ U.family.realizations) :
    T.family = U.family := by
  rcases inverse_decorated_realizations
      hT hwordT with ⟨V, hV, hVword⟩
  have hTV :
      T.family = V.family :=
    family_raw_realizations hT hV (by
      simpa [hVword] using hwordT)
  have hUV :
      U.family = V.family :=
    family_raw_realizations hU hV (by
      simpa [hVword] using hwordU)
  exact hTV.trans hUV.symm

lemma realization_distinct_nodup
    (M N : ℕ) :
    (BFam.realizationList
      (distinctBlockFamilies (inverseDecoratedTerms M N))).Nodup := by
  rw [BFam.realizationList, List.nodup_flatMap]
  constructor
  · intro F hF
    rcases distinct_block_families.mp hF with ⟨T, hT, rfl⟩
    exact realizations_nodup_raw hT
  · exact
      (distinct_families_nodup
        (inverseDecoratedTerms M N)).imp_of_mem fun hF hG hne => by
          change List.Disjoint _ _
          rw [List.disjoint_left]
          intro word hwordF hwordG
          apply hne
          rcases distinct_block_families.mp hF with ⟨T, hT, rfl⟩
          rcases distinct_block_families.mp hG with ⟨U, hU, rfl⟩
          exact family_realizations_overlap
            hT hU hwordF hwordG

lemma nodup_flat_insert
    {α : Type*}
    [DecidableEq α]
    (a : α)
    (supports : List (Finset α))
    (hnodup : supports.Nodup)
    (ha : ∀ support ∈ supports, a ∉ support) :
    (supports.flatMap fun support => [support, insert a support]).Nodup := by
  rw [List.nodup_flatMap]
  constructor
  · intro support hsupport
    rw [List.nodup_cons]
    constructor
    · intro h
      simp only [List.mem_singleton] at h
      exact (ha support hsupport) (by rw [h]; simp)
    · simp
  · exact hnodup.imp_of_mem fun {support support'} hsupport hsupport' hne => by
      change List.Disjoint [support, insert a support]
        [support', insert a support']
      rw [List.disjoint_left]
      intro entry hentry hentry'
      apply hne
      have herase : entry.erase a = support := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry
        rcases hentry with rfl | rfl
        · simp [ha _ hsupport]
        · simp [ha _ hsupport]
      have herase' : entry.erase a = support' := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hentry'
        rcases hentry' with rfl | rfl
        · simp [ha _ hsupport']
        · simp [ha _ hsupport']
      exact herase.symm.trans herase'

lemma label_flat_atom
    {M N : ℕ}
    (a : LabelledAtom M N)
    (L : List (CWord (LabelledAtom M N))) :
    (L.flatMap (inverseConjugateAtom a)).map labelSupport =
      (L.map labelSupport).flatMap fun support => [support, insert a support] := by
  induction L with
  | nil => rfl
  | cons D L ih =>
      simp [inverseConjugateAtom, label_swap_word,
        Finset.union_comm, ih]

lemma label_support_inverse
    {M N : ℕ}
    (x : LabelledAtom M N) :
    ∀ ys D, D ∈ inverseRightTrace x ys →
      ∃ y ∈ ys, y ∈ labelSupport D
  | [], D, hD => by
      simp [inverseRightTrace] at hD
  | y :: ys, D, hD => by
      simp only [inverseRightTrace, List.mem_cons] at hD
      rcases hD with rfl | hD
      · exact ⟨y, by simp, by simp [labelSupport]⟩
      · rcases List.mem_flatMap.mp hD with ⟨F, hF, hDF⟩
        rcases label_support_inverse
            x ys F hF with ⟨z, hzys, hzF⟩
        exact ⟨z, by simp [hzys],
          label_support_subset [y] F D hDF hzF⟩

lemma label_inverse_nodup
    {M N : ℕ}
    (x : LabelledAtom M N) :
    ∀ ys : List (LabelledAtom M N),
      ys.Nodup →
        x ∉ ys →
          ((inverseRightTrace x ys).map labelSupport).Nodup
  | [], _hys, _hxys => by
      simp [inverseRightTrace]
  | y :: ys, hys, hxys => by
      have hyys : y ∉ ys := (List.nodup_cons.mp hys).1
      have hysNodup : ys.Nodup := (List.nodup_cons.mp hys).2
      have hxys' : x ∉ ys := by
        intro hx
        exact hxys (by simp [hx])
      rw [inverseRightTrace, List.map_cons, List.nodup_cons]
      constructor
      · intro hbase
        rcases List.mem_map.mp hbase with ⟨E, hE, heq⟩
        rcases List.mem_flatMap.mp hE with ⟨F, hF, hFE⟩
        rcases label_support_inverse
            x ys F hF with ⟨z, hzys, hzF⟩
        have hzE :
            z ∈ labelSupport E :=
          label_support_subset [y] F E hFE hzF
        have hzbase :
            z ∈ labelSupport (.commutator (.atom x) (.atom y)) := by
          simpa [heq] using hzE
        simp only [labelSupport, Finset.mem_union, Finset.mem_singleton] at hzbase
        rcases hzbase with hzx | hzy
        · subst z
          exact hxys' hzys
        · subst z
          exact hyys hzys
      · rw [inverseTraceList]
        simp only [inverseConjTrace, List.flatMap_singleton]
        rw [label_flat_atom]
        apply nodup_flat_insert
        · exact label_inverse_nodup x ys hysNodup hxys'
        · intro support hsupport
          rcases List.mem_map.mp hsupport with ⟨F, hF, rfl⟩
          intro hyF
          have hy :
              y ∈ insert x ys.toFinset :=
            label_subset_inverse x ys F hF hyF
          rcases Finset.mem_insert.mp hy with hyx | hyys'
          · exact hxys (by simp [hyx])
          · exact hyys (List.mem_toFinset.mp hyys')

lemma label_support_trace
    {M N : ℕ} :
    ∀ (xs ys : List (LabelledAtom M N))
      (D : CWord (LabelledAtom M N)),
      D ∈ inverseLeftTrace xs ys →
      ∃ x ∈ xs, x ∈ labelSupport D
  | [], ys, D, hD => by
      simp [inverseLeftTrace] at hD
  | x :: xs, ys, D, hD => by
      rw [inverseLeftTrace, List.mem_append] at hD
      rcases hD with hD | hD
      · rcases List.mem_flatMap.mp hD with ⟨F, hF, hFD⟩
        rcases label_support_trace
            xs ys F hF with ⟨z, hzxs, hzF⟩
        exact ⟨z, by simp [hzxs],
          label_support_subset [x] F D hFD hzF⟩
      · exact ⟨x, by simp, label_support_right x ys D hD⟩

lemma label_support_nodup
    {M N : ℕ} :
    ∀ xs ys : List (LabelledAtom M N),
      xs.Nodup →
        ys.Nodup →
          Disjoint xs.toFinset ys.toFinset →
            ((inverseLeftTrace xs ys).map labelSupport).Nodup
  | [], ys, _hxs, _hys, _hdisjoint => by
      simp [inverseLeftTrace]
  | x :: xs, ys, hxs, hys, hdisjoint => by
      have hxxs : x ∉ xs := (List.nodup_cons.mp hxs).1
      have hxsNodup : xs.Nodup := (List.nodup_cons.mp hxs).2
      have hdisjointInsert :
          Disjoint (insert x xs.toFinset) ys.toFinset := by
        simpa [List.toFinset_cons] using hdisjoint
      have hxys : x ∉ ys := by
        intro hxys
        exact Finset.disjoint_left.mp hdisjointInsert
          (Finset.mem_insert_self x xs.toFinset) (List.mem_toFinset.mpr hxys)
      have hdisjoint' :
          Disjoint xs.toFinset ys.toFinset :=
        Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hdisjointInsert
      have htail :
          ((inverseLeftTrace xs ys).map labelSupport).Nodup :=
        label_support_nodup
          xs ys hxsNodup hys hdisjoint'
      rw [inverseLeftTrace, List.map_append]
      apply List.Nodup.append
      · rw [inverseTraceList]
        simp only [inverseConjTrace, List.flatMap_singleton]
        rw [label_flat_atom]
        apply nodup_flat_insert
        · exact htail
        · intro support hsupport
          rcases List.mem_map.mp hsupport with ⟨F, hF, rfl⟩
          intro hxF
          have hx :
              x ∈ xs.toFinset ∪ ys.toFinset :=
            label_subset_trace xs ys F hF hxF
          rcases Finset.mem_union.mp hx with hxxs' | hxys'
          · exact hxxs (List.mem_toFinset.mp hxxs')
          · exact hxys (List.mem_toFinset.mp hxys')
      · exact label_inverse_nodup x ys hys hxys
      · change
          List.Disjoint
            ((inverseTraceList [x]
              (inverseLeftTrace xs ys)).map labelSupport)
            ((inverseRightTrace x ys).map labelSupport)
        rw [List.disjoint_left]
        intro support hsupportLeft hsupportRight
        rcases List.mem_map.mp hsupportLeft with ⟨E, hE, heqE⟩
        rcases List.mem_flatMap.mp hE with ⟨F, hF, hFE⟩
        rcases label_support_trace
            xs ys F hF with ⟨z, hzxs, hzF⟩
        have hzE :
            z ∈ labelSupport E :=
          label_support_subset [x] F E hFE hzF
        rcases List.mem_map.mp hsupportRight with ⟨D, hD, heqD⟩
        have hzD :
            z ∈ labelSupport D := by
          rw [heqD, ← heqE]
          exact hzE
        have hz :
            z ∈ insert x ys.toFinset :=
          label_subset_inverse x ys D hD hzD
        rcases Finset.mem_insert.mp hz with hzx | hzys
        · subst z
          exact hxxs hzxs
        · exact Finset.disjoint_left.mp hdisjoint'
            (List.mem_toFinset.mpr hzxs) hzys

lemma labelled_atoms_nodup
    (M N : ℕ) :
    (inverseLeftTrace
      (labelledLeftAtoms M N)
      (labelledRightAtoms M N)).Nodup := by
  apply List.Nodup.of_map labelSupport
  apply label_support_nodup
  · simp only [labelledLeftAtoms]
    exact List.nodup_ofFn_ofInjective fun _ _ h => Sum.inl.inj h
  · simp only [labelledRightAtoms]
    exact List.nodup_ofFn_ofInjective fun _ _ h => Sum.inr.inj h
  · rw [Finset.disjoint_left]
    intro a haLeft haRight
    have hleft :
        collapseLabel a = .left :=
      collapse_label_atoms
        (List.mem_toFinset.mp haLeft)
    have hright :
        collapseLabel a = .right :=
      collapse_labelled_atoms
        (List.mem_toFinset.mp haRight)
    rw [hleft] at hright
    cases hright

/--
The raw inverse trace is covered, with multiplicity, by the realization lists
of its distinct initial one-block linear families.
-/
lemma inverse_families_cover
    (M N : ℕ) :
    ∃ families : List (BFam M N),
      List.Perm
        (inverseLeftTrace
          (labelledLeftAtoms M N)
          (labelledRightAtoms M N))
        (BFam.realizationList families) := by
  refine
    ⟨distinctBlockFamilies (inverseDecoratedTerms M N), ?_⟩
  have hwords :
      decoratedFamilyList (inverseDecoratedTerms M N) =
        inverseLeftTrace
          (labelledLeftAtoms M N)
          (labelledRightAtoms M N) := by
    simp only [decoratedFamilyList, inverseDecoratedTerms,
      List.map_ofFn, Function.comp_def,
      inverseLabelledCollection, DFTerm.ofLabelLinear,
      DTerm.raw]
    exact List.ofFn_getElem
  apply (List.perm_ext_iff_of_nodup
    (labelled_atoms_nodup M N)
    (realization_distinct_nodup M N)).2
  intro word
  rw [← hwords]
  constructor
  · intro hword
    exact
      decorated_distinct_families
        (inverseDecoratedTerms M N) hword
  · intro hword
    exact realization_distinct_words M N hword

/-- One adjacent transposition is implemented by a concrete correction rewrite. -/
lemma packetize_adjacent_transposition
    {M N : ℕ}
    (P S : List (LabelledWord M N))
    (B A : LabelledWord M N) :
    LWRw
      (P ++ [B, A] ++ S)
      (P ++ [labelledWordCorrection B A, A, B] ++ S) :=
  LWRw.single_step P S B A

/-- Evaluation hom from the universal two-generator free group into any group. -/
def universalEvalHom
    {Q : Type*} [Group Q]
    (x y : Q) : UniversalGroup →* Q :=
  FreeGroup.lift (HPAtom.eval x y)

@[simp]
lemma universal_hom_left
    {Q : Type*} [Group Q]
    (x y : Q) :
    universalEvalHom x y universalLeft = x := by
  simp [universalEvalHom, universalLeft, HPAtom.eval]

@[simp]
lemma universal_hom_right
    {Q : Type*} [Group Q]
    (x y : Q) :
    universalEvalHom x y universalRight = y := by
  simp [universalEvalHom, universalRight, HPAtom.eval]

lemma universal_hom_word
    {Q : Type*} [Group Q]
    (x y : Q)
    (w : CWord HPAtom) :
    universalEvalHom x y
        (w.eval (HPAtom.eval universalLeft universalRight)) =
      w.eval (HPAtom.eval x y) := by
  induction w with
  | atom a =>
      cases a <;> simp [CWord.eval, HPAtom.eval]
  | commutator u v ihu ihv =>
      simp [CWord.eval_commutator, map_commutatorElement, ihu, ihv]

/-- Quotient-form admissible relations. -/
def AdmissibleRelations
    (M N : ℕ)
    {Q : Type*} [Group Q]
    (x y : Q) : Prop :=
  ∀ (w : CWord HPAtom) (c : ℤ),
    w.PBPos →
      c ∈ submodule M N w.pairLeftDegree w.pairRightDegree →
        w.eval (HPAtom.eval x y) ^ c = 1

/-- One signed diagonal finite-difference class. -/
structure DHFactor
    (M N : ℕ) where
  word : CWord HPAtom
  leftDegrees : List ℕ
  rightDegrees : List ℕ
  positive : word.PBPos
  left_pos : ∀ d ∈ leftDegrees, 0 < d
  right_pos : ∀ d ∈ rightDegrees, 0 < d
  left_degree_eq : word.pairLeftDegree = leftDegrees.sum
  right_degree_eq : word.pairRightDegree = rightDegrees.sum
  sign : ℤ

namespace DHFactor

def coeff
    {M N : ℕ}
    (H : DHFactor M N) : ℤ :=
  H.sign *
    (diagonalLeftProduct M H.leftDegrees *
      diagonalRightProduct N H.rightDegrees)

lemma coeff_mem_submodule
    {M N : ℕ}
    (H : DHFactor M N) :
    H.coeff ∈
      submodule M N H.word.pairLeftDegree H.word.pairRightDegree := by
  have hdiag :
      diagonalLeftProduct M H.leftDegrees *
          diagonalRightProduct N H.rightDegrees ∈
        submodule M N H.leftDegrees.sum H.rightDegrees.sum :=
    diagonal_products_submodule M N
      H.leftDegrees H.rightDegrees H.left_pos H.right_pos
  have hdiag' :
      diagonalLeftProduct M H.leftDegrees *
          diagonalRightProduct N H.rightDegrees ∈
        submodule M N H.word.pairLeftDegree H.word.pairRightDegree := by
    simpa [H.left_degree_eq, H.right_degree_eq] using hdiag
  simpa [coeff, smul_eq_mul, mul_assoc] using
    (submodule M N H.word.pairLeftDegree H.word.pairRightDegree).smul_mem
      H.sign hdiag'

def eval
    {M N : ℕ}
    {Q : Type*} [Group Q]
    (H : DHFactor M N)
    (x y : Q) : Q :=
  H.word.eval (HPAtom.eval x y) ^ H.coeff

lemma eval_admissible_relations
    {M N : ℕ}
    {Q : Type*} [Group Q]
    {x y : Q}
    (hrel : AdmissibleRelations M N x y)
    (H : DHFactor M N) :
    H.eval x y = 1 := by
  exact hrel H.word H.coeff H.positive H.coeff_mem_submodule

end DHFactor

/-- A signed diagonal class with an outer universal conjugator. -/
structure CDHistor
    (M N : ℕ) where
  factor : DHFactor M N
  conjugator : UniversalGroup

namespace CDHistor

def eval
    {M N : ℕ}
    {Q : Type*} [Group Q]
    (F : CDHistor M N)
    (x y : Q) : Q :=
  universalEvalHom x y F.conjugator *
    F.factor.eval x y *
    (universalEvalHom x y F.conjugator)⁻¹

lemma eval_admissible_relations
    {M N : ℕ}
    {Q : Type*} [Group Q]
    {x y : Q}
    (hrel : AdmissibleRelations M N x y)
    (F : CDHistor M N) :
    F.eval x y = 1 := by
  simp [eval, DHFactor.eval_admissible_relations hrel F.factor]

end CDHistor

/-- Product of conjugated diagonal-history factors. -/
def conjugatedDiagonalHistory
    {M N : ℕ}
    {Q : Type*} [Group Q]
    (Fs : List (CDHistor M N))
    (x y : Q) : Q :=
  (Fs.map fun F => F.eval x y).prod

lemma conjugated_history_relations
    {M N : ℕ}
    {Q : Type*} [Group Q]
    {x y : Q}
    (hrel : AdmissibleRelations M N x y) :
    ∀ Fs : List (CDHistor M N),
      conjugatedDiagonalHistory Fs x y = 1 := by
  intro Fs
  induction Fs with
  | nil =>
      simp [conjugatedDiagonalHistory]
  | cons F Fs ih =>
      change F.eval x y * conjugatedDiagonalHistory Fs x y = 1
      rw [CDHistor.eval_admissible_relations hrel F,
        ih, one_mul]

universe u

/--
The correct finite certificate target for `nonempty_trace`.

This is deliberately normal-closure-shaped: signed diagonal factors may be
conjugated. Therefore it does not assert an exact packet expansion and is not
subject to the parity/deficit invariants of the rewrite scheduler.
-/
structure CHCert
    (M N : ℕ) where
  factors : List (CDHistor M N)
  eval_eq :
    ∀ {Q : Type u} [Group Q] (x y : Q),
      ⁅x ^ M, y ^ N⁆ = conjugatedDiagonalHistory factors x y

namespace CHCert

lemma commutator_admissible_relations
    {M N : ℕ}
    (C : CHCert.{u} M N)
    {Q : Type u} [Group Q]
    (x y : Q)
    (hrel : AdmissibleRelations M N x y) :
    ⁅x ^ M, y ^ N⁆ = 1 := by
  exact (C.eval_eq x y).trans
    (conjugated_history_relations hrel C.factors)

def zero_left
    (N : ℕ) :
    CHCert.{u} 0 N where
  factors := []
  eval_eq := by
    intro Q _inst x y
    simp [conjugatedDiagonalHistory, commutatorElement_def]

def zero_right
    (M : ℕ) :
    CHCert.{u} M 0 where
  factors := []
  eval_eq := by
    intro Q _inst x y
    simp [conjugatedDiagonalHistory, commutatorElement_def]

end CHCert

namespace ANClos

lemma admissibleRelations_quotient
    (M N : ℕ)
    {G : Type*} [Group G]
    (x y : G) :
    AdmissibleRelations M N
      (QuotientGroup.mk' (subgroup M N x y) x)
      (QuotientGroup.mk' (subgroup M N x y) y) := by
  let q : G →* G ⧸ subgroup M N x y :=
    QuotientGroup.mk' (subgroup M N x y)
  change AdmissibleRelations M N (q x) (q y)
  intro w c hw hc
  have hmem :
      w.eval (HPAtom.eval x y) ^ c ∈ subgroup M N x y := by
    exact zpow_word_eval x y w c hw hc
  have hq :
      q (w.eval (HPAtom.eval x y) ^ c) = 1 :=
    (QuotientGroup.eq_one_iff
      (N := subgroup M N x y)
      (w.eval (HPAtom.eval x y) ^ c)).mpr hmem
  have hatoms :
      (fun a => q (HPAtom.eval x y a)) =
        HPAtom.eval (q x) (q y) := by
    funext a
    cases a <;> rfl
  rw [map_zpow, CWord.map_eval, hatoms] at hq
  exact hq

end ANClos

/-- Merge adjacent factors with the same erased Hall word. -/
def Factor.addSame
    {M N : ℕ}
    (F G : Factor M N)
    (hword : G.word = F.word) :
    Factor M N where
  word := F.word
  coefficient := F.coefficient + G.coefficient
  positive := F.positive
  coefficient_admissible := by
    have hG :
        G.coefficient ∈
          submodule M N F.word.pairLeftDegree F.word.pairRightDegree := by
      simpa [hword] using G.coefficient_admissible
    exact
      (submodule M N F.word.pairLeftDegree F.word.pairRightDegree).add_mem
        F.coefficient_admissible hG

lemma Factor.eval_muleval_addsame
    {M N : ℕ}
    {G : Type*} [Group G]
    (x y : G)
    (F E : Factor M N)
    (hword : E.word = F.word) :
    F.eval x y * E.eval x y =
      (F.addSame E hword).eval x y := by
  rw [Factor.eval, Factor.eval, Factor.addSame, Factor.eval]
  rw [hword]
  rw [← zpow_add]

/-- The first inverse-oriented Hall word used by the corrected right collector. -/
def rightLeftBase :
    CWord HPAtom :=
  .commutator (.atom .right) (.atom .left)

/-- The right correction emitted after grouping two copies of `[X, Y]`. -/
def rightLeftRight :
    CWord HPAtom :=
  .commutator rightLeftBase (.atom .right)

@[simp]
lemma eval_left_base
    {G : Type*} [Group G]
    (x y : G) :
    rightLeftBase.eval (HPAtom.eval x y) = ⁅y, x⁆ :=
  rfl

@[simp]
lemma eval_right_left
    {G : Type*} [Group G]
    (x y : G) :
    rightLeftRight.eval (HPAtom.eval x y) = ⁅⁅y, x⁆, y⁆ :=
  rfl

lemma commutator_element_signed
    {G : Type*} [Group G]
    (x y : G) :
    ⁅x, y ^ (2 : ℕ)⁆ =
      ⁅y, x⁆ ^ (-2 : ℤ) * ⁅⁅y, x⁆, y⁆ := by
  simp only [commutatorElement_def, pow_two]
  rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg,
    zpow_natCast, ← inv_pow]
  simp only [pow_two]
  simp [mul_inv_rev, mul_assoc]

def rightBaseTwo :
    Factor 1 2 where
  word := rightLeftBase
  coefficient := -2
  positive := by
    simp [rightLeftBase, CWord.PBPos]
  coefficient_admissible := by
    apply (submodule 1 2 1 1).neg_mem
    have hright :
        (Nat.choose 2 1 : ℤ) * 1 ∈ submodule 1 2 0 (1 + 0) :=
      choose_submodule_right 1
        (one_submodule_zero 1 2)
    have hleft :
        (Nat.choose 1 1 : ℤ) * ((Nat.choose 2 1 : ℤ) * 1) ∈
          submodule 1 2 (1 + 0) (1 + 0) :=
      choose_submodule_left 1 hright
    norm_num at hleft ⊢
    exact hleft

def rightFactorTwo :
    Factor 1 2 where
  word := rightLeftRight
  coefficient := 1
  positive := by
    simp [rightLeftRight, rightLeftBase,
      CWord.PBPos]
  coefficient_admissible := by
    change (1 : ℤ) ∈ submodule 1 2 1 2
    apply Submodule.subset_span
    refine
      ⟨[{ sign := .positive, degree := 1 }],
        [{ sign := .positive, degree := 2 }], ?_, ?_, ?_⟩
    all_goals simp [degreeSum, blockProduct, signedChoose]

lemma canonical_factors_two :
    ∃ factors : List (Factor 1 2),
      listEval universalLeft universalRight factors =
        ⁅universalLeft ^ 1, universalRight ^ 2⁆ := by
  refine ⟨[rightBaseTwo, rightFactorTwo], ?_⟩
  simpa [listEval, Factor.eval, rightBaseTwo,
    rightFactorTwo] using
    (commutator_element_signed universalLeft universalRight).symm

end HACoeff
end Towers
