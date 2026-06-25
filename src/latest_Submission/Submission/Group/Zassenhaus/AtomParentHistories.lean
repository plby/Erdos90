import Submission.Group.Zassenhaus.PacketScheduling
import Submission.Group.Zassenhaus.InverseConjTrace
import Submission.Group.Zassenhaus.FamilyOperationalCollector
import Submission.Group.Zassenhaus.TruncatedTraceEvaluation

/-!
# Exact atom-parent histories for the inverse-oriented raw Hall trace

The reusable inverse trace expands conjugation by a source atom before the
More3 collector groups positive terms into complete counted families.  At this
raw stage, a conjugation parent is therefore a `LabelledAtom`, not a
`BFam`: block-family recipes are required to have positive left and
right Hall degree and cannot represent a pure source atom.

This file records the exact finite raw-history recurrence and proves that
forgetting history recovers `inverseConjTrace`, `inverseRightTrace`, and
`inverseLeftTrace`.  The later family collector may attach one-block
families to the resulting positive words and then use family-level correction
packets.  This file is intentionally not imported by the existing collection
proof.
-/

namespace Submission
namespace TCTex
namespace RHRecurs

open HACoeff

/--
One raw inverse-trace history.  Root commutators remember their two source
atoms.  Every further history remembers the source atom across which an older
positive word was conjugated.
-/
inductive RHistor
    (M N : ℕ) where
  | hallPair
      (left right : LabelledAtom M N) :
      RHistor M N
  | conjugate
      (parent : LabelledAtom M N)
      (emitted : RHistor M N) :
      RHistor M N

namespace RHistor

/-- Labelled Hall word represented by one raw inverse-trace history. -/
def word
    {M N : ℕ} :
    RHistor M N →
      CWord (LabelledAtom M N)
  | .hallPair left right =>
      .commutator (.atom left) (.atom right)
  | .conjugate parent emitted =>
      .commutator (rootSwapWord emitted.word) (.atom parent)

@[simp]
lemma word_hallPair
    {M N : ℕ}
    (left right : LabelledAtom M N) :
    (hallPair left right).word =
      .commutator (.atom left) (.atom right) :=
  rfl

@[simp]
lemma word_conjugate
    {M N : ℕ}
    (parent : LabelledAtom M N)
    (emitted : RHistor M N) :
    (conjugate parent emitted).word =
      .commutator (rootSwapWord emitted.word) (.atom parent) :=
  rfl

end RHistor

/-- Expand one raw history across one source atom. -/
def conjugateAtomHistories
    {M N : ℕ}
    (parent : LabelledAtom M N)
    (emitted : RHistor M N) :
    List (RHistor M N) :=
  [emitted, .conjugate parent emitted]

@[simp]
lemma conjugate_atom_histories
    {M N : ℕ}
    (parent : LabelledAtom M N)
    (emitted : RHistor M N) :
    (conjugateAtomHistories parent emitted).map RHistor.word =
      inverseConjugateAtom parent emitted.word :=
  rfl

/-- Raw-history version of inverse-oriented conjugation by a source-atom list. -/
def inverseConjHistories
    {M N : ℕ} :
    List (LabelledAtom M N) →
      RHistor M N →
        List (RHistor M N)
  | [], emitted =>
      [emitted]
  | parent :: parents, emitted =>
      (inverseConjHistories parents emitted).flatMap
        (conjugateAtomHistories parent)

lemma word_conj_histories
    {M N : ℕ} :
    ∀ (parents : List (LabelledAtom M N)) (emitted : RHistor M N),
      (inverseConjHistories parents emitted).map RHistor.word =
        inverseConjTrace parents emitted.word
  | [], emitted => by
      rfl
  | parent :: parents, emitted => by
      rw [inverseConjHistories, inverseConjTrace, List.map_flatMap]
      calc
        _ =
            (inverseConjHistories parents emitted).flatMap
              (fun history =>
                inverseConjugateAtom parent history.word) := by
              simp only [conjugate_atom_histories]
        _ =
            ((inverseConjHistories parents emitted).map RHistor.word).flatMap
              (inverseConjugateAtom parent) := by
              rw [List.flatMap_map]
        _ = _ := by
              rw [word_conj_histories]

/-- Expand a raw-history list by inverse-oriented source-atom conjugation. -/
def inverseConjHistory
    {M N : ℕ}
    (parents : List (LabelledAtom M N))
    (histories : List (RHistor M N)) :
    List (RHistor M N) :=
  histories.flatMap (inverseConjHistories parents)

lemma inverse_conj_history
    {M N : ℕ}
    (parents : List (LabelledAtom M N))
    (histories : List (RHistor M N)) :
    (inverseConjHistory parents histories).map RHistor.word =
      inverseTraceList parents (histories.map RHistor.word) := by
  simp [inverseConjHistory, inverseTraceList,
    List.map_flatMap, word_conj_histories, List.flatMap_map]

/-- Raw histories in one right-input row. -/
def inverseRightHistories
    {M N : ℕ}
    (left : LabelledAtom M N) :
    List (LabelledAtom M N) →
      List (RHistor M N)
  | [] =>
      []
  | right :: rights =>
      .hallPair left right ::
        inverseConjHistory [right] (inverseRightHistories left rights)

lemma inverse_right_histories
    {M N : ℕ}
    (left : LabelledAtom M N) :
    ∀ rights : List (LabelledAtom M N),
      (inverseRightHistories left rights).map RHistor.word =
        inverseRightTrace left rights
  | [] => by
      rfl
  | right :: rights => by
      rw [inverseRightHistories, inverseRightTrace, List.map_cons,
        inverse_conj_history, inverse_right_histories]
      rfl

/-- Raw histories in the complete left-right inverse trace. -/
def inverseLeftHistories
    {M N : ℕ} :
    List (LabelledAtom M N) →
      List (LabelledAtom M N) →
        List (RHistor M N)
  | [], _rights =>
      []
  | left :: lefts, rights =>
      inverseConjHistory [left]
          (inverseLeftHistories lefts rights) ++
        inverseRightHistories left rights

lemma inverse_left_histories
    {M N : ℕ} :
    ∀ (lefts rights : List (LabelledAtom M N)),
      (inverseLeftHistories lefts rights).map RHistor.word =
        inverseLeftTrace lefts rights
  | [], rights => by
      rfl
  | left :: lefts, rights => by
      rw [inverseLeftHistories, inverseLeftTrace, List.map_append,
        inverse_conj_history, inverse_left_histories,
        inverse_right_histories]

/-- The reusable inverse-labelled collection is exactly the raw-history word list. -/
lemma histories_labelled_atoms
    (M N : ℕ) :
    (inverseLeftHistories
        (labelledLeftAtoms M N)
        (labelledRightAtoms M N)).map RHistor.word =
      inverseLeftTrace
        (labelledLeftAtoms M N)
        (labelledRightAtoms M N) :=
  inverse_left_histories _ _

/--
The smallest nontrivial right row already conjugates by a pure source atom.
This is the concrete reason raw histories need atom parents.
-/
@[simp]
lemma inverse_histories_two
    {M N : ℕ}
    (left right₀ right₁ : LabelledAtom M N) :
    inverseRightHistories left [right₀, right₁] =
      [.hallPair left right₀,
        .hallPair left right₁,
        .conjugate right₀ (.hallPair left right₁)] :=
  rfl

/-- A positive block recipe cannot represent a pure erased Hall-pair atom. -/
lemma BRecipe.erased_shape_neatom
    (recipe : BRecipe)
    (atom : HPAtom) :
    recipe.erasedShape ≠ .atom atom := by
  intro hshape
  have hpositive := recipe.positive
  change recipe.erasedShape.PBPos at hpositive
  rw [hshape] at hpositive
  cases atom <;>
    simp [CWord.PBPos] at hpositive

/-- Consequently, a counted positive block family cannot represent a source atom. -/
lemma BFam.erased_shape_neatom
    {M N : ℕ}
    (family : BFam M N)
    (atom : HPAtom) :
    family.recipe.erasedShape ≠ .atom atom :=
  BRecipe.erased_shape_neatom family.recipe atom

end RHRecurs
end TCTex
end Submission

/-!
# Strict correction histories for the inverse-oriented raw trace

The raw inverse-trace collector already remembers the exact occurrence
history of every emitted word.  This file separates the retained source
history from the genuinely new conjugation histories.

Forgetting history recovers the strict correction tails from
`SymbolicHallPowerInverseConjCorrectionTrace`.  Consequently every emitted
correction history has strictly larger formal word weight than its retained
source history.  This is the occurrence-preserving interface needed by a
cutoff scheduler: retained occurrences may stay in the current stratum, while
correction occurrences move upward.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace RHTrace

open HACoeff
open RHRecurs

/-- The strict history tail left after retaining the original history. -/
def inverseCorrectionHistories
    {M N : ℕ}
    (parents : List (LabelledAtom M N))
    (emitted : RHistor M N) :
    List (RHistor M N) :=
  (inverseConjHistories parents emitted).tail

/-- The history trace always starts with the retained source occurrence. -/
lemma tail_histories_cons
    {M N : ℕ} :
    ∀ (parents : List (LabelledAtom M N))
      (emitted : RHistor M N),
      ∃ tail, inverseConjHistories parents emitted = emitted :: tail
  | [], emitted => ⟨[], rfl⟩
  | parent :: parents, emitted => by
      rcases tail_histories_cons parents emitted with
        ⟨tail, htail⟩
      refine
        ⟨.conjugate parent emitted ::
            tail.flatMap (conjugateAtomHistories parent), ?_⟩
      simp [inverseConjHistories, htail, conjugateAtomHistories]

/-- Split a history trace into its retained occurrence and strict tail. -/
lemma histories_cons_correction
    {M N : ℕ}
    (parents : List (LabelledAtom M N))
    (emitted : RHistor M N) :
    inverseConjHistories parents emitted =
      emitted :: inverseCorrectionHistories parents emitted := by
  rcases tail_histories_cons parents emitted with
    ⟨tail, htail⟩
  simp [inverseCorrectionHistories, htail]

/-- Forgetting strict correction histories gives the strict correction words. -/
lemma word_inverse_histories
    {M N : ℕ}
    (parents : List (LabelledAtom M N))
    (emitted : RHistor M N) :
    (inverseCorrectionHistories parents emitted).map RHistor.word =
      inverseConjCorrection parents emitted.word := by
  rw [inverseCorrectionHistories, inverseConjCorrection,
    ← word_conj_histories]
  simp

/-- Every strict correction history gains formal word weight. -/
lemma inverse_conj_histories
    {M N : ℕ}
    (wt : LabelledAtom M N → ℕ)
    (hwt : ∀ a, 0 < wt a)
    (parents : List (LabelledAtom M N))
    (emitted correction : RHistor M N)
    (hcorrection : correction ∈
      inverseCorrectionHistories parents emitted) :
    emitted.word.weight wt < correction.word.weight wt := by
  apply
    inverse_conj_trace wt hwt parents emitted.word
      correction.word
  rw [← word_inverse_histories parents emitted]
  exact List.mem_map.mpr ⟨correction, hcorrection, rfl⟩

/-- Strict correction histories for every retained history in a list. -/
def inverseHistoryList
    {M N : ℕ}
    (parents : List (LabelledAtom M N))
    (histories : List (RHistor M N)) :
    List (RHistor M N) :=
  histories.flatMap (inverseCorrectionHistories parents)

/-- Forgetting a strict correction-history list gives the strict word-tail list. -/
lemma correction_history_list
    {M N : ℕ}
    (parents : List (LabelledAtom M N))
    (histories : List (RHistor M N)) :
    (inverseHistoryList parents histories).map RHistor.word =
      inverseConjList parents (histories.map RHistor.word) := by
  simp [inverseHistoryList, inverseConjList,
    List.map_flatMap, word_inverse_histories,
    List.flatMap_map]

/--
The history-list trace interleaves every retained occurrence with its strict
correction histories.
-/
lemma history_cons_histories
    {M N : ℕ}
    (parents : List (LabelledAtom M N))
    (histories : List (RHistor M N)) :
    inverseConjHistory parents histories =
      histories.flatMap fun emitted =>
        emitted :: inverseCorrectionHistories parents emitted := by
  rw [inverseConjHistory]
  induction histories with
  | nil =>
      rfl
  | cons emitted histories ih =>
      simp only [List.flatMap_cons]
      rw [histories_cons_correction, ih]

/-- Every list-tail correction history points to a strictly lighter source. -/
lemma source_history_list
    {M N : ℕ}
    (wt : LabelledAtom M N → ℕ)
    (hwt : ∀ a, 0 < wt a)
    (parents : List (LabelledAtom M N))
    (histories : List (RHistor M N))
    (correction : RHistor M N)
    (hcorrection : correction ∈
      inverseHistoryList parents histories) :
    ∃ emitted ∈ histories,
      emitted.word.weight wt < correction.word.weight wt := by
  rcases List.mem_flatMap.mp hcorrection with
    ⟨emitted, hemitted, htail⟩
  exact
    ⟨emitted, hemitted,
      inverse_conj_histories wt hwt parents
        emitted correction htail⟩

/--
If all retained histories lie in one supported stratum, every strict
correction history lies at least one stratum higher.
-/
lemma add_history_list
    {M N lowerWeight : ℕ}
    (wt : LabelledAtom M N → ℕ)
    (hwt : ∀ a, 0 < wt a)
    (parents : List (LabelledAtom M N))
    {histories : List (RHistor M N)}
    (hhistories : ∀ emitted ∈ histories,
      lowerWeight ≤ emitted.word.weight wt)
    (correction : RHistor M N)
    (hcorrection : correction ∈
      inverseHistoryList parents histories) :
    lowerWeight + 1 ≤ correction.word.weight wt := by
  rcases
      source_history_list
        wt hwt parents histories correction hcorrection with
    ⟨emitted, hemitted, hweight⟩
  have hlower := hhistories emitted hemitted
  omega

end RHTrace
end TCTex
end Submission

/-!
# Exact realization-slot coverage of the inverse raw trace

The inverse-labelled source trace is not yet arranged into consecutive family
packets.  It nevertheless contains every realization slot of every represented
initial one-block family exactly once.  This file upgrades the existing
word-level saturation and duplicate-freeness lemmas to the realization-token
invariant required by the operational packet collector.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace RSCovera

open HACoeff

namespace BFam.RToken

/-- Recover the labelled realization word named by one exact family slot. -/
def word
    {M N : ℕ}
    (token : BFam.RToken M N) :
    CWord (LabelledAtom M N) :=
  token.1.realizations.get token.2

end BFam.RToken

namespace DFTerm

@[simp]
lemma realizationToken_word
    {M N K : ℕ}
    (T : DFTerm M N K) :
    BFam.RToken.word T.realizationToken =
      T.decorated.word :=
  T.realizationIndex_get

end DFTerm

/-- Forgetting family provenance recovers the inverse-labelled source trace. -/
lemma decorated_raw_terms
    (M N : ℕ) :
    decoratedFamilyList (inverseDecoratedTerms M N) =
      inverseLeftTrace
        (labelledLeftAtoms M N)
        (labelledRightAtoms M N) := by
  simp only [decoratedFamilyList, inverseDecoratedTerms,
    List.map_ofFn, Function.comp_def,
    inverseLabelledCollection, DFTerm.ofLabelLinear,
    DTerm.raw]
  exact List.ofFn_getElem

/--
The inverse raw words are a permutation of the realization lists of their
distinct represented one-block families.
-/
lemma decorated_perm_realization
    (M N : ℕ) :
    List.Perm
      (decoratedFamilyList (inverseDecoratedTerms M N))
      (BFam.realizationList
        (distinctBlockFamilies (inverseDecoratedTerms M N))) := by
  apply (List.perm_ext_iff_of_nodup
    (by
      rw [decorated_raw_terms]
      exact labelled_atoms_nodup M N)
    (realization_distinct_nodup M N)).2
  intro word
  constructor
  · intro hword
    exact
      decorated_distinct_families
        (inverseDecoratedTerms M N) hword
  · intro hword
    exact realization_distinct_words M N hword

/--
The inverse raw source terms enumerate every represented realization token
exactly once.  Their operational order may differ from the canonical family
concatenation order.
-/
lemma realization_indexed_decorated
    (M N : ℕ) :
    RealizationIndexedBlock (inverseDecoratedTerms M N) := by
  let raw := inverseDecoratedTerms M N
  let families := distinctBlockFamilies raw
  have hwordsNodup :
      (decoratedFamilyList raw).Nodup := by
    dsimp [raw]
    rw [decorated_raw_terms]
    exact labelled_atoms_nodup M N
  have htokensNodup :
      (raw.map DFTerm.realizationToken).Nodup := by
    apply List.Nodup.of_map BFam.RToken.word
    simpa [decoratedFamilyList, List.map_map, Function.comp_def] using
      hwordsNodup
  have htokensSubset :
      raw.map DFTerm.realizationToken ⊆
        BFam.realizationTokenList families := by
    intro token htoken
    rcases List.mem_map.mp htoken with ⟨T, hT, rfl⟩
    exact List.mem_sigma.mpr
      ⟨distinct_block_families.mpr ⟨T, hT, rfl⟩,
        List.mem_finRange T.realizationIndex⟩
  have htokenLength :
      (BFam.realizationTokenList families).length =
        (BFam.realizationList families).length := by
    calc
      (BFam.realizationTokenList families).length =
          (BFam.realizationFamilyList families).length := by
        rw [← BFam.realization_tokenlist_fammap]
        simp
      _ = (BFam.realizationList families).length :=
        BFam.realization_fam_listlength families
  have hwordsPerm :
      List.Perm (decoratedFamilyList raw)
        (BFam.realizationList families) := by
    simpa [raw, families] using
      decorated_perm_realization M N
  have hlength :
      (BFam.realizationTokenList families).length ≤
        (raw.map DFTerm.realizationToken).length := by
    rw [htokenLength]
    simpa [decoratedFamilyList] using hwordsPerm.length_eq.symm.le
  have htokensPerm :
      List.Perm
        (raw.map DFTerm.realizationToken)
        (BFam.realizationTokenList families) :=
    (List.subperm_of_subset htokensNodup htokensSubset).perm_of_length_le hlength
  simpa [RealizationIndexedBlock, raw, families] using htokensPerm.symm

end RSCovera
end TCTex
end Submission

/-!
# Positive recipe attachment for exact inverse raw histories

The inverse-oriented trace first records conjugation histories with source-atom
parents.  Its output words are nevertheless positive and label-linear, so each
output occurrence can be attached to the one-block family recipe used by the
later More3 collector.

This file identifies the exact history-word list with the existing indexed raw
family terms and packages their realization-slot inventory.  Raw atom-parent
provenance is retained until after the inverse trace has been constructed; only
the resulting positive words receive block families.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace RHRecipe

open HACoeff
open RHRecurs
open RSCovera

/-- Exact raw histories of the reusable inverse-labelled collection. -/
def inverseRawHistories
    (M N : ℕ) :
    List (RHistor M N) :=
  inverseLeftHistories
    (labelledLeftAtoms M N)
    (labelledRightAtoms M N)

/-- Forgetting exact raw histories recovers the inverse-labelled factors. -/
lemma word_raw_histories
    (M N : ℕ) :
    (inverseRawHistories M N).map RHistor.word =
      (inverseLabelledCollection M N).factors := by
  simpa [inverseRawHistories, inverseLabelledCollection] using
    (histories_labelled_atoms M N)

/-- Every actual raw history names one factor of the inverse-labelled collection. -/
lemma inverse_labelled_histories
    {M N : ℕ}
    {history : RHistor M N}
    (hhistory : history ∈ inverseRawHistories M N) :
    history.word ∈ (inverseLabelledCollection M N).factors := by
  rw [← word_raw_histories]
  exact List.mem_map.mpr ⟨history, hhistory, rfl⟩

namespace RHistor

/-- Every actual raw history has positive erased Hall-pair bidegree. -/
lemma positive_raw_histories
    {M N : ℕ}
    {history : RHistor M N}
    (hhistory : history ∈ inverseRawHistories M N) :
    (collapseWord history.word).PBPos :=
  (inverseLabelledCollection M N).factors_positive history.word
    (inverse_labelled_histories hhistory)

/-- Every actual raw history uses each source label linearly. -/
lemma inverse_raw_histories
    {M N : ℕ}
    {history : RHistor M N}
    (hhistory : history ∈ inverseRawHistories M N) :
    LabelLinear history.word :=
  inverse_labelled_linear M N history.word
    (inverse_labelled_histories hhistory)

/--
Attach a positive one-block family only after the atom-parent raw recurrence has
finished constructing an actual inverse-trace history.
-/
noncomputable def initialFamily
    {M N : ℕ}
    (history : RHistor M N)
    (hhistory : history ∈ inverseRawHistories M N) :
    BFam M N :=
  BFam.ofLinear M N
    (LRecipe.ofLabelLinear history.word
      (positive_raw_histories hhistory)
      (inverse_raw_histories hhistory))

end RHistor

/--
The exact history-word list and the indexed raw family-term word list agree in
their operational order.
-/
lemma raw_histories_decorated
    (M N : ℕ) :
    (inverseRawHistories M N).map RHistor.word =
      decoratedFamilyList (inverseDecoratedTerms M N) := by
  calc
    (inverseRawHistories M N).map RHistor.word =
        (inverseLabelledCollection M N).factors :=
      word_raw_histories M N
    _ =
        inverseLeftTrace
          (labelledLeftAtoms M N)
          (labelledRightAtoms M N) :=
      rfl
    _ = decoratedFamilyList (inverseDecoratedTerms M N) :=
      (decorated_raw_terms M N).symm

/-- Every indexed raw family term is represented by an exact raw history. -/
lemma history_decorated_terms
    {M N : ℕ}
    {term : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hterm : term ∈ inverseDecoratedTerms M N) :
    ∃ history ∈ inverseRawHistories M N,
      history.word = term.decorated.word := by
  have hword :
      term.decorated.word ∈
        decoratedFamilyList (inverseDecoratedTerms M N) :=
    List.mem_map.mpr ⟨term, hterm, rfl⟩
  rw [← raw_histories_decorated] at hword
  exact List.mem_map.mp hword

/-- Every exact raw history is represented by an indexed raw family term. -/
lemma term_raw_histories
    {M N : ℕ}
    {history : RHistor M N}
    (hhistory : history ∈ inverseRawHistories M N) :
    ∃ term ∈ inverseDecoratedTerms M N,
      term.decorated.word = history.word := by
  have hword :
      history.word ∈ (inverseRawHistories M N).map RHistor.word :=
    List.mem_map.mpr ⟨history, hhistory, rfl⟩
  rw [raw_histories_decorated] at hword
  exact List.mem_map.mp hword

/--
Raw atom-parent histories together with the positive one-block realization
inventory consumed by the later family collector.
-/
structure InverseHistoryEndpoint
    (M N : ℕ) where
  histories :
    List (RHistor M N)
  terms :
    List (DFTerm M N
      (inverseLabelledCollection M N).factors.length)
  history_words_term :
    histories.map RHistor.word =
      decoratedFamilyList terms
  realizationIndexed :
    RealizationIndexedBlock terms

/-- Canonical exact recipe attachment for the reusable inverse raw trace. -/
noncomputable def inverseHistoryEndpoint
    (M N : ℕ) :
    InverseHistoryEndpoint M N where
  histories := inverseRawHistories M N
  terms := inverseDecoratedTerms M N
  history_words_term :=
    raw_histories_decorated M N
  realizationIndexed :=
    realization_indexed_decorated M N

end RHRecipe
end TCTex
end Submission

/-!
# Truncating exact atom-parent inverse histories

The reusable inverse trace is already a genuine finite Hall-Petresco
expansion, before the later family collector coalesces equal erased shapes.
This file truncates that exact occurrence-level expansion at a nilpotent
cutoff.  Histories below the cutoff remain as an ordered finite packet;
histories at or above the cutoff disappear only after evaluation in the
matching quotient.

The retained endpoint is intentionally precompression.  Its histories still
remember source-atom parents, and this file does not claim that equal recipe
occurrences have already been grouped into polynomial families.  It is
intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace HHTrunc

open scoped commutatorElement

open HACoeff
open BFTrunc
open BRScheda
open RHRecurs
open RHRecipe
open ITEvalua

namespace RHistor

/-- Weighted Hall degree of one exact atom-parent inverse history. -/
def weight
    {M N : ℕ}
    (leftWeight rightWeight : ℕ)
    (history : RHistor M N) :
    ℕ :=
  (collapseWord history.word).weight
    (HPAtom.weight leftWeight rightWeight)

@[simp]
lemma weight_hallPair
    {M N leftWeight rightWeight : ℕ}
    (left right : LabelledAtom M N) :
    weight leftWeight rightWeight (RHistor.hallPair left right) =
      HPAtom.weight leftWeight rightWeight (collapseLabel left) +
        HPAtom.weight leftWeight rightWeight (collapseLabel right) :=
  rfl

@[simp]
lemma weight_conjugate
    {M N leftWeight rightWeight : ℕ}
    (parent : LabelledAtom M N)
    (emitted : RHistor M N) :
    weight leftWeight rightWeight (RHistor.conjugate parent emitted) =
      weight leftWeight rightWeight emitted +
        HPAtom.weight leftWeight rightWeight (collapseLabel parent) := by
  unfold weight
  change
    (collapseWord (rootSwapWord emitted.word)).weight
          (HPAtom.weight leftWeight rightWeight) +
        HPAtom.weight leftWeight rightWeight (collapseLabel parent) =
      (collapseWord emitted.word).weight
          (HPAtom.weight leftWeight rightWeight) +
        HPAtom.weight leftWeight rightWeight (collapseLabel parent)
  rw [collapse_root_swap, weight_root_swap]

/-- Every exact atom-parent history has positive weighted Hall degree. -/
lemma weight_pos
    {M N leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (history : RHistor M N) :
    0 < weight leftWeight rightWeight history := by
  induction history with
  | hallPair left right =>
      simp only [weight_hallPair]
      exact Nat.add_pos_left
        (HPAtom.weight_pos hleftWeight hrightWeight (collapseLabel left)) _
  | conjugate parent emitted ih =>
      rw [weight_conjugate]
      exact Nat.add_pos_left ih _

/-- Conjugating a previously emitted history strictly raises its weight. -/
lemma weight_conjugate_emitted
    {M N leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (parent : LabelledAtom M N)
    (emitted : RHistor M N) :
    weight leftWeight rightWeight emitted <
      weight leftWeight rightWeight (RHistor.conjugate parent emitted) := by
  rw [weight_conjugate]
  exact Nat.lt_add_of_pos_right
    (HPAtom.weight_pos hleftWeight hrightWeight (collapseLabel parent))

/-- A conjugation history also lies strictly above the source atom it crosses. -/
lemma parent_weight_conjugate
    {M N leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (parent : LabelledAtom M N)
    (emitted : RHistor M N) :
    HPAtom.weight leftWeight rightWeight (collapseLabel parent) <
      weight leftWeight rightWeight (RHistor.conjugate parent emitted) := by
  rw [weight_conjugate, Nat.add_comm]
  exact Nat.lt_add_of_pos_right
    (weight_pos hleftWeight hrightWeight emitted)

end RHistor

/-- Ordered labelled words represented by exact raw histories. -/
def historyWords
    {M N : ℕ}
    (histories : List (RHistor M N)) :
    List (CWord (LabelledAtom M N)) :=
  histories.map RHistor.word

/-- Exact histories whose weighted words survive the cutoff. -/
def retainedHistories
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (histories : List (RHistor M N)) :
    List (RHistor M N) :=
  histories.filter fun history =>
    decide (RHistor.weight leftWeight rightWeight history < n)

/-- Exact histories whose weighted words have reached the cutoff. -/
def residualHistories
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (histories : List (RHistor M N)) :
    List (RHistor M N) :=
  histories.filter fun history =>
    decide (n ≤ RHistor.weight leftWeight rightWeight history)

/-- Ordered below-cutoff labelled words retained by polynomial consumers. -/
def retainedWords
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (histories : List (RHistor M N)) :
    List (CWord (LabelledAtom M N)) :=
  historyWords (retainedHistories n leftWeight rightWeight histories)

/-- Ordered above-cutoff labelled words retained only by the exact trace. -/
def residualWords
    {M N : ℕ}
    (n leftWeight rightWeight : ℕ)
    (histories : List (RHistor M N)) :
    List (CWord (LabelledAtom M N)) :=
  historyWords (residualHistories n leftWeight rightWeight histories)

@[simp]
lemma mem_retainedHistories
    {M N n leftWeight rightWeight : ℕ}
    {history : RHistor M N}
    {histories : List (RHistor M N)} :
    history ∈ retainedHistories n leftWeight rightWeight histories ↔
      history ∈ histories ∧
        RHistor.weight leftWeight rightWeight history < n := by
  simp [retainedHistories]

@[simp]
lemma mem_residualHistories
    {M N n leftWeight rightWeight : ℕ}
    {history : RHistor M N}
    {histories : List (RHistor M N)} :
    history ∈ residualHistories n leftWeight rightWeight histories ↔
      history ∈ histories ∧
        n ≤ RHistor.weight leftWeight rightWeight history := by
  simp [residualHistories]

/-- Every residual raw word has reached the nilpotent cutoff after collapse. -/
lemma words_above_cutoff
    {M N n leftWeight rightWeight : ℕ}
    (histories : List (RHistor M N)) :
    WordsAboveCutoff n leftWeight rightWeight
      (residualWords n leftWeight rightWeight histories) := by
  intro word hword
  rcases List.mem_map.mp hword with ⟨history, hhistory, rfl⟩
  exact (mem_residualHistories.mp hhistory).2

/--
Removing above-cutoff occurrence histories preserves collapsed evaluation in
every matching nilpotent quotient.
-/
lemma collapsed_history_words
    {M N n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    (histories : List (RHistor M N)) :
    collapsedList x y (historyWords histories) =
      collapsedList x y
        (retainedWords n leftWeight rightWeight histories) := by
  induction histories with
  | nil =>
      rfl
  | cons history histories ih =>
      by_cases hweight : RHistor.weight leftWeight rightWeight history < n
      · simpa [historyWords, retainedWords, retainedHistories, hweight,
          collapsedList] using ih
      · have hcutoff : n ≤ RHistor.weight leftWeight rightWeight history :=
          Nat.le_of_not_gt hweight
        have hvanish :
            (collapseWord history.word).eval (HPAtom.eval x y) = 1 :=
          collapsed_weight_least
            hleftWeight hrightWeight hx hy hbot history.word hcutoff
        simpa [historyWords, retainedWords, retainedHistories, hweight,
          collapsedList, hvanish] using ih

/--
Finite below-cutoff occurrence packet extracted directly from the genuine
inverse-oriented raw trace.
-/
structure TruncatedHistoryPacket
    (M N n leftWeight rightWeight : ℕ) where
  histories :
    List (RHistor M N)
  histories_eq :
    histories =
      retainedHistories n leftWeight rightWeight (inverseRawHistories M N)
  weight_lt_cutoff :
    ∀ history ∈ histories,
      RHistor.weight leftWeight rightWeight history < n
  collapsed_list_eval :
    ∀ {G : Type*} [Group G]
      (x y : G),
      x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1) →
      y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1) →
      Subgroup.lowerCentralSeries G (n - 1) = ⊥ →
      collapsedList x y (historyWords histories) =
        ⁅x ^ M, y ^ N⁆

/-- Canonical truncated occurrence packet supplied by the raw inverse trace. -/
def truncatedHistoryPacket
    (M N n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    TruncatedHistoryPacket M N n leftWeight rightWeight where
  histories :=
    retainedHistories n leftWeight rightWeight (inverseRawHistories M N)
  histories_eq :=
    rfl
  weight_lt_cutoff := by
    intro history hhistory
    exact (mem_retainedHistories.mp hhistory).2
  collapsed_list_eval := by
    intro G _ x y hx hy hbot
    calc
      collapsedList x y
          (historyWords
            (retainedHistories n leftWeight rightWeight
              (inverseRawHistories M N))) =
          collapsedList x y
            (historyWords (inverseRawHistories M N)) :=
        (collapsed_history_words
          (n := n) hleftWeight hrightWeight hx hy hbot
            (inverseRawHistories M N)).symm
      _ =
          collapsedList x y
            (inverseLeftTrace
              (labelledLeftAtoms M N)
              (labelledRightAtoms M N)) := by
        rw [historyWords, inverseRawHistories,
          histories_labelled_atoms]
      _ = ⁅x ^ M, y ^ N⁆ :=
        collapsed_commutator_pow x y

end HHTrunc
end TCTex
end Submission

/-!
# Cutoff routing for strict inverse raw-history corrections

The exact inverse-history truncation layer assigns weighted Hall degree to
raw histories.  The strict-tail splitter supplies the missing list-level
statement: if retained source histories start in stratum `s`, every genuine
conjugation correction starts in stratum at least `s + 1`.

In particular, once `s + 1` reaches the nilpotent cutoff, the entire strict
correction-history list disappears from the retained occurrence packet.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace RHTrunc

open HACoeff
open RHTrace
open RHRecurs
open HHTrunc

private abbrev rawWeight
    {M N : ℕ}
    (leftWeight rightWeight : ℕ)
    (history : RHistor M N) :
    ℕ :=
  HHTrunc.RHistor.weight
    leftWeight rightWeight history

namespace RHistor

/-- The collapsed weighted Hall degree agrees with labelled-word weighting. -/
lemma word_eq_weight
    {M N : ℕ}
    (leftWeight rightWeight : ℕ)
    (history : RHistor M N) :
    history.word.weight
        (fun atom =>
          HPAtom.weight leftWeight rightWeight (collapseLabel atom)) =
      rawWeight leftWeight rightWeight history := by
  simp [rawWeight, HHTrunc.RHistor.weight,
    collapseWord, CWord.weight_bind]

end RHistor

/-- Every strict correction history has larger weighted Hall degree. -/
lemma conj_correction_histories
    {M N leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (parents : List (LabelledAtom M N))
    (emitted correction : RHistor M N)
    (hcorrection : correction ∈
      inverseCorrectionHistories parents emitted) :
    rawWeight leftWeight rightWeight emitted <
      rawWeight leftWeight rightWeight correction := by
  simpa only [RHistor.word_eq_weight] using
    (inverse_conj_histories
      (fun atom =>
        HPAtom.weight leftWeight rightWeight (collapseLabel atom))
      (fun atom =>
        HPAtom.weight_pos hleftWeight hrightWeight (collapseLabel atom))
      parents emitted correction hcorrection)

/-- Every list-tail correction points to a strictly lighter source history. -/
lemma conj_history_list
    {M N leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (parents : List (LabelledAtom M N))
    (histories : List (RHistor M N))
    (correction : RHistor M N)
    (hcorrection : correction ∈
      inverseHistoryList parents histories) :
    ∃ emitted ∈ histories,
      rawWeight leftWeight rightWeight emitted <
        rawWeight leftWeight rightWeight correction := by
  rcases
      source_history_list
        (fun atom =>
          HPAtom.weight leftWeight rightWeight (collapseLabel atom))
        (fun atom =>
          HPAtom.weight_pos hleftWeight hrightWeight (collapseLabel atom))
        parents histories correction hcorrection with
    ⟨emitted, hemitted, hweight⟩
  exact
    ⟨emitted, hemitted, by
      simpa only [RHistor.word_eq_weight] using hweight⟩

/--
Strict correction histories sourced in stratum `lowerWeight` land at least
one weighted Hall stratum higher.
-/
lemma inverse_history_list
    {M N leftWeight rightWeight lowerWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (parents : List (LabelledAtom M N))
    {histories : List (RHistor M N)}
    (hhistories : ∀ emitted ∈ histories,
      lowerWeight ≤ rawWeight leftWeight rightWeight emitted)
    (correction : RHistor M N)
    (hcorrection : correction ∈
      inverseHistoryList parents histories) :
    lowerWeight + 1 ≤ rawWeight leftWeight rightWeight correction := by
  rcases
      conj_history_list
        hleftWeight hrightWeight parents histories correction hcorrection with
    ⟨emitted, hemitted, hweight⟩
  have hlower := hhistories emitted hemitted
  omega

/--
At a terminal cutoff, every strict correction history is removed from the
retained occurrence packet.
-/
lemma histories_history_nil
    {M N n leftWeight rightWeight lowerWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (parents : List (LabelledAtom M N))
    {histories : List (RHistor M N)}
    (hhistories : ∀ emitted ∈ histories,
      lowerWeight ≤ rawWeight leftWeight rightWeight emitted)
    (hcutoff : n ≤ lowerWeight + 1) :
    retainedHistories n leftWeight rightWeight
        (inverseHistoryList parents histories) =
      [] := by
  rw [retainedHistories]
  apply List.filter_eq_nil_iff.2
  intro correction hcorrection hdecide
  exact
    not_lt_of_ge
      (hcutoff.trans
        (inverse_history_list
          hleftWeight hrightWeight parents hhistories correction hcorrection))
      (of_decide_eq_true hdecide)

/--
At a terminal cutoff, every strict correction history belongs to the
above-cutoff residual packet.
-/
lemma histories_history_self
    {M N n leftWeight rightWeight lowerWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (parents : List (LabelledAtom M N))
    {histories : List (RHistor M N)}
    (hhistories : ∀ emitted ∈ histories,
      lowerWeight ≤ rawWeight leftWeight rightWeight emitted)
    (hcutoff : n ≤ lowerWeight + 1) :
    residualHistories n leftWeight rightWeight
        (inverseHistoryList parents histories) =
      inverseHistoryList parents histories := by
  rw [residualHistories]
  apply List.filter_eq_self.2
  intro correction hcorrection
  simpa only [decide_eq_true_eq] using
    hcutoff.trans
      (inverse_history_list
        hleftWeight hrightWeight parents hhistories correction hcorrection)

end RHTrunc
end TCTex
end Submission
