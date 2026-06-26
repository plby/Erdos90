import Towers.Group.Zassenhaus.RetainedHistoryFibers
import Towers.Group.Zassenhaus.InverseUniversalClosure
import Towers.Group.Zassenhaus.EndpointShapeInterpolation
import Towers.Group.Zassenhaus.BlockRecipe
import Towers.Group.Zassenhaus.InverseRaw
import Towers.Group.Zassenhaus.CorrectionClosureVocabulary
import Towers.Group.Zassenhaus.PolynomialOrbitVocabulary
import Towers.Group.Zassenhaus.CompatiblePacketRouting


/-!
# Ordered canonical packet alignment for cutoff-full shape fibers

The cutoff-full interpolation pipeline attaches profiles to the sorted erased
Hall vocabulary.  The finite correction closure also has canonical
coefficient-sum profiles, but its original global packet uses the unsorted
deduplicated vocabulary order.

This file separates the two issues:

* word-local agreement with the canonical coefficient-sum profile;
* the order-aware signed law for the sorted canonical packet.

The first issue compiles to literal packet-list equality.  Any comparison
between sorted and unsorted products remains explicit, as required for a
noncommutative collector.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace
  FFCanon

universe u


open scoped commutatorElement

open
  FPInterp
open
  CRLayer
open
  NRSubinv
open
  CFSubsti
open
  CPSplit
open
  CTAssign
open
  GRPolys
open
  ACAlign
open
  FCAssign
open
  UCSuppor

/--
Canonical coefficient-sum profiles attached in the sorted cutoff-full
vocabulary order.
-/
noncomputable def globalRecollectionPackets
    (n leftWeight rightWeight : ℕ) :
    List RFPkt :=
  (canonicalProfileAssignment n leftWeight rightWeight)
    |>.erasedVocabPackets

/--
One profile assignment agrees word by word with the canonical
coefficient-sum assignment.
-/
def CanonicalProfileAlignment
    {n leftWeight rightWeight : ℕ}
    (assignment :
      SPAssign n leftWeight rightWeight) :
    Prop :=
  ∀ word hword,
    assignment.profiles word hword =
      (canonicalProfileAssignment
        n leftWeight rightWeight).profiles word hword

/--
Word-local canonical profile agreement gives literal equality of the sorted
packet lists.
-/
lemma
    ordered_erased_alignment
    {n leftWeight rightWeight : ℕ}
    (assignment :
      SPAssign n leftWeight rightWeight)
    (halignment :
      CanonicalProfileAlignment assignment) :
    assignment.erasedVocabPackets =
      globalRecollectionPackets
        n leftWeight rightWeight := by
  unfold
    globalRecollectionPackets
  unfold
    FCAssign.SPAssign.erasedVocabPackets
  apply List.map_congr_left
  intro word _hword
  congr 1
  exact
    halignment word.1
      (ordered_erased_vocabulary.mp word.2)

/--
The cutoff-specific signed recollection law for the sorted canonical packet.
-/
def SatisfiesGlobalTruncated
    (d n : ℕ) :
    Prop :=
  ∀ (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ),
      ((globalRecollectionPackets n 1 1).map
        fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod =
        ⁅left ^ leftExponent, right ^ rightExponent⁆

/--
The sorted canonical packet happens to agree literally with the original
unsorted global canonical packet.  This is a separate order theorem.
-/
def GlobalVocabularyAlignment
    (n leftWeight rightWeight : ℕ) :
    Prop :=
  globalRecollectionPackets
      n leftWeight rightWeight =
    globalProfilePackets
      n leftWeight rightWeight

/--
When the sorted and original canonical orders coincide, the original
canonical recipe-product law supplies the sorted canonical signed law.
-/
lemma
    satisfies_global_trunc
    {d n : ℕ}
    (horder :
      GlobalVocabularyAlignment n 1 1)
    (hlistEval :
      SatisfiesRecipeTruncated.{u} d n) :
    SatisfiesGlobalTruncated.{u} d n := by
  intro left right leftExponent rightExponent
  rw [horder]
  simpa only [globalProfilePackets] using
    (satisfies_profile_assignment
      hlistEval left right leftExponent rightExponent)

/--
Literal alignment with the sorted canonical packet transports its signed law
to an arbitrary endpoint shape-fiber interpolation packet.
-/
def
    allGlobalAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (interpolation :
      EFInterp layer packets)
    (halignment :
      packets =
        globalRecollectionPackets n 1 1)
    (hlistEval :
      SatisfiesGlobalTruncated.{u} d n) :
    FPInterp.EFInterp.AILift.{u}
      (d := d) interpolation where
  listEval_eq left right leftExponent rightExponent := by
    rw [
      FPInterp.EFInterp.packetsTruncNatural,
      halignment]
    exact hlistEval left right leftExponent rightExponent

end
  FFCanon
end TCTex
end Towers

/-!
# Polynomial-orbit transversals for retained raw shape fibers

The cutoff-sized dummy inverse trace contains a finite source-recipe
vocabulary, but it may contain repeated recipes with the same symbolic
coefficient polynomial.  The polynomial-orbit partition supplies a canonical
finite transversal: choose one source-recipe representative for each
polynomial orbit and then filter those representatives by erased Hall shape.

This file isolates the remaining raw stabilization theorem for that concrete
candidate.  It is enough to prove that the fixed transversal profile agrees
with the already constructed local retained-raw profile at every natural
specialization.  Once that scalar identity is available, the uniform raw
profile kernel required by the scheduler-correction split is automatic.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace
  RFTransv

open HACoeff
open ROAggreg
open RFPacket
open BRSpec
open
  RFLocal
open
  FUBounda
open
  CFSubsti
open
  ACAlign
open
  UCSuppor
open URVocabu

/--
One fixed source-recipe representative for each polynomial orbit in the
cutoff-sized dummy raw trace.
-/
noncomputable def retainedRawTransversal
    (n leftWeight rightWeight : ℕ) :
    List BRecipe :=
  (polynomialOrbitVocabulary
    (sourceRecipes n leftWeight rightWeight)).attach.map fun key =>
      recipePolynomialOrbit
        (sourceRecipes n leftWeight rightWeight) key

/-- Every raw source-orbit representative comes from the finite dummy trace. -/
lemma source_recipes_transversal
    {n leftWeight rightWeight : ℕ}
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈
        retainedRawTransversal
          n leftWeight rightWeight) :
    recipe ∈ sourceRecipes n leftWeight rightWeight := by
  rcases List.mem_map.mp hrecipe with
    ⟨key, _hkey, rfl⟩
  exact
    recipes_polynomial_orbit
      (recipe_polynomial_orbit
        (sourceRecipes n leftWeight rightWeight) key)

/-- Keep the fixed raw source-orbit representatives with one erased shape. -/
noncomputable def rawTransversalShape
    (n leftWeight rightWeight : ℕ)
    (word : CWord HPAtom) :
    List BRecipe :=
  (retainedRawTransversal
    n leftWeight rightWeight).filter fun recipe =>
      decide (recipe.erasedShape = word)

/-- Every representative in one raw source-orbit chunk has its requested shape. -/
lemma erased_raw_transversal
    {n leftWeight rightWeight : ℕ}
    {word : CWord HPAtom}
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈
        rawTransversalShape
          n leftWeight rightWeight word) :
    recipe.erasedShape = word := by
  exact of_decide_eq_true (List.mem_filter.mp hrecipe).2

/--
The fixed homogeneous raw-profile candidate obtained from one representative
of each source polynomial orbit with the requested erased shape.
-/
noncomputable def rawTransversalProfile
    (n leftWeight rightWeight : ℕ)
    (word : CWord HPAtom) :
    HFPkt
      word.pairLeftDegree word.pairRightDegree :=
  HFPkt.ofRecipeChunk word
    (rawTransversalShape
      n leftWeight rightWeight word)
    fun _recipe hrecipe =>
      erased_raw_transversal
        hrecipe

/-- The fixed raw source-orbit profile evaluates as its explicit recipe sum. -/
lemma value_transversal_profile
    (n leftWeight rightWeight : ℕ)
    (word : CWord HPAtom)
    (leftExponent rightExponent : ℤ) :
    (rawTransversalProfile
      n leftWeight rightWeight word).value
        leftExponent rightExponent =
      ((rawTransversalShape
        n leftWeight rightWeight word).map fun recipe =>
          coefficientValue recipe leftExponent rightExponent).sum := by
  rw [rawTransversalProfile,
    HFPkt.value_recipe_chunk]

/--
The remaining scalar raw-stabilization theorem for the canonical finite
source-orbit transversal.
-/
structure PTStab
    (n leftWeight rightWeight : ℕ) : Prop where
  profile_cast_local :
    ∀ (M N : ℕ) word,
      word ∈ erasedShapeVocabulary n leftWeight rightWeight →
        (rawTransversalProfile
          n leftWeight rightWeight word).value (M : ℤ) (N : ℤ) =
          (retainedFiberProfile
            M N n leftWeight rightWeight word).value (M : ℤ) (N : ℤ)

namespace PTStab

/--
The canonical finite source-orbit transversal supplies uniform raw profiles.
-/
def fiberUniformProfile
    {n leftWeight rightWeight : ℕ}
    (kernel :
      PTStab
        n leftWeight rightWeight) :
    FUProf n leftWeight rightWeight where
  profiles := fun word _hword =>
    rawTransversalProfile
      n leftWeight rightWeight word
  profiles_cast_local := by
    intro M N word hword
    exact kernel.profile_cast_local M N word hword

end PTStab

end
  RFTransv
end TCTex
end Towers

/-!
# Shallow cutoff-full collection preserves filtered occurrence counts

When the cutoff is no larger than twice the initial commutator degree, every
new correction produced by cutoff-full insertion is residual.  The collector
therefore only reorders retained source terms.  The preceding class-two file
used the resulting total-length invariant.  This file strengthens it to every
Boolean-filtered occurrence count and records the direct endpoint bridge.

At source weights `(1, 1)`, the theorem applies through cutoff four.  This is
the occurrence-preserving interface needed to count the basic and two triple
shape fibers separately.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace SFCard

open HACoeff
open BRSpec
open CFCollec.DFTerm
open FFCard
open
  CTBoundaa
open CRLayer
open CCAggreg
open OCPartit
open RRTrunc

namespace DFTerm

/--
In the shallow range, cutoff insertion preserves every filtered occurrence
count and adds exactly the filtered contribution of the inserted term.
-/
lemma length_inserts_twice
    {M N K n leftWeight rightWeight : ℕ}
    (hcutoff : n ≤ 2 * (leftWeight + rightWeight))
    (predicate : DFTerm M N K → Bool)
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert : CInsert n leftWeight rightWeight L A R) :
    (R.filter predicate).length =
      (L.filter predicate).length + ([A].filter predicate).length := by
  induction hinsert with
  | nil A =>
      simp
  | append P B A _hBA =>
      rw [show [B, A] = [B] ++ [A] by rfl, List.filter_append]
      simp only [List.filter_append, List.length_append]
      omega
  | retained P B A _hAB hweight hcorrection hinsert
      ihcorrection ihinsert =>
      have hBmin :
          leftWeight + rightWeight ≤
            decoratedFamilyWeight leftWeight rightWeight B := by
        simpa only [decoratedFamilyWeight, weighted_word_pair] using
          weighted_weight_basic leftWeight rightWeight B.family.recipe
      have hAmin :
          leftWeight + rightWeight ≤
            decoratedFamilyWeight leftWeight rightWeight A := by
        simpa only [decoratedFamilyWeight, weighted_word_pair] using
          weighted_weight_basic leftWeight rightWeight A.family.recipe
      rw [decorated_family_correction] at hweight
      omega
  | residual P B A _hAB _hweight hinsert ihinsert =>
      simp only [List.filter_append, List.length_append]
      rw [ihinsert]
      omega

/--
In the same shallow range, cutoff collection preserves every filtered
occurrence count of its initial below-cutoff packet.
-/
lemma length_collects_twice
    {M N K n leftWeight rightWeight : ℕ}
    (hcutoff : n ≤ 2 * (leftWeight + rightWeight))
    (predicate : DFTerm M N K → Bool)
    {L R : List (DFTerm M N K)}
    (hcollect : CCollec n leftWeight rightWeight L R) :
    (R.filter predicate).length =
      ((belowCutoffTerms n leftWeight rightWeight L).filter predicate).length := by
  induction hcollect with
  | nil =>
      rfl
  | retained P A hweight hcollect hinsert ihcollect =>
      rw [length_inserts_twice
        hcutoff predicate hinsert, ihcollect]
      simp [belowCutoffTerms, List.filter_append, hweight]
  | residual P A hweight hcollect ihcollect =>
      rw [ihcollect]
      simp [belowCutoffTerms, List.filter_append, Nat.not_lt.mpr hweight]

end DFTerm

/--
Through cutoff four at source weights `(1, 1)`, every Boolean-filtered
cutoff-full endpoint fiber has the same cardinality as its retained raw-term
fiber.
-/
lemma endpoint_filter_length
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (M N : ℕ)
    (predicate :
      DFTerm M N
        (inverseLabelledCollection M N).factors.length → Bool) :
    ((layer.endpoint M N).factors.filter predicate).length =
      ((retainedRawTerms M N n 1 1).filter predicate).length := by
  exact
    DFTerm.length_collects_twice
      (by omega) predicate (layer.endpoint M N).family_cutoff_collects

/--
Through cutoff four, endpoint recipe-shape fibers can be counted directly in
the initially retained raw recipe packet.
-/
lemma filter_n_four
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (M N : ℕ)
    (word : CWord HPAtom) :
    endpointRecipeMultiplicity layer M N word =
      ((retainedRawTerms M N n 1 1).filter fun term =>
        decide (term.family.recipe.erasedShape = word)).length := by
  exact
    endpoint_filter_length
      layer hhigh M N fun term =>
        decide (term.family.recipe.erasedShape = word)

/--
The equivalent erased-shape form is convenient when bridging to exact raw
history words.
-/
lemma endpoint_filter_four
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (M N : ℕ)
    (word : CWord HPAtom) :
    endpointErasedMultiplicity layer M N word =
      ((retainedRawTerms M N n 1 1).filter fun term =>
        decide (term.erasedShape = word)).length := by
  exact
    endpoint_filter_length
      layer hhigh M N fun term =>
        decide (term.erasedShape = word)

end SFCard
end TCTex
end Towers

/-!
# Class-three raw-history occurrence cardinalities

The inverse-oriented raw trace has three structural history layers below
weight four: roots, roots conjugated by a left atom, and roots conjugated by a
right atom.  Their occurrence counts are respectively

* `M * N`,
* `Nat.choose M 2 * N`,
* `M * Nat.choose N 2`.

This file proves those formulas directly from the raw-history recurrence and
records that a cutoff strictly above three and at most four retains exactly
those three layers.  The later endpoint adapter can transport these
occurrence counts through shallow cutoff-full collection.

This file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex
namespace THCard

open HACoeff
open
  CTBoundaa
open RHRecurs
open RHRecipe
open HHTrunc

namespace RHistor

/-- One root history conjugated by a left source atom. -/
def isLeftTriple
    {M N : ℕ} :
    RHistor M N → Bool
  | .conjugate (.inl _) (.hallPair _ _) =>
      true
  | _ =>
      false

/-- One root history conjugated by a right source atom. -/
def isRightTriple
    {M N : ℕ} :
    RHistor M N → Bool
  | .conjugate (.inr _) (.hallPair _ _) =>
      true
  | _ =>
      false

end RHistor

/-- Crossing one left atom adds one left triple for each root history. -/
lemma length_histories_inl
    {M N : ℕ}
    (parent : Fin M)
    (emitted : RHistor M N) :
    ((conjugateAtomHistories (Sum.inl parent) emitted).filter
      RHistor.isLeftTriple).length =
        ([emitted].filter RHistor.isLeftTriple).length +
          ([emitted].filter RHistor.isBasic).length := by
  cases emitted with
  | hallPair left right =>
      rfl
  | conjugate emittedParent emitted =>
      cases emittedParent <;> rfl

/-- Crossing one right atom preserves the left-triple subinventory. -/
lemma length_histories_inr
    {M N : ℕ}
    (parent : Fin N)
    (emitted : RHistor M N) :
    ((conjugateAtomHistories (Sum.inr parent) emitted).filter
      RHistor.isLeftTriple).length =
        ([emitted].filter RHistor.isLeftTriple).length := by
  cases emitted with
  | hallPair left right =>
      rfl
  | conjugate emittedParent emitted =>
      cases emittedParent <;> rfl

/-- Crossing one right atom adds one right triple for each root history. -/
lemma atom_histories_inr
    {M N : ℕ}
    (parent : Fin N)
    (emitted : RHistor M N) :
    ((conjugateAtomHistories (Sum.inr parent) emitted).filter
      RHistor.isRightTriple).length =
        ([emitted].filter RHistor.isRightTriple).length +
          ([emitted].filter RHistor.isBasic).length := by
  cases emitted with
  | hallPair left right =>
      rfl
  | conjugate emittedParent emitted =>
      cases emittedParent <;> rfl

/-- Crossing one left atom preserves the right-triple subinventory. -/
lemma atom_histories_inl
    {M N : ℕ}
    (parent : Fin M)
    (emitted : RHistor M N) :
    ((conjugateAtomHistories (Sum.inl parent) emitted).filter
      RHistor.isRightTriple).length =
        ([emitted].filter RHistor.isRightTriple).length := by
  cases emitted with
  | hallPair left right =>
      rfl
  | conjugate emittedParent emitted =>
      cases emittedParent <;> rfl

/-- Crossing one left atom adds one left triple for each root in a list. -/
lemma filter_history_inl
    {M N : ℕ}
    (parent : Fin M) :
    ∀ histories : List (RHistor M N),
      ((inverseConjHistory [Sum.inl parent] histories).filter
        RHistor.isLeftTriple).length =
          (histories.filter RHistor.isLeftTriple).length +
            (histories.filter RHistor.isBasic).length
  | [] => by
      rfl
  | history :: histories => by
      rw [inverseConjHistory, List.flatMap_cons, List.filter_append,
        List.length_append]
      rw [show
          inverseConjHistories [Sum.inl parent] history =
            conjugateAtomHistories (Sum.inl parent) history by
            rfl,
        show
          List.flatMap (inverseConjHistories [Sum.inl parent]) histories =
            inverseConjHistory [Sum.inl parent] histories by
            rfl,
        length_histories_inl,
        filter_history_inl]
      cases history with
      | hallPair left right =>
          simp [RHistor.isLeftTriple, RHistor.isBasic]
          omega
      | conjugate emittedParent emitted =>
          cases emitted <;> cases emittedParent <;>
            simp [RHistor.isLeftTriple, RHistor.isBasic] ;
            omega

/-- Crossing one right atom preserves left-triple cardinality in a list. -/
lemma filter_history_inr
    {M N : ℕ}
    (parent : Fin N) :
    ∀ histories : List (RHistor M N),
      ((inverseConjHistory [Sum.inr parent] histories).filter
        RHistor.isLeftTriple).length =
          (histories.filter RHistor.isLeftTriple).length
  | [] => by
      rfl
  | history :: histories => by
      rw [inverseConjHistory, List.flatMap_cons, List.filter_append,
        List.length_append]
      rw [show
          inverseConjHistories [Sum.inr parent] history =
            conjugateAtomHistories (Sum.inr parent) history by
            rfl,
        show
          List.flatMap (inverseConjHistories [Sum.inr parent]) histories =
            inverseConjHistory [Sum.inr parent] histories by
            rfl,
        length_histories_inr,
        filter_history_inr]
      cases history with
      | hallPair left right =>
          simp [RHistor.isLeftTriple]
      | conjugate emittedParent emitted =>
          cases emitted <;> cases emittedParent <;>
            simp [RHistor.isLeftTriple] ;
            omega

/-- Crossing one right atom adds one right triple for each root in a list. -/
lemma length_history_inr
    {M N : ℕ}
    (parent : Fin N) :
    ∀ histories : List (RHistor M N),
      ((inverseConjHistory [Sum.inr parent] histories).filter
        RHistor.isRightTriple).length =
          (histories.filter RHistor.isRightTriple).length +
            (histories.filter RHistor.isBasic).length
  | [] => by
      rfl
  | history :: histories => by
      rw [inverseConjHistory, List.flatMap_cons, List.filter_append,
        List.length_append]
      rw [show
          inverseConjHistories [Sum.inr parent] history =
            conjugateAtomHistories (Sum.inr parent) history by
            rfl,
        show
          List.flatMap (inverseConjHistories [Sum.inr parent]) histories =
            inverseConjHistory [Sum.inr parent] histories by
            rfl,
        atom_histories_inr,
        length_history_inr]
      cases history with
      | hallPair left right =>
          simp [RHistor.isRightTriple, RHistor.isBasic]
          omega
      | conjugate emittedParent emitted =>
          cases emitted <;> cases emittedParent <;>
            simp [RHistor.isRightTriple, RHistor.isBasic] ;
            omega

/-- Crossing one left atom preserves right-triple cardinality in a list. -/
lemma length_history_inl
    {M N : ℕ}
    (parent : Fin M) :
    ∀ histories : List (RHistor M N),
      ((inverseConjHistory [Sum.inl parent] histories).filter
        RHistor.isRightTriple).length =
          (histories.filter RHistor.isRightTriple).length
  | [] => by
      rfl
  | history :: histories => by
      rw [inverseConjHistory, List.flatMap_cons, List.filter_append,
        List.length_append]
      rw [show
          inverseConjHistories [Sum.inl parent] history =
            conjugateAtomHistories (Sum.inl parent) history by
            rfl,
        show
          List.flatMap (inverseConjHistories [Sum.inl parent]) histories =
            inverseConjHistory [Sum.inl parent] histories by
            rfl,
        atom_histories_inl,
        length_history_inl]
      cases history with
      | hallPair left right =>
          simp [RHistor.isRightTriple]
      | conjugate emittedParent emitted =>
          cases emitted <;> cases emittedParent <;>
            simp [RHistor.isRightTriple] ;
            omega

/-- A right row has no left-parent triple histories. -/
lemma length_inverse_histories
    {M N : ℕ}
    (left : LabelledAtom M N) :
    ∀ rights : List (Fin N),
      ((inverseRightHistories left
        (rights.map fun right => (Sum.inr right : LabelledAtom M N))).filter
          RHistor.isLeftTriple).length = 0
  | [] => by
      rfl
  | right :: rights => by
      rw [List.map_cons, inverseRightHistories]
      simp only [List.filter_cons, RHistor.isLeftTriple, Bool.false_eq_true,
        if_false]
      rw [filter_history_inr,
        length_inverse_histories]

/-- A right row has one right-parent triple for each unordered right pair. -/
lemma filter_triple_histories
    {M N : ℕ}
    (left : LabelledAtom M N) :
    ∀ rights : List (Fin N),
      ((inverseRightHistories left
        (rights.map fun right => (Sum.inr right : LabelledAtom M N))).filter
          RHistor.isRightTriple).length =
        Nat.choose rights.length 2
  | [] => by
      rfl
  | right :: rights => by
      rw [List.map_cons, inverseRightHistories]
      simp only [List.filter_cons, RHistor.isRightTriple,
        Bool.false_eq_true, if_false]
      rw [length_history_inr,
        filter_triple_histories,
        length_basic_histories]
      simp [Nat.choose_succ_succ, Nat.add_comm]

/-- The complete inverse trace has `choose M 2 * N` left-parent triples. -/
lemma length_triple_histories
    {M N : ℕ} :
    ∀ (lefts : List (Fin M)) (rights : List (Fin N)),
      ((inverseLeftHistories
          (lefts.map fun left => (Sum.inl left : LabelledAtom M N))
          (rights.map fun right => (Sum.inr right : LabelledAtom M N))).filter
        RHistor.isLeftTriple).length =
          Nat.choose lefts.length 2 * rights.length
  | [], rights => by
      simp [inverseLeftHistories]
  | left :: lefts, rights => by
      rw [List.map_cons, inverseLeftHistories, List.filter_append,
        List.length_append,
        filter_history_inl,
        length_triple_histories,
        filter_basic_histories,
        length_inverse_histories]
      rw [show (left :: lefts).length = lefts.length + 1 by rfl,
        Nat.choose_succ_succ']
      simp
      ring

/-- The complete inverse trace has `M * choose N 2` right-parent triples. -/
lemma length_filter_histories
    {M N : ℕ} :
    ∀ (lefts : List (Fin M)) (rights : List (Fin N)),
      ((inverseLeftHistories
          (lefts.map fun left => (Sum.inl left : LabelledAtom M N))
          (rights.map fun right => (Sum.inr right : LabelledAtom M N))).filter
        RHistor.isRightTriple).length =
          lefts.length * Nat.choose rights.length 2
  | [], rights => by
      simp [inverseLeftHistories]
  | left :: lefts, rights => by
      rw [List.map_cons, inverseLeftHistories, List.filter_append,
        List.length_append,
        length_history_inl,
        length_filter_histories,
        filter_triple_histories]
      simp [Nat.succ_mul]

/-- The inverse raw trace has `choose M 2 * N` left-parent triples. -/
lemma filter_raw_histories
    (M N : ℕ) :
    ((inverseRawHistories M N).filter RHistor.isLeftTriple).length =
      Nat.choose M 2 * N := by
  simpa [inverseRawHistories, labelledLeftAtoms, labelledRightAtoms] using
    length_triple_histories
      (List.ofFn fun left : Fin M => left)
      (List.ofFn fun right : Fin N => right)

/-- The inverse raw trace has `M * choose N 2` right-parent triples. -/
lemma length_raw_histories
    (M N : ℕ) :
    ((inverseRawHistories M N).filter RHistor.isRightTriple).length =
      M * Nat.choose N 2 := by
  simpa [inverseRawHistories, labelledLeftAtoms, labelledRightAtoms] using
    length_filter_histories
      (List.ofFn fun left : Fin M => left)
      (List.ofFn fun right : Fin N => right)

/--
Through cutoff four and above weight three, retained histories are exactly
the roots and the two one-parent triple layers.
-/
lemma histories_layers_four
    {M N n : ℕ}
    (hlow : 3 < n)
    (hhigh : n ≤ 4)
    (histories : List (RHistor M N)) :
    retainedHistories n 1 1 histories =
      histories.filter fun history =>
        RHistor.isBasic history ||
          RHistor.isLeftTriple history ||
            RHistor.isRightTriple history := by
  unfold retainedHistories
  apply congrArg (fun predicate => histories.filter predicate)
  funext history
  cases history with
  | hallPair left right =>
      have hleft :
          HPAtom.weight 1 1 (collapseLabel left) = 1 := by
        cases left <;> rfl
      have hright :
          HPAtom.weight 1 1 (collapseLabel right) = 1 := by
        cases right <;> rfl
      simp [RHistor.isBasic, RHistor.isLeftTriple,
        RHistor.isRightTriple, hleft, hright]
      omega
  | conjugate parent emitted =>
      cases emitted with
      | hallPair left right =>
          have hleft :
              HPAtom.weight 1 1 (collapseLabel left) = 1 := by
            cases left <;> rfl
          have hright :
              HPAtom.weight 1 1 (collapseLabel right) = 1 := by
            cases right <;> rfl
          have hparent :
              HPAtom.weight 1 1 (collapseLabel parent) = 1 := by
            cases parent <;> rfl
          cases parent <;>
            simp [RHistor.isBasic, RHistor.isLeftTriple,
              RHistor.isRightTriple, hleft, hright, hparent] <;>
            omega
      | conjugate emittedParent emitted =>
          have hemittedMin :
              2 ≤ RHistor.weight 1 1 emitted :=
            RHistor.two_weight_one emitted
          have hparent :
              HPAtom.weight 1 1 (collapseLabel parent) = 1 := by
            cases parent <;> rfl
          have hemittedParent :
              HPAtom.weight 1 1 (collapseLabel emittedParent) = 1 := by
            cases emittedParent <;> rfl
          cases parent <;> cases emittedParent <;>
            simp [RHistor.isBasic, RHistor.isLeftTriple,
              RHistor.isRightTriple, hparent, hemittedParent] <;>
            omega

end THCard
end TCTex
end Towers

/-!
# Finite-index profile kernels for retained inverse-raw shape fibers

The retained inverse-raw packet is encoded by a trace over one fixed finite
polynomial-orbit alphabet.  This file states raw stabilization directly at
that finite-index level: one multiplicity-independent homogeneous profile for
each erased Hall word must count the corresponding filtered source trace.

The exact source-trace bridge then compiles this finite-alphabet counting
kernel to the uniform retained-raw profile kernel consumed by the cutoff-full
collector split.  Conversely, every uniform raw profile kernel satisfies the
finite-index formulation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace
  FIProf

open HACoeff
open CRLayer
open
  CRInv
open
  RHSplit
open
  FUBounda
open
  CFSubsti
open
  RFIndex
open
  UCSuppor
open
  RITrace
open
  IEDecomp

/--
One multiplicity-independent homogeneous profile per retained erased Hall
word, stated directly as a filtered finite source-index trace count.
-/
structure RFProf
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  profiles :
    ∀ word ∈ erasedShapeVocabulary n leftWeight rightWeight,
      HFPkt
        word.pairLeftDegree word.pairRightDegree
  profiles_cast_trace :
    ∀ (M N : ℕ) word hword,
      (profiles word hword).value (M : ℤ) (N : ℤ) =
        (((universalIndexTrace
          M N n leftWeight rightWeight hleftWeight hrightWeight).filter
            (fun index =>
              decide
                ((retainedOrbitKey index).erasedShape = word))).length :
                  ℤ)

namespace RFProf

/--
A fixed finite-index raw profile kernel supplies the uniform raw profile
kernel consumed by the cutoff-full scheduler split.
-/
def fiberUniformProfile
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight) :
    FUProf n leftWeight rightWeight where
  profiles :=
    kernel.profiles
  profiles_cast_local M N word hword := by
    rw [
      fiber_cast_filter
        M N n leftWeight rightWeight hleftWeight hrightWeight word]
    exact
      kernel.profiles_cast_trace
        M N word hword

end RFProf

namespace FUProf

/--
Every uniform raw profile kernel also satisfies the exact finite-index
source-trace counting interface.
-/
def idxFiberProfile
    {n leftWeight rightWeight : ℕ}
    (kernel :
      FUProf n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight where
  profiles :=
    kernel.profiles
  profiles_cast_trace M N word hword := by
    rw [kernel.profiles_cast_local M N word hword]
    exact
      fiber_cast_filter
        M N n leftWeight rightWeight hleftWeight hrightWeight word

end FUProf

namespace EFSplit

/--
Finite-index raw-history profiles and retained scheduler-correction profiles
supply the history-correction endpoint-fiber split directly.
-/
def idx_shape_fiber
    {n leftWeight rightWeight : ℕ}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    {layer : NRLayer n leftWeight rightWeight}
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (retainedCorrectionProfiles :
      ∀ word ∈ erasedShapeVocabulary n leftWeight rightWeight,
        HFPkt
          word.pairLeftDegree word.pairRightDegree)
    (retained_correction_cast :
      ∀ (M N : ℕ) word hword,
        (retainedCorrectionProfiles word hword).value (M : ℤ) (N : ℤ) =
          ((((endpointCorrectionInventory layer M N).corrections.filter
            fun term =>
              decide (term.family.recipe.erasedShape = word)).length : ℕ) :
                ℤ)) :
    EFSplit layer :=
  FUBounda.EFSplit.fiber_uniform_profile
    raw.fiberUniformProfile
      retainedCorrectionProfiles
      retained_correction_cast

end EFSplit

end
  FIProf
end TCTex
end Towers

/-!
# Class-three cutoff-full endpoint shape-fiber cardinalities

Actual inverse raw histories have oriented roots: every root starts with a
left-labelled atom and ends with a right-labelled atom.  Under this invariant,
the three structural layers below weight four are exactly the basic Hall-pair
word and the two inverse-oriented triple words.

This file transports the raw-history counts through retained raw terms and
shallow cutoff-full collection.  The resulting endpoint recipe-shape fibers
have the standard class-three cardinalities.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace CFCard

open HACoeff
open THCard
open FFCard
open
  CTBoundaa
open CRLayer
open SFCard
open RHRecurs
open RHRecipe
open HHTrunc
open RRTrunc
open
  CTPacket

abbrev rawHistoryBasic
    {M N : ℕ} :
    RHistor M N → Bool :=
  CTBoundaa.RHistor.isBasic

abbrev historyLeftTriple
    {M N : ℕ} :
    RHistor M N → Bool :=
  THCard.RHistor.isLeftTriple

abbrev rawHistoryTriple
    {M N : ℕ} :
    RHistor M N → Bool :=
  THCard.RHistor.isRightTriple

namespace ROrient

/-- Collapsing labels preserves the root commutator form of a basic history. -/
@[simp]
lemma collapse_word_pair
    {M N : ℕ}
    (left right : LabelledAtom M N) :
    collapseWord (RHistor.hallPair left right).word =
      .commutator (.atom (collapseLabel left)) (.atom (collapseLabel right)) :=
  rfl

/-- Collapsing labels commutes with the root swap in a conjugate history. -/
@[simp]
lemma collapse_conjugate
    {M N : ℕ}
    (parent : LabelledAtom M N)
    (emitted : RHistor M N) :
    collapseWord (RHistor.conjugate parent emitted).word =
      .commutator (rootSwapWord (collapseWord emitted.word))
        (.atom (collapseLabel parent)) := by
  rw [RHistor.word_conjugate]
  change
    CWord.commutator (collapseWord (rootSwapWord emitted.word))
      (.atom (collapseLabel parent)) =
        CWord.commutator (rootSwapWord (collapseWord emitted.word))
          (.atom (collapseLabel parent))
  rw [collapse_root_swap]

/-- Swapping the Hall-pair base reverses its two atoms. -/
@[simp]
lemma root_swap_base :
    rootSwapWord CWord.hallPairBase =
      .commutator (.atom .right) (.atom .left) :=
  rfl

/-- Swapping a collapsed basic history reverses its two collapsed atoms. -/
@[simp]
lemma swap_collapse_pair
    {M N : ℕ}
    (left right : LabelledAtom M N) :
    rootSwapWord (collapseWord (RHistor.hallPair left right).word) =
      .commutator (.atom (collapseLabel right)) (.atom (collapseLabel left)) :=
  rfl

/-- Swapping a collapsed conjugate history exposes its newest parent atom. -/
@[simp]
lemma swap_collapse_conjugate
    {M N : ℕ}
    (parent : LabelledAtom M N)
    (emitted : RHistor M N) :
    rootSwapWord (collapseWord (RHistor.conjugate parent emitted).word) =
      .commutator (.atom (collapseLabel parent))
        (rootSwapWord (collapseWord emitted.word)) := by
  rw [collapse_conjugate]
  rfl

/-- One conjugation of a root has the canonical collapsed triple form. -/
@[simp]
lemma collapse_conjugate_pair
    {M N : ℕ}
    (parent left right : LabelledAtom M N) :
    collapseWord (RHistor.conjugate parent (.hallPair left right)).word =
      .commutator
        (.commutator (.atom (collapseLabel right)) (.atom (collapseLabel left)))
        (.atom (collapseLabel parent)) := by
  rw [collapse_conjugate]
  rfl

/-- Two conjugations expose a nested commutator after collapsing labels. -/
@[simp]
lemma collapse_word_conjugate
    {M N : ℕ}
    (parent emittedParent : LabelledAtom M N)
    (emitted : RHistor M N) :
    collapseWord
        (RHistor.conjugate parent (.conjugate emittedParent emitted)).word =
      .commutator
        (.commutator (.atom (collapseLabel emittedParent))
          (rootSwapWord (collapseWord emitted.word)))
        (.atom (collapseLabel parent)) := by
  rw [collapse_conjugate,
    swap_collapse_conjugate]

/-- A swapped collapsed raw-history word is still a commutator, never an atom. -/
@[simp]
lemma swap_collapse_atom
    {M N : ℕ}
    (history : RHistor M N)
    (atom : HPAtom) :
    rootSwapWord (collapseWord history.word) ≠ .atom atom := by
  cases history <;>
    simp [RHistor.word, collapseWord, rootSwapWord]

/-- A conjugate history cannot collapse back to the basic Hall-pair word. -/
lemma collapse_conjugate_base
    {M N : ℕ}
    (parent : LabelledAtom M N)
    (emitted : RHistor M N) :
    collapseWord (RHistor.conjugate parent emitted).word ≠
      CWord.hallPairBase := by
  rw [collapse_conjugate]
  intro heq
  injection heq with hroot _hparent
  exact swap_collapse_atom emitted .left hroot

/-- A history with at least two conjugation parents cannot be a triple word. -/
lemma collapse_conjugate_triple
    {M N : ℕ}
    (parent emittedParent : LabelledAtom M N)
    (emitted : RHistor M N)
    (targetParent : HPAtom) :
    collapseWord
        (RHistor.conjugate parent (.conjugate emittedParent emitted)).word ≠
      .commutator (rootSwapWord CWord.hallPairBase)
        (.atom targetParent) := by
  rw [collapse_word_conjugate]
  intro heq
  injection heq with hinner _hparent
  injection hinner with _hemittedParent hroot
  exact swap_collapse_atom emitted .left hroot

/-- Every actual inverse raw history has a left-right-oriented root. -/
def RootOriented
    {M N : ℕ} :
    RHistor M N → Prop
  | .hallPair left right =>
      collapseLabel left = .left ∧ collapseLabel right = .right
  | .conjugate _ emitted =>
      RootOriented emitted

/-- An oriented history has the basic Hall shape exactly when it is a root. -/
lemma decide_collapse_oriented
    {M N : ℕ}
    (history : RHistor M N)
    (horiented : RootOriented history) :
    decide (collapseWord history.word = CWord.hallPairBase) =
      rawHistoryBasic history := by
  induction history with
  | hallPair left right =>
      rcases horiented with ⟨hleft, hright⟩
      simp [RHistor.word, collapseWord, CWord.hallPairBase,
        rawHistoryBasic,
        CTBoundaa.RHistor.isBasic,
        hleft, hright]
  | conjugate parent emitted ih =>
      have hdecide :
          decide
              (collapseWord (RHistor.conjugate parent emitted).word =
                CWord.hallPairBase) =
            false := by
        rw [decide_eq_false_iff_not]
        exact collapse_conjugate_base parent emitted
      simpa [rawHistoryBasic,
        CTBoundaa.RHistor.isBasic] using
          hdecide

/-- An oriented history has the left triple shape exactly at its left-parent layer. -/
lemma decide_root_oriented
    {M N : ℕ}
    (history : RHistor M N)
    (horiented : RootOriented history) :
    decide (collapseWord history.word = inverseLeftTriple) =
      historyLeftTriple history := by
  induction history with
  | hallPair left right =>
      rcases horiented with ⟨hleft, hright⟩
      simp [RHistor.word, collapseWord, inverseLeftTriple,
        CWord.hallPairBase, historyLeftTriple,
        THCard.RHistor.isLeftTriple,
        hleft, hright]
  | conjugate parent emitted ih =>
      cases emitted with
      | hallPair left right =>
          rcases horiented with ⟨hleft, hright⟩
          rw [collapse_conjugate_pair]
          cases parent <;>
            simp [inverseLeftTriple, CWord.hallPairBase,
              historyLeftTriple,
              THCard.RHistor.isLeftTriple,
              rootSwapWord, hleft, hright] <;>
            simp [collapseLabel]
      | conjugate emittedParent emitted =>
          have hdecide :
              decide
                  (collapseWord
                      (RHistor.conjugate parent
                        (.conjugate emittedParent emitted)).word =
                    inverseLeftTriple) =
                false := by
            rw [decide_eq_false_iff_not]
            exact
              collapse_conjugate_triple
                parent emittedParent emitted .left
          simpa [inverseLeftTriple, historyLeftTriple,
            THCard.RHistor.isLeftTriple] using
              hdecide

/-- An oriented history has the right triple shape exactly at its right-parent layer. -/
lemma decide_triple_oriented
    {M N : ℕ}
    (history : RHistor M N)
    (horiented : RootOriented history) :
    decide (collapseWord history.word = inverseTripleWord) =
      rawHistoryTriple history := by
  induction history with
  | hallPair left right =>
      rcases horiented with ⟨hleft, hright⟩
      simp [RHistor.word, collapseWord, inverseTripleWord,
        CWord.hallPairBase, rawHistoryTriple,
        THCard.RHistor.isRightTriple,
        rootSwapWord, hleft, hright]
  | conjugate parent emitted ih =>
      cases emitted with
      | hallPair left right =>
          rcases horiented with ⟨hleft, hright⟩
          rw [collapse_conjugate_pair]
          cases parent <;>
            simp [inverseTripleWord, CWord.hallPairBase,
              rawHistoryTriple,
              THCard.RHistor.isRightTriple,
              rootSwapWord, hleft, hright] <;>
            simp [collapseLabel]
      | conjugate emittedParent emitted =>
          have hdecide :
              decide
                  (collapseWord
                      (RHistor.conjugate parent
                        (.conjugate emittedParent emitted)).word =
                    inverseTripleWord) =
                false := by
            rw [decide_eq_false_iff_not]
            exact
              collapse_conjugate_triple
                parent emittedParent emitted .right
          simpa [inverseTripleWord, rawHistoryTriple,
            THCard.RHistor.isRightTriple] using
              hdecide

end ROrient

/-- Conjugating an oriented history across any atom preserves root orientation. -/
lemma oriented_conj_histories
    {M N : ℕ} :
    ∀ (parents : List (LabelledAtom M N))
      (emitted history : RHistor M N),
      ROrient.RootOriented emitted →
        history ∈ inverseConjHistories parents emitted →
          ROrient.RootOriented history
  | [], emitted, history, horiented, hhistory => by
      simp only [inverseConjHistories, List.mem_singleton] at hhistory
      subst history
      exact horiented
  | parent :: parents, emitted, history, horiented, hhistory => by
      rw [inverseConjHistories, List.mem_flatMap] at hhistory
      rcases hhistory with ⟨next, hnext, hhistory⟩
      have hnextOriented :=
        oriented_conj_histories
          parents emitted next horiented hnext
      simp only [conjugateAtomHistories, List.mem_cons,
        List.not_mem_nil, or_false] at hhistory
      rcases hhistory with rfl | rfl
      · exact hnextOriented
      · exact hnextOriented

/-- Conjugating an oriented history list preserves root orientation. -/
lemma root_oriented_history
    {M N : ℕ}
    (parents : List (LabelledAtom M N))
    (histories : List (RHistor M N))
    (horiented : ∀ history ∈ histories, ROrient.RootOriented history) :
    ∀ history ∈ inverseConjHistory parents histories,
      ROrient.RootOriented history := by
  intro history hhistory
  rw [inverseConjHistory, List.mem_flatMap] at hhistory
  rcases hhistory with ⟨emitted, hemitted, hhistory⟩
  exact oriented_conj_histories
    parents emitted history (horiented emitted hemitted) hhistory

/-- Every history in one oriented right row has an oriented root. -/
lemma oriented_inverse_histories
    {M N : ℕ}
    (left : LabelledAtom M N)
    (hleft : collapseLabel left = .left) :
    ∀ (rights : List (LabelledAtom M N)),
      (∀ right ∈ rights, collapseLabel right = .right) →
        ∀ history ∈ inverseRightHistories left rights,
          ROrient.RootOriented history
  | [], hrights, history, hhistory => by
      simp [inverseRightHistories] at hhistory
  | right :: rights, hrights, history, hhistory => by
      rw [inverseRightHistories] at hhistory
      rcases List.mem_cons.mp hhistory with rfl | hhistory
      · exact ⟨hleft, hrights right (by simp)⟩
      · exact
          root_oriented_history [right]
            (inverseRightHistories left rights)
            (oriented_inverse_histories left hleft rights
              (fun next hnext => hrights next (by simp [hnext])))
            history hhistory

/-- Every history in an oriented left-right trace has an oriented root. -/
lemma root_oriented_histories
    {M N : ℕ} :
    ∀ (lefts rights : List (LabelledAtom M N)),
      (∀ left ∈ lefts, collapseLabel left = .left) →
        (∀ right ∈ rights, collapseLabel right = .right) →
          ∀ history ∈ inverseLeftHistories lefts rights,
            ROrient.RootOriented history
  | [], rights, hlefts, hrights, history, hhistory => by
      simp [inverseLeftHistories] at hhistory
  | left :: lefts, rights, hlefts, hrights, history, hhistory => by
      rw [inverseLeftHistories] at hhistory
      rcases List.mem_append.mp hhistory with hhistory | hhistory
      · exact
          root_oriented_history [left]
            (inverseLeftHistories lefts rights)
            (root_oriented_histories lefts rights
              (fun next hnext => hlefts next (by simp [hnext])) hrights)
            history hhistory
      · exact
          oriented_inverse_histories left
            (hlefts left (by simp)) rights hrights history hhistory

/-- Every actual inverse raw history has an oriented root. -/
lemma oriented_raw_histories
    {M N : ℕ}
    {history : RHistor M N}
    (hhistory : history ∈ inverseRawHistories M N) :
    ROrient.RootOriented history := by
  apply root_oriented_histories
    (labelledLeftAtoms M N) (labelledRightAtoms M N)
  · intro left hleft
    exact collapse_label_atoms hleft
  · intro right hright
    exact collapse_labelled_atoms hright
  · exact hhistory

/-- Filtering retained raw terms by erased shape is filtering retained
histories by collapsed word. -/
lemma length_collapse_histories
    (M N n : ℕ)
    (word : CWord HPAtom) :
    ((retainedRawTerms M N n 1 1).filter fun term =>
      decide (term.erasedShape = word)).length =
        ((retainedHistories n 1 1 (inverseRawHistories M N)).filter fun history =>
          decide (collapseWord history.word = word)).length := by
  have hwords :=
    congrArg
      (fun words =>
        (words.filter fun next => decide (collapseWord next = word)).length)
      (history_words_histories
        M N n 1 1)
  simpa [historyWords, decoratedFamilyList, List.filter_map,
    DFTerm.erasedShape, DTerm.erasedShape] using hwords.symm

/-- Filtering twice is redundant when the inner Boolean predicate implies the outer one. -/
lemma filter_imp
    {α : Type*}
    (outer inner : α → Bool)
    (himp : ∀ value, inner value = true → outer value = true)
    (values : List α) :
    (values.filter outer).filter inner = values.filter inner := by
  induction values with
  | nil =>
      rfl
  | cons value values ih =>
      by_cases hinner : inner value = true
      · have houter := himp value hinner
        simp [hinner, houter, ih]
      · by_cases houter : outer value = true
        · simp [hinner, houter, ih]
        · simp [hinner, houter, ih]

/-- The retained basic-shape history fiber has cardinality `M * N`. -/
lemma collapse_base_histories
    {M N n : ℕ}
    (hlow : 3 < n)
    (hhigh : n ≤ 4) :
    ((retainedHistories n 1 1 (inverseRawHistories M N)).filter fun history =>
      decide (collapseWord history.word = CWord.hallPairBase)).length =
        M * N := by
  rw [show
    (retainedHistories n 1 1 (inverseRawHistories M N)).filter
        (fun history =>
          decide (collapseWord history.word = CWord.hallPairBase)) =
      (retainedHistories n 1 1 (inverseRawHistories M N)).filter
        rawHistoryBasic by
      apply List.filter_congr
      intro history hhistory
      exact
        ROrient.decide_collapse_oriented
          history
          (oriented_raw_histories
            (mem_retainedHistories.mp hhistory).1)]
  rw [histories_layers_four
    hlow hhigh,
    filter_imp]
  · simpa [inverseRawHistories, labelledLeftAtoms, labelledRightAtoms] using
      filter_basic_histories
        (labelledLeftAtoms M N) (labelledRightAtoms M N)
  · intro history hhistory
    simpa only [Bool.or_eq_true] using (Or.inl (Or.inl hhistory))

/-- The retained left-triple history fiber has cardinality `choose M 2 * N`. -/
lemma collapse_triple_histories
    {M N n : ℕ}
    (hlow : 3 < n)
    (hhigh : n ≤ 4) :
    ((retainedHistories n 1 1 (inverseRawHistories M N)).filter fun history =>
      decide (collapseWord history.word = inverseLeftTriple)).length =
        Nat.choose M 2 * N := by
  rw [show
    (retainedHistories n 1 1 (inverseRawHistories M N)).filter
        (fun history => decide (collapseWord history.word = inverseLeftTriple)) =
      (retainedHistories n 1 1 (inverseRawHistories M N)).filter
        historyLeftTriple by
      apply List.filter_congr
      intro history hhistory
      exact
        ROrient.decide_root_oriented
          history
          (oriented_raw_histories
            (mem_retainedHistories.mp hhistory).1)]
  rw [histories_layers_four
    hlow hhigh,
    filter_imp]
  · exact filter_raw_histories M N
  · intro history hhistory
    simpa only [Bool.or_eq_true] using (Or.inl (Or.inr hhistory))

/-- The retained right-triple history fiber has cardinality `M * choose N 2`. -/
lemma filter_collapse_histories
    {M N n : ℕ}
    (hlow : 3 < n)
    (hhigh : n ≤ 4) :
    ((retainedHistories n 1 1 (inverseRawHistories M N)).filter fun history =>
      decide (collapseWord history.word = inverseTripleWord)).length =
        M * Nat.choose N 2 := by
  rw [show
    (retainedHistories n 1 1 (inverseRawHistories M N)).filter
        (fun history => decide (collapseWord history.word = inverseTripleWord)) =
      (retainedHistories n 1 1 (inverseRawHistories M N)).filter
        rawHistoryTriple by
      apply List.filter_congr
      intro history hhistory
      exact
        ROrient.decide_triple_oriented
          history
          (oriented_raw_histories
            (mem_retainedHistories.mp hhistory).1)]
  rw [histories_layers_four
    hlow hhigh,
    filter_imp]
  · exact length_raw_histories M N
  · intro history hhistory
    simpa only [Bool.or_eq_true] using (Or.inr hhistory)

/-- The cutoff-full class-three basic fiber has cardinality `M * N`. -/
lemma endpoint_n_four
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hlow : 3 < n)
    (hhigh : n ≤ 4)
    (M N : ℕ) :
    endpointRecipeMultiplicity layer M N CWord.hallPairBase =
      M * N := by
  rw [endpoint_multiplicity_erased,
    endpoint_filter_four
      layer hhigh,
    length_collapse_histories,
    collapse_base_histories hlow hhigh]

/-- The cutoff-full class-three left-triple fiber has cardinality `choose M 2 * N`. -/
lemma mult_n_four
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hlow : 3 < n)
    (hhigh : n ≤ 4)
    (M N : ℕ) :
    endpointRecipeMultiplicity layer M N inverseLeftTriple =
      Nat.choose M 2 * N := by
  rw [endpoint_multiplicity_erased,
    endpoint_filter_four
      layer hhigh,
    length_collapse_histories,
    collapse_triple_histories
      hlow hhigh]

/-- The cutoff-full class-three right-triple fiber has cardinality `M * choose N 2`. -/
lemma endpoint_mult_four
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hlow : 3 < n)
    (hhigh : n ≤ 4)
    (M N : ℕ) :
    endpointRecipeMultiplicity layer M N inverseTripleWord =
      M * Nat.choose N 2 := by
  rw [endpoint_multiplicity_erased,
    endpoint_filter_four
      layer hhigh,
    length_collapse_histories,
    filter_collapse_histories
      hlow hhigh]

end CFCard
end TCTex
end Towers

/-!
# Finite-index form of retained inverse-raw transversal stabilization

The canonical retained inverse-raw profile candidate chooses one cutoff-sized
source recipe from every polynomial orbit.  Its stabilization theorem was
originally stated against the multiplicity-dependent local recipe profile.

The finite-index source-fiber bridge gives an equivalent concrete target:
the canonical transversal profile must count filtered traces over the fixed
polynomial-orbit alphabet.  This file records that reduction and compiles the
transversal stabilization kernel directly to the finite-index profile kernel.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace
  TFIdx

open HACoeff
open
  FIProf
open
  RFTransv
open
  RFIndex
open
  UCSuppor
open
  RITrace
open
  IEDecomp

/--
The canonical transversal stabilization law specializes to exact filtered
finite source-index trace counts.
-/
lemma
    transversal_cast_filter
    {n leftWeight rightWeight : ℕ}
    (kernel :
      PTStab
        n leftWeight rightWeight)
    (M N : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom)
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    (rawTransversalProfile
      n leftWeight rightWeight word).value (M : ℤ) (N : ℤ) =
        (((universalIndexTrace
          M N n leftWeight rightWeight hleftWeight hrightWeight).filter
            (fun index =>
              decide
                ((retainedOrbitKey index).erasedShape = word))).length :
                  ℤ) := by
  rw [kernel.profile_cast_local M N word hword]
  exact
    fiber_cast_filter
      M N n leftWeight rightWeight hleftWeight hrightWeight word

/--
Concrete finite-alphabet form of canonical retained inverse-raw transversal
stabilization.
-/
def SatisfiesTransversalCounts
    (n leftWeight rightWeight : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    Prop :=
  ∀ (M N : ℕ) word,
    word ∈ erasedShapeVocabulary n leftWeight rightWeight →
      (rawTransversalProfile
        n leftWeight rightWeight word).value (M : ℤ) (N : ℤ) =
          (((universalIndexTrace
            M N n leftWeight rightWeight hleftWeight hrightWeight).filter
              (fun index =>
                decide
                  ((retainedOrbitKey index).erasedShape =
                    word))).length : ℤ)

/--
The older local-profile stabilization kernel implies the concrete
finite-source-trace counting law.
-/
lemma
    satisfies_counts_stabilization
    {n leftWeight rightWeight : ℕ}
    (kernel :
      PTStab
        n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    SatisfiesTransversalCounts
      n leftWeight rightWeight hleftWeight hrightWeight := by
  intro M N word hword
  exact
    transversal_cast_filter
      kernel M N hleftWeight hrightWeight word hword

/--
Conversely, concrete finite-source-trace counting proves the older local
transversal stabilization interface.
-/
def transversalStabilizationCounts
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (hcounts :
      SatisfiesTransversalCounts
        n leftWeight rightWeight hleftWeight hrightWeight) :
    PTStab
      n leftWeight rightWeight where
  profile_cast_local M N word hword := by
    rw [
      fiber_cast_filter
        M N n leftWeight rightWeight hleftWeight hrightWeight word]
    exact hcounts M N word hword

/--
For positive source weights, canonical transversal stabilization is exactly
the finite-index source-trace fiber-counting theorem.
-/
theorem
    transversal_stabilization_counts
    {n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    PTStab
        n leftWeight rightWeight ↔
      SatisfiesTransversalCounts
        n leftWeight rightWeight hleftWeight hrightWeight :=
  ⟨fun kernel =>
      satisfies_counts_stabilization
        kernel hleftWeight hrightWeight,
    transversalStabilizationCounts
      hleftWeight hrightWeight⟩

namespace PTStab

/--
The canonical transversal stabilization kernel supplies the finite-alphabet
raw shape-fiber profile kernel directly.
-/
def idxFiberProfile
    {n leftWeight rightWeight : ℕ}
    (kernel :
      PTStab
        n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    RFProf
      n leftWeight rightWeight hleftWeight hrightWeight where
  profiles word _hword :=
    rawTransversalProfile
      n leftWeight rightWeight word
  profiles_cast_trace M N word hword :=
    transversal_cast_filter
      kernel M N hleftWeight hrightWeight word hword

end PTStab

end
  TFIdx
end TCTex
end Towers

/-!
# Finite-index shape fibers for cutoff-full retained corrections

The cutoff-full scheduler records an ordered list of generated corrections
that survive the nilpotent cutoff.  Every such correction has an erased-word
representative in the fixed finite correction-closure vocabulary.

This file chooses one representative occurrence-by-occurrence, encodes the
resulting ordered packet by indices into the finite polynomial-orbit
dictionary, and proves that filtering the index trace by erased Hall shape
counts the exact selected correction fiber.

The final compiler adapter combines a finite-index raw-source profile kernel
with a finite-index retained-correction profile kernel.  This leaves the
arbitrary-cutoff polynomial counting theorem as an explicit finite-alphabet
obligation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace
  ISFiber

open HACoeff
open ROSuppor
open ROAggreg
open CRLayer
open
  CRInv
open
  CMAccoun
open
  RHSplit
open
  FIProf
open
  CFSubsti
open
  UCSuppor
open UCVocabu
open
  RITrace
open
  PTRecipe

/-- Filtering a mapped list is the same cardinality as filtering its source
by the pulled-back predicate. -/
lemma length_filter
    {α β : Type*}
    (mapEntry : α → β)
    (predicate : β → Bool) :
    ∀ entries : List α,
      ((entries.map mapEntry).filter predicate).length =
        (entries.filter fun entry => predicate (mapEntry entry)).length
  | [] =>
      rfl
  | entry :: entries => by
      by_cases hentry : predicate (mapEntry entry) = true
      · simp [hentry,
          length_filter mapEntry predicate entries]
      · simp [hentry,
          length_filter mapEntry predicate entries]

/-- Choose one finite correction-closure representative for one selected
scheduler correction occurrence. -/
noncomputable def closureSelectedTerm
    {M N n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (term : DFTerm M N
      (inverseLabelledCollection M N).factors.length)
    (hterm :
      term ∈ (endpointCorrectionInventory layer M N).corrections) :
    BRecipe :=
  Classical.choose
    (recipe_endpoint_corrections
      layer hleftWeight hrightWeight M N hterm)

/-- The selected occurrence representative belongs to the finite correction
closure. -/
lemma closure_selected_term
    {M N n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (term : DFTerm M N
      (inverseLabelledCollection M N).factors.length)
    (hterm :
      term ∈ (endpointCorrectionInventory layer M N).corrections) :
    closureSelectedTerm
        layer hleftWeight hrightWeight term hterm ∈
      correctionClosureRecipes n leftWeight rightWeight :=
  (Classical.choose_spec
    (recipe_endpoint_corrections
      layer hleftWeight hrightWeight M N hterm)).1

/-- The selected occurrence representative has the concrete scheduler
correction's erased Hall word. -/
@[simp]
lemma erased_selected_term
    {M N n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (term : DFTerm M N
      (inverseLabelledCollection M N).factors.length)
    (hterm :
      term ∈ (endpointCorrectionInventory layer M N).corrections) :
    (closureSelectedTerm
      layer hleftWeight hrightWeight term hterm).erasedShape =
        term.erasedShape :=
  (Classical.choose_spec
    (recipe_endpoint_corrections
      layer hleftWeight hrightWeight M N hterm)).2

/-- Ordered finite-closure representatives of all selected scheduler
correction occurrences. -/
noncomputable def selectedClosurePacket
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List BRecipe :=
  (endpointCorrectionInventory layer M N).corrections.attach.map
    fun term =>
      closureSelectedTerm
        layer hleftWeight hrightWeight term.1 term.2

/-- Every representative in the selected correction packet belongs to the
finite correction closure. -/
lemma recipes_selected_packet
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {recipe : BRecipe}
    (hrecipe :
      recipe ∈ selectedClosurePacket
        layer M N hleftWeight hrightWeight) :
    recipe ∈ correctionClosureRecipes n leftWeight rightWeight := by
  unfold selectedClosurePacket at hrecipe
  rcases List.mem_map.mp hrecipe with ⟨term, _hterm, rfl⟩
  exact
    closure_selected_term
      layer hleftWeight hrightWeight term.1 term.2

/-- The selected correction representative packet is pointwise supported by
the retained polynomial-orbit dictionary. -/
lemma supported_selected_closure
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    RecipeOrbitSupported n leftWeight rightWeight
      (selectedClosurePacket
        layer M N hleftWeight hrightWeight) := by
  intro recipe hrecipe
  apply
    key_vocabulary_recipes
  exact
    recipes_selected_packet
      layer M N hleftWeight hrightWeight hrecipe

/-- Occurrence-preserving finite orbit-index trace of the selected scheduler
corrections. -/
noncomputable def selectedIndexTrace
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    List (RetainedOrbitIndex n leftWeight rightWeight) :=
  recipeIndexTrace
    (selectedClosurePacket
      layer M N hleftWeight hrightWeight)
    (supported_selected_closure
      layer M N hleftWeight hrightWeight)

/-- Decoding the selected correction trace recovers its ordered chosen
orbit-key packet literally. -/
lemma key_selected_trace
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) :
    (selectedIndexTrace
      layer M N hleftWeight hrightWeight).map retainedOrbitKey =
        (selectedClosurePacket
          layer M N hleftWeight hrightWeight).map polynomialOrbitKey := by
  unfold selectedIndexTrace
  exact
    key_recipe_trace
      (selectedClosurePacket
        layer M N hleftWeight hrightWeight)
      (supported_selected_closure
        layer M N hleftWeight hrightWeight)

/--
Filtering the selected scheduler-correction index trace by erased shape counts
exactly the corresponding concrete correction fiber.
-/
lemma
    key_selected_corrections
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (M N : ℕ)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    (word : CWord HPAtom) :
    ((selectedIndexTrace
      layer M N hleftWeight hrightWeight).filter fun index =>
        decide ((retainedOrbitKey index).erasedShape = word)).length =
      ((endpointCorrectionInventory layer M N).corrections.filter
        fun term =>
          decide (term.family.recipe.erasedShape = word)).length := by
  rw [←
    List.length_map
      (f := retainedOrbitKey)
      (as :=
        (selectedIndexTrace
          layer M N hleftWeight hrightWeight).filter fun index =>
            decide
              ((retainedOrbitKey index).erasedShape = word))]
  rw [show
    ((selectedIndexTrace
      layer M N hleftWeight hrightWeight).filter fun index =>
        decide ((retainedOrbitKey index).erasedShape = word)).map
          retainedOrbitKey =
      ((selectedIndexTrace
        layer M N hleftWeight hrightWeight).map
          retainedOrbitKey).filter fun key =>
            decide (key.erasedShape = word) by
      rw [List.filter_map]
      rfl]
  rw [
    key_selected_trace,
    length_filter]
  simp only [polynomialOrbitKey]
  unfold selectedClosurePacket
  rw [length_filter]
  simp only [
    erased_selected_term,
    DFTerm.erased_shape_family]
  let corrections :=
    (endpointCorrectionInventory layer M N).corrections
  let predicate :=
    fun term : DFTerm M N
      (inverseLabelledCollection M N).factors.length =>
        decide (term.family.recipe.erasedShape = word)
  change
    (corrections.attach.filter fun term => predicate term.1).length =
      (corrections.filter predicate).length
  simpa only [List.length_map, List.length_attach] using
    congrArg List.length (List.filter_attach corrections predicate)

/--
One multiplicity-independent homogeneous profile per retained erased Hall
word, stated directly as a filtered selected-correction index-trace count.
-/
structure SFProf
    {n leftWeight rightWeight : ℕ}
    (layer : NRLayer n leftWeight rightWeight)
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight) where
  profiles :
    ∀ word ∈ erasedShapeVocabulary n leftWeight rightWeight,
      HFPkt
        word.pairLeftDegree word.pairRightDegree
  profiles_nat_trace :
    ∀ (M N : ℕ) word hword,
      (profiles word hword).value (M : ℤ) (N : ℤ) =
        (((selectedIndexTrace
          layer M N hleftWeight hrightWeight).filter
            (fun index =>
              decide
                ((retainedOrbitKey index).erasedShape =
                  word))).length : ℤ)

namespace SFProf

/-- A finite-index correction kernel counts the concrete scheduler-correction
fibers consumed by the endpoint profile split. -/
lemma profiles_cast_corrections
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (kernel :
      SFProf
        layer hleftWeight hrightWeight)
    (M N : ℕ)
    (word : CWord HPAtom)
    (hword : word ∈ erasedShapeVocabulary n leftWeight rightWeight) :
    (kernel.profiles word hword).value (M : ℤ) (N : ℤ) =
      ((((endpointCorrectionInventory layer M N).corrections.filter
        fun term =>
          decide (term.family.recipe.erasedShape = word)).length : ℕ) : ℤ) := by
  rw [kernel.profiles_nat_trace M N word hword]
  exact
    congrArg (fun length : ℕ => (length : ℤ))
      (key_selected_corrections
        layer M N hleftWeight hrightWeight word)

end SFProf

namespace EFSplit

/--
Finite-index raw-source and selected scheduler-correction kernels compile
directly to the raw-history/correction endpoint-fiber split.
-/
def idx_fiber_profile
    {n leftWeight rightWeight : ℕ}
    {layer : NRLayer n leftWeight rightWeight}
    {hleftWeight : 0 < leftWeight}
    {hrightWeight : 0 < rightWeight}
    (raw :
      RFProf
        n leftWeight rightWeight hleftWeight hrightWeight)
    (corrections :
      SFProf
        layer hleftWeight hrightWeight) :
    EFSplit layer :=
  FIProf.EFSplit.idx_shape_fiber
    raw corrections.profiles corrections.profiles_cast_corrections

end EFSplit

end
  ISFiber
end TCTex
end Towers

/-!
# The class-three cutoff-full endpoint packet

Above weight three and through cutoff four, the cutoff-full endpoint has
exactly three erased-shape fibers: the inverse-oriented left triple, the basic
Hall pair, and the inverse-oriented right triple.  Their exact cardinalities
agree with the three retained recipe-coefficient profiles.

This file packages that scalar agreement as a homogeneous endpoint-fiber
presentation kernel and the resulting fixed natural stabilization record.
It is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace CCThreeb

open CFCard
open CFStab
open FFCard
open
  FFInhomo
open CRLayer
open NRSubinv
open
  CTPacket
open
  CTAssigna
open
  SWSep
open
  FCAssign
open UCSuppor

/--
The retained class-three recipe profiles count the three cutoff-full endpoint
shape fibers at natural source multiplicities.
-/
lemma coeff_n_four
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hlow : 3 < n)
    (hhigh : n ≤ 4) :
    (blockProfileAssignment n)
      |>.toSPAssign
      |>.CountsFibersCast layer := by
  intro M N word hword
  let selected :
      { next // next ∈ erasedShapeVocabulary n 1 1 } :=
    ⟨word, ordered_erased_vocabulary.mp hword⟩
  change
    (retainedRecipeProfiles selected).value (M : ℤ) (N : ℤ) =
      (endpointRecipeMultiplicity layer M N word : ℤ)
  rcases
      or_vocabulary_four
        hhigh selected.2 with
    hwordEq | hwordEq | hwordEq
  · have hwordEq' : word = inverseLeftTriple := by
      simpa [selected] using hwordEq
    rw [
      value_profiles_triple
        selected hwordEq,
      hwordEq',
      mult_n_four
        layer hlow hhigh]
    simp [Ring.choose_natCast]
  · have hwordEq' : word = CWord.hallPairBase := by
      simpa [selected] using hwordEq
    rw [
      value_profiles_base
        selected hwordEq,
      hwordEq',
      endpoint_n_four
        layer hlow hhigh]
    norm_cast
  · have hwordEq' : word = inverseTripleWord := by
      simpa [selected] using hwordEq
    rw [
      profiles_choose_triple
        selected hwordEq,
      hwordEq',
      endpoint_mult_four
        layer hlow hhigh]
    simp [Ring.choose_natCast]

/--
The retained class-three profiles promote to uniform unrestricted endpoint
packets with homogeneous presentations.
-/
def fiberHomogeneousFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hlow : 3 < n)
    (hhigh : n ≤ 4) :
    FHPres layer :=
  FHPres.counts_fibers_cast
    (blockProfileAssignment n
      |>.toSPAssign)
    (coeff_n_four
      layer hlow hhigh)

/-- The class-three endpoint packet kernel supplies fixed natural stabilization. -/
def runStabilizationFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hlow : 3 < n)
    (hhigh : n ≤ 4)
    (d : ℕ) :
    NRStab layer d
      ((fiberHomogeneousFour
          layer hlow hhigh).signedProfileAssignment
        |>.erasedVocabPackets) :=
  (fiberHomogeneousFour
      layer hlow hhigh).runPacketStabilization
    (by omega) (by omega) d

end CCThreeb
end TCTex
end Towers

/-!
# Uniform retained-raw profiles through cutoff four

The arbitrary-cutoff endpoint-fiber split separates the retained inverse-raw
packet from the corrections retained by the actual cutoff scheduler.  Through
cutoff four at root weights, the scheduler cannot retain any generated
correction: every correction has weight at least four.  This file derives
that fact from the exact traced-inventory decomposition and the shallow
filtered-cardinality theorem.

The retained-recipe singleton profile assignment already counts all endpoint
shape fibers in the same range.  Since the endpoint consists only of retained
raw terms, those profiles construct the uniform retained-raw profile kernel
required by the arbitrary-cutoff split.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace
  FUClass

open HACoeff
open
  CFCard
open
  FFCard
open
  CTBoundaa
open
  CCThreeb
open CRLayer
open
  NRSubinv
open
  CRInv
open
  RHSplit
open
  RFLocal
open
  FUBounda
open
  SFCard
open
  CFAlg
open
  CFSubsti
open
  CTAssigna
open
  FTCollec
open
  CPSplit
open
  FCAssign
open
  UCSuppor
open RRTrunc

/--
Through cutoff four at root weights, the selected traced scheduler inventory
contains no retained generated corrections.
-/
lemma inventory_corrections_nil
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (M N : ℕ) :
    (endpointCorrectionInventory layer M N).corrections = [] := by
  apply List.length_eq_zero_iff.mp
  have hsplit :=
    filter_length_corrections
      layer M N (fun _term => true)
  have hshallow :=
    endpoint_filter_length
      layer hhigh M N (fun _term => true)
  simp only [List.filter_true] at hsplit hshallow
  omega

/-- Every retained scheduler-correction shape fiber is empty in the same range. -/
lemma inventory_corrections_four
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (M N : ℕ)
    (word : CWord HPAtom) :
    (((endpointCorrectionInventory layer M N).corrections.filter
      fun term => decide (term.family.recipe.erasedShape = word)).length : ℤ) =
        0 := by
  rw [inventory_corrections_nil
    layer hhigh M N]
  rfl

/--
Through cutoff four, the retained-recipe singleton assignment counts every
selected cutoff-full endpoint shape fiber.
-/
lemma
    signed_n_four
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4) :
    (blockProfileAssignment n)
      |>.toSPAssign
      |>.CountsFibersCast layer := by
  by_cases htwo : n ≤ 2
  · intro M N word hword
    have hword' :=
      ordered_erased_vocabulary.mp hword
    rw [vocabulary_nil_n htwo] at hword'
    simp at hword'
  by_cases hthree : n ≤ 3
  · intro M N word hword
    have hword' :=
      ordered_erased_vocabulary.mp hword
    have hwordEq :
        word = CWord.hallPairBase := by
      rw [
        erased_vocabulary_singleton
          (by omega) hthree] at hword'
      simpa using hword'
    change
      (retainedRecipeProfiles
        ⟨word, ordered_erased_vocabulary.mp hword⟩).value
          (M : ℤ) (N : ℤ) =
        (endpointRecipeMultiplicity layer M N word : ℤ)
    rw [
      value_profiles_base
        ⟨word, ordered_erased_vocabulary.mp hword⟩ hwordEq,
      hwordEq,
      endpoint_multiplicity_n
        layer (by omega) hthree]
    norm_cast
  · exact
      coeff_n_four
        layer (by omega) hhigh

/--
The retained-recipe singleton profiles specialize to exact retained inverse-
raw shape-fiber counts through cutoff four.
-/
lemma profiles_filter_four
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (M N : ℕ)
    (word : CWord HPAtom)
    (hword : word ∈ erasedShapeVocabulary n 1 1) :
    (retainedRecipeProfiles ⟨word, hword⟩).value
        (M : ℤ) (N : ℤ) =
      (((retainedRawTerms M N n 1 1).filter fun term =>
        decide (term.family.recipe.erasedShape = word)).length : ℤ) := by
  rw [←
    filter_n_four
      layer hhigh M N word]
  exact
    signed_n_four
      layer hhigh M N word
        (ordered_erased_vocabulary.mpr hword)

/--
Through cutoff four, retained-recipe singleton profiles provide the uniform
retained-raw profile kernel required by the arbitrary-cutoff split.
-/
noncomputable def uniformNFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4) :
    FUProf n 1 1 where
  profiles word hword :=
    retainedRecipeProfiles ⟨word, hword⟩
  profiles_cast_local M N word hword := by
    rw [fiber_filter_length]
    exact
      profiles_filter_four
        layer hhigh M N word hword

/-- Zero homogeneous profiles for the absent shallow scheduler corrections. -/
def retainedZeroProfiles
    {n : ℕ} :
    ∀ word ∈ erasedShapeVocabulary n 1 1,
      HFPkt
        word.pairLeftDegree word.pairRightDegree :=
  fun word _hword =>
    FPkt.zero word.pairLeftDegree word.pairRightDegree

/-- The zero profiles count the absent shallow scheduler corrections. -/
lemma profiles_value_cast
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4)
    (M N : ℕ)
    (word : CWord HPAtom)
    (hword : word ∈ erasedShapeVocabulary n 1 1) :
    (retainedZeroProfiles word hword).value (M : ℤ) (N : ℤ) =
      ((((endpointCorrectionInventory layer M N).corrections.filter
        fun term =>
          decide (term.family.recipe.erasedShape = word)).length : ℕ) : ℤ) := by
  rw [
    inventory_corrections_four
      layer hhigh M N word]
  exact FPkt.value_zero _ _ _ _

/--
Through cutoff four, retained-recipe singleton profiles and zero correction
profiles compile to the raw-history/correction split kernel.
-/
noncomputable def
    fiberHistoryFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4) :
    EFSplit layer :=
  EFSplit.fiber_uniform_profile
      (uniformNFour layer hhigh)
      retainedZeroProfiles
      (profiles_value_cast layer hhigh)

end
  FUClass
end TCTex
end Towers

/-!
# Finite-index retained-correction profiles through cutoff four

Through cutoff four at root weights, the cutoff-full scheduler retains no
generated corrections.  The selected retained-correction finite-index trace
therefore has zero shape-fiber counts, represented by the existing zero
homogeneous profiles.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex


namespace
  IFClass

open
  CRLayer
open
  ISFiber
open
  FUClass
open
  CFAlg
open
  UCSuppor

/--
Through cutoff four, zero homogeneous profiles count every selected
retained-correction finite-index trace shape fiber.
-/
noncomputable def fiberNFour
    {n : ℕ}
    (layer : NRLayer n 1 1)
    (hhigh : n ≤ 4) :
    SFProf
      layer (by simp) (by simp) where
  profiles :=
    retainedZeroProfiles
  profiles_nat_trace M N word hword := by
    rw [
      key_selected_corrections
        layer M N (by simp) (by simp) word,
      inventory_corrections_nil
        layer hhigh M N]
    exact FPkt.value_zero _ _ _ _

end
  IFClass
end TCTex
end Towers

/-!
# Canonical polynomial-orbit raw profiles through cutoff four

The arbitrary-cutoff raw stabilization boundary proposes a canonical profile:
deduplicate the cutoff-sized dummy source recipes by symbolic polynomial orbit,
choose one representative per orbit, and filter those representatives by erased
Hall shape.

Through cutoff four at root weights, every retained recipe is already a raw
source recipe.  Moreover, a raw source recipe has one block on each side, so
its erased Hall shape determines its complete polynomial-orbit key.  Hence the
canonical filtered transversal has exactly one representative for each shallow
retained shape.  Its profile agrees with the retained-recipe singleton profile
and supplies the concrete polynomial-orbit stabilization kernel.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace
  TCThree

open HACoeff
open RPEquiv
open ROAggreg
open RFPacket
open BRSpec
open
  RFTransv
open
  RFLocal
open
  FUClass
open
  CTAssigna
open
  SWSep
open UCSuppor
open UCVocabu
open RRVocabu
open URVocabu

private lemma singleton_nodup_forall
    {α : Type*}
    {values : List α}
    {value : α}
    (hnodup : values.Nodup)
    (hvalue : value ∈ values)
    (hunique : ∀ nextValue ∈ values, nextValue = value) :
    values = [value] := by
  induction values with
  | nil =>
      simp at hvalue
  | cons head tail _ih =>
      have hhead : head = value :=
        hunique head (by simp)
      subst head
      have hvalueNotMem : value ∉ tail :=
        (List.nodup_cons.mp hnodup).1
      have htail : tail = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro nextValue hnextValue
        have hnextValueEq : nextValue = value :=
          hunique nextValue (by simp [hnextValue])
        subst nextValue
        exact hvalueNotMem hnextValue
      subst tail
      rfl

/--
Two standardized raw source recipes with the same erased Hall shape have the
same complete symbolic polynomial-orbit key.
-/
lemma key_recipes_shape
    {n leftWeight rightWeight : ℕ}
    {left right : BRecipe}
    (hleft : left ∈ sourceRecipes n leftWeight rightWeight)
    (hright : right ∈ sourceRecipes n leftWeight rightWeight)
    (hshape : left.erasedShape = right.erasedShape) :
    polynomialOrbitKey left = polynomialOrbitKey right := by
  rw [polynomial_orbit_key]
  rcases initial_recipe_recipes hleft with
    ⟨leftSource, _hleftSource, rfl⟩
  rcases initial_recipe_recipes hright with
    ⟨rightSource, _hrightSource, rfl⟩
  have hshape' :
      leftSource.linear.erasedShape = rightSource.linear.erasedShape := by
    simpa [IRecipe.blockRecipe, BRecipe.erased_shape_linear] using
      hshape
  refine ⟨?_, ?_, hshape⟩
  · simp only [IRecipe.blockRecipe, BRecipe.ofLinear]
    rw [← leftSource.linear.erased_left_degree,
      ← rightSource.linear.erased_left_degree, hshape']
  · simp only [IRecipe.blockRecipe, BRecipe.ofLinear]
    rw [← leftSource.linear.erased_shape_degree,
      ← rightSource.linear.erased_shape_degree, hshape']

/--
Through cutoff four, the retained singleton recipe for a finite-skeleton word
already belongs to the raw source vocabulary.
-/
lemma recipes_n_four
    {n : ℕ}
    (hn : n ≤ 4)
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 }) :
    retainedRecipeWord word ∈ sourceRecipes n 1 1 :=
  source_recipes_four
    (retained_recipe_word word)
    ((weighted_closure_recipes
      (retained_recipe_word word)).trans_le hn)

/-- The source polynomial-orbit key selected by one shallow retained word. -/
noncomputable def keyNFour
    {n : ℕ}
    (hn : n ≤ 4)
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 }) :
    { key // key ∈ polynomialOrbitVocabulary (sourceRecipes n 1 1) } :=
  ⟨polynomialOrbitKey (retainedRecipeWord word), by
    unfold polynomialOrbitVocabulary
    rw [List.mem_dedup]
    exact List.mem_map.mpr
      ⟨retainedRecipeWord word,
        recipes_n_four hn word, rfl⟩⟩

/-- Canonical raw-source representative selected for one shallow retained word. -/
noncomputable def representativeNFour
    {n : ℕ}
    (hn : n ≤ 4)
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 }) :
    BRecipe :=
  recipePolynomialOrbit (sourceRecipes n 1 1)
    (keyNFour hn word)

/-- The canonical shallow representative belongs to the raw source vocabulary. -/
lemma representative_n_recipes
    {n : ℕ}
    (hn : n ≤ 4)
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 }) :
    representativeNFour hn word ∈
      sourceRecipes n 1 1 :=
  recipes_polynomial_orbit
    (recipe_polynomial_orbit (sourceRecipes n 1 1)
      (keyNFour hn word))

/-- The canonical shallow representative has the requested erased shape. -/
lemma erased_representative_four
    {n : ℕ}
    (hn : n ≤ 4)
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 }) :
    (representativeNFour hn word).erasedShape =
      word.1 := by
  have hkey :=
    polynomial_key_recipes
      (recipe_polynomial_orbit (sourceRecipes n 1 1)
        (keyNFour hn word))
  have hshape := congrArg POKey.erasedShape hkey
  simpa [keyNFour,
    polynomialOrbitKey] using
      hshape.trans (erased_shape_recipe word)

/--
For every shallow retained word, filtering the canonical raw source-orbit
transversal by shape leaves exactly its selected orbit representative.
-/
lemma transversal_n_four
    {n : ℕ}
    (hn : n ≤ 4)
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 }) :
    rawTransversalShape n 1 1 word.1 =
      [representativeNFour hn word] := by
  apply singleton_nodup_forall
  · apply List.Nodup.filter
    unfold retainedRawTransversal
    apply List.Nodup.map_on
    · intro left hleft right hright heq
      apply Subtype.ext
      have hleftKey :=
        polynomial_key_recipes
          (recipe_polynomial_orbit (sourceRecipes n 1 1) left)
      have hrightKey :=
        polynomial_key_recipes
          (recipe_polynomial_orbit (sourceRecipes n 1 1) right)
      exact hleftKey.symm.trans ((congrArg polynomialOrbitKey heq).trans hrightKey)
    · exact List.nodup_attach.mpr (List.nodup_dedup _)
  · apply List.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · unfold retainedRawTransversal
      apply List.mem_map.mpr
      exact
        ⟨keyNFour hn word,
          by simp, rfl⟩
    · simpa using
        erased_representative_four
          hn word
  · intro recipe hrecipe
    have htransversal :
        recipe ∈ retainedRawTransversal n 1 1 :=
      List.mem_of_mem_filter hrecipe
    rcases List.mem_map.mp htransversal with ⟨key, _hkey, hrecipeEq⟩
    have hrecipeSource :
        recipe ∈ sourceRecipes n 1 1 :=
      source_recipes_transversal
        htransversal
    have hrecipeShape :
        recipe.erasedShape = word.1 :=
      erased_raw_transversal
        hrecipe
    have hkeyEq :
        key =
          keyNFour hn word := by
      apply Subtype.ext
      have hchosenKey :=
        polynomial_key_recipes
          (recipe_polynomial_orbit (sourceRecipes n 1 1) key)
      have htargetKey :
          polynomialOrbitKey recipe =
            polynomialOrbitKey (retainedRecipeWord word) :=
        key_recipes_shape
          hrecipeSource
          (recipes_n_four hn word)
          (hrecipeShape.trans (erased_shape_recipe word).symm)
      simpa [keyNFour] using
        hchosenKey.symm.trans
          ((congrArg polynomialOrbitKey hrecipeEq).trans htargetKey)
    simpa [representativeNFour,
      hkeyEq] using hrecipeEq.symm

/--
Through cutoff four, the canonical raw source-orbit profile agrees with the
retained singleton recipe profile at every integer specialization.
-/
lemma poly_n_four
    {n : ℕ}
    (hn : n ≤ 4)
    (word : { word // word ∈ erasedShapeVocabulary n 1 1 })
    (leftExponent rightExponent : ℤ) :
    (rawTransversalProfile n 1 1 word.1).value
        leftExponent rightExponent =
      (retainedRecipeProfiles word).value leftExponent rightExponent := by
  rw [value_transversal_profile,
    transversal_n_four
      hn word,
    value_recipe_profiles]
  simp only [List.map_singleton, List.sum_singleton]
  apply
    BRecipe.coeff_poly_equivalent
      (polynomial_orbit_key.mp ?_)
  exact
    (by
      simpa [representativeNFour,
        keyNFour] using
          (polynomial_key_recipes
            (recipe_polynomial_orbit (sourceRecipes n 1 1)
              (keyNFour hn word))))

/--
Through cutoff four, the canonical source polynomial-orbit transversal
constructs the raw stabilization kernel proposed by the arbitrary-cutoff
boundary.
-/
noncomputable def transversalStabilizationFour
    {n : ℕ}
    (layer :
      CRLayer.NRLayer
        n 1 1)
    (hn : n ≤ 4) :
    PTStab n 1 1 where
  profile_cast_local M N word hword := by
    rw [
      poly_n_four
        hn ⟨word, hword⟩,
      fiber_filter_length]
    exact
      profiles_filter_four
        layer hn M N word hword

end
  TCThree
end TCTex
end Towers

/-!
# Ordered retained-transversal packet alignment for cutoff-full shape fibers

The retained recipe-coefficient transversal chooses one actual retained
finite-closure representative for every erased Hall word.  The cutoff-full
interpolation pipeline attaches profiles in sorted shape order, while the
original retained-transversal recipe law uses the deduplicated skeleton
order.

This file isolates:

* word-local agreement with the retained-transversal profiles;
* the order-aware signed law for the sorted retained packet;
* the optional theorem that sorted and skeleton packet orders coincide.

This is the provenance-preserving alternative to the conservative canonical
coefficient-sum packet, which is known to overcount.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace
  SOAlign

universe u


open scoped commutatorElement

open
  FPInterp
open
  CRLayer
open
  NRSubinv
open
  CFSubsti
open
  CTAssigna
open
  CCThree
open
  RPThree
open
  FCAssign
open
  UCSuppor

/--
Retained-transversal singleton profiles attached in sorted cutoff-full
vocabulary order.
-/
noncomputable def profileRecollectionPackets
    (n : ℕ) :
    List RFPkt :=
  (blockProfileAssignment n)
    |>.toSPAssign
    |>.erasedVocabPackets

/--
The retained-provenance packet attached to one root skeleton word.
-/
noncomputable def retainedProfileRecollection
    {n : ℕ}
    (word : CWord HPAtom)
    (hword : word ∈ erasedShapeVocabulary n 1 1) :
    RFPkt :=
  {
    word := word
    positive :=
      bidegree_positive_vocabulary hword
    profiles :=
      (blockProfileAssignment n)
        |>.toSPAssign.profiles word hword
  }

/--
The retained packet constructor depends only on its skeleton word.
-/
lemma profile_recollection_congr
    {n : ℕ}
    {left right : CWord HPAtom}
    (hleft : left ∈ erasedShapeVocabulary n 1 1)
    (hright : right ∈ erasedShapeVocabulary n 1 1)
    (hword : left = right) :
    retainedProfileRecollection left hleft =
      retainedProfileRecollection
        right hright := by
  subst right
  rfl

/--
One root-weight profile assignment agrees word by word with the retained
recipe-coefficient transversal.
-/
def RetainedProfileAlignment
    {n : ℕ}
    (assignment :
      SPAssign n 1 1) :
    Prop :=
  ∀ word hword,
    assignment.profiles word hword =
      ((blockProfileAssignment n)
        |>.toSPAssign.profiles word hword)

/--
Word-local retained-transversal profile agreement gives literal equality of
the sorted packet lists.
-/
lemma
    coeff_profile_alignment
    {n : ℕ}
    (assignment :
      SPAssign n 1 1)
    (halignment :
      RetainedProfileAlignment assignment) :
    assignment.erasedVocabPackets =
      profileRecollectionPackets n := by
  unfold
    profileRecollectionPackets
  unfold
    FCAssign.SPAssign.erasedVocabPackets
  apply List.map_congr_left
  intro word _hword
  congr 1
  exact
    halignment word.1
      (ordered_erased_vocabulary.mp word.2)

/--
The cutoff-specific signed recollection law for the sorted
retained-transversal packet.
-/
def SatisfiesCoefficientTruncated
    (d n : ℕ) :
    Prop :=
  ∀ (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ),
      ((profileRecollectionPackets n).map
        fun packet =>
          packet.word.eval (HPAtom.eval left right) ^
            packet.profiles.value leftExponent rightExponent).prod =
        ⁅left ^ leftExponent, right ^ rightExponent⁆

/--
The sorted retained-transversal packet agrees literally with the original
skeleton-order retained packet.  This remains an explicit order theorem.
-/
def CoefficientVocabularyAlignment
    (n : ℕ) :
    Prop :=
  profileRecollectionPackets n =
    globalSignedPackets n

/--
Literal equality of the sorted and skeleton vocabularies lifts to retained
packet-order alignment.
-/
lemma
    erased_shape_vocab
    {n : ℕ}
    (hwords :
      orderedErasedVocabulary n 1 1 =
        erasedShapeVocabulary n 1 1) :
    CoefficientVocabularyAlignment n := by
  classical
  unfold CoefficientVocabularyAlignment
  unfold
    profileRecollectionPackets
  unfold globalSignedPackets
  unfold
    FCAssign.SPAssign.erasedVocabPackets
  unfold
    FCAssign.SPAssign.toPackets
  change
    (orderedErasedVocabulary n 1 1).attach.map
        (fun word =>
          retainedProfileRecollection
            word.1 (ordered_erased_vocabulary.mp word.2)) =
      (erasedShapeVocabulary n 1 1).attach.map
        (fun word =>
          retainedProfileRecollection
            word.1 word.2)
  apply List.ext_getElem
  · simp [hwords]
  · intro index hleft hright
    simp only [List.length_map, List.length_attach] at hleft hright
    simp only [List.getElem_map]
    apply
      profile_recollection_congr
    simp only [List.getElem_attach, hwords]

/--
Retained packet-order alignment forces literal equality of the sorted and
skeleton vocabularies after forgetting profiles.
-/
lemma
    vocab_coeff_alignment
    {n : ℕ}
    (horder :
      CoefficientVocabularyAlignment n) :
    orderedErasedVocabulary n 1 1 =
      erasedShapeVocabulary n 1 1 := by
  have hwords :=
    congrArg
      (List.map RFPkt.word)
      horder
  unfold
    profileRecollectionPackets at hwords
  simpa only [
    SPAssign.ordered_vocabulary_packets,
    profile_recollection_packets] using hwords

/--
If the retained root skeleton is already in primary More3 order, sorting does
nothing and the retained packet orders agree.
-/
lemma
    recipe_coeff_vocab
    {n : ℕ}
    (hsorted :
      (erasedShapeVocabulary n 1 1).Pairwise erasedShapeLE) :
    CoefficientVocabularyAlignment n :=
  erased_shape_vocab
    (by
      unfold orderedErasedVocabulary
      exact hsorted.insertionSort_eq)

/--
Retained packet-order alignment implies that the root skeleton is already in
primary More3 order.
-/
lemma
    pairwise_vocab_alignment
    {n : ℕ}
    (horder :
      CoefficientVocabularyAlignment n) :
    (erasedShapeVocabulary n 1 1).Pairwise erasedShapeLE := by
  rw [←
    vocab_coeff_alignment
      horder]
  exact pairwise_erased_vocabulary n 1 1

/--
Retained packet-order alignment is exactly primary More3 sortedness of the
root skeleton.
-/
lemma
    coeff_erased_vocab
    {n : ℕ} :
    CoefficientVocabularyAlignment n ↔
      (erasedShapeVocabulary n 1 1).Pairwise erasedShapeLE :=
  ⟨pairwise_vocab_alignment,
    recipe_coeff_vocab⟩

/--
When sorted and skeleton retained-transversal orders coincide, the original
retained recipe-product law supplies the sorted signed law.
-/
lemma
    satisfies_recipe_trunc
    {d n : ℕ}
    (horder :
      CoefficientVocabularyAlignment n)
    (hlistEval :
      SatisfiesRecipeCoefficient.{u} d n) :
    SatisfiesCoefficientTruncated.{u} d n := by
  intro left right leftExponent rightExponent
  rw [horder]
  unfold globalSignedPackets
  exact
    (coefficient_recipes_assignment
      left right leftExponent rightExponent).symm.trans
        (hlistEval left right leftExponent rightExponent)

/--
Literal alignment with the sorted retained-transversal packet transports its
signed law to an arbitrary endpoint shape-fiber interpolation packet.
-/
def
    allLiftAlignment
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    {packets : List RFPkt}
    (interpolation :
      EFInterp layer packets)
    (halignment :
      packets =
        profileRecollectionPackets n)
    (hlistEval :
      SatisfiesCoefficientTruncated.{u} d n) :
    FPInterp.EFInterp.AILift.{u}
      (d := d) interpolation where
  listEval_eq left right leftExponent rightExponent := by
    rw [
      FPInterp.EFInterp.packetsTruncNatural,
      halignment]
    exact hlistEval left right leftExponent rightExponent

end
  SOAlign
end TCTex
end Towers
