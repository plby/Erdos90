import Submission.Group.Zassenhaus.OperationalInventory
import Submission.Group.Zassenhaus.FamilyOperationalCollector
import Submission.Group.Zassenhaus.SchedulingContracts
import Submission.Group.Zassenhaus.AtomParentHistories


-- Merged from FamilyOperationalEmissionAccounting.lean

/-!
# Operational More3 emission accounting

`DFTerm.IInsert` performs actual one-slot More3
obstructions.  Because that derivation lives in `Prop`, emitted terms are
recorded by a relation rather than computed by eliminating the derivation
into data.

Every finite insertion and collection derivation admits a finite correction
list with exact multiset accounting.  This is the bridge between the stable
recursive trace and multiplicity-preserving Cartesian batch ledgers.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace OEAccoun

open HACoeff

namespace FInsert

/-- Finite concrete correction list emitted by one actual More3 insertion. -/
inductive ECorrec
    {M N K : ℕ} :
    {L R : List (DFTerm M N K)} →
      {A : DFTerm M N K} →
        DFTerm.IInsert L A R →
          List (DFTerm M N K) →
            Prop where
  | nil
      (A : DFTerm M N K) :
      ECorrec (DFTerm.IInsert.nil A) []
  | append
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hAB : ¬ A.decorated.independentBefore B.decorated) :
      ECorrec
        (DFTerm.IInsert.append P B A hAB) []
  | obstruction
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hAB : A.decorated.independentBefore B.decorated)
      {Q R : List (DFTerm M N K)}
      {hcorrection :
        DFTerm.IInsert P (B.correction A) Q}
      {hinsert : DFTerm.IInsert Q A R}
      {correctionTerms insertTerms : List (DFTerm M N K)}
      (hcorrectionTerms : ECorrec hcorrection correctionTerms)
      (hinsertTerms : ECorrec hinsert insertTerms) :
      ECorrec
        (DFTerm.IInsert.obstruction
          P B A hAB hcorrection hinsert)
        (B.correction A :: (correctionTerms ++ insertTerms))

/-- Every actual insertion derivation emits some finite correction list. -/
lemma exists_emitsCorrections
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert : DFTerm.IInsert L A R) :
    ∃ corrections, ECorrec hinsert corrections := by
  induction hinsert with
  | nil A =>
      exact ⟨[], ECorrec.nil A⟩
  | append P B A hAB =>
      exact ⟨[], ECorrec.append P B A hAB⟩
  | obstruction P B A hAB hcorrection hinsert
      ihcorrection ihinsert =>
      rcases ihcorrection with ⟨correctionTerms, hcorrectionTerms⟩
      rcases ihinsert with ⟨insertTerms, hinsertTerms⟩
      exact ⟨B.correction A :: (correctionTerms ++ insertTerms),
        ECorrec.obstruction P B A hAB
          hcorrectionTerms hinsertTerms⟩

/--
Insertion output contains exactly the source, inserted term, and recursively
emitted corrections.
-/
lemma coe_inserted_corrections
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {hinsert : DFTerm.IInsert L A R}
    (hemits : ECorrec hinsert corrections) :
    (R : Multiset (DFTerm M N K)) =
      (L : Multiset (DFTerm M N K)) +
        {A} + corrections := by
  induction hemits with
  | nil A =>
      simp
  | append P B A _hAB =>
      rw [show P ++ [B, A] = (P ++ [B]) ++ [A] by simp]
      rw [← Multiset.coe_add, Multiset.coe_singleton]
      simp
  | obstruction P B A _hAB hcorrectionTerms hinsertTerms
      ihcorrection ihinsert =>
      simp only [← Multiset.coe_add,
        ← Multiset.cons_coe, ← Multiset.singleton_add] at ihcorrection ihinsert ⊢
      rw [ihinsert, ihcorrection]
      simp [-Multiset.coe_add, -Multiset.singleton_add,
        add_comm, add_left_comm, add_assoc]

/-- List-permutation form of insertion correction accounting. -/
lemma perm_inserted_corrections
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {hinsert : DFTerm.IInsert L A R}
    (hemits : ECorrec hinsert corrections) :
    List.Perm R (L ++ [A] ++ corrections) := by
  apply Multiset.coe_eq_coe.mp
  rw [← Multiset.coe_add, ← Multiset.coe_add, Multiset.coe_singleton]
  exact coe_inserted_corrections hemits

end FInsert

namespace FCollec

/-- Finite concrete correction list emitted by one complete actual collection. -/
inductive ECorrec
    {M N K : ℕ} :
    {L R : List (DFTerm M N K)} →
      DFTerm.ICollec L R →
        List (DFTerm M N K) →
          Prop where
  | nil :
      ECorrec DFTerm.ICollec.nil []
  | snoc
      (P : List (DFTerm M N K))
      (A : DFTerm M N K)
      {C R : List (DFTerm M N K)}
      {hcollect : DFTerm.ICollec P C}
      {hinsert : DFTerm.IInsert C A R}
      {collectTerms insertTerms : List (DFTerm M N K)}
      (hcollectTerms : ECorrec hcollect collectTerms)
      (hinsertTerms : FInsert.ECorrec hinsert insertTerms) :
      ECorrec
        (DFTerm.ICollec.snoc
          P A hcollect hinsert)
        (collectTerms ++ insertTerms)

/-- Every complete actual collection emits some finite correction list. -/
lemma exists_emitsCorrections
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    (hcollect : DFTerm.ICollec L R) :
    ∃ corrections, ECorrec hcollect corrections := by
  induction hcollect with
  | nil =>
      exact ⟨[], ECorrec.nil⟩
  | snoc P A hcollect hinsert ihcollect =>
      rcases ihcollect with ⟨collectTerms, hcollectTerms⟩
      rcases FInsert.exists_emitsCorrections hinsert with
        ⟨insertTerms, hinsertTerms⟩
      exact ⟨collectTerms ++ insertTerms,
        ECorrec.snoc P A hcollectTerms hinsertTerms⟩

/-- Collection output contains exactly the source and emitted corrections. -/
lemma result_add_corrections
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {hcollect : DFTerm.ICollec L R}
    (hemits : ECorrec hcollect corrections) :
    (R : Multiset (DFTerm M N K)) =
      (L : Multiset (DFTerm M N K)) +
        corrections := by
  induction hemits with
  | nil =>
      simp
  | snoc P A hcollectTerms hinsertTerms ihcollect =>
      simp only [← Multiset.coe_add, Multiset.coe_singleton] at ihcollect ⊢
      rw [FInsert.coe_inserted_corrections
        hinsertTerms, ihcollect]
      simp [-Multiset.coe_add, add_comm, add_left_comm, add_assoc]

/-- List-permutation form of complete collection correction accounting. -/
lemma result_perm_append
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {hcollect : DFTerm.ICollec L R}
    (hemits : ECorrec hcollect corrections) :
    List.Perm R (L ++ corrections) := by
  apply Multiset.coe_eq_coe.mp
  rw [← Multiset.coe_add]
  exact result_add_corrections hemits

end FCollec

end OEAccoun
end TCTex
end Submission

-- Merged from FamilyOperationalCorrectionClosure.lean

/-!
# Causal closure of operational More3 corrections

The operational More3 collector emits correction terms recursively.  Exact
multiset accounting alone does not record where those terms came from.  This
file adds the causal invariant: every emitted and final term is generated from
the original concrete source by finitely many pairwise corrections.

The same invariant is projected to counted `BFam` values.  Its
weighted-degree ancestry theorem is the structural fact used by recursive
polynomial specialization: every generated family has an original source
ancestor of no larger weighted Hall degree.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace OCClos

open HACoeff
open BRSpec
open HOCollec
open OEAccoun

namespace DFTerm

/-- Finite correction closure of a concrete decorated-family source. -/
inductive CGFrom
    {M N K : ℕ}
    (source : List (DFTerm M N K)) :
    DFTerm M N K → Prop where
  | source
      {term : DFTerm M N K}
      (hterm : term ∈ source) :
      CGFrom source term
  | correction
      {left right : DFTerm M N K}
      (hleft : CGFrom source left)
      (hright : CGFrom source right) :
      CGFrom source (left.correction right)

namespace CGFrom

/-- Enlarge the available source of a recursively generated correction term. -/
lemma mono
    {M N K : ℕ}
    {source source' : List (DFTerm M N K)}
    {term : DFTerm M N K}
    (hterm : CGFrom source term)
    (hsource : ∀ T ∈ source, T ∈ source') :
    CGFrom source' term := by
  induction hterm with
  | source hT =>
      exact CGFrom.source (hsource _ hT)
  | correction _ _ ihleft ihright =>
      exact CGFrom.correction ihleft ihright

/-- Substitute generated terms for every source leaf of a correction tree. -/
lemma bind
    {M N K : ℕ}
    {source source' : List (DFTerm M N K)}
    {term : DFTerm M N K}
    (hterm : CGFrom source term)
    (hsource : ∀ T ∈ source, CGFrom source' T) :
    CGFrom source' term := by
  induction hterm with
  | source hT =>
      exact hsource _ hT
  | correction _ _ ihleft ihright =>
      exact CGFrom.correction ihleft ihright

/-- Every concrete source member is generated from that source. -/
lemma of_mem
    {M N K : ℕ}
    {source : List (DFTerm M N K)}
    {term : DFTerm M N K}
    (hterm : term ∈ source) :
    CGFrom source term :=
  CGFrom.source hterm

end CGFrom
end DFTerm

namespace BFam

/-- Family-level image of finite concrete correction closure. -/
inductive CGFrom
    {M N : ℕ}
    (source : List (BFam M N)) :
    BFam M N → Prop where
  | source
      {family : BFam M N}
      (hfamily : family ∈ source) :
      CGFrom source family
  | correction
      {left right : BFam M N}
      (hleft : CGFrom source left)
      (hright : CGFrom source right) :
      CGFrom source (left.correction right)

namespace CGFrom

/-- Enlarge the available family source of a generated family. -/
lemma mono
    {M N : ℕ}
    {source source' : List (BFam M N)}
    {family : BFam M N}
    (hfamily : CGFrom source family)
    (hsource : ∀ F ∈ source, F ∈ source') :
    CGFrom source' family := by
  induction hfamily with
  | source hF =>
      exact CGFrom.source (hsource _ hF)
  | correction _ _ ihleft ihright =>
      exact CGFrom.correction ihleft ihright

/-- Substitute generated families for every source leaf of a correction tree. -/
lemma bind
    {M N : ℕ}
    {source source' : List (BFam M N)}
    {family : BFam M N}
    (hfamily : CGFrom source family)
    (hsource : ∀ F ∈ source, CGFrom source' F) :
    CGFrom source' family := by
  induction hfamily with
  | source hF =>
      exact hsource _ hF
  | correction _ _ ihleft ihright =>
      exact CGFrom.correction ihleft ihright

/--
Every generated family has an original source ancestor of no larger weighted
Hall degree.
-/
lemma source_weight
    {M N leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {source : List (BFam M N)}
    {family : BFam M N}
    (hfamily : CGFrom source family) :
    ∃ ancestor ∈ source,
      weightedWordWeight leftWeight rightWeight ancestor.recipe ≤
        weightedWordWeight leftWeight rightWeight family.recipe := by
  induction hfamily with
  | source hF =>
      exact ⟨_, hF, le_rfl⟩
  | @correction left right _ _ ihleft _ihright =>
      rcases ihleft with ⟨ancestor, hancestor, hle⟩
      refine ⟨ancestor, hancestor, hle.trans ?_⟩
      apply Nat.le_of_lt
      rw [BFam.recipe_correction]
      exact weighted_correction_left
        hleftWeight hrightWeight left.recipe right.recipe

end CGFrom
end BFam

namespace DFTerm.CGFrom

/-- Forget concrete realization slots and retain family-level correction closure. -/
lemma family
    {M N K : ℕ}
    {source : List (DFTerm M N K)}
    {term : DFTerm M N K}
    (hterm : DFTerm.CGFrom source term) :
    BFam.CGFrom
      (source.map DFTerm.family) term.family := by
  induction hterm with
  | source hT =>
      exact BFam.CGFrom.source
        (List.mem_map.mpr ⟨_, hT, rfl⟩)
  | correction _ _ ihleft ihright =>
      exact BFam.CGFrom.correction ihleft ihright

/--
Every generated concrete term has an original source family ancestor of no
larger weighted Hall degree.
-/
lemma source_family_weight
    {M N K leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {source : List (DFTerm M N K)}
    {term : DFTerm M N K}
    (hterm : DFTerm.CGFrom source term) :
    ∃ ancestor ∈ source,
      weightedWordWeight leftWeight rightWeight ancestor.family.recipe ≤
        weightedWordWeight leftWeight rightWeight term.family.recipe := by
  rcases hterm.family.source_weight hleftWeight hrightWeight with
    ⟨ancestorFamily, hancestorFamily, hle⟩
  rcases List.mem_map.mp hancestorFamily with ⟨ancestor, hancestor, rfl⟩
  exact ⟨ancestor, hancestor, hle⟩

end DFTerm.CGFrom

namespace FInsert.ECorrec

/-- Every correction emitted by one insertion is causally generated from its input. -/
lemma correctionGeneratedFrom
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {hinsert : DFTerm.IInsert L A R}
    (hemits : FInsert.ECorrec hinsert corrections) :
    ∀ T ∈ corrections,
      DFTerm.CGFrom (L ++ [A]) T := by
  induction hemits with
  | nil A =>
      simp
  | append P B A _hAB =>
      simp
  | obstruction P B A _hAB hcorrectionTerms hinsertTerms
      ihcorrection ihinsert =>
      intro T hT
      simp only [List.mem_cons, List.mem_append] at hT
      rcases hT with rfl | hT | hT
      · exact DFTerm.CGFrom.correction
          (DFTerm.CGFrom.source (by simp))
          (DFTerm.CGFrom.source (by simp))
      · apply (ihcorrection T hT).bind
        intro U hU
        rcases List.mem_append.mp hU with hU | hU
        · exact DFTerm.CGFrom.source (by simp [hU])
        · rcases List.mem_singleton.mp hU with rfl
          exact DFTerm.CGFrom.correction
            (DFTerm.CGFrom.source (by simp))
            (DFTerm.CGFrom.source (by simp))
      · apply (ihinsert T hT).bind
        intro U hU
        rcases List.mem_append.mp hU with hU | hU
        · have hcanonical :=
            (FInsert.perm_inserted_corrections
              hcorrectionTerms).subset hU
          rcases List.mem_append.mp hcanonical with hU | hU
          · rcases List.mem_append.mp hU with hU | hU
            · exact DFTerm.CGFrom.source
                (by simp [hU])
            · rcases List.mem_singleton.mp hU with rfl
              exact DFTerm.CGFrom.correction
                (DFTerm.CGFrom.source (by simp))
                (DFTerm.CGFrom.source (by simp))
          · apply (ihcorrection U hU).bind
            intro V hV
            rcases List.mem_append.mp hV with hV | hV
            · exact DFTerm.CGFrom.source
                (by simp [hV])
            · rcases List.mem_singleton.mp hV with rfl
              exact DFTerm.CGFrom.correction
                (DFTerm.CGFrom.source (by simp))
                (DFTerm.CGFrom.source (by simp))
        · rcases List.mem_singleton.mp hU with rfl
          exact DFTerm.CGFrom.source (by simp)

/-- Every final insertion term is causally generated from its input. -/
lemma result_corre_gener
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {hinsert : DFTerm.IInsert L A R}
    (hemits : FInsert.ECorrec hinsert corrections) :
    ∀ T ∈ R,
      DFTerm.CGFrom (L ++ [A]) T := by
  intro T hT
  have hcanonical :
      T ∈ L ++ [A] ++ corrections :=
    (FInsert.perm_inserted_corrections
      hemits).subset hT
  rcases List.mem_append.mp hcanonical with hT | hT
  · exact DFTerm.CGFrom.source hT
  · exact correctionGeneratedFrom hemits T hT

end FInsert.ECorrec

namespace FCollec.ECorrec

/-- Every correction emitted by one collection is generated from its raw source. -/
lemma correctionGeneratedFrom
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {hcollect : DFTerm.ICollec L R}
    (hemits : FCollec.ECorrec hcollect corrections) :
    ∀ T ∈ corrections,
      DFTerm.CGFrom L T := by
  induction hemits with
  | nil =>
      simp
  | snoc P A hcollectTerms hinsertTerms ihcollect =>
      intro T hT
      rcases List.mem_append.mp hT with hT | hT
      · exact (ihcollect T hT).mono (by
          intro U hU
          simp [hU])
      · apply
          (FInsert.ECorrec.correctionGeneratedFrom
            hinsertTerms T hT).bind
        intro U hU
        rcases List.mem_append.mp hU with hU | hU
        · have hcanonical :=
            (FCollec.result_perm_append
              hcollectTerms).subset hU
          rcases List.mem_append.mp hcanonical with hU | hU
          · exact DFTerm.CGFrom.source
              (by simp [hU])
          · exact (ihcollect U hU).mono (by
              intro V hV
              simp [hV])
        · rcases List.mem_singleton.mp hU with rfl
          exact DFTerm.CGFrom.source (by simp)

/-- Every final collected term is generated from the original raw source. -/
lemma result_corre_gener
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {hcollect : DFTerm.ICollec L R}
    (hemits : FCollec.ECorrec hcollect corrections) :
    ∀ T ∈ R,
      DFTerm.CGFrom L T := by
  intro T hT
  have hcanonical :
      T ∈ L ++ corrections :=
    (FCollec.result_perm_append hemits).subset hT
  rcases List.mem_append.mp hcanonical with hT | hT
  · exact DFTerm.CGFrom.source hT
  · exact correctionGeneratedFrom hemits T hT

end FCollec.ECorrec

namespace ODTerms

/--
Every operational inverse-raw endpoint admits an exact emitted-correction
list, and every final term is causally generated from the inverse-raw source.
-/
lemma emitted_corrections_generated
    {M N : ℕ}
    (collected : ODTerms M N) :
    ∃ corrections,
      FCollec.ECorrec collected.family_collects corrections ∧
        List.Perm collected.factors
          (inverseDecoratedTerms M N ++ corrections) ∧
        (∀ T ∈ corrections,
          DFTerm.CGFrom
            (inverseDecoratedTerms M N) T) ∧
        ∀ T ∈ collected.factors,
          DFTerm.CGFrom
            (inverseDecoratedTerms M N) T := by
  rcases FCollec.exists_emitsCorrections collected.family_collects with
    ⟨corrections, hemits⟩
  exact ⟨corrections, hemits,
    FCollec.result_perm_append hemits,
    FCollec.ECorrec.correctionGeneratedFrom hemits,
    FCollec.ECorrec.result_corre_gener hemits⟩

end ODTerms

end OCClos
end TCTex
end Submission

-- Merged from FamilyOperationalMultiplicityEndpoint.lean

/-!
# Operational More3 multiplicity endpoints

The stable terminating More3 collector emits a finite list of concrete
correction terms.  Exact multiset accounting says that its final factors are
a permutation of the raw source followed by those emitted terms.

The raw source already carries a complete multiplicity-preserving inventory.
Consequently, once the emitted correction list has been assembled into closed
Cartesian batches, the entire operational endpoint carries an exact inventory.
This file packages that reduction.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace FMEnd

open HACoeff
open IMPropag
open HOCollec
open OEAccoun

/--
One terminating operational More3 output together with an extracted finite
list of every concrete correction term emitted by its recursive trace.
-/
structure ODEmissi
    (M N : ℕ) where
  collected :
    ODTerms M N
  corrections :
    List (DFTerm M N
      (inverseLabelledCollection M N).factors.length)
  emits :
    FCollec.ECorrec
      collected.family_collects corrections

namespace ODEmissi

/-- Endpoint factors are exactly raw terms followed by emitted corrections. -/
lemma perm_append_corrections
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    List.Perm endpoint.collected.factors
      (inverseDecoratedTerms M N ++ endpoint.corrections) :=
  FCollec.result_perm_append endpoint.emits

/--
Any closed multiplicity inventory for emitted corrections extends to a closed
inventory for the complete operational endpoint.
-/
noncomputable def factorsInventoryBlock
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (corrections :
      MIBlock endpoint.corrections) :
    MIBlock endpoint.collected.factors :=
  ((MIBlock.inverseRaw M N).append corrections).permTerms
    endpoint.perm_append_corrections.symm

end ODEmissi

/-- The stable terminating collector supplies an endpoint with emission data. -/
lemma nonempty_decorated_emissions
    (M N : ℕ) :
    Nonempty (ODEmissi M N) := by
  let collected :=
    Classical.choice
      (nonempty_decorated_terms M N)
  rcases FCollec.exists_emitsCorrections collected.family_collects with
    ⟨corrections, hemits⟩
  exact ⟨{
    collected := collected
    corrections := corrections
    emits := hemits }⟩

/--
Remaining emitted-correction batching law: every finite correction list
extracted from a terminating More3 run assembles into closed multiplicity
inventories.
-/
structure OMClos : Prop where
  correctionsInventory :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N),
      Nonempty (MIBlock endpoint.corrections)

namespace OMClos

/-- Resolve an exact multiplicity inventory for one complete More3 endpoint. -/
noncomputable def factorsInventory
    (kernel : OMClos)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    MIBlock endpoint.collected.factors :=
  endpoint.factorsInventoryBlock
    (Classical.choice (kernel.correctionsInventory endpoint))

end OMClos

end FMEnd
end TCTex
end Submission

-- Merged from FamilyOperationalCutoffPartition.lean

/-!
# Cutoff partition of operational More3 corrections

The terminating More3 collector emits an exact finite correction list.  For a
fixed nilpotent cutoff, this file separates that concrete list into retained
below-cutoff terms and residual terms whose weighted Hall degree has reached
the cutoff.

The partition is permutation-aware and keeps the causal invariant proved for
the operational trace: every retained term is generated from the inverse raw
source and therefore has a raw ancestor of no larger weighted degree.

This is the interface needed before specializing retained families to global
symbolic polynomials and discarding residual families semantically in a
matching nilpotent quotient.  This file is intentionally not imported by the
existing collection proof.
-/

namespace Submission
namespace TCTex
namespace OCPartit

open HACoeff
open BRSpec
open BFTrunc
open HOCollec
open OCClos
open OEAccoun
open FMEnd

/--
Every list is a permutation of the entries satisfying a Boolean predicate
followed by the entries failing it.
-/
lemma List.perm_filterappend_filternot
    {α : Type*}
    (predicate : α → Bool) :
    ∀ terms : List α,
      List.Perm terms
        (terms.filter predicate ++ terms.filter fun term => !predicate term)
  | [] => by simp
  | term :: terms => by
      cases hterm : predicate term with
      | false =>
          simpa [List.filter, hterm] using
            (List.Perm.cons term
              (List.perm_filterappend_filternot predicate terms)).trans
                List.perm_middle.symm
      | true =>
          simpa [List.filter, hterm] using
            List.Perm.cons term
              (List.perm_filterappend_filternot predicate terms)

/-- Weighted Hall degree of one concrete decorated-family term. -/
def decoratedFamilyWeight
    {M N K : ℕ}
    (leftWeight rightWeight : ℕ)
    (term : DFTerm M N K) :
    ℕ :=
  BRSpec.weightedWordWeight
    leftWeight rightWeight term.family.recipe

/-- Retain exactly the concrete terms whose weighted Hall degree is below the cutoff. -/
def belowCutoffTerms
    {M N K : ℕ}
    (n leftWeight rightWeight : ℕ)
    (terms : List (DFTerm M N K)) :
    List (DFTerm M N K) :=
  terms.filter fun term =>
    decide (decoratedFamilyWeight leftWeight rightWeight term < n)

/-- Retain exactly the concrete terms whose weighted Hall degree has reached the cutoff. -/
def orAboveTerms
    {M N K : ℕ}
    (n leftWeight rightWeight : ℕ)
    (terms : List (DFTerm M N K)) :
    List (DFTerm M N K) :=
  terms.filter fun term =>
    !decide (decoratedFamilyWeight leftWeight rightWeight term < n)

@[simp]
lemma below_cutoff_terms
    {M N K n leftWeight rightWeight : ℕ}
    {terms : List (DFTerm M N K)}
    {term : DFTerm M N K} :
    term ∈ belowCutoffTerms n leftWeight rightWeight terms ↔
      term ∈ terms ∧ decoratedFamilyWeight leftWeight rightWeight term < n := by
  simp [belowCutoffTerms]

@[simp]
lemma or_above_terms
    {M N K n leftWeight rightWeight : ℕ}
    {terms : List (DFTerm M N K)}
    {term : DFTerm M N K} :
    term ∈ orAboveTerms n leftWeight rightWeight terms ↔
      term ∈ terms ∧
        n ≤ decoratedFamilyWeight leftWeight rightWeight term := by
  simp [orAboveTerms]

/-- The cutoff split retains every concrete occurrence up to permutation. -/
lemma perm_or_above
    {M N K : ℕ}
    (n leftWeight rightWeight : ℕ)
    (terms : List (DFTerm M N K)) :
    List.Perm terms
      (belowCutoffTerms n leftWeight rightWeight terms ++
        orAboveTerms n leftWeight rightWeight terms) := by
  exact List.perm_filterappend_filternot
    (fun term : DFTerm M N K =>
      decide (decoratedFamilyWeight leftWeight rightWeight term < n))
    terms

/-- One concrete term at or above the cutoff evaluates trivially after truncation. -/
lemma collapsed_one_weight
    {M N K n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    (term : DFTerm M N K)
    (hweight : n ≤ decoratedFamilyWeight leftWeight rightWeight term) :
    (collapseWord term.decorated.word).eval (HPAtom.eval x y) = 1 := by
  apply eq_bot_iff.mp hbot
  exact Subgroup.lowerCentralSeries_antitone (Nat.sub_le_sub_right hweight 1)
    (BFam.collap_memlo_centr
      hleftWeight hrightWeight hx hy term.family term.word_mem)

/-- A concrete list entirely at or above the cutoff evaluates trivially. -/
lemma collapsed_decorated_forall
    {M N K n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    (terms : List (DFTerm M N K))
    (hterms :
      ∀ term ∈ terms,
        n ≤ decoratedFamilyWeight leftWeight rightWeight term) :
    collapsedList x y (decoratedFamilyList terms) = 1 := by
  induction terms with
  | nil =>
      rfl
  | cons term terms ih =>
      simp only [decoratedFamilyList, List.map_cons, collapsedList,
        List.prod_cons]
      rw [collapsed_one_weight
        hleftWeight hrightWeight hx hy hbot term (hterms term (by simp))]
      simpa [decoratedFamilyList, collapsedList] using
        ih (fun residual hresidual => hterms residual (by simp [hresidual]))

/--
The concrete cutoff partition of all corrections emitted by one terminating
operational More3 trace.
-/
structure CCPartit
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (n leftWeight rightWeight : ℕ) where
  retained :
    List (DFTerm M N
      (inverseLabelledCollection M N).factors.length)
  residual :
    List (DFTerm M N
      (inverseLabelledCollection M N).factors.length)
  corrections_perm :
    List.Perm endpoint.corrections (retained ++ residual)
  retained_weight_lt :
    ∀ term ∈ retained,
      decoratedFamilyWeight leftWeight rightWeight term < n
  residual_weight_ge :
    ∀ term ∈ residual,
      n ≤ decoratedFamilyWeight leftWeight rightWeight term
  retained_generated :
    ∀ term ∈ retained,
      DFTerm.CGFrom
        (inverseDecoratedTerms M N) term
  residual_generated :
    ∀ term ∈ residual,
      DFTerm.CGFrom
        (inverseDecoratedTerms M N) term

namespace CCPartit

/-- Construct the canonical cutoff partition of one exact operational correction list. -/
def ofEndpoint
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (n leftWeight rightWeight : ℕ) :
    CCPartit endpoint n leftWeight rightWeight where
  retained := belowCutoffTerms n leftWeight rightWeight endpoint.corrections
  residual := orAboveTerms n leftWeight rightWeight endpoint.corrections
  corrections_perm :=
    perm_or_above
      n leftWeight rightWeight endpoint.corrections
  retained_weight_lt := by
    intro term hterm
    exact (below_cutoff_terms.mp hterm).2
  residual_weight_ge := by
    intro term hterm
    exact (or_above_terms.mp hterm).2
  retained_generated := by
    intro term hterm
    exact FCollec.ECorrec.correctionGeneratedFrom
      endpoint.emits term (below_cutoff_terms.mp hterm).1
  residual_generated := by
    intro term hterm
    exact FCollec.ECorrec.correctionGeneratedFrom
      endpoint.emits term (or_above_terms.mp hterm).1

/--
Operational endpoint factors consist of the inverse raw source, retained
below-cutoff corrections, and residual corrections, up to permutation.
-/
lemma factors_perm_append
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint n leftWeight rightWeight) :
    List.Perm endpoint.collected.factors
      (inverseDecoratedTerms M N ++
        partition.retained ++ partition.residual) := by
  exact endpoint.perm_append_corrections.trans <| by
    simpa only [List.append_assoc] using
      List.Perm.append_left
        (inverseDecoratedTerms M N) partition.corrections_perm

/--
Every retained correction has a raw source ancestor of no larger weighted
degree, and that ancestor is itself below the cutoff.
-/
lemma retained_raw_cutoff
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint n leftWeight rightWeight)
    {term : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hterm : term ∈ partition.retained) :
    ∃ ancestor ∈ inverseDecoratedTerms M N,
      decoratedFamilyWeight leftWeight rightWeight ancestor ≤
          decoratedFamilyWeight leftWeight rightWeight term ∧
        decoratedFamilyWeight leftWeight rightWeight ancestor < n := by
  rcases
      (partition.retained_generated term hterm).source_family_weight
        hleftWeight hrightWeight with
    ⟨ancestor, hancestor, hle⟩
  exact ⟨ancestor, hancestor, hle,
    hle.trans_lt (partition.retained_weight_lt term hterm)⟩

/-- Every residual correction vanishes semantically in the matching truncation. -/
lemma residual_collapsed_list
    {M N n leftWeight rightWeight : ℕ}
    {G : Type*}
    [Group G]
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {x y : G}
    (hx : x ∈ Subgroup.lowerCentralSeries G (leftWeight - 1))
    (hy : y ∈ Subgroup.lowerCentralSeries G (rightWeight - 1))
    (hbot : Subgroup.lowerCentralSeries G (n - 1) = ⊥)
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint n leftWeight rightWeight) :
    collapsedList x y (decoratedFamilyList partition.residual) = 1 :=
  collapsed_decorated_forall
    hleftWeight hrightWeight hx hy hbot partition.residual
      partition.residual_weight_ge

end CCPartit

end OCPartit
end TCTex
end Submission

-- Merged from FamilyOperationalMultiplicityBatchScheduling.lean

/-!
# Closed multiplicity-batch schedules for operational More3 collection

The remaining operational theorem is a finite batching statement.  Every
concrete correction emitted by the stable More3 trace must be assigned to one
open Cartesian ledger, and every ledger must eventually close.

This file packages the endpoint of that scheduler.  A finite list of closed
multiplicity batches assembles automa into one exact correction
inventory, then into one exact inventory for all collected factors.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace MBScheda

open HACoeff
open IMPropag
open FIWork
open FMEnd

/-- One finite closed Cartesian correction batch with exact slot inventory. -/
structure CMBatch
    (M N K : ℕ) where
  terms :
    List (DFTerm M N K)
  inventory :
    MIBlock terms

namespace CMBatch

/-- An exhausted open Cartesian ledger is one closed multiplicity batch. -/
noncomputable def ofClosedLedger
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger : MTLedger left right)
    (hpending : ledger.pending = []) :
    CMBatch M N K where
  terms := ledger.emitted
  inventory := ledger.closedInventoryBlock hpending

end CMBatch

/-- Concatenate concrete terms emitted by a finite closed-batch schedule. -/
def closedBatchTerms
    {M N K : ℕ}
    (batches : List (CMBatch M N K)) :
    List (DFTerm M N K) :=
  batches.flatMap CMBatch.terms

/-- Concatenate retained family lists of a finite closed-batch schedule. -/
def closedBatchFamilies
    {M N K : ℕ}
    (batches : List (CMBatch M N K)) :
    List (BFam M N) :=
  batches.flatMap fun batch => batch.inventory.families

/--
A finite list of closed batches assembles into one exact
multiplicity-preserving inventory.
-/
def MIBlock.ofClosedBatches
    {M N K : ℕ}
    (batches : List (CMBatch M N K)) :
    MIBlock (closedBatchTerms batches) := by
  induction batches with
  | nil =>
      exact MIBlock.nil
  | cons batch batches ih =>
      exact batch.inventory.append ih

@[simp]
lemma MIBlock.closed_batches_fams
    {M N K : ℕ}
    (batches : List (CMBatch M N K)) :
    (MIBlock.ofClosedBatches batches).families =
      closedBatchFamilies batches := by
  induction batches with
  | nil =>
      rfl
  | cons batch batches ih =>
      change
        batch.inventory.families ++
              (MIBlock.ofClosedBatches batches).families =
            batch.inventory.families ++ closedBatchFamilies batches
      exact congrArg (List.append batch.inventory.families) ih

/-- Finite closed-batch schedule for an arbitrary concrete correction list. -/
structure MBSched
    {M N K : ℕ}
    (terms : List (DFTerm M N K)) where
  batches :
    List (CMBatch M N K)
  terms_perm :
    List.Perm (closedBatchTerms batches) terms

namespace MBSched

/-- The empty correction list has the empty closed-batch schedule. -/
def nil
    {M N K : ℕ} :
    MBSched
      ([] : List (DFTerm M N K)) where
  batches := []
  terms_perm := List.Perm.refl []

/-- One closed batch schedules its retained concrete terms. -/
def singleton
    {M N K : ℕ}
    (batch : CMBatch M N K) :
    MBSched batch.terms where
  batches := [batch]
  terms_perm := by
    simp [closedBatchTerms]

/-- Concatenate two finite closed-batch schedules. -/
def append
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : MBSched leftTerms)
    (right : MBSched rightTerms) :
    MBSched (leftTerms ++ rightTerms) where
  batches := left.batches ++ right.batches
  terms_perm := by
    simpa [closedBatchTerms] using
      left.terms_perm.append right.terms_perm

/-- Transport a closed-batch schedule across a concrete-term permutation. -/
def permTerms
    {M N K : ℕ}
    {source target : List (DFTerm M N K)}
    (schedule : MBSched source)
    (hperm : List.Perm source target) :
    MBSched target where
  batches := schedule.batches
  terms_perm := schedule.terms_perm.trans hperm

/-- A finite closed-batch schedule assembles to an exact multiplicity inventory. -/
noncomputable def inventory
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (schedule : MBSched terms) :
    MIBlock terms :=
  (MIBlock.ofClosedBatches schedule.batches).permTerms
    schedule.terms_perm

/-- An exhausted open ledger supplies a one-batch finite schedule. -/
noncomputable def ofClosedLedger
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger : MTLedger left right)
    (hpending : ledger.pending = []) :
    MBSched ledger.emitted :=
  singleton (CMBatch.ofClosedLedger ledger hpending)

end MBSched

/--
Finite closed-batch endpoint for the correction list extracted from one
terminating operational More3 run.
-/
structure OBSched
    {M N : ℕ}
    (endpoint : ODEmissi M N) where
  batches :
    List (CMBatch M N
      (inverseLabelledCollection M N).factors.length)
  corrections_perm :
    List.Perm (closedBatchTerms batches) endpoint.corrections

namespace OBSched

/-- Forget the operational wrapper and retain its generic finite schedule. -/
def multiplicityBatch
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (schedule : OBSched endpoint) :
    MBSched endpoint.corrections where
  batches := schedule.batches
  terms_perm := schedule.corrections_perm

/-- Attach a generic finite schedule to one operational endpoint. -/
def multiplicityBatchSchedule
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (schedule : MBSched endpoint.corrections) :
    OBSched endpoint where
  batches := schedule.batches
  corrections_perm := schedule.terms_perm

/-- Closed batches assemble to an exact inventory of emitted corrections. -/
noncomputable def correctionsInventory
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (schedule : OBSched endpoint) :
    MIBlock endpoint.corrections :=
  (MIBlock.ofClosedBatches schedule.batches).permTerms
    schedule.corrections_perm

/-- Closed batches therefore resolve an exact inventory of all output factors. -/
noncomputable def factorsInventory
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (schedule : OBSched endpoint) :
    MIBlock endpoint.collected.factors :=
  endpoint.factorsInventoryBlock schedule.correctionsInventory

end OBSched

/--
Concrete remaining scheduler kernel: partition every finite operational
correction list into closed Cartesian multiplicity batches.
-/
structure OMBatch : Prop where
  schedule :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N),
      Nonempty (OBSched endpoint)

namespace OMBatch

/-- Closed-batch scheduling resolves the emitted-correction inventory kernel. -/
def operat_multi_closu
    (kernel : OMBatch) :
    OMClos where
  correctionsInventory endpoint :=
    ⟨(Classical.choice (kernel.schedule endpoint)).correctionsInventory⟩

/-- Resolve an exact multiplicity inventory for one complete More3 endpoint. -/
noncomputable def factorsInventory
    (kernel : OMBatch)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    MIBlock endpoint.collected.factors :=
  (Classical.choice (kernel.schedule endpoint)).factorsInventory

end OMBatch

end MBScheda
end TCTex
end Submission

-- Merged from FamilyInventory.lean

/-!
# Cutoff filtering of multiplicity-preserving family inventories

Weighted Hall degree depends only on a term's represented `BFam`.
Consequently, exact multiplicity inventories may be restricted below or above
a nilpotent cutoff without losing realization-token accounting.

The operational cutoff partition permits any retained and residual lists with
the required weight bounds.  This file proves that both lists are permutations
of the corresponding canonical family filters and transports exact inventories
onto them.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace ICFilter

open HACoeff
open BRSpec
open FIFilter.MIBlock
open IMPropag
open IMWitnes.MIBlock
open OCPartit
open FMEnd

/-- Weighted Hall degree of one represented block family. -/
def blockFamilyWeight
    {M N : ℕ}
    (leftWeight rightWeight : ℕ)
    (family : BFam M N) :
    ℕ :=
  weightedWordWeight leftWeight rightWeight family.recipe

lemma decorated_family_block
    {M N K : ℕ}
    (leftWeight rightWeight : ℕ)
    (term : DFTerm M N K) :
    decoratedFamilyWeight leftWeight rightWeight term =
      blockFamilyWeight leftWeight rightWeight term.family :=
  rfl

namespace MIBlock

/-- Restrict an exact family inventory to concrete terms below the cutoff. -/
noncomputable def filterBelowCutoff
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (block : MIBlock terms)
    (n leftWeight rightWeight : ℕ) :
    MIBlock
      (belowCutoffTerms n leftWeight rightWeight terms) := by
  change MIBlock
    (terms.filter fun term =>
      blockFamilyWeight leftWeight rightWeight term.family < n)
  exact filterFamilies block fun family =>
    blockFamilyWeight leftWeight rightWeight family < n

/-- Restrict an exact family inventory to concrete terms at or above the cutoff. -/
noncomputable def filterOrAbove
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (block : MIBlock terms)
    (n leftWeight rightWeight : ℕ) :
    MIBlock
      (terms.filter fun term =>
        ¬ decoratedFamilyWeight leftWeight rightWeight term < n) := by
  change MIBlock
    (terms.filter fun term =>
      ¬ blockFamilyWeight leftWeight rightWeight term.family < n)
  exact filterFamilies block fun family =>
    ¬ blockFamilyWeight leftWeight rightWeight family < n

@[simp]
lemma filter_below_families
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (block : MIBlock terms)
    (n leftWeight rightWeight : ℕ) :
    (filterBelowCutoff block n leftWeight rightWeight).families =
      block.families.filter fun family =>
        blockFamilyWeight leftWeight rightWeight family < n := by
  rfl

@[simp]
lemma filter_or_families
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (block : MIBlock terms)
    (n leftWeight rightWeight : ℕ) :
    (filterOrAbove block n leftWeight rightWeight).families =
      block.families.filter fun family =>
        ¬ blockFamilyWeight leftWeight rightWeight family < n := by
  rfl

/-- Every represented family retained below the cutoff has small weighted degree. -/
lemma filter_below_cutoff
    {M N K n leftWeight rightWeight : ℕ}
    {terms : List (DFTerm M N K)}
    (block : MIBlock terms)
    {family : BFam M N}
    (hfamily :
      family ∈ (filterBelowCutoff block n leftWeight rightWeight).families) :
    blockFamilyWeight leftWeight rightWeight family < n := by
  rw [filter_below_families] at hfamily
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hfamily).2

/-- Every represented residual family has weighted degree at least the cutoff. -/
lemma filter_or_above
    {M N K n leftWeight rightWeight : ℕ}
    {terms : List (DFTerm M N K)}
    (block : MIBlock terms)
    {family : BFam M N}
    (hfamily :
      family ∈
        (filterOrAbove block n leftWeight rightWeight).families) :
    n ≤ blockFamilyWeight leftWeight rightWeight family := by
  rw [filter_or_families] at hfamily
  apply Nat.le_of_not_lt
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hfamily).2

end MIBlock

open MIBlock

namespace CCPartit

/--
The canonical below-cutoff filter of emitted corrections is a permutation of
the retained side of any operational cutoff partition.
-/
lemma belowTermsPerm
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint n leftWeight rightWeight) :
    List.Perm
      (belowCutoffTerms n leftWeight rightWeight endpoint.corrections)
      partition.retained := by
  have hretained :
      partition.retained.filter
          (fun term =>
            decide (decoratedFamilyWeight leftWeight rightWeight term < n)) =
        partition.retained := by
    apply List.filter_eq_self.2
    intro term hterm
    simpa only [decide_eq_true_eq] using
      partition.retained_weight_lt term hterm
  have hresidual :
      partition.residual.filter
          (fun term =>
            decide (decoratedFamilyWeight leftWeight rightWeight term < n)) =
        [] := by
    apply List.filter_eq_nil_iff.2
    intro term hterm
    have hnot := not_lt_of_ge (partition.residual_weight_ge term hterm)
    simp [hnot]
  simpa [belowCutoffTerms, List.filter_append, hretained, hresidual] using
    partition.corrections_perm.filter
      (fun term =>
        decide (decoratedFamilyWeight leftWeight rightWeight term < n))

/--
The canonical residual filter of emitted corrections is a permutation of the
at-or-above-cutoff side of any operational cutoff partition.
-/
lemma or_above_perm
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint n leftWeight rightWeight) :
    List.Perm
      (orAboveTerms n leftWeight rightWeight endpoint.corrections)
      partition.residual := by
  have hretained :
      partition.retained.filter
          (fun term =>
            !decide (decoratedFamilyWeight leftWeight rightWeight term < n)) =
        [] := by
    apply List.filter_eq_nil_iff.2
    intro term hterm
    have hlt := partition.retained_weight_lt term hterm
    simp [hlt]
  have hresidual :
      partition.residual.filter
          (fun term =>
            !decide (decoratedFamilyWeight leftWeight rightWeight term < n)) =
        partition.residual := by
    apply List.filter_eq_self.2
    intro term hterm
    have hnot := not_lt_of_ge (partition.residual_weight_ge term hterm)
    simp [hnot]
  simpa [orAboveTerms, List.filter_append, hretained, hresidual] using
    partition.corrections_perm.filter
      (fun term =>
        !decide (decoratedFamilyWeight leftWeight rightWeight term < n))

/--
The proposition-valued residual filter of emitted corrections is a permutation
of the residual side of any operational cutoff partition.
-/
lemma filter_perm_residual
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint n leftWeight rightWeight) :
    List.Perm
      (endpoint.corrections.filter fun term =>
        ¬ decoratedFamilyWeight leftWeight rightWeight term < n)
      partition.residual := by
  have hretained :
      partition.retained.filter
          (fun term =>
            ¬ decoratedFamilyWeight leftWeight rightWeight term < n) =
        [] := by
    apply List.filter_eq_nil_iff.2
    intro term hterm
    have hlt := partition.retained_weight_lt term hterm
    simp [hlt]
  have hresidual :
      partition.residual.filter
          (fun term =>
            ¬ decoratedFamilyWeight leftWeight rightWeight term < n) =
        partition.residual := by
    apply List.filter_eq_self.2
    intro term hterm
    have hnot := not_lt_of_ge (partition.residual_weight_ge term hterm)
    simpa only [decide_eq_true_eq] using hnot
  simpa only [List.filter_append, hretained, hresidual, List.append_nil] using
    partition.corrections_perm.filter
      (fun term =>
        decide (¬ decoratedFamilyWeight leftWeight rightWeight term < n))

/-- Exact emitted-correction inventory transports to the retained partition. -/
noncomputable def retainedInventoryBlock
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint n leftWeight rightWeight)
    (corrections : MIBlock endpoint.corrections) :
    MIBlock partition.retained :=
  (MIBlock.filterBelowCutoff
    corrections n leftWeight rightWeight).permTerms
    (belowTermsPerm partition)

/-- Exact emitted-correction inventory transports to the residual partition. -/
noncomputable def residualInventoryBlock
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint n leftWeight rightWeight)
    (corrections : MIBlock endpoint.corrections) :
    MIBlock partition.residual :=
  (MIBlock.filterOrAbove
    corrections n leftWeight rightWeight).permTerms
    (filter_perm_residual partition)

/-- Every represented retained family has weighted Hall degree below the cutoff. -/
lemma family_inventory_block
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint n leftWeight rightWeight)
    (corrections : MIBlock endpoint.corrections)
    {family : BFam M N}
    (hfamily :
      family ∈
        (retainedInventoryBlock partition corrections).families) :
    blockFamilyWeight leftWeight rightWeight family < n :=
  MIBlock.filter_below_cutoff
    corrections hfamily

/-- Every represented residual family has weighted Hall degree at least the cutoff. -/
lemma multiplicity_inventory_block
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint n leftWeight rightWeight)
    (corrections : MIBlock endpoint.corrections)
    {family : BFam M N}
    (hfamily :
      family ∈
        (residualInventoryBlock partition corrections).families) :
    n ≤ blockFamilyWeight leftWeight rightWeight family :=
  MIBlock.filter_or_above
    corrections hfamily

/--
Every represented retained family has an inverse-raw concrete ancestor of no
larger weighted Hall degree.  In particular, that ancestor is below cutoff.
-/
lemma family_raw_cutoff
    {M N n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint n leftWeight rightWeight)
    (corrections : MIBlock endpoint.corrections)
    {family : BFam M N}
    (hfamily :
      family ∈
        (retainedInventoryBlock partition corrections).families) :
    ∃ ancestor ∈ inverseDecoratedTerms M N,
      decoratedFamilyWeight leftWeight rightWeight ancestor ≤
          blockFamilyWeight leftWeight rightWeight family ∧
        decoratedFamilyWeight leftWeight rightWeight ancestor < n := by
  let retained :=
    retainedInventoryBlock partition corrections
  rcases term_family retained hfamily with
    ⟨term, hterm, htermFamily⟩
  rcases
      partition.retained_raw_cutoff
        hleftWeight hrightWeight hterm with
    ⟨ancestor, hancestor, hle, hlt⟩
  rw [decorated_family_block
    leftWeight rightWeight term, htermFamily] at hle
  refine ⟨ancestor, hancestor, ?_, hlt⟩
  rw [decorated_family_block
    leftWeight rightWeight ancestor]
  exact hle

end CCPartit

/--
Exact multiplicity inventories for both sides of one operational correction
cutoff partition.
-/
structure OperationalMultiplicityInventories
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint n leftWeight rightWeight) where
  retained :
    MIBlock partition.retained
  residual :
    MIBlock partition.residual

/--
Any emitted-correction multiplicity closure kernel supplies exact inventories
on both sides of every operational cutoff partition.
-/
noncomputable def operationalMultiplicityInventories
    (kernel : OMClos)
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint n leftWeight rightWeight) :
    OperationalMultiplicityInventories partition := by
  let corrections :=
    Classical.choice (kernel.correctionsInventory endpoint)
  exact {
    retained :=
      CCPartit.retainedInventoryBlock
        partition corrections
    residual :=
      CCPartit.residualInventoryBlock
        partition corrections }

end ICFilter
end TCTex
end Submission

/-!
# Heterogeneous multiplicity-batch worklists

The operational More3 trace interleaves correction slots from different
Cartesian parent grids.  A single ledger therefore is not enough as global
scheduler state.  This file packages heterogeneous open ledgers into one
finite worklist.

Every arithmetic emission step consumes one selected pending slot and strictly
decreases the total pending count.  When every item closes, the retained
emission lists assemble compositionally into a finite closed-batch schedule.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace IMWork

open HACoeff
open IMPropag
open FIWork
open MBScheda

/-- One heterogeneous open Cartesian correction batch. -/
structure MWItem
    (M N K : ℕ) where
  leftTerms :
    List (DFTerm M N K)
  rightTerms :
    List (DFTerm M N K)
  left :
    MIBlock leftTerms
  right :
    MIBlock rightTerms
  ledger :
    MTLedger left right

namespace MWItem

/-- Open one heterogeneous batch with every Cartesian slot pending. -/
noncomputable def initial
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : MIBlock leftTerms)
    (right : MIBlock rightTerms) :
    MWItem M N K where
  leftTerms := leftTerms
  rightTerms := rightTerms
  left := left
  right := right
  ledger := MTLedger.initial left right

/-- Consume one selected pending slot in one heterogeneous batch. -/
def emit
    {M N K : ℕ}
    (item : MWItem M N K)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : item.ledger.pending = before ++ term :: after) :
    MWItem M N K where
  leftTerms := item.leftTerms
  rightTerms := item.rightTerms
  left := item.left
  right := item.right
  ledger := item.ledger.emit before term after hpending

/-- One heterogeneous batch is closed when no Cartesian slots remain pending. -/
def Closed
    {M N K : ℕ}
    (item : MWItem M N K) :
    Prop :=
  item.ledger.pending = []

/-- A closed heterogeneous batch supplies one exact closed batch. -/
noncomputable def closedBatch
    {M N K : ℕ}
    (item : MWItem M N K)
    (hclosed : item.Closed) :
    CMBatch M N K :=
  CMBatch.ofClosedLedger item.ledger hclosed

/-- Number of Cartesian slots still pending in one heterogeneous batch. -/
def pendingSlots
    {M N K : ℕ}
    (item : MWItem M N K) :
    ℕ :=
  item.ledger.pending.length

/-- Consuming one selected slot strictly decreases the item pending count. -/
lemma pendingSlots_emit
    {M N K : ℕ}
    (item : MWItem M N K)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : item.ledger.pending = before ++ term :: after) :
    (item.emit before term after hpending).pendingSlots + 1 =
      item.pendingSlots :=
  item.ledger.pending_length_emit before term after hpending

end MWItem

/-- One concrete More3 obstruction routed to one heterogeneous open batch. -/
structure MBEmissi
    {M N K : ℕ}
    (item : MWItem M N K) where
  emission :
    CMEmissi item.ledger

namespace MBEmissi

/-- Route a selected Cartesian parent pair to its pending worklist slot. -/
noncomputable def ofMemPending
    {M N K : ℕ}
    (item : MWItem M N K)
    (leftTerm : DFTerm M N K)
    (rightTerm : DFTerm M N K)
    (hleft : leftTerm ∈ item.leftTerms)
    (hright : rightTerm ∈ item.rightTerms)
    (hpending :
      leftTerm.correction rightTerm ∈ item.ledger.pending) :
    MBEmissi item := by
  let hdecomposition := List.mem_iff_append.mp hpending
  let before := hdecomposition.choose
  let after := hdecomposition.choose_spec.choose
  have hpending_eq :
      item.ledger.pending =
        before ++ leftTerm.correction rightTerm :: after :=
    hdecomposition.choose_spec.choose_spec
  exact ⟨{
    leftTerm := leftTerm
    rightTerm := rightTerm
    left_mem := hleft
    right_mem := hright
    pendingPrefix := before
    pendingSuffix := after
    pending_eq := hpending_eq }⟩

/-- Consume the routed More3 correction slot in its heterogeneous batch. -/
noncomputable def emitItem
    {M N K : ℕ}
    {item : MWItem M N K}
    (emission : MBEmissi item) :
    MWItem M N K :=
  item.emit emission.emission.pendingPrefix
    (emission.emission.leftTerm.correction emission.emission.rightTerm)
    emission.emission.pendingSuffix emission.emission.pending_eq

/-- The routed More3 obstruction is one explicit adjacent labelled-word step. -/
def labelledWordStep
    {M N K : ℕ}
    {item : MWItem M N K}
    (emission : MBEmissi item)
    (pre post :
      List (CWord (LabelledAtom M N))) :
    BBSched.LWStep
      (pre ++
        [emission.emission.leftTerm.decorated.word,
          emission.emission.rightTerm.decorated.word] ++ post)
      (pre ++
        [(emission.emission.leftTerm.correction
            emission.emission.rightTerm).decorated.word,
          emission.emission.rightTerm.decorated.word,
          emission.emission.leftTerm.decorated.word] ++ post) :=
  emission.emission.labelledWordStep pre post

end MBEmissi

/-- A finite list of heterogeneous open or closed correction batches. -/
abbrev MBWork
    (M N K : ℕ) :=
  List (MWItem M N K)

namespace MBWork

/-- Total number of pending Cartesian slots in a heterogeneous worklist. -/
def pendingSlots
    {M N K : ℕ}
    (worklist : MBWork M N K) :
    ℕ :=
  (worklist.map MWItem.pendingSlots).sum

/-- Every heterogeneous batch in a worklist has been exhausted. -/
def Closed
    {M N K : ℕ}
    (worklist : MBWork M N K) :
    Prop :=
  ∀ item ∈ worklist, item.Closed

/-- Consume one selected pending slot inside one heterogeneous worklist item. -/
inductive Step
    {M N K : ℕ} :
    MBWork M N K →
      MBWork M N K →
        Prop where
  | emit
      (pre post : MBWork M N K)
      (item : MWItem M N K)
      (before : List (DFTerm M N K))
      (term : DFTerm M N K)
      (after : List (DFTerm M N K))
      (hpending : item.ledger.pending = before ++ term :: after) :
      Step
        (pre ++ item :: post)
        (pre ++ item.emit before term after hpending :: post)

/-- Finite arithmetic emission run for a heterogeneous batch worklist. -/
abbrev Rewrites
    {M N K : ℕ}
    (worklist final : MBWork M N K) :
    Prop :=
  Relation.ReflTransGen Step worklist final

/-- Every heterogeneous worklist emission strictly decreases open-slot count. -/
lemma pending_slots_step
    {M N K : ℕ}
    {before after : MBWork M N K}
    (hstep : Step before after) :
    pendingSlots after < pendingSlots before := by
  cases hstep with
  | emit pre post item before term after hpending =>
      simp only [pendingSlots, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons]
      have hlength := item.pendingSlots_emit before term after hpending
      omega

/-- Every nonclosed heterogeneous worklist admits one arithmetic emission. -/
lemma step_not_closed
    {M N K : ℕ}
    (worklist : MBWork M N K)
    (hclosed : ¬ worklist.Closed) :
    ∃ next, Step worklist next := by
  simp only [Closed, not_forall] at hclosed
  rcases hclosed with ⟨item, hitem⟩
  rcases hitem with ⟨hitem, hopen⟩
  rcases List.mem_iff_append.mp hitem with ⟨pre, post, hworklist⟩
  simp only [MWItem.Closed] at hopen
  cases hpending : item.ledger.pending with
  | nil =>
      exact False.elim (hopen hpending)
  | cons term after =>
      refine ⟨pre ++ item.emit [] term after hpending :: post, ?_⟩
      rw [hworklist]
      exact Step.emit pre post item [] term after hpending

/-- Every finite heterogeneous arithmetic worklist can be drained. -/
lemma exists_rewrites_closed
    {M N K : ℕ}
    (worklist : MBWork M N K) :
    ∃ final, Rewrites worklist final ∧ final.Closed := by
  by_cases hclosed : worklist.Closed
  · exact ⟨worklist, Relation.ReflTransGen.refl, hclosed⟩
  · rcases step_not_closed worklist hclosed with ⟨next, hstep⟩
    rcases exists_rewrites_closed next with ⟨final, hrewrites, hclosed⟩
    exact ⟨final, hrewrites.head hstep, hclosed⟩
termination_by worklist.pendingSlots
decreasing_by
  exact pending_slots_step hstep

/-- A routed concrete More3 obstruction consumes one worklist slot. -/
def stepConcreteEmission
    {M N K : ℕ}
    (pre post : MBWork M N K)
    (item : MWItem M N K)
    (emission : MBEmissi item) :
    Step
      (pre ++ item :: post)
      (pre ++ emission.emitItem :: post) :=
  Step.emit pre post item emission.emission.pendingPrefix
    (emission.emission.leftTerm.correction emission.emission.rightTerm)
    emission.emission.pendingSuffix emission.emission.pending_eq

/-- Closed heterogeneous worklists assemble into finite closed-batch schedules. -/
noncomputable def closedSchedule
    {M N K : ℕ}
    (worklist : MBWork M N K)
    (hclosed : worklist.Closed) :
    MBSched
      (worklist.flatMap fun item => item.ledger.emitted) := by
  induction worklist with
  | nil =>
      exact MBSched.nil
  | cons item worklist ih =>
      exact
        (MBSched.ofClosedLedger item.ledger
          (hclosed item (by simp))).append
            (ih (by
              intro next hnext
              exact hclosed next (by simp [hnext])))

end MBWork

end IMWork
end TCTex
end Submission

-- Merged from FamilyOperational.lean

-- Merged from FamilyOperationalCorrectionAccounting.lean

/-!
# Operational More3 correction accounting

`DFTerm.IInsert` performs actual one-slot More3
obstructions.  This file records the finite list of correction terms emitted
by a derivation and proves exact multiset accounting:

* insertion output = insertion source + inserted term + emitted corrections;
* collection output = collection source + emitted corrections.

The trace types are propositions, so the emitted list is represented by an
indexed proposition rather than extracted as computational data.  The
endpoint order is intentionally forgotten only when deriving permutations.
This is the global bridge between the stable recursive trace and the open
Cartesian batch ledgers used by multiplicity-preserving packet scheduling.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace FOAccoun

open HACoeff

lemma multisetCoe_append
    {α : Type*}
    (left right : List α) :
    ((left ++ right : List α) : Multiset α) =
      (left : Multiset α) + (right : Multiset α) :=
  (Multiset.coe_add left right).symm

lemma multisetCoe_cons
    {α : Type*}
    (head : α)
    (tail : List α) :
    ((head :: tail : List α) : Multiset α) =
      {head} + (tail : Multiset α) :=
  rfl

namespace DFTerm.IInsert

/-- Concrete correction terms emitted by one actual More3 insertion trace. -/
inductive GeneratedCorrections
    {M N K : ℕ} :
    {L R : List (DFTerm M N K)} →
      {A : DFTerm M N K} →
        DFTerm.IInsert L A R →
          List (DFTerm M N K) →
            Prop where
  | nil
      (A : DFTerm M N K) :
      GeneratedCorrections (.nil A) []
  | append
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hAB : ¬ A.decorated.independentBefore B.decorated) :
      GeneratedCorrections (.append P B A hAB) []
  | obstruction
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hAB : A.decorated.independentBefore B.decorated)
      {Q R : List (DFTerm M N K)}
      {correctionCorrections insertCorrections :
        List (DFTerm M N K)}
      {hcorrection :
        DFTerm.IInsert P (B.correction A) Q}
      {hinsert : DFTerm.IInsert Q A R}
      (hcorrectionGenerated :
        GeneratedCorrections hcorrection correctionCorrections)
      (hinsertGenerated :
        GeneratedCorrections hinsert insertCorrections) :
      GeneratedCorrections
        (.obstruction P B A hAB hcorrection hinsert)
        (B.correction A ::
          (correctionCorrections ++ insertCorrections))

/-- Every actual insertion trace has a recursively ordered correction list. -/
lemma exists_generate
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert : DFTerm.IInsert L A R) :
    ∃ corrections, GeneratedCorrections hinsert corrections := by
  induction hinsert with
  | nil A =>
      exact ⟨[], .nil A⟩
  | append P B A hAB =>
      exact ⟨[], .append P B A hAB⟩
  | obstruction P B A hAB hcorrection hinsert
      ihcorrection ihinsert =>
      rcases ihcorrection with ⟨correctionCorrections, hcorrectionGenerated⟩
      rcases ihinsert with ⟨insertCorrections, hinsertGenerated⟩
      exact ⟨B.correction A ::
        (correctionCorrections ++ insertCorrections),
        .obstruction P B A hAB hcorrectionGenerated hinsertGenerated⟩

/--
Insertion output contains exactly the old terms, the inserted term, and every
concrete correction emitted by recursive More3 obstruction steps.
-/
lemma result_inser_corre
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {corrections : List (DFTerm M N K)}
    {hinsert : DFTerm.IInsert L A R}
    (hgenerated : GeneratedCorrections hinsert corrections) :
    (R : Multiset (DFTerm M N K)) =
      (L : Multiset (DFTerm M N K)) +
        {A} + corrections := by
  induction hgenerated with
  | nil A =>
      simp only [Multiset.coe_nil, Multiset.coe_singleton, add_zero, zero_add]
  | append P B A _hAB =>
      simp only [multisetCoe_append, multisetCoe_cons,
        Multiset.coe_nil, add_zero]
      rw [← add_assoc]
  | obstruction P B A _hAB hcorrectionGenerated hinsertGenerated
      ihcorrection ihinsert =>
      simp only [multisetCoe_append, multisetCoe_cons,
        Multiset.coe_nil, add_zero]
      rw [ihinsert, ihcorrection]
      simp only [add_comm, add_left_comm, add_assoc]

/-- List-permutation form of insertion correction accounting. -/
lemma result_perm_inserted
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {corrections : List (DFTerm M N K)}
    {hinsert : DFTerm.IInsert L A R}
    (hgenerated : GeneratedCorrections hinsert corrections) :
    List.Perm R (L ++ [A] ++ corrections) := by
  apply Multiset.coe_eq_coe.mp
  rw [multisetCoe_append, multisetCoe_append, Multiset.coe_singleton]
  exact result_inser_corre hgenerated

end DFTerm.IInsert

open DFTerm.IInsert

namespace DFTerm.ICollec

/-- Concrete correction terms emitted by one complete actual More3 collection. -/
inductive GeneratedCorrections
    {M N K : ℕ} :
    {L R : List (DFTerm M N K)} →
      DFTerm.ICollec L R →
        List (DFTerm M N K) →
          Prop where
  | nil :
      GeneratedCorrections
        (DFTerm.ICollec.nil
          (M := M) (N := N) (K := K))
        []
  | snoc
      (P : List (DFTerm M N K))
      (A : DFTerm M N K)
      {C R : List (DFTerm M N K)}
      {collectCorrections insertCorrections :
        List (DFTerm M N K)}
      {hcollect : DFTerm.ICollec P C}
      {hinsert : DFTerm.IInsert C A R}
      (hcollectGenerated : GeneratedCorrections hcollect collectCorrections)
      (hinsertGenerated :
        DFTerm.IInsert.GeneratedCorrections
          hinsert insertCorrections) :
      GeneratedCorrections
        (.snoc P A hcollect hinsert)
        (collectCorrections ++ insertCorrections)

/-- Every complete collection trace has a recursively ordered correction list. -/
lemma exists_generate
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    (hcollect : DFTerm.ICollec L R) :
    ∃ corrections, GeneratedCorrections hcollect corrections := by
  induction hcollect with
  | nil =>
      exact ⟨[], .nil⟩
  | snoc P A hcollect hinsert ihcollect =>
      rcases ihcollect with ⟨collectCorrections, hcollectGenerated⟩
      rcases
          DFTerm.IInsert.exists_generate
            hinsert with
        ⟨insertCorrections, hinsertGenerated⟩
      exact ⟨collectCorrections ++ insertCorrections,
        .snoc P A hcollectGenerated hinsertGenerated⟩

/--
Collection output contains exactly the input terms and all recursively emitted
concrete corrections.
-/
lemma result_gener_corre
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    {corrections : List (DFTerm M N K)}
    {hcollect : DFTerm.ICollec L R}
    (hgenerated : GeneratedCorrections hcollect corrections) :
    (R : Multiset (DFTerm M N K)) =
      (L : Multiset (DFTerm M N K)) +
        corrections := by
  induction hgenerated with
  | nil =>
      simp only [Multiset.coe_nil, add_zero]
  | snoc P A hcollectGenerated hinsertGenerated ihcollect =>
      simp only [multisetCoe_append, Multiset.coe_singleton] at ihcollect ⊢
      rw [
        result_inser_corre
          hinsertGenerated,
        ihcollect]
      simp only [add_comm, add_left_comm, add_assoc]

/-- List-permutation form of complete collection correction accounting. -/
lemma result_appen_corre
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    {corrections : List (DFTerm M N K)}
    {hcollect : DFTerm.ICollec L R}
    (hgenerated : GeneratedCorrections hcollect corrections) :
    List.Perm R (L ++ corrections) := by
  apply Multiset.coe_eq_coe.mp
  rw [multisetCoe_append]
  exact result_gener_corre hgenerated

end DFTerm.ICollec

open HOCollec
open DFTerm.ICollec

namespace ODTerms

/--
Every stable operational endpoint retains a recursively ordered list of the
concrete corrections emitted by its More3 derivation.
-/
lemma exists_generate
    {M N : ℕ}
    (collected : ODTerms M N) :
    ∃ corrections,
      DFTerm.ICollec.GeneratedCorrections
        collected.family_collects corrections :=
  DFTerm.ICollec.exists_generate
    collected.family_collects

/--
The concrete factors of a stable operational endpoint are exactly the raw
inverse factors plus the corrections emitted by its retained More3 trace,
up to permutation.
-/
lemma perm_generated_corrections
    {M N : ℕ}
    (collected : ODTerms M N) :
    ∃ corrections,
      DFTerm.ICollec.GeneratedCorrections
          collected.family_collects corrections ∧
        List.Perm collected.factors
          (inverseDecoratedTerms M N ++ corrections) := by
  rcases exists_generate collected with
    ⟨corrections, hgenerated⟩
  exact ⟨corrections, hgenerated,
    result_appen_corre hgenerated⟩

end ODTerms

end FOAccoun
end TCTex
end Submission

-- Merged from FamilyOperationalMultiplicityWorklistScheduling.lean

/-!
# Operational heterogeneous-worklist scheduling

The multiplicity-preserving endpoint is reduced here to one concrete
scheduler law.  For every terminating More3 endpoint, construct a finite
closed heterogeneous worklist whose concatenated emitted slots are a
permutation of the correction trace retained by the collector.

All arithmetic closure and endpoint compression are already automatic.
The remaining proof obligation is the operational assignment of actual More3
obstructions to pending slots in opened Cartesian batches.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace MWSched

open HACoeff
open IMWork
open MBScheda
open FMEnd

/--
A closed heterogeneous worklist whose emitted terms account for one complete
operational More3 correction trace.
-/
structure OWSched
    {M N : ℕ}
    (endpoint : ODEmissi M N) where
  worklist :
    MBWork M N
      (inverseLabelledCollection M N).factors.length
  closed :
    worklist.Closed
  corrections_perm :
    List.Perm
      (worklist.flatMap fun item => item.ledger.emitted)
      endpoint.corrections

namespace OWSched

/-- Closed heterogeneous worklists forget to finite closed-batch schedules. -/
noncomputable def batchSchedule
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (schedule : OWSched endpoint) :
    OBSched endpoint :=
  OBSched.multiplicityBatchSchedule
    endpoint
    ((schedule.worklist.closedSchedule schedule.closed).permTerms
      schedule.corrections_perm)

/-- Resolve an exact multiplicity inventory for one complete More3 endpoint. -/
noncomputable def factorsInventory
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (schedule : OWSched endpoint) :
    IMPropag.MIBlock
      endpoint.collected.factors :=
  schedule.batchSchedule.factorsInventory

end OWSched

/--
Concrete remaining scheduler kernel: route every actual More3 obstruction to
a pending slot in a finite heterogeneous worklist and close every opened batch.
-/
structure OMWork : Prop where
  schedule :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N),
      Nonempty (OWSched endpoint)

namespace OMWork

/-- Heterogeneous-worklist scheduling resolves finite closed-batch scheduling. -/
def operationalMultiplicityBatch
    (kernel : OMWork) :
    OMBatch where
  schedule endpoint :=
    ⟨(Classical.choice (kernel.schedule endpoint)).batchSchedule⟩

/-- Heterogeneous-worklist scheduling resolves the complete endpoint inventory. -/
noncomputable def factorsInventory
    (kernel : OMWork)
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    IMPropag.MIBlock
      endpoint.collected.factors :=
  (Classical.choice (kernel.schedule endpoint)).factorsInventory

end OMWork

end MWSched
end TCTex
end Submission

-- Merged from FamilyOperationalMultiplicityTraceRouting.lean

/-!
# Sequential routing of operational More3 corrections

The collector emits correction terms in recursive operational order, while a
closed heterogeneous worklist groups them by Cartesian batch.  This file
bridges those two orders.

A routing state remembers the operational correction prefix already consumed
and a permutation certificate saying that the same terms are exactly the
emitted slots of its open worklist.  Opening a fresh batch preserves the
prefix.  Routing one selected pending slot appends that concrete correction to
the prefix.  Once every open batch closes, the state supplies a finite
closed-batch schedule for the routed trace.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace MTRoute

open HACoeff
open IMWork
open IMPropag
open FIWork
open OEAccoun
open MBScheda
open FMEnd
open MWSched

namespace FInsert.ECorrec

/-- Insertion into an empty concrete source emits no correction terms. -/
lemma nil_source
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {hinsert : DFTerm.IInsert L A R}
    (hemits : FInsert.ECorrec hinsert corrections)
    (hsource : L = []) :
    corrections = [] := by
  cases hemits
  · rfl
  · simp at hsource
  · simp at hsource

end FInsert.ECorrec

namespace FCollec.ECorrec

/-- Collection from an empty concrete source emits no correction terms. -/
lemma nil_source
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {hcollect :
      DFTerm.ICollec L R}
    (hemits : FCollec.ECorrec hcollect corrections)
    (hsource : L = []) :
    corrections = [] := by
  cases hemits
  · rfl
  · simp at hsource

/-- A concrete collection of at most one source term emits no corrections. -/
lemma nil_source_length
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {hcollect : DFTerm.ICollec L R}
    (hemits : FCollec.ECorrec hcollect corrections)
    (hsource : L.length ≤ 1) :
    corrections = [] := by
  cases hemits with
  | nil =>
      rfl
  | @snoc P A C R hcollect hinsert collectTerms insertTerms
      hcollectTerms hinsertTerms =>
      have hP : P = [] := by
        apply List.length_eq_zero_iff.mp
        simpa using hsource
      have hcollectTermsNil :
          collectTerms = [] :=
        nil_source hcollectTerms hP
      have hCperm :=
        FCollec.result_perm_append hcollectTerms
      have hClength : C.length = 0 := by
        rw [hP, hcollectTermsNil] at hCperm
        simpa using hCperm.length_eq
      have hC : C = [] :=
        List.length_eq_zero_iff.mp hClength
      have hinsertTermsNil :
          insertTerms = [] :=
        FInsert.ECorrec.nil_source
          hinsertTerms hC
      simp [hcollectTermsNil, hinsertTermsNil]

end FCollec.ECorrec

/-- The inverse raw decorated-family source is empty when no left labels exist. -/
lemma inverse_decorated_terms
    (N : ℕ) :
    inverseDecoratedTerms 0 N = [] := by
  simp [inverseDecoratedTerms, inverseLabelledCollection,
    labelledLeftAtoms, inverseLeftTrace]

/-- The inverse raw decorated-family source is empty when no right labels exist. -/
lemma inverse_raw_decorated
    (M : ℕ) :
    inverseDecoratedTerms M 0 = [] := by
  simp [inverseDecoratedTerms, inverseLabelledCollection,
    labelledRightAtoms,
    HACoeff.inverse_left_nil]

/-- The first positive-positive inverse raw source has exactly one term. -/
lemma inverse_decorated_length :
    (inverseDecoratedTerms 1 1).length = 1 := by
  simp [inverseDecoratedTerms, inverseLabelledCollection,
    labelledLeftAtoms, labelledRightAtoms, inverseLeftTrace,
    inverseRightTrace, inverseTraceList, inverseConjTrace]

/-- Concrete terms emitted so far by every heterogeneous batch in list order. -/
def multiplicityWorklistEmitted
    {M N K : ℕ}
    (worklist : MBWork M N K) :
    List (DFTerm M N K) :=
  worklist.flatMap fun item => item.ledger.emitted

/--
One worklist emission appends the selected concrete term up to permutation of
the terms emitted by later heterogeneous batches.
-/
lemma emitted_emit_perm
    {M N K : ℕ}
    (pre post : MBWork M N K)
    (item : MWItem M N K)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : item.ledger.pending = before ++ term :: after) :
    List.Perm
      (multiplicityWorklistEmitted
        (pre ++ item.emit before term after hpending :: post))
      (multiplicityWorklistEmitted
        (pre ++ item :: post) ++ [term]) := by
  simp only [multiplicityWorklistEmitted, List.flatMap_append,
    List.flatMap_cons, MWItem.emit,
    MTLedger.emit]
  have hcomm :
      List.Perm
        (([term] : List (DFTerm M N K)) ++
          (post.flatMap fun item => item.ledger.emitted))
        ((post.flatMap fun item => item.ledger.emitted) ++ [term]) :=
    List.perm_append_comm
  simpa [List.append_assoc] using
    hcomm.append_left
        ((pre.flatMap fun item => item.ledger.emitted) ++ item.ledger.emitted)

/--
Sequential routing state for a finite operational correction prefix.  Batch
order and operational emission order may differ only by permutation.
-/
structure MRStatea
    (M N K : ℕ) where
  worklist :
    MBWork M N K
  routedTerms :
    List (DFTerm M N K)
  emitted_perm :
    List.Perm
      (multiplicityWorklistEmitted worklist)
      routedTerms

namespace MRStatea

/-- Empty worklist state before any operational correction has been routed. -/
def nil
    (M N K : ℕ) :
    MRStatea M N K where
  worklist := []
  routedTerms := []
  emitted_perm := List.Perm.refl []

/-- Open one fresh Cartesian batch without changing the routed prefix. -/
noncomputable def openBatch
    {M N K : ℕ}
    (state : MRStatea M N K)
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : MIBlock leftTerms)
    (right : MIBlock rightTerms) :
    MRStatea M N K where
  worklist :=
    state.worklist ++ [MWItem.initial left right]
  routedTerms := state.routedTerms
  emitted_perm := by
    simpa [multiplicityWorklistEmitted,
      MWItem.initial,
      MTLedger.initial] using state.emitted_perm

/-- Route one selected pending correction slot and append it operationally. -/
noncomputable def route
    {M N K : ℕ}
    (state : MRStatea M N K)
    (pre post : MBWork M N K)
    (item : MWItem M N K)
    (hworklist : state.worklist = pre ++ item :: post)
    (emission : MBEmissi item) :
    MRStatea M N K where
  worklist := pre ++ emission.emitItem :: post
  routedTerms :=
    state.routedTerms ++
      [emission.emission.leftTerm.correction emission.emission.rightTerm]
  emitted_perm := by
    have hroute :=
      emitted_emit_perm
        pre post item emission.emission.pendingPrefix
          (emission.emission.leftTerm.correction emission.emission.rightTerm)
          emission.emission.pendingSuffix emission.emission.pending_eq
    apply hroute.trans
    rw [← hworklist]
    exact state.emitted_perm.append_right _

/-- Open one fresh Cartesian batch and immediately route its selected first slot. -/
noncomputable def batchRoute
    {M N K : ℕ}
    (state : MRStatea M N K)
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : MIBlock leftTerms)
    (right : MIBlock rightTerms)
    (emission :
      MBEmissi
        (MWItem.initial left right)) :
    MRStatea M N K :=
  (state.openBatch left right).route state.worklist []
    (MWItem.initial left right)
    (by simp [openBatch]) emission

/-- A closed routing state supplies a finite schedule for its operational prefix. -/
noncomputable def closedSchedule
    {M N K : ℕ}
    (state : MRStatea M N K)
    (hclosed : state.worklist.Closed) :
    MBSched state.routedTerms :=
  (state.worklist.closedSchedule hclosed).permTerms state.emitted_perm

end MRStatea

/--
A closed routing state for the complete emitted-correction list resolves one
operational finite batch schedule.
-/
noncomputable def batchRoutingState
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (state : MRStatea M N
      (inverseLabelledCollection M N).factors.length)
    (hclosed : state.worklist.Closed)
    (hrouted : state.routedTerms = endpoint.corrections) :
    OBSched endpoint :=
  OBSched.multiplicityBatchSchedule
    endpoint
    ((state.closedSchedule hclosed).permTerms (by rw [hrouted]))

/--
A closed routing state for the complete emitted-correction list also retains
the stronger heterogeneous-worklist schedule.
-/
noncomputable def worklistRoutingState
    {M N : ℕ}
    (endpoint : ODEmissi M N)
    (state : MRStatea M N
      (inverseLabelledCollection M N).factors.length)
    (hclosed : state.worklist.Closed)
    (hrouted : state.routedTerms = endpoint.corrections) :
    OWSched endpoint where
  worklist := state.worklist
  closed := hclosed
  corrections_perm := state.emitted_perm.trans (by rw [hrouted])

/--
Concrete sequential scheduler kernel: route each complete operational
correction trace through finitely many open Cartesian batches and exhaust all
of them.
-/
structure ORKern : Prop where
  route :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N),
      ∃ state : MRStatea M N
          (inverseLabelledCollection M N).factors.length,
        state.worklist.Closed ∧
          state.routedTerms = endpoint.corrections

namespace ORKern

/-- Sequential routing resolves the heterogeneous-worklist scheduler kernel. -/
noncomputable def operationalMultiplicityWorklist
    (kernel : ORKern) :
    OMWork where
  schedule endpoint := by
    rcases kernel.route endpoint with ⟨state, hclosed, hrouted⟩
    exact ⟨worklistRoutingState
      endpoint state hclosed hrouted⟩

end ORKern

/-- No-left-label operational traces have the empty closed routing state. -/
lemma routing_state_left
    (N : ℕ)
    (endpoint : ODEmissi 0 N) :
    ∃ state : MRStatea 0 N
        (inverseLabelledCollection 0 N).factors.length,
      state.worklist.Closed ∧
        state.routedTerms = endpoint.corrections := by
  have hcorrections :
      endpoint.corrections = [] :=
    FCollec.ECorrec.nil_source endpoint.emits
      (inverse_decorated_terms N)
  refine ⟨MRStatea.nil 0 N
    (inverseLabelledCollection 0 N).factors.length, ?_, ?_⟩
  · simp [MRStatea.nil, MBWork.Closed]
  · exact hcorrections.symm

/-- No-right-label operational traces have the empty closed routing state. -/
lemma closed_routing_right
    (M : ℕ)
    (endpoint : ODEmissi M 0) :
    ∃ state : MRStatea M 0
        (inverseLabelledCollection M 0).factors.length,
      state.worklist.Closed ∧
        state.routedTerms = endpoint.corrections := by
  have hcorrections :
      endpoint.corrections = [] :=
    FCollec.ECorrec.nil_source endpoint.emits
      (inverse_raw_decorated M)
  refine ⟨MRStatea.nil M 0
    (inverseLabelledCollection M 0).factors.length, ?_, ?_⟩
  · simp [MRStatea.nil, MBWork.Closed]
  · exact hcorrections.symm

/-- The first positive-positive operational trace has the empty routing state. -/
lemma closed_routing_one
    (endpoint : ODEmissi 1 1) :
    ∃ state : MRStatea 1 1
        (inverseLabelledCollection 1 1).factors.length,
      state.worklist.Closed ∧
        state.routedTerms = endpoint.corrections := by
  have hcorrections :
      endpoint.corrections = [] :=
    FCollec.ECorrec.nil_source_length
      endpoint.emits (by
        rw [inverse_decorated_length])
  refine ⟨MRStatea.nil 1 1
    (inverseLabelledCollection 1 1).factors.length, ?_, ?_⟩
  · simp [MRStatea.nil, MBWork.Closed]
  · exact hcorrections.symm

/--
Only the positive-positive routing constructor remains after the two empty
inverse-raw cases.
-/
structure PMRoute : Prop where
  route :
    ∀ (M N : ℕ),
      0 < M →
        0 < N →
          ∀ endpoint : ODEmissi M N,
            ∃ state : MRStatea M N
                (inverseLabelledCollection M N).factors.length,
              state.worklist.Closed ∧
                state.routedTerms = endpoint.corrections

namespace PMRoute

/-- Zero cases plus positive-positive routing resolve every operational trace. -/
def operationalMultiplicityRouting
    (kernel : PMRoute) :
    ORKern where
  route {M N} endpoint := by
    by_cases hM : M = 0
    · subst M
      exact routing_state_left N endpoint
    by_cases hN : N = 0
    · subst N
      exact closed_routing_right M endpoint
    exact kernel.route M N (Nat.pos_of_ne_zero hM) (Nat.pos_of_ne_zero hN)
      endpoint

end PMRoute

/--
After the empty cases and the first positive-positive case, only nontrivial
positive inputs still require operational routing.
-/
structure NPRoute :
    Prop where
  route :
    ∀ (M N : ℕ),
      0 < M →
        0 < N →
          (M ≠ 1 ∨ N ≠ 1) →
            ∀ endpoint : ODEmissi M N,
              ∃ state : MRStatea M N
                  (inverseLabelledCollection M N).factors.length,
                state.worklist.Closed ∧
                  state.routedTerms = endpoint.corrections

namespace NPRoute

/-- The explicit `1 × 1` base case resolves the full positive-input kernel. -/
def positiveMultiplicityRouting
    (kernel :
      NPRoute) :
    PMRoute where
  route M N hM hN endpoint := by
    by_cases hMone : M = 1
    · by_cases hNone : N = 1
      · subst M
        subst N
        exact closed_routing_one endpoint
      · exact kernel.route M N hM hN (Or.inr hNone) endpoint
    · exact kernel.route M N hM hN (Or.inl hMone) endpoint

/-- Empty and `1 × 1` base cases reduce all routing to nontrivial positives. -/
def operationalMultiplicityRouting
    (kernel :
      NPRoute) :
    ORKern :=
  kernel.positiveMultiplicityRouting
    |>.operationalMultiplicityRouting

end NPRoute

end MTRoute
end TCTex
end Submission

-- Merged from FamilyOperationalMultiplicityShapeCompression.lean

/-!
# Shape compression of operational multiplicity inventories

A routed heterogeneous worklist supplies one exact global inventory for every
factor in a terminating More3 endpoint.  Polynomial compression consumes
inventories block by block.  This file isolates the remaining order statement:
each maximal adjacent same-shape block is the complete fiber of its erased
Hall shape.

Once that shape-fiber law is available, filtering the global inventory gives
the required multiplicity inventory for every block and therefore the
canonical finite `BFam.Expansion`.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace MSCompre

open HACoeff
open FIFilter.MIBlock
open IMPropag
open HOCollec
open OEAccoun
open MBScheda
open FMEnd
open MTRoute
open MWSched

/-- Every operational endpoint carries one exact global multiplicity inventory. -/
structure OFMultip : Prop where
  inventory :
    ∀ {M N : ℕ}
      (collected : ODTerms M N),
      Nonempty (MIBlock collected.factors)

/--
Every canonical maximal same-shape output block is the complete fiber of one
erased Hall shape in the operational endpoint.
-/
structure OperationalShapeFiber : Prop where
  filter_eq :
    ∀ {M N : ℕ}
      (collected : ODTerms M N)
      (block : List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)),
      block ∈ sameErasedBlocks collected.factors →
        ∃ shape : CWord HPAtom,
          collected.factors.filter
            (fun T => T.family.recipe.erasedShape = shape) = block

namespace OFMultip

/--
Filter a global factors inventory along a complete shape fiber to resolve the
block-local multiplicity kernel consumed by polynomial compression.
-/
noncomputable def shapeMultiplicityInventory
    (inventoryKernel : OFMultip)
    (shapeKernel : OperationalShapeFiber) :
    SMInv where
  inventory collected block hblock := by
    let full := Classical.choice (inventoryKernel.inventory collected)
    rcases shapeKernel.filter_eq collected block hblock with
      ⟨shape, hshape⟩
    rw [← hshape]
    exact ⟨filterShape full shape⟩

/-- Resolve the canonical finite family expansion from the two separated laws. -/
noncomputable def expansion
    (inventoryKernel : OFMultip)
    (shapeKernel : OperationalShapeFiber)
    (M N : ℕ) :
    BFam.Expansion M N :=
  (inventoryKernel.shapeMultiplicityInventory shapeKernel).expansion
    M N

end OFMultip

/--
An inventory for every emitted-correction list extends the exact raw inventory
to a global factors-inventory kernel.
-/
noncomputable def operationalMultiplicityCorrections
    (kernel : OMClos) :
    OFMultip where
  inventory collected := by
    rcases FCollec.exists_emitsCorrections collected.family_collects with
      ⟨corrections, hemits⟩
    let endpoint : ODEmissi _ _ := {
      collected := collected
      corrections := corrections
      emits := hemits }
    exact ⟨kernel.factorsInventory endpoint⟩

/--
Closed heterogeneous worklist scheduling and shape-fiber completeness resolve
the block-local multiplicity kernel.
-/
noncomputable def multiplicityInventoryWorklists
    (worklistKernel : OMWork)
    (shapeKernel : OperationalShapeFiber) :
    SMInv :=
  let batchKernel :=
    worklistKernel.operationalMultiplicityBatch
  let correctionsKernel :=
    batchKernel.operat_multi_closu
  (operationalMultiplicityCorrections correctionsKernel)
    |>.shapeMultiplicityInventory shapeKernel

/--
Closed heterogeneous worklist scheduling and shape-fiber completeness resolve
the canonical finite family expansion.
-/
noncomputable def expansionOfWorklists
    (worklistKernel : OMWork)
    (shapeKernel : OperationalShapeFiber)
    (M N : ℕ) :
    BFam.Expansion M N :=
  (multiplicityInventoryWorklists
    worklistKernel shapeKernel).expansion M N

/--
Sequential correction routing and shape-fiber completeness resolve the
canonical finite family expansion.
-/
noncomputable def expansionTraceRouting
    (routingKernel : ORKern)
    (shapeKernel : OperationalShapeFiber)
    (M N : ℕ) :
    BFam.Expansion M N :=
  expansionOfWorklists
    routingKernel.operationalMultiplicityWorklist
      shapeKernel M N

end MSCompre
end TCTex
end Submission

-- Merged from FamilyOperationalMultiplicityTraceRoutingMeasure.lean

/-!
# Strict measure descent for routed operational corrections

Sequential trace routing is not merely bookkeeping.  Every routed More3
correction consumes one selected pending Cartesian slot in the heterogeneous
worklist.  This file records the corresponding worklist step and its strict
pending-slot descent.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace MTRoute

open HACoeff
open IMWork

namespace MRStatea

/-- Routed terms and emitted worklist terms always have the same length. -/
lemma worklist_emitted_routed
    {M N K : ℕ}
    (state : MRStatea M N K) :
    (multiplicityWorklistEmitted state.worklist).length =
      state.routedTerms.length :=
  state.emitted_perm.length_eq

/-- Routing one selected correction is an actual heterogeneous-worklist step. -/
lemma worklist_step_route
    {M N K : ℕ}
    (state : MRStatea M N K)
    (pre post : MBWork M N K)
    (item : MWItem M N K)
    (hworklist : state.worklist = pre ++ item :: post)
    (emission : MBEmissi item) :
    MBWork.Step state.worklist
      (state.route pre post item hworklist emission).worklist := by
  rw [hworklist]
  exact MBWork.stepConcreteEmission pre post item emission

/-- Routing one selected correction strictly decreases the open-slot count. -/
lemma pending_slots_route
    {M N K : ℕ}
    (state : MRStatea M N K)
    (pre post : MBWork M N K)
    (item : MWItem M N K)
    (hworklist : state.worklist = pre ++ item :: post)
    (emission : MBEmissi item) :
    (state.route pre post item hworklist emission).worklist.pendingSlots <
      state.worklist.pendingSlots :=
  MBWork.pending_slots_step
    (state.worklist_step_route pre post item hworklist emission)

/-- Routing one selected correction appends exactly one operational term. -/
lemma routed_length_route
    {M N K : ℕ}
    (state : MRStatea M N K)
    (pre post : MBWork M N K)
    (item : MWItem M N K)
    (hworklist : state.worklist = pre ++ item :: post)
    (emission : MBEmissi item) :
    (state.route pre post item hworklist emission).routedTerms.length =
      state.routedTerms.length + 1 := by
  simp [route]

end MRStatea

end MTRoute
end TCTex
end Submission

-- Merged from FamilyOperationalTruncatedMultiplicity.lean

/-!
# Truncated multiplicity-preserving correction ledgers

For a nilpotent cutoff `n`, operational scheduling does not need to exhaust
Cartesian correction slots whose weighted Hall degree has already reached
`n`: those terms vanish semantically in the matching truncation.

This file filters one Cartesian multiplicity grid at the source.  The open
ledger consumes only below-cutoff concrete slots, retains arbitrary
operational emission order by permutation, and closes to the corresponding
filtered exact multiplicity inventory.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace OTWork

open HACoeff
open BBSched
open BRSpec
open ICFilter.MIBlock
open IMPropag
open OCPartit
open HSInvent
open HSPacket

/-- Below-cutoff concrete slots of one Cartesian decorated-family grid. -/
noncomputable def truncatedDecoratedGrid
    {M N K : ℕ}
    (n leftWeight rightWeight : ℕ)
    (leftTerms rightTerms : List (DFTerm M N K)) :
    List (DFTerm M N K) :=
  belowCutoffTerms n leftWeight rightWeight
    (DFTerm.correctionGrid leftTerms rightTerms)

/--
Permutation-aware Cartesian correction ledger retaining only slots below one
nilpotent cutoff.
-/
structure TMLedger
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (n leftWeight rightWeight : ℕ)
    (left : MIBlock leftTerms)
    (right : MIBlock rightTerms) where
  emitted :
    List (DFTerm M N K)
  pending :
    List (DFTerm M N K)
  accounting :
    List.Perm (emitted ++ pending)
      (truncatedDecoratedGrid
        n leftWeight rightWeight leftTerms rightTerms)

namespace TMLedger

/-- Open one truncated Cartesian ledger with every retained slot pending. -/
noncomputable def initial
    {M N K : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (n leftWeight rightWeight : ℕ)
    (left : MIBlock leftTerms)
    (right : MIBlock rightTerms) :
    TMLedger
      n leftWeight rightWeight left right where
  emitted := []
  pending :=
    truncatedDecoratedGrid
      n leftWeight rightWeight leftTerms rightTerms
  accounting := by simp

/-- Consume any selected retained correction slot. -/
def emit
    {M N K n leftWeight rightWeight : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger :
      TMLedger
        n leftWeight rightWeight left right)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : ledger.pending = before ++ term :: after) :
    TMLedger
      n leftWeight rightWeight left right where
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

/-- Emitting one retained slot removes exactly one pending position. -/
lemma pending_length_emit
    {M N K n leftWeight rightWeight : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger :
      TMLedger
        n leftWeight rightWeight left right)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : ledger.pending = before ++ term :: after) :
    (ledger.emit before term after hpending).pending.length + 1 =
      ledger.pending.length := by
  simp [emit, hpending]
  omega

/-- Every pending truncated slot has weighted Hall degree below the cutoff. -/
lemma weight_pending
    {M N K n leftWeight rightWeight : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger :
      TMLedger
        n leftWeight rightWeight left right)
    {term : DFTerm M N K}
    (hterm : term ∈ ledger.pending) :
    decoratedFamilyWeight leftWeight rightWeight term < n := by
  have hcanonical :
      term ∈ truncatedDecoratedGrid
        n leftWeight rightWeight leftTerms rightTerms :=
    ledger.accounting.subset (List.mem_append_right ledger.emitted hterm)
  exact (below_cutoff_terms.mp hcanonical).2

/-- Every retained pending term comes from one concrete Cartesian parent pair. -/
lemma parent_terms_pending
    {M N K n leftWeight rightWeight : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger :
      TMLedger
        n leftWeight rightWeight left right)
    {term : DFTerm M N K}
    (hterm : term ∈ ledger.pending) :
    ∃ leftTerm ∈ leftTerms, ∃ rightTerm ∈ rightTerms,
      term = leftTerm.correction rightTerm := by
  have hcanonical :
      term ∈ truncatedDecoratedGrid
        n leftWeight rightWeight leftTerms rightTerms :=
    ledger.accounting.subset (List.mem_append_right ledger.emitted hterm)
  have hgrid :
      term ∈ DFTerm.correctionGrid leftTerms rightTerms :=
    (below_cutoff_terms.mp hcanonical).1
  rcases List.mem_flatMap.mp hgrid with ⟨leftTerm, hleft, hterm⟩
  rcases List.mem_map.mp hterm with ⟨rightTerm, hright, rfl⟩
  exact ⟨leftTerm, hleft, rightTerm, hright, rfl⟩

/-- Every retained pending family belongs to the represented correction grid. -/
lemma family_grid_pending
    {M N K n leftWeight rightWeight : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger :
      TMLedger
        n leftWeight rightWeight left right)
    {term : DFTerm M N K}
    (hterm : term ∈ ledger.pending) :
    term.family ∈
      BFam.correctionGrid left.families right.families := by
  rcases ledger.parent_terms_pending hterm with
    ⟨leftTerm, hleft, rightTerm, hright, rfl⟩
  exact BFam.mem_correctionGrid.mpr
    ⟨leftTerm.family, left.family_mem hleft,
      rightTerm.family, right.family_mem hright, rfl⟩

/-- Every retained pending term lies strictly above one left-parent family. -/
lemma left_family_pending
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger :
      TMLedger
        n leftWeight rightWeight left right)
    {term : DFTerm M N K}
    (hterm : term ∈ ledger.pending) :
    ∃ family ∈ left.families,
      weightedWordWeight leftWeight rightWeight family.recipe <
        weightedWordWeight leftWeight rightWeight term.family.recipe :=
  BFam.weight_weigh_memca
    hleftWeight hrightWeight
      (ledger.family_grid_pending hterm)

/-- Every retained pending term lies strictly above one right-parent family. -/
lemma right_family_pending
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger :
      TMLedger
        n leftWeight rightWeight left right)
    {term : DFTerm M N K}
    (hterm : term ∈ ledger.pending) :
    ∃ family ∈ right.families,
      weightedWordWeight leftWeight rightWeight family.recipe <
        weightedWordWeight leftWeight rightWeight term.family.recipe :=
  BFam.weight_weigh_memcb
    hleftWeight hrightWeight
      (ledger.family_grid_pending hterm)

/--
Every retained pending term lies in the strict recursive interval above one
left-parent family and below the cutoff.
-/
lemma left_family_cutoff
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger :
      TMLedger
        n leftWeight rightWeight left right)
    {term : DFTerm M N K}
    (hterm : term ∈ ledger.pending) :
    ∃ family ∈ left.families,
      weightedWordWeight leftWeight rightWeight family.recipe <
          decoratedFamilyWeight leftWeight rightWeight term ∧
        decoratedFamilyWeight leftWeight rightWeight term < n := by
  rcases ledger.left_family_pending
      hleftWeight hrightWeight hterm with
    ⟨family, hfamily, hlt⟩
  exact ⟨family, hfamily, hlt, ledger.weight_pending hterm⟩

/--
Every retained pending term lies in the strict recursive interval above one
right-parent family and below the cutoff.
-/
lemma right_family_cutoff
    {M N K n leftWeight rightWeight : ℕ}
    (hleftWeight : 0 < leftWeight)
    (hrightWeight : 0 < rightWeight)
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger :
      TMLedger
        n leftWeight rightWeight left right)
    {term : DFTerm M N K}
    (hterm : term ∈ ledger.pending) :
    ∃ family ∈ right.families,
      weightedWordWeight leftWeight rightWeight family.recipe <
          decoratedFamilyWeight leftWeight rightWeight term ∧
        decoratedFamilyWeight leftWeight rightWeight term < n := by
  rcases ledger.right_family_pending
      hleftWeight hrightWeight hterm with
    ⟨family, hfamily, hlt⟩
  exact ⟨family, hfamily, hlt, ledger.weight_pending hterm⟩

/--
Closing a truncated ledger yields the exact multiplicity inventory obtained by
filtering its full Cartesian correction grid by weighted Hall degree.
-/
noncomputable def closedInventoryBlock
    {M N K n leftWeight rightWeight : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger :
      TMLedger
        n leftWeight rightWeight left right)
    (hpending : ledger.pending = []) :
    MIBlock ledger.emitted := by
  apply
    (filterBelowCutoff (left.correctionGrid right)
      n leftWeight rightWeight).permTerms
  simpa [hpending, truncatedDecoratedGrid] using
    ledger.accounting.symm

/-- One exact retained-slot consumption transition. -/
inductive Step
    {M N K n leftWeight rightWeight : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms} :
    TMLedger
        n leftWeight rightWeight left right →
      TMLedger
          n leftWeight rightWeight left right →
        Prop where
  | emit
      (ledger :
        TMLedger
          n leftWeight rightWeight left right)
      (before : List (DFTerm M N K))
      (term : DFTerm M N K)
      (after : List (DFTerm M N K))
      (hpending : ledger.pending = before ++ term :: after) :
      Step ledger (ledger.emit before term after hpending)

/-- Finite arithmetic drain for one truncated Cartesian ledger. -/
abbrev Rewrites
    {M N K n leftWeight rightWeight : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger final :
      TMLedger
        n leftWeight rightWeight left right) :
    Prop :=
  Relation.ReflTransGen Step ledger final

/-- Every finite truncated ledger can be drained arithmetically. -/
lemma rewrites_pending_nil
    {M N K n leftWeight rightWeight : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    {left : MIBlock leftTerms}
    {right : MIBlock rightTerms}
    (ledger :
      TMLedger
        n leftWeight rightWeight left right) :
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

end TMLedger

end OTWork
end TCTex
end Submission

/-!
# Heterogeneous truncated multiplicity-batch worklists

Nilpotent collection interleaves retained below-cutoff correction slots from
different Cartesian parent grids.  This file packages those truncated ledgers
into one finite heterogeneous worklist.

Every arithmetic step consumes one retained slot and strictly decreases the
total pending count.  Once every truncated batch closes, their emitted lists
assemble into one exact multiplicity-preserving inventory.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace TMWork

open HACoeff
open IMPropag
open OCPartit
open OTWork
open HSPacket

/-- One heterogeneous open Cartesian batch filtered below a fixed cutoff. -/
structure TWItem
    (M N K n leftWeight rightWeight : ℕ) where
  leftTerms :
    List (DFTerm M N K)
  rightTerms :
    List (DFTerm M N K)
  left :
    MIBlock leftTerms
  right :
    MIBlock rightTerms
  ledger :
    TMLedger
      n leftWeight rightWeight left right

namespace TWItem

/-- Open one heterogeneous truncated batch with every retained slot pending. -/
noncomputable def initial
    {M N K n leftWeight rightWeight : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : MIBlock leftTerms)
    (right : MIBlock rightTerms) :
    TWItem
      M N K n leftWeight rightWeight where
  leftTerms := leftTerms
  rightTerms := rightTerms
  left := left
  right := right
  ledger :=
    TMLedger.initial
      n leftWeight rightWeight left right

/-- Consume one selected retained slot in one heterogeneous truncated batch. -/
def emit
    {M N K n leftWeight rightWeight : ℕ}
    (item :
      TWItem M N K n leftWeight rightWeight)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : item.ledger.pending = before ++ term :: after) :
    TWItem M N K n leftWeight rightWeight where
  leftTerms := item.leftTerms
  rightTerms := item.rightTerms
  left := item.left
  right := item.right
  ledger := item.ledger.emit before term after hpending

/-- One truncated batch closes when no retained slots remain pending. -/
def Closed
    {M N K n leftWeight rightWeight : ℕ}
    (item :
      TWItem M N K n leftWeight rightWeight) :
    Prop :=
  item.ledger.pending = []

/-- A closed truncated batch supplies an exact retained multiplicity inventory. -/
noncomputable def closedInventoryBlock
    {M N K n leftWeight rightWeight : ℕ}
    (item :
      TWItem M N K n leftWeight rightWeight)
    (hclosed : item.Closed) :
    MIBlock item.ledger.emitted :=
  item.ledger.closedInventoryBlock hclosed

/-- Number of retained slots still pending in one truncated batch. -/
def pendingSlots
    {M N K n leftWeight rightWeight : ℕ}
    (item :
      TWItem M N K n leftWeight rightWeight) :
    ℕ :=
  item.ledger.pending.length

/-- Consuming one retained slot removes exactly one pending position. -/
lemma pendingSlots_emit
    {M N K n leftWeight rightWeight : ℕ}
    (item :
      TWItem M N K n leftWeight rightWeight)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : item.ledger.pending = before ++ term :: after) :
    (item.emit before term after hpending).pendingSlots + 1 =
      item.pendingSlots :=
  item.ledger.pending_length_emit before term after hpending

end TWItem

/-- One concrete More3 obstruction routed to one truncated open batch. -/
structure CBEmissia
    {M N K n leftWeight rightWeight : ℕ}
    (item :
      TWItem M N K n leftWeight rightWeight) where
  leftTerm :
    DFTerm M N K
  rightTerm :
    DFTerm M N K
  left_mem :
    leftTerm ∈ item.leftTerms
  right_mem :
    rightTerm ∈ item.rightTerms
  pendingPrefix :
    List (DFTerm M N K)
  pendingSuffix :
    List (DFTerm M N K)
  pending_eq :
    item.ledger.pending =
      pendingPrefix ++ leftTerm.correction rightTerm :: pendingSuffix

namespace CBEmissia

/--
A below-cutoff correction of represented parent terms belongs to the freshly
opened filtered Cartesian batch.
-/
lemma correction_initial_pending
    {M N K n leftWeight rightWeight : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : MIBlock leftTerms)
    (right : MIBlock rightTerms)
    (leftTerm : DFTerm M N K)
    (rightTerm : DFTerm M N K)
    (hleft : leftTerm ∈ leftTerms)
    (hright : rightTerm ∈ rightTerms)
    (hweight :
      OCPartit.decoratedFamilyWeight
          leftWeight rightWeight (leftTerm.correction rightTerm) < n) :
    leftTerm.correction rightTerm ∈
      (TWItem.initial
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        left right).ledger.pending := by
  change leftTerm.correction rightTerm ∈
    belowCutoffTerms n leftWeight rightWeight
      (DFTerm.correctionGrid leftTerms rightTerms)
  apply below_cutoff_terms.mpr
  refine ⟨?_, hweight⟩
  apply List.mem_flatMap.mpr
  refine ⟨leftTerm, hleft, ?_⟩
  exact List.mem_map.mpr ⟨rightTerm, hright, rfl⟩

/-- Route a selected retained Cartesian parent pair to its pending slot. -/
noncomputable def ofMemPending
    {M N K n leftWeight rightWeight : ℕ}
    (item :
      TWItem M N K n leftWeight rightWeight)
    (leftTerm : DFTerm M N K)
    (rightTerm : DFTerm M N K)
    (hleft : leftTerm ∈ item.leftTerms)
    (hright : rightTerm ∈ item.rightTerms)
    (hpending :
      leftTerm.correction rightTerm ∈ item.ledger.pending) :
    CBEmissia item := by
  let hdecomposition := List.mem_iff_append.mp hpending
  let before := hdecomposition.choose
  let after := hdecomposition.choose_spec.choose
  have hpending_eq :
      item.ledger.pending =
        before ++ leftTerm.correction rightTerm :: after :=
    hdecomposition.choose_spec.choose_spec
  exact {
    leftTerm := leftTerm
    rightTerm := rightTerm
    left_mem := hleft
    right_mem := hright
    pendingPrefix := before
    pendingSuffix := after
    pending_eq := hpending_eq }

/-- Route one represented below-cutoff correction in a freshly opened batch. -/
noncomputable def ofInitialCorrection
    {M N K n leftWeight rightWeight : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : MIBlock leftTerms)
    (right : MIBlock rightTerms)
    (leftTerm : DFTerm M N K)
    (rightTerm : DFTerm M N K)
    (hleft : leftTerm ∈ leftTerms)
    (hright : rightTerm ∈ rightTerms)
    (hweight :
      OCPartit.decoratedFamilyWeight
          leftWeight rightWeight (leftTerm.correction rightTerm) < n) :
    CBEmissia
      (TWItem.initial
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        left right) :=
  ofMemPending _ leftTerm rightTerm hleft hright
    (correction_initial_pending
      left right leftTerm rightTerm hleft hright hweight)

/-- Every pending retained slot admits one concrete routed parent pair. -/
lemma exists_of_pending
    {M N K n leftWeight rightWeight : ℕ}
    (item :
      TWItem M N K n leftWeight rightWeight)
    {term : DFTerm M N K}
    (hpending : term ∈ item.ledger.pending) :
    ∃ emission : CBEmissia item,
      term = emission.leftTerm.correction emission.rightTerm := by
  rcases item.ledger.parent_terms_pending hpending with
    ⟨leftTerm, hleft, rightTerm, hright, rfl⟩
  exact ⟨ofMemPending item leftTerm rightTerm hleft hright hpending, rfl⟩

/-- Consume the routed retained More3 correction slot. -/
noncomputable def emitItem
    {M N K n leftWeight rightWeight : ℕ}
    {item :
      TWItem M N K n leftWeight rightWeight}
    (emission : CBEmissia item) :
    TWItem M N K n leftWeight rightWeight :=
  item.emit emission.pendingPrefix
    (emission.leftTerm.correction emission.rightTerm)
    emission.pendingSuffix emission.pending_eq

/-- The retained More3 obstruction is one explicit adjacent labelled-word step. -/
def labelledWordStep
    {M N K n leftWeight rightWeight : ℕ}
    {item :
      TWItem M N K n leftWeight rightWeight}
    (emission : CBEmissia item)
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

end CBEmissia

/-- A finite list of heterogeneous truncated correction batches. -/
abbrev TBWork
    (M N K n leftWeight rightWeight : ℕ) :=
  List (TWItem
    M N K n leftWeight rightWeight)

namespace TBWork

/-- Total number of retained pending slots in a truncated worklist. -/
def pendingSlots
    {M N K n leftWeight rightWeight : ℕ}
    (worklist :
      TBWork M N K n leftWeight rightWeight) :
    ℕ :=
  (worklist.map TWItem.pendingSlots).sum

/-- Every truncated Cartesian batch in a worklist has been exhausted. -/
def Closed
    {M N K n leftWeight rightWeight : ℕ}
    (worklist :
      TBWork M N K n leftWeight rightWeight) :
    Prop :=
  ∀ item ∈ worklist, item.Closed

/-- Consume one retained slot inside one heterogeneous truncated worklist item. -/
inductive Step
    {M N K n leftWeight rightWeight : ℕ} :
    TBWork M N K n leftWeight rightWeight →
      TBWork M N K n leftWeight rightWeight →
        Prop where
  | emit
      (pre post :
        TBWork M N K n leftWeight rightWeight)
      (item :
        TWItem M N K n leftWeight rightWeight)
      (before : List (DFTerm M N K))
      (term : DFTerm M N K)
      (after : List (DFTerm M N K))
      (hpending : item.ledger.pending = before ++ term :: after) :
      Step
        (pre ++ item :: post)
        (pre ++ item.emit before term after hpending :: post)

/-- Finite retained-slot emission run for one truncated worklist. -/
abbrev Rewrites
    {M N K n leftWeight rightWeight : ℕ}
    (worklist final :
      TBWork M N K n leftWeight rightWeight) :
    Prop :=
  Relation.ReflTransGen Step worklist final

/-- Every truncated worklist step strictly decreases retained pending slots. -/
lemma pending_slots_step
    {M N K n leftWeight rightWeight : ℕ}
    {before after :
      TBWork M N K n leftWeight rightWeight}
    (hstep : Step before after) :
    pendingSlots after < pendingSlots before := by
  cases hstep with
  | emit pre post item before term after hpending =>
      simp only [pendingSlots, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons]
      have hlength := item.pendingSlots_emit before term after hpending
      omega

/-- Every nonclosed truncated worklist admits one retained-slot emission. -/
lemma step_not_closed
    {M N K n leftWeight rightWeight : ℕ}
    (worklist :
      TBWork M N K n leftWeight rightWeight)
    (hclosed : ¬ worklist.Closed) :
    ∃ next, Step worklist next := by
  simp only [Closed, not_forall] at hclosed
  rcases hclosed with ⟨item, hitem⟩
  rcases hitem with ⟨hitem, hopen⟩
  rcases List.mem_iff_append.mp hitem with ⟨pre, post, hworklist⟩
  simp only [TWItem.Closed] at hopen
  cases hpending : item.ledger.pending with
  | nil =>
      exact False.elim (hopen hpending)
  | cons term after =>
      refine ⟨pre ++ item.emit [] term after hpending :: post, ?_⟩
      rw [hworklist]
      exact Step.emit pre post item [] term after hpending

/-- Every finite heterogeneous truncated worklist can be drained. -/
lemma exists_rewrites_closed
    {M N K n leftWeight rightWeight : ℕ}
    (worklist :
      TBWork M N K n leftWeight rightWeight) :
    ∃ final, Rewrites worklist final ∧ final.Closed := by
  by_cases hclosed : worklist.Closed
  · exact ⟨worklist, Relation.ReflTransGen.refl, hclosed⟩
  · rcases step_not_closed worklist hclosed with ⟨next, hstep⟩
    rcases exists_rewrites_closed next with ⟨final, hrewrites, hclosed⟩
    exact ⟨final, hrewrites.head hstep, hclosed⟩
termination_by worklist.pendingSlots
decreasing_by
  exact pending_slots_step hstep

/-- A routed concrete retained obstruction consumes one worklist slot. -/
def stepConcreteEmission
    {M N K n leftWeight rightWeight : ℕ}
    (pre post :
      TBWork M N K n leftWeight rightWeight)
    (item :
      TWItem M N K n leftWeight rightWeight)
    (emission : CBEmissia item) :
    Step
      (pre ++ item :: post)
      (pre ++ emission.emitItem :: post) :=
  Step.emit pre post item emission.pendingPrefix
    (emission.leftTerm.correction emission.rightTerm)
    emission.pendingSuffix emission.pending_eq

/-- Closed truncated worklists assemble into one exact retained inventory. -/
noncomputable def closedInventoryBlock
    {M N K n leftWeight rightWeight : ℕ}
    (worklist :
      TBWork M N K n leftWeight rightWeight)
    (hclosed : worklist.Closed) :
    MIBlock
      (worklist.flatMap fun item => item.ledger.emitted) := by
  induction worklist with
  | nil =>
      exact MIBlock.nil
  | cons item worklist ih =>
      exact (item.closedInventoryBlock (hclosed item (by simp))).append
        (ih (by
          intro next hnext
          exact hclosed next (by simp [hnext])))

end TBWork

end TMWork
end TCTex
end Submission

/-!
# Finite batch plans for retained below-cutoff corrections

The local truncated ledger proves that one represented pair of parent
inventories contributes exactly its below-cutoff Cartesian correction grid.
The remaining global Hall-Petresco theorem is a coverage statement: the
retained operational correction trace must be a permutation of finitely many
such filtered grids.

This file packages that boundary without assuming any artificial injectivity
of correction families.  A finite batch plan composes directly to an exact
multiplicity-preserving inventory for its target terms.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace TMPlanni

open HACoeff
open ICFilter.MIBlock
open IMPropag
open OCPartit
open FMEnd
open MTRoute
open TMWork
open OTWork

/-- One represented parent-inventory pair contributing a filtered grid. -/
structure TBSpec
    (M N K n leftWeight rightWeight : ℕ) where
  leftTerms :
    List (DFTerm M N K)
  rightTerms :
    List (DFTerm M N K)
  left :
    MIBlock leftTerms
  right :
    MIBlock rightTerms

namespace TBSpec

/-- Retained concrete correction slots contributed by one parent pair. -/
noncomputable def terms
    {M N K n leftWeight rightWeight : ℕ}
    (spec :
      TBSpec M N K n leftWeight rightWeight) :
    List (DFTerm M N K) :=
  truncatedDecoratedGrid
    n leftWeight rightWeight spec.leftTerms spec.rightTerms

/-- One batch specification carries the exact inventory of its retained grid. -/
noncomputable def inventory
    {M N K n leftWeight rightWeight : ℕ}
    (spec :
      TBSpec M N K n leftWeight rightWeight) :
    MIBlock spec.terms :=
  filterBelowCutoff (spec.left.correctionGrid spec.right)
    n leftWeight rightWeight

/-- Open the arithmetic truncated-ledger item associated to one batch spec. -/
noncomputable def initialItem
    {M N K n leftWeight rightWeight : ℕ}
    (spec :
      TBSpec M N K n leftWeight rightWeight) :
    TWItem
      M N K n leftWeight rightWeight :=
  TWItem.initial spec.left spec.right

@[simp]
lemma initialItem_pending
    {M N K n leftWeight rightWeight : ℕ}
    (spec :
      TBSpec M N K n leftWeight rightWeight) :
    spec.initialItem.ledger.pending = spec.terms :=
  rfl

@[simp]
lemma initialItem_emitted
    {M N K n leftWeight rightWeight : ℕ}
    (spec :
      TBSpec M N K n leftWeight rightWeight) :
    spec.initialItem.ledger.emitted = [] :=
  rfl

end TBSpec

/-- Concatenate retained concrete terms contributed by finitely many batches. -/
noncomputable def batchSpecTerms
    {M N K n leftWeight rightWeight : ℕ}
    (specs :
      List (TBSpec
        M N K n leftWeight rightWeight)) :
    List (DFTerm M N K) :=
  specs.flatMap TBSpec.terms

/-- Open the finite truncated worklist associated to a finite batch plan. -/
noncomputable def initialBatchWorklist
    {M N K n leftWeight rightWeight : ℕ}
    (specs :
      List (TBSpec
        M N K n leftWeight rightWeight)) :
    TBWork M N K n leftWeight rightWeight :=
  specs.map TBSpec.initialItem

@[simp]
lemma batch_worklist_emitted
    {M N K n leftWeight rightWeight : ℕ}
    (specs :
      List (TBSpec
        M N K n leftWeight rightWeight)) :
    (initialBatchWorklist specs).flatMap
        (fun item => item.ledger.emitted) = [] := by
  simp [initialBatchWorklist]

/-- Inventories of finitely many filtered Cartesian grids compose by append. -/
noncomputable def batchSpecsInventory
    {M N K n leftWeight rightWeight : ℕ} :
    ∀ specs :
      List (TBSpec
        M N K n leftWeight rightWeight),
      MIBlock (batchSpecTerms specs)
  | [] =>
      MIBlock.nil
  | spec :: specs =>
      spec.inventory.append (batchSpecsInventory specs)

/--
A finite represented-parent batch list covers one concrete retained target
trace exactly up to operational reordering.
-/
structure TBPlan
    {M N K n leftWeight rightWeight : ℕ}
    (terms : List (DFTerm M N K)) where
  specs :
    List (TBSpec
      M N K n leftWeight rightWeight)
  terms_perm :
    List.Perm (batchSpecTerms specs) terms

namespace TBPlan

/-- The empty retained trace has the empty finite batch plan. -/
def nil
    {M N K n leftWeight rightWeight : ℕ} :
    TBPlan
      (M := M) (N := N) (K := K)
      (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
      [] where
  specs := []
  terms_perm := List.Perm.refl []

/-- Reorder the retained operational target of one finite batch plan. -/
def permTerms
    {M N K n leftWeight rightWeight : ℕ}
    {source target : List (DFTerm M N K)}
    (plan :
      TBPlan
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        source)
    (hterms : List.Perm source target) :
    TBPlan
      (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
      target where
  specs := plan.specs
  terms_perm := plan.terms_perm.trans hterms

/-- Every exact finite filtered-grid plan supplies its target inventory. -/
noncomputable def inventory
    {M N K n leftWeight rightWeight : ℕ}
    {terms : List (DFTerm M N K)}
    (plan :
      TBPlan
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        terms) :
    MIBlock terms :=
  (batchSpecsInventory plan.specs).permTerms
    plan.terms_perm

end TBPlan

/--
Primitive retained-grid coverage law for operational cutoff partitions.  This
is the finite combinatorial constructor still required from the parametrized
Hall algorithm.
-/
structure OBPlan
    (n leftWeight rightWeight : ℕ) : Prop where
  plan :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N)
      (partition :
        CCPartit endpoint
          n leftWeight rightWeight),
      Nonempty
        (TBPlan
          (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
          partition.retained)

namespace OBPlan

/-- Finite retained-grid coverage resolves the exact retained inventory law. -/
lemma nonempty_retainedInventory
    {n leftWeight rightWeight : ℕ}
    (kernel :
      OBPlan
        n leftWeight rightWeight)
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint
        n leftWeight rightWeight) :
    Nonempty (MIBlock partition.retained) := by
  rcases kernel.plan endpoint partition with ⟨plan⟩
  exact ⟨plan.inventory⟩

end OBPlan

/-- An empty complete correction trace has the empty retained batch plan. -/
lemma batch_plan_nil
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint n leftWeight rightWeight)
    (hcorrections : endpoint.corrections = []) :
    Nonempty
      (TBPlan
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        partition.retained) := by
  have hlength := partition.corrections_perm.length_eq
  rw [hcorrections] at hlength
  simp only [List.length_nil, List.length_append] at hlength
  have hretained : partition.retained = [] := by
    apply List.length_eq_zero_iff.mp
    omega
  exact ⟨TBPlan.nil.permTerms (by rw [hretained])⟩

/-- No-left-label traces have the empty retained batch plan. -/
lemma multiplicity_batch_plan
    (N n leftWeight rightWeight : ℕ)
    (endpoint : ODEmissi 0 N)
    (partition :
      CCPartit endpoint n leftWeight rightWeight) :
    Nonempty
      (TBPlan
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        partition.retained) := by
  apply batch_plan_nil partition
  exact
    FCollec.ECorrec.nil_source endpoint.emits
      (inverse_decorated_terms N)

/-- No-right-label traces have the empty retained batch plan. -/
lemma truncated_batch_plan
    (M n leftWeight rightWeight : ℕ)
    (endpoint : ODEmissi M 0)
    (partition :
      CCPartit endpoint n leftWeight rightWeight) :
    Nonempty
      (TBPlan
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        partition.retained) := by
  apply batch_plan_nil partition
  exact
    FCollec.ECorrec.nil_source endpoint.emits
      (inverse_raw_decorated M)

/-- The first positive-positive trace has the empty retained batch plan. -/
lemma batch_plan_one
    (n leftWeight rightWeight : ℕ)
    (endpoint : ODEmissi 1 1)
    (partition :
      CCPartit endpoint n leftWeight rightWeight) :
    Nonempty
      (TBPlan
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        partition.retained) := by
  apply batch_plan_nil partition
  exact
    FCollec.ECorrec.nil_source_length
      endpoint.emits (by
        rw [inverse_decorated_length])

/-- Only positive-positive filtered-grid coverage remains after empty inputs. -/
structure PBPlan
    (n leftWeight rightWeight : ℕ) : Prop where
  plan :
    ∀ (M N : ℕ),
      0 < M →
        0 < N →
          ∀ (endpoint :
              ODEmissi M N)
            (partition :
              CCPartit endpoint
                n leftWeight rightWeight),
            Nonempty
              (TBPlan
                (n := n) (leftWeight := leftWeight)
                (rightWeight := rightWeight) partition.retained)

namespace PBPlan

/-- Empty inputs plus positive coverage resolve every retained trace. -/
def operationalBatchPlan
    {n leftWeight rightWeight : ℕ}
    (kernel :
      PBPlan
        n leftWeight rightWeight) :
    OBPlan
      n leftWeight rightWeight where
  plan {M N} endpoint partition := by
    by_cases hM : M = 0
    · subst M
      exact multiplicity_batch_plan
        N n leftWeight rightWeight endpoint partition
    by_cases hN : N = 0
    · subst N
      exact truncated_batch_plan
        M n leftWeight rightWeight endpoint partition
    exact kernel.plan M N (Nat.pos_of_ne_zero hM) (Nat.pos_of_ne_zero hN)
      endpoint partition

end PBPlan

/--
After empty inputs and `1 × 1`, only nontrivial positive filtered-grid
coverage remains.
-/
structure NBPlan
    (n leftWeight rightWeight : ℕ) : Prop where
  plan :
    ∀ (M N : ℕ),
      0 < M →
        0 < N →
          (M ≠ 1 ∨ N ≠ 1) →
            ∀ (endpoint :
                ODEmissi M N)
              (partition :
                CCPartit endpoint
                  n leftWeight rightWeight),
              Nonempty
                (TBPlan
                  (n := n) (leftWeight := leftWeight)
                  (rightWeight := rightWeight) partition.retained)

namespace NBPlan

/-- The explicit `1 × 1` plan resolves the full positive-input coverage law. -/
def positiveBatchPlan
    {n leftWeight rightWeight : ℕ}
    (kernel :
      NBPlan
        n leftWeight rightWeight) :
    PBPlan
      n leftWeight rightWeight where
  plan M N hM hN endpoint partition := by
    by_cases hMone : M = 1
    · by_cases hNone : N = 1
      · subst M
        subst N
        exact batch_plan_one
          n leftWeight rightWeight endpoint partition
      · exact kernel.plan M N hM hN (Or.inr hNone) endpoint partition
    · exact kernel.plan M N hM hN (Or.inl hMone) endpoint partition

/-- Empty and `1 × 1` cases reduce coverage to nontrivial positive inputs. -/
def operationalBatchPlan
    {n leftWeight rightWeight : ℕ}
    (kernel :
      NBPlan
        n leftWeight rightWeight) :
    OBPlan
      n leftWeight rightWeight :=
  kernel.positiveBatchPlan
    |>.operationalBatchPlan

end NBPlan

end TMPlanni
end TCTex
end Submission

/-!
# Filter full multiplicity worklists into retained-grid plans

A full operational multiplicity worklist retains the represented left and
right parent inventories of every exhausted Cartesian correction batch.
Filtering each such batch below a nilpotent cutoff therefore gives a finite
retained-grid plan.  The composed filtered permutation is exactly the retained
side of any operational cutoff partition.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace TMPlanni

open HACoeff
open ICFilter
open ICFilter.CCPartit
open IMWork
open OCPartit
open FMEnd
open MTRoute
open MWSched
open HSPacket

namespace TBSpec

/-- Reuse the represented parent inventories of one full Cartesian batch. -/
noncomputable def batchWorkItem
    {M N K n leftWeight rightWeight : ℕ}
    (item : MWItem M N K) :
    TBSpec M N K n leftWeight rightWeight where
  leftTerms := item.leftTerms
  rightTerms := item.rightTerms
  left := item.left
  right := item.right

@[simp]
lemma batch_work_item
    {M N K n leftWeight rightWeight : ℕ}
    (item : MWItem M N K) :
    (batchWorkItem
      (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
      item).terms =
        belowCutoffTerms n leftWeight rightWeight
          (DFTerm.correctionGrid
            item.leftTerms item.rightTerms) :=
  rfl

/--
Filtering one exhausted full Cartesian batch gives exactly its retained grid
up to the operational emission order.
-/
lemma perm_emitted_closed
    {M N K n leftWeight rightWeight : ℕ}
    (item : MWItem M N K)
    (hclosed : item.Closed) :
    List.Perm
      (batchWorkItem
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        item).terms
      (belowCutoffTerms n leftWeight rightWeight item.ledger.emitted) := by
  have hpending : item.ledger.pending = [] :=
    hclosed
  have hperm :=
    item.ledger.accounting.filter fun term =>
      decide (decoratedFamilyWeight leftWeight rightWeight term < n)
  rw [hpending] at hperm
  simpa [belowCutoffTerms, List.filter_append] using hperm.symm

end TBSpec

/--
Filtering every exhausted full worklist batch gives the concatenated retained
grids, up to permutation of the emitted operational trace.
-/
lemma batch_spec_perm
    {M N K n leftWeight rightWeight : ℕ}
    (worklist : MBWork M N K)
    (hclosed : MBWork.Closed worklist) :
    List.Perm
      (batchSpecTerms
        (worklist.map fun item =>
          TBSpec.batchWorkItem
            (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
            item))
      (belowCutoffTerms n leftWeight rightWeight
        (worklist.flatMap fun item => item.ledger.emitted)) := by
  induction worklist with
  | nil =>
      exact List.Perm.refl []
  | cons item worklist ih =>
      have hitemClosed : item.Closed :=
        hclosed item (by simp)
      have htailClosed : MBWork.Closed worklist := by
        intro next hnext
        exact hclosed next (by simp [hnext])
      have hitem :=
        TBSpec.perm_emitted_closed
            (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
            item hitemClosed
      have htail := ih htailClosed
      simpa [batchSpecTerms, belowCutoffTerms,
        List.filter_append] using hitem.append htail

namespace FWSched

/--
Every full closed multiplicity worklist filters to a finite exact plan for the
retained side of any operational cutoff partition.
-/
noncomputable def truncatedBatchPlan
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (schedule : OWSched endpoint)
    (partition :
      CCPartit endpoint
        n leftWeight rightWeight) :
    TBPlan
      (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
      partition.retained where
  specs :=
    schedule.worklist.map fun item =>
      TBSpec.batchWorkItem
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight) item
  terms_perm := by
    have hplanned :=
      batch_spec_perm
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        schedule.worklist schedule.closed
    have hfiltered :
        List.Perm
          (belowCutoffTerms n leftWeight rightWeight
            (schedule.worklist.flatMap fun item => item.ledger.emitted))
          (belowCutoffTerms n leftWeight rightWeight endpoint.corrections) := by
      simpa [belowCutoffTerms] using
        schedule.corrections_perm.filter fun term =>
          decide (decoratedFamilyWeight leftWeight rightWeight term < n)
    exact hplanned.trans <| hfiltered.trans <|
      belowTermsPerm partition

end FWSched

namespace FWKern

/--
Full operational worklist scheduling is stronger than retained-grid planning
at every nilpotent cutoff.
-/
noncomputable def operationalBatchPlan
    (kernel : OMWork)
    (n leftWeight rightWeight : ℕ) :
    OBPlan
      n leftWeight rightWeight where
  plan endpoint partition :=
    ⟨FWSched.truncatedBatchPlan
        (Classical.choice (kernel.schedule endpoint)) partition⟩

end FWKern

namespace TRKern

/--
Full sequential correction routing is stronger than retained-grid planning at
every nilpotent cutoff.
-/
noncomputable def operationalBatchPlan
    (kernel : ORKern)
    (n leftWeight rightWeight : ℕ) :
    OBPlan
      n leftWeight rightWeight :=
  FWKern.operationalBatchPlan
      kernel.operationalMultiplicityWorklist
        n leftWeight rightWeight

end TRKern

end TMPlanni
end TCTex
end Submission

/-!
# Sequential routing of retained below-cutoff corrections

Nilpotent collection only has to route correction terms whose weighted Hall
degree remains below the cutoff.  This file is the cutoff-aware analogue of
the full operational routing state.

The state may open filtered Cartesian batches in any order and consume any
concrete retained parent-pair slot.  Its permutation certificate remembers
that the consumed slots are exactly the routed operational prefix.  A closed
state therefore supplies an exact multiplicity inventory for the retained
trace.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace TMRoutea

open HACoeff
open IMPropag
open OCPartit
open FMEnd
open MTRoute
open TMWork
open OTWork

/-- Concrete retained terms emitted so far by every truncated batch. -/
def worklistEmittedTerms
    {M N K n leftWeight rightWeight : ℕ}
    (worklist :
      TBWork M N K n leftWeight rightWeight) :
    List (DFTerm M N K) :=
  worklist.flatMap fun item => item.ledger.emitted

/--
One truncated-worklist emission appends the selected retained concrete term up
to permutation of terms emitted by later heterogeneous batches.
-/
lemma emitted_emit_append
    {M N K n leftWeight rightWeight : ℕ}
    (pre post :
      TBWork M N K n leftWeight rightWeight)
    (item :
      TWItem M N K n leftWeight rightWeight)
    (before : List (DFTerm M N K))
    (term : DFTerm M N K)
    (after : List (DFTerm M N K))
    (hpending : item.ledger.pending = before ++ term :: after) :
    List.Perm
      (worklistEmittedTerms
        (pre ++ item.emit before term after hpending :: post))
      (worklistEmittedTerms
        (pre ++ item :: post) ++ [term]) := by
  simp only [worklistEmittedTerms,
    List.flatMap_append, List.flatMap_cons,
    TWItem.emit,
    TMLedger.emit]
  have hcomm :
      List.Perm
        (([term] : List (DFTerm M N K)) ++
          (post.flatMap fun item => item.ledger.emitted))
        ((post.flatMap fun item => item.ledger.emitted) ++ [term]) :=
    List.perm_append_comm
  simpa [List.append_assoc] using
    hcomm.append_left
      ((pre.flatMap fun item => item.ledger.emitted) ++ item.ledger.emitted)

/--
Sequential routing state for a finite below-cutoff operational correction
prefix.
-/
structure MRState
    (M N K n leftWeight rightWeight : ℕ) where
  worklist :
    TBWork M N K n leftWeight rightWeight
  routedTerms :
    List (DFTerm M N K)
  emitted_perm :
    List.Perm
      (worklistEmittedTerms worklist)
      routedTerms

namespace MRState

/-- Empty state before any retained operational correction has been routed. -/
def nil
    (M N K n leftWeight rightWeight : ℕ) :
    MRState
      M N K n leftWeight rightWeight where
  worklist := []
  routedTerms := []
  emitted_perm := List.Perm.refl []

/-- Open one filtered Cartesian batch without changing the routed prefix. -/
noncomputable def openBatch
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : MIBlock leftTerms)
    (right : MIBlock rightTerms) :
    MRState
      M N K n leftWeight rightWeight where
  worklist :=
    state.worklist ++
      [TWItem.initial left right]
  routedTerms := state.routedTerms
  emitted_perm := by
    simpa [worklistEmittedTerms,
      TWItem.initial,
      TMLedger.initial] using
        state.emitted_perm

/-- Route one retained parent-pair slot and append its correction operationally. -/
noncomputable def route
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    (pre post :
      TBWork M N K n leftWeight rightWeight)
    (item :
      TWItem M N K n leftWeight rightWeight)
    (hworklist : state.worklist = pre ++ item :: post)
    (emission : CBEmissia item) :
    MRState
      M N K n leftWeight rightWeight where
  worklist := pre ++ emission.emitItem :: post
  routedTerms :=
    state.routedTerms ++
      [emission.leftTerm.correction emission.rightTerm]
  emitted_perm := by
    have hroute :=
      emitted_emit_append
        pre post item emission.pendingPrefix
          (emission.leftTerm.correction emission.rightTerm)
          emission.pendingSuffix emission.pending_eq
    apply hroute.trans
    rw [← hworklist]
    exact state.emitted_perm.append_right _

/-- Open one filtered batch and immediately route one selected retained slot. -/
noncomputable def batchRoute
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : MIBlock leftTerms)
    (right : MIBlock rightTerms)
    (emission :
      CBEmissia
        (TWItem.initial
          (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
          left right)) :
    MRState
      M N K n leftWeight rightWeight :=
  (state.openBatch left right).route state.worklist []
    (TWItem.initial
      (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
      left right)
    (by simp [openBatch]) emission

/--
Open one filtered represented parent grid and immediately consume its known
below-cutoff operational correction.
-/
noncomputable def openBatchRoute
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left : MIBlock leftTerms)
    (right : MIBlock rightTerms)
    (leftTerm : DFTerm M N K)
    (rightTerm : DFTerm M N K)
    (hleft : leftTerm ∈ leftTerms)
    (hright : rightTerm ∈ rightTerms)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
          (leftTerm.correction rightTerm) < n) :
    MRState
      M N K n leftWeight rightWeight :=
  state.batchRoute left right
    (CBEmissia.ofInitialCorrection
      left right leftTerm rightTerm hleft hright hweight)

/-- A closed retained routing state supplies its exact multiplicity inventory. -/
noncomputable def closedInventoryBlock
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    (hclosed : state.worklist.Closed) :
    MIBlock state.routedTerms :=
  (state.worklist.closedInventoryBlock hclosed).permTerms state.emitted_perm

/-- Every arithmetic worklist emission lifts to one concrete routed correction. -/
lemma route_worklist_step
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    {nextWorklist :
      TBWork M N K n leftWeight rightWeight}
    (hstep :
      TBWork.Step
        state.worklist nextWorklist) :
    ∃ next :
        MRState
          M N K n leftWeight rightWeight,
      next.worklist = nextWorklist ∧
        next.worklist.pendingSlots < state.worklist.pendingSlots := by
  generalize hworklist : state.worklist = worklist at hstep
  cases hstep with
  | emit pre post item before term after hpending =>
      have hterm : term ∈ item.ledger.pending := by
        rw [hpending]
        simp
      rcases
          item.ledger.parent_terms_pending hterm with
        ⟨leftTerm, hleft, rightTerm, hright, htermEq⟩
      subst term
      let emission : CBEmissia item := {
        leftTerm := leftTerm
        rightTerm := rightTerm
        left_mem := hleft
        right_mem := hright
        pendingPrefix := before
        pendingSuffix := after
        pending_eq := hpending }
      let next := state.route pre post item hworklist emission
      refine ⟨next, ?_, ?_⟩
      · simp [next, route, CBEmissia.emitItem,
          emission]
      simpa [next, route] using
        TBWork.pending_slots_step
          (TBWork.stepConcreteEmission
            pre post item emission)

/-- Every nonclosed retained routing state admits one concrete routed step. -/
lemma route_not_closed
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    (hclosed : ¬ state.worklist.Closed) :
    ∃ next :
        MRState
          M N K n leftWeight rightWeight,
      next.worklist.pendingSlots < state.worklist.pendingSlots := by
  rcases
      TBWork.step_not_closed
        state.worklist hclosed with
    ⟨nextWorklist, hstep⟩
  rcases state.route_worklist_step hstep with
    ⟨next, _hworklist, hlt⟩
  exact ⟨next, hlt⟩

/-- Every finite opened retained routing state can be concretely exhausted. -/
lemma exists_closed_extension
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight) :
    ∃ final :
        MRState
          M N K n leftWeight rightWeight,
      final.worklist.Closed := by
  by_cases hclosed : state.worklist.Closed
  · exact ⟨state, hclosed⟩
  · rcases state.route_not_closed hclosed with
      ⟨next, hlt⟩
    exact exists_closed_extension next
termination_by state.worklist.pendingSlots
decreasing_by
  exact hlt

end MRState

/-- A closed retained routing state supplies the partition's retained inventory. -/
noncomputable def inventoryRoutingState
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint n leftWeight rightWeight)
    (state :
      MRState M N
        (inverseLabelledCollection M N).factors.length
        n leftWeight rightWeight)
    (hclosed : state.worklist.Closed)
    (hrouted : state.routedTerms = partition.retained) :
    MIBlock partition.retained :=
  (state.closedInventoryBlock hclosed).permTerms (by rw [hrouted])

/--
Concrete cutoff-aware sequential scheduler: route each retained operational
correction trace through finitely many filtered Cartesian batches and exhaust
all of them.
-/
structure OMRoute
    (n leftWeight rightWeight : ℕ) : Prop where
  route :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N)
      (partition :
        CCPartit endpoint
          n leftWeight rightWeight),
      ∃ state : MRState M N
          (inverseLabelledCollection M N).factors.length
          n leftWeight rightWeight,
        state.worklist.Closed ∧
          state.routedTerms = partition.retained

namespace OMRoute

/-- Cutoff-aware sequential routing resolves every retained exact inventory. -/
lemma nonempty_retainedInventory
    {n leftWeight rightWeight : ℕ}
    (kernel :
      OMRoute
        n leftWeight rightWeight)
    {M N : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint
        n leftWeight rightWeight) :
    Nonempty (MIBlock partition.retained) := by
  rcases kernel.route endpoint partition with ⟨state, hclosed, hrouted⟩
  exact ⟨inventoryRoutingState
    partition state hclosed hrouted⟩

end OMRoute

/-- An empty complete correction trace has no retained cutoff terms. -/
lemma retained_nil_corrections
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint n leftWeight rightWeight)
    (hcorrections : endpoint.corrections = []) :
    partition.retained = [] := by
  have hlength := partition.corrections_perm.length_eq
  rw [hcorrections] at hlength
  simp only [List.length_nil, List.length_append] at hlength
  apply List.length_eq_zero_iff.mp
  omega

/-- No-left-label traces have the empty retained closed routing state. -/
lemma closed_routing_left
    (N n leftWeight rightWeight : ℕ)
    (endpoint : ODEmissi 0 N)
    (partition :
      CCPartit endpoint
        n leftWeight rightWeight) :
    ∃ state : MRState 0 N
        (inverseLabelledCollection 0 N).factors.length
        n leftWeight rightWeight,
      state.worklist.Closed ∧
        state.routedTerms = partition.retained := by
  have hcorrections :
      endpoint.corrections = [] :=
    FCollec.ECorrec.nil_source endpoint.emits
      (inverse_decorated_terms N)
  have hretained :
      partition.retained = [] :=
    retained_nil_corrections partition hcorrections
  refine ⟨MRState.nil 0 N
    (inverseLabelledCollection 0 N).factors.length
      n leftWeight rightWeight, ?_, ?_⟩
  · simp [MRState.nil,
      TBWork.Closed]
  · exact hretained.symm

/-- No-right-label traces have the empty retained closed routing state. -/
lemma closed_routing_state
    (M n leftWeight rightWeight : ℕ)
    (endpoint : ODEmissi M 0)
    (partition :
      CCPartit endpoint
        n leftWeight rightWeight) :
    ∃ state : MRState M 0
        (inverseLabelledCollection M 0).factors.length
        n leftWeight rightWeight,
      state.worklist.Closed ∧
        state.routedTerms = partition.retained := by
  have hcorrections :
      endpoint.corrections = [] :=
    FCollec.ECorrec.nil_source endpoint.emits
      (inverse_raw_decorated M)
  have hretained :
      partition.retained = [] :=
    retained_nil_corrections partition hcorrections
  refine ⟨MRState.nil M 0
    (inverseLabelledCollection M 0).factors.length
      n leftWeight rightWeight, ?_, ?_⟩
  · simp [MRState.nil,
      TBWork.Closed]
  · exact hretained.symm

/-- The first positive-positive trace also has the empty retained state. -/
lemma closed_truncated_routing
    (n leftWeight rightWeight : ℕ)
    (endpoint : ODEmissi 1 1)
    (partition :
      CCPartit endpoint
        n leftWeight rightWeight) :
    ∃ state : MRState 1 1
        (inverseLabelledCollection 1 1).factors.length
        n leftWeight rightWeight,
      state.worklist.Closed ∧
        state.routedTerms = partition.retained := by
  have hcorrections :
      endpoint.corrections = [] :=
    FCollec.ECorrec.nil_source_length
      endpoint.emits (by
        rw [inverse_decorated_length])
  have hretained :
      partition.retained = [] :=
    retained_nil_corrections partition hcorrections
  refine ⟨MRState.nil 1 1
    (inverseLabelledCollection 1 1).factors.length
      n leftWeight rightWeight, ?_, ?_⟩
  · simp [MRState.nil,
      TBWork.Closed]
  · exact hretained.symm

/-- Only positive-positive cutoff-aware routing remains after the empty cases. -/
structure PORoute
    (n leftWeight rightWeight : ℕ) : Prop where
  route :
    ∀ (M N : ℕ),
      0 < M →
        0 < N →
          ∀ (endpoint :
              ODEmissi M N)
            (partition :
              CCPartit endpoint
                n leftWeight rightWeight),
            ∃ state : MRState M N
                (inverseLabelledCollection M N).factors.length
                n leftWeight rightWeight,
              state.worklist.Closed ∧
                state.routedTerms = partition.retained

namespace PORoute

/-- Zero cases plus positive routing resolve every retained operational trace. -/
def truncMultRouting
    {n leftWeight rightWeight : ℕ}
    (kernel :
      PORoute
        n leftWeight rightWeight) :
    OMRoute
      n leftWeight rightWeight where
  route {M N} endpoint partition := by
    by_cases hM : M = 0
    · subst M
      exact closed_routing_left
        N n leftWeight rightWeight endpoint partition
    by_cases hN : N = 0
    · subst N
      exact closed_routing_state
        M n leftWeight rightWeight endpoint partition
    exact kernel.route M N (Nat.pos_of_ne_zero hM) (Nat.pos_of_ne_zero hN)
      endpoint partition

end PORoute

/--
After the empty cases and `1 × 1`, only nontrivial positive cutoff-aware
routing remains.
-/
structure NORoute
    (n leftWeight rightWeight : ℕ) : Prop where
  route :
    ∀ (M N : ℕ),
      0 < M →
        0 < N →
          (M ≠ 1 ∨ N ≠ 1) →
            ∀ (endpoint :
                ODEmissi M N)
              (partition :
                CCPartit endpoint
                  n leftWeight rightWeight),
              ∃ state : MRState M N
                  (inverseLabelledCollection M N).factors.length
                  n leftWeight rightWeight,
                state.worklist.Closed ∧
                  state.routedTerms = partition.retained

namespace NORoute

/-- The explicit `1 × 1` state resolves the full positive-input kernel. -/
def positiveOperationalRouting
    {n leftWeight rightWeight : ℕ}
    (kernel :
      NORoute
        n leftWeight rightWeight) :
    PORoute
      n leftWeight rightWeight where
  route M N hM hN endpoint partition := by
    by_cases hMone : M = 1
    · by_cases hNone : N = 1
      · subst M
        subst N
        exact closed_truncated_routing
          n leftWeight rightWeight endpoint partition
      · exact kernel.route M N hM hN (Or.inr hNone) endpoint partition
    · exact kernel.route M N hM hN (Or.inl hMone) endpoint partition

/-- Empty and `1 × 1` cases reduce routing to nontrivial positive inputs. -/
def truncMultRouting
    {n leftWeight rightWeight : ℕ}
    (kernel :
      NORoute
        n leftWeight rightWeight) :
    OMRoute
      n leftWeight rightWeight :=
  kernel.positiveOperationalRouting
    |>.truncMultRouting

end NORoute

end TMRoutea
end TCTex
end Submission

/-!
# Routing finite retained-grid plans

Finite retained-grid plans compose recursively and open concrete truncated
worklists.  Draining such a worklist emits exactly the plan's target trace up
to permutation.  This is the operational handoff required after constructing
the nontrivial positive filtered-grid coverage plan.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace TMPlanni

open HACoeff
open TMWork
open TMRoutea
open OTWork

namespace TBPlan

/-- One retained filtered grid is a singleton finite batch plan. -/
noncomputable def ofSpec
    {M N K n leftWeight rightWeight : ℕ}
    (spec :
      TBSpec M N K n leftWeight rightWeight) :
    TBPlan
      (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
      spec.terms where
  specs := [spec]
  terms_perm := by
    simp [batchSpecTerms]

/-- Concatenate two finite retained-grid plans. -/
noncomputable def append
    {M N K n leftWeight rightWeight : ℕ}
    {leftTerms rightTerms : List (DFTerm M N K)}
    (left :
      TBPlan
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        leftTerms)
    (right :
      TBPlan
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        rightTerms) :
    TBPlan
      (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
      (leftTerms ++ rightTerms) where
  specs := left.specs ++ right.specs
  terms_perm := by
    rw [batchSpecTerms, List.flatMap_append]
    exact left.terms_perm.append right.terms_perm

/-- Prepend one retained filtered grid to an existing finite batch plan. -/
noncomputable def consSpec
    {M N K n leftWeight rightWeight : ℕ}
    (spec :
      TBSpec M N K n leftWeight rightWeight)
    {terms : List (DFTerm M N K)}
    (plan :
      TBPlan
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        terms) :
    TBPlan
      (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
      (spec.terms ++ terms) :=
  (ofSpec spec).append plan

end TBPlan

/-- Canonical retained filtered-grid terms represented by an open worklist. -/
noncomputable def batchWorklistTerms
    {M N K n leftWeight rightWeight : ℕ}
    (worklist :
      TBWork M N K n leftWeight rightWeight) :
    List (DFTerm M N K) :=
  worklist.flatMap fun item =>
    truncatedDecoratedGrid
      n leftWeight rightWeight item.leftTerms item.rightTerms

/-- Opening a planned worklist represents exactly its concatenated grids. -/
@[simp]
lemma batch_worklist_initial
    {M N K n leftWeight rightWeight : ℕ}
    (specs :
      List (TBSpec
        M N K n leftWeight rightWeight)) :
    batchWorklistTerms
        (initialBatchWorklist specs) =
      batchSpecTerms specs := by
  induction specs with
  | nil =>
      rfl
  | cons spec specs ih =>
      change
        spec.terms ++
            batchWorklistTerms
              (initialBatchWorklist specs) =
          spec.terms ++ batchSpecTerms specs
      rw [ih]

/-- Arithmetic worklist emission preserves the represented filtered grids. -/
lemma truncated_batch_worklist
    {M N K n leftWeight rightWeight : ℕ}
    {before after :
      TBWork M N K n leftWeight rightWeight}
    (hstep : TBWork.Step before after) :
    batchWorklistTerms after =
      batchWorklistTerms before := by
  cases hstep with
  | emit pre post item before term after hpending =>
      simp [batchWorklistTerms,
        TWItem.emit]

/--
A closed worklist has emitted exactly the represented retained grids up to
operational ordering.
-/
lemma worklist_emitted_closed
    {M N K n leftWeight rightWeight : ℕ}
    (worklist :
      TBWork M N K n leftWeight rightWeight)
    (hclosed : worklist.Closed) :
    List.Perm
      (worklistEmittedTerms worklist)
      (batchWorklistTerms worklist) := by
  induction worklist with
  | nil =>
      exact List.Perm.refl []
  | cons item worklist ih =>
      have hitem : item.ledger.pending = [] :=
        hclosed item (by simp)
      have hitemPerm :
          List.Perm item.ledger.emitted
            (truncatedDecoratedGrid
              n leftWeight rightWeight item.leftTerms item.rightTerms) := by
        simpa [hitem] using item.ledger.accounting
      have htailClosed :
          TBWork.Closed worklist := by
        intro next hnext
        exact hclosed next (by simp [hnext])
      simpa [worklistEmittedTerms,
        batchWorklistTerms] using
          hitemPerm.append (ih htailClosed)

namespace TBPlan

/-- Open all grids of a finite plan before routing any retained term. -/
noncomputable def initialRoutingState
    {M N K n leftWeight rightWeight : ℕ}
    {terms : List (DFTerm M N K)}
    (plan :
      TBPlan
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        terms) :
    MRState
      M N K n leftWeight rightWeight where
  worklist := initialBatchWorklist plan.specs
  routedTerms := []
  emitted_perm := by
    simp [worklistEmittedTerms]

end TBPlan

namespace MRState

/-- Reorder the routed operational trace without changing its open worklist. -/
def permRoutedTerms
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    {terms : List (DFTerm M N K)}
    (hperm : List.Perm state.routedTerms terms) :
    MRState
      M N K n leftWeight rightWeight where
  worklist := state.worklist
  routedTerms := terms
  emitted_perm := state.emitted_perm.trans hperm

@[simp]
lemma worklist_perm_routed
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    {terms : List (DFTerm M N K)}
    (hperm : List.Perm state.routedTerms terms) :
    (permRoutedTerms state hperm).worklist = state.worklist :=
  rfl

@[simp]
lemma routed_terms_perm
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    {terms : List (DFTerm M N K)}
    (hperm : List.Perm state.routedTerms terms) :
    (permRoutedTerms state hperm).routedTerms = terms :=
  rfl

/--
Every finite concrete routing state closes without changing the represented
filtered grids.
-/
lemma closed_worklist_terms
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight) :
    ∃ final :
        MRState
          M N K n leftWeight rightWeight,
      final.worklist.Closed ∧
        batchWorklistTerms final.worklist =
          batchWorklistTerms state.worklist := by
  by_cases hclosed : state.worklist.Closed
  · exact ⟨state, hclosed, rfl⟩
  · rcases
        TBWork.step_not_closed
          state.worklist hclosed with
      ⟨nextWorklist, hstep⟩
    rcases state.route_worklist_step hstep with
      ⟨next, hnextWorklist, hlt⟩
    rcases closed_worklist_terms next with
      ⟨final, hfinalClosed, hfinalTerms⟩
    refine ⟨final, hfinalClosed, hfinalTerms.trans ?_⟩
    rw [hnextWorklist]
    exact truncated_batch_worklist hstep
termination_by state.worklist.pendingSlots
decreasing_by
  exact hlt

end MRState

namespace TBPlan

/--
Every finite retained-grid plan has a closed concrete routing state whose
routed trace is a permutation of the plan target.
-/
theorem closed_state
    {M N K n leftWeight rightWeight : ℕ}
    {terms : List (DFTerm M N K)}
    (plan :
      TBPlan
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        terms) :
    ∃ final :
        MRState
          M N K n leftWeight rightWeight,
      final.worklist.Closed ∧
        List.Perm final.routedTerms terms := by
  let initial := plan.initialRoutingState
  rcases
      MRState.closed_worklist_terms
        initial with
    ⟨final, hfinalClosed, hfinalTerms⟩
  refine ⟨final, hfinalClosed, ?_⟩
  apply final.emitted_perm.symm.trans
  apply
    (worklist_emitted_closed
      final.worklist hfinalClosed).trans
  rw [hfinalTerms]
  change
    List.Perm
      (batchWorklistTerms
        (initialBatchWorklist plan.specs))
      terms
  rw [batch_worklist_initial]
  exact plan.terms_perm

/--
Every finite retained-grid plan has a closed concrete routing state whose
routed trace is exactly the plan target.
-/
theorem routing_state
    {M N K n leftWeight rightWeight : ℕ}
    {terms : List (DFTerm M N K)}
    (plan :
      TBPlan
        (n := n) (leftWeight := leftWeight) (rightWeight := rightWeight)
        terms) :
    ∃ final :
        MRState
          M N K n leftWeight rightWeight,
      final.worklist.Closed ∧
        final.routedTerms = terms := by
  rcases plan.closed_state with
    ⟨final, hclosed, hperm⟩
  exact
    ⟨MRState.permRoutedTerms final hperm,
      hclosed, rfl⟩

end TBPlan

namespace OBPlan

/--
Finite retained-grid planning is strong enough to construct a concrete closed
trace-routing state for every operational cutoff partition.
-/
noncomputable def truncMultRouting
    {n leftWeight rightWeight : ℕ}
    (kernel :
      OBPlan
        n leftWeight rightWeight) :
    OMRoute
      n leftWeight rightWeight where
  route endpoint partition := by
    rcases kernel.plan endpoint partition with ⟨plan⟩
    exact plan.routing_state

end OBPlan

end TMPlanni
end TCTex
end Submission

/-!
# Route retained correction grids from a full operational trace router

A full operational correction router contains enough information to schedule
every complete multiplicity grid.  Filtering those grids below a nilpotent
cutoff gives a finite retained-grid plan, and finite retained-grid plans route
to an exact closed truncated trace.  This file packages that composition.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace TMPlanni

open MTRoute
open TMRoutea

namespace TRKern

/--
Full sequential correction routing is stronger than exact retained correction
routing at every nilpotent cutoff.
-/
noncomputable def truncMultRouting
    (kernel : ORKern)
    (n leftWeight rightWeight : ℕ) :
    OMRoute
      n leftWeight rightWeight :=
  OBPlan.truncMultRouting
      (operationalBatchPlan
        kernel n leftWeight rightWeight)

end TRKern

namespace NPKern

/--
The one remaining nontrivial positive full-routing constructor is sufficient
for exact retained correction routing at every nilpotent cutoff.
-/
noncomputable def truncMultRouting
    (kernel :
      NPRoute)
    (n leftWeight rightWeight : ℕ) :
    OMRoute
      n leftWeight rightWeight :=
  TRKern.truncMultRouting
      kernel.operationalMultiplicityRouting
        n leftWeight rightWeight

end NPKern

end TMPlanni
end TCTex
end Submission

/-!
# Strict measure descent for routed truncated corrections

Every concrete cutoff-aware routing step consumes one retained Cartesian slot.
This file records strict pending-slot descent and lifts it to a finite routed
extension theorem: any routed prefix can be completed to a closed truncated
worklist while remaining a prefix of the resulting operational trace.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace TMRoutea

open HACoeff
open OCPartit
open TMWork

namespace MRState

/-- Routed terms and emitted retained-worklist terms always have equal length. -/
lemma emitted_length_routed
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight) :
    (worklistEmittedTerms state.worklist).length =
      state.routedTerms.length :=
  state.emitted_perm.length_eq

/-- Routing one selected retained correction is one truncated-worklist step. -/
lemma worklist_step_route
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    (pre post :
      TBWork M N K n leftWeight rightWeight)
    (item :
      TWItem M N K n leftWeight rightWeight)
    (hworklist : state.worklist = pre ++ item :: post)
    (emission : CBEmissia item) :
    TBWork.Step state.worklist
      (state.route pre post item hworklist emission).worklist := by
  rw [hworklist]
  exact TBWork.stepConcreteEmission
    pre post item emission

/-- Routing one selected retained correction strictly decreases open slots. -/
lemma pending_slots_route
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    (pre post :
      TBWork M N K n leftWeight rightWeight)
    (item :
      TWItem M N K n leftWeight rightWeight)
    (hworklist : state.worklist = pre ++ item :: post)
    (emission : CBEmissia item) :
    (state.route pre post item hworklist emission).worklist.pendingSlots <
      state.worklist.pendingSlots :=
  TBWork.pending_slots_step
    (state.worklist_step_route pre post item hworklist emission)

/-- Every concrete correction selected for truncated routing is below cutoff. -/
lemma routed_correction_cutoff
    {M N K n leftWeight rightWeight : ℕ}
    {item :
      TWItem M N K n leftWeight rightWeight}
    (emission : CBEmissia item) :
    decoratedFamilyWeight leftWeight rightWeight
        (emission.leftTerm.correction emission.rightTerm) < n := by
  apply item.ledger.weight_pending
  rw [emission.pending_eq]
  simp

/-- Routing one retained correction appends exactly one operational term. -/
lemma routed_length_route
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    (pre post :
      TBWork M N K n leftWeight rightWeight)
    (item :
      TWItem M N K n leftWeight rightWeight)
    (hworklist : state.worklist = pre ++ item :: post)
    (emission : CBEmissia item) :
    (state.route pre post item hworklist emission).routedTerms.length =
      state.routedTerms.length + 1 := by
  simp [route]

/--
Any routed retained prefix extends through finitely many concrete emissions to
a closed truncated-worklist state.
-/
lemma exists_closedExtension
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight) :
    ∃ final :
        MRState
          M N K n leftWeight rightWeight,
      final.worklist.Closed ∧
        state.routedTerms <+: final.routedTerms := by
  by_cases hclosed : state.worklist.Closed
  · exact ⟨state, hclosed, List.prefix_rfl⟩
  · simp only [TBWork.Closed,
      not_forall] at hclosed
    rcases hclosed with ⟨item, hitem, hopen⟩
    rcases List.mem_iff_append.mp hitem with ⟨pre, post, hworklist⟩
    simp only [TWItem.Closed] at hopen
    cases hpending : item.ledger.pending with
    | nil =>
        exact False.elim (hopen hpending)
    | cons term after =>
        have hterm : term ∈ item.ledger.pending := by
          rw [hpending]
          simp
        rcases
            CBEmissia.exists_of_pending
              item hterm with
          ⟨emission, _hterm⟩
        let next := state.route pre post item hworklist emission
        rcases exists_closedExtension next with
          ⟨final, hfinalClosed, hprefix⟩
        refine ⟨final, hfinalClosed, ?_⟩
        apply (List.prefix_append state.routedTerms
          [emission.leftTerm.correction emission.rightTerm]).trans
        simpa [next, route] using hprefix
termination_by state.worklist.pendingSlots
decreasing_by
  exact state.pending_slots_route pre post item hworklist emission

end MRState

end TMRoutea
end TCTex
end Submission

-- Merged from FamilyOperationalExistingShapeBlockCollection.lean

/-!
# Existing shape-block collection for operational family endpoints

The operational family collector retains the genuine independent More3
derivation.  The older counted-family carrier stores the equivalent
`Collects` derivation and already proves exact realization-index coverage for
every maximal adjacent erased-shape block.

This file connects those two interfaces and isolates the precise older
shape-block theorem needed to resolve the newer packet and
multiplicity-inventory kernels.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace ESColl

open HACoeff
open IMPropag
open HOCollec
open SBEnd

/--
Forget the operational wrapper while retaining the equivalent counted-family
More3 derivation consumed by the existing shape-block theorem.
-/
def decoratedFamilyTerms
    {M N : ℕ}
    (collected : ODTerms M N) :
    CDTerms M N where
  factors := collected.factors
  eval_eq := collected.eval_eq
  family_collects :=
    DFTerm.collects_independent
      collected.family_collects
  decorated_collects :=
    DFTerm.independent_collects
      collected.family_collects

/--
Older counted-carrier form of the remaining shape-block theorem: every
canonical maximal erased-shape block has exact realization-index coverage.
-/
structure CSClos : Prop where
  realizationIndexed :
    ∀ {M N : ℕ}
      (collected : CDTerms M N)
      (block : List (DFTerm M N
        (inverseLabelledCollection M N).factors.length)),
      block ∈ sameErasedBlocks collected.factors →
        RealizationIndexedBlock block

namespace CSClos

/--
The counted-carrier shape-block theorem resolves the operational packet
interface.
-/
def shapeClosureKernel
    (kernel : CSClos) :
    SCKern where
  realizationIndexed collected block hblock :=
    kernel.realizationIndexed
      (decoratedFamilyTerms collected) block hblock

/--
The counted-carrier shape-block theorem also resolves the
multiplicity-preserving inventory interface used by the newer packet
compressors.
-/
def shapeMultiplicityInventory
    (kernel : CSClos) :
    SMInv where
  inventory collected block hblock :=
    ⟨MIBlock.realization_indexed
      (kernel.shapeClosureKernel.realizationIndexed
        collected block hblock)⟩

/--
The stable operational collector and the counted-carrier shape theorem supply
a canonical finite block-family expansion for every pair of natural
exponents.
-/
noncomputable def operationalBlockExpansion
    (kernel : CSClos)
    (M N : ℕ) :
    BFam.Expansion M N :=
  kernel.shapeClosureKernel.expansion M N

end CSClos

end ESColl
end TCTex
end Submission

-- Merged from FamilyOperationalShapeFiberOrderingReduction.lean

/-!
# Ordering reduction for operational shape fibers

The support-sensitive operational collector does not by itself prove that
maximal adjacent same-shape blocks are complete erased-shape fibers.  This
file isolates a sufficient primary-order statement and records its semantic
consequence: equal erased shapes cannot have a different shape between them.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace FORed

open HACoeff
open HOCollec
open MSCompre

/-- The primary deterministic shape order is transitive. -/
lemma shapeBefore_trans
    {M N K : ℕ}
    {left middle right : DTerm M N K}
    (hleftMiddle : left.shapeBefore middle)
    (hmiddleRight : middle.shapeBefore right) :
    left.shapeBefore right := by
  simp only [DTerm.shapeBefore, DTerm.higherDegreeBefore] at hleftMiddle
  simp only [DTerm.shapeBefore, DTerm.higherDegreeBefore] at hmiddleRight
  simp only [DTerm.shapeBefore, DTerm.higherDegreeBefore]
  rcases hleftMiddle with hleftMiddle | ⟨hleftMiddleDegree, hleftMiddleCode⟩
  · rcases hmiddleRight with hmiddleRight | ⟨hmiddleRightDegree, _⟩
    · exact Or.inl (lt_trans hmiddleRight hleftMiddle)
    · exact Or.inl (by omega)
  · rcases hmiddleRight with hmiddleRight | ⟨hmiddleRightDegree, hmiddleRightCode⟩
    · exact Or.inl (by omega)
    · exact Or.inr
        ⟨hleftMiddleDegree.trans hmiddleRightDegree,
          lt_trans hleftMiddleCode hmiddleRightCode⟩

/-- Equal erased shapes cannot be strictly ordered by the primary shape key. -/
lemma not_before_erased
    {M N K : ℕ}
    {left right : DTerm M N K}
    (hshape : left.erasedShape = right.erasedShape) :
    ¬ left.shapeBefore right := by
  apply DTerm.not_before_key
  · simp [DTerm.erasedDegree, hshape]
  · exact DTerm.erased_shape_code hshape

/--
Every operational endpoint is sorted by erased shape: earlier terms either
have the same erased shape or strictly precede later terms in the primary
shape order.
-/
structure OESorted : Prop where
  sorted :
    ∀ {M N : ℕ}
      (collected : ODTerms M N),
      collected.factors.Pairwise fun left right =>
        left.erasedShape = right.erasedShape ∨
          left.decorated.shapeBefore right.decorated

/--
Equal erased shapes form convex intervals in every operational endpoint.
This is the semantic order fact needed before proving complete shape fibers.
-/
structure EIConvex : Prop where
  convex :
    ∀ {M N : ℕ}
      (collected : ODTerms M N)
      (routingPrefix middle routingSuffix :
        List (DFTerm M N
          (inverseLabelledCollection M N).factors.length))
      (left right :
        DFTerm M N
          (inverseLabelledCollection M N).factors.length),
      collected.factors =
          routingPrefix ++ (left :: middle ++ (right :: routingSuffix)) →
        left.erasedShape = right.erasedShape →
          ∀ term ∈ middle, term.erasedShape = left.erasedShape

namespace OESorted

/--
Pairwise sorting by the primary shape order forces equal erased shapes to be
convex.  In particular, a different shape cannot occur between two copies of
one erased Hall shape.
-/
def operationalIntervalConvex
    (kernel : OESorted) :
    EIConvex where
  convex collected routingPrefix middle routingSuffix left right
      hfactors hleftRight term hterm := by
    have hsorted :
        (routingPrefix ++ (left :: middle ++ (right :: routingSuffix))).Pairwise
          fun earlier later =>
            earlier.erasedShape = later.erasedShape ∨
              earlier.decorated.shapeBefore later.decorated := by
      rw [← hfactors]
      exact kernel.sorted collected
    have hleftTail :
        (left :: middle ++ right :: routingSuffix).Pairwise
          fun earlier later =>
            earlier.erasedShape = later.erasedShape ∨
              earlier.decorated.shapeBefore later.decorated :=
      (List.pairwise_append.mp hsorted).2.1
    have hleftTerm :
        left.erasedShape = term.erasedShape ∨
          left.decorated.shapeBefore term.decorated :=
      (List.pairwise_cons.mp hleftTail).1 term (by simp [hterm])
    have hmiddleTail :
        (middle ++ right :: routingSuffix).Pairwise
          fun earlier later =>
            earlier.erasedShape = later.erasedShape ∨
              earlier.decorated.shapeBefore later.decorated :=
      (List.pairwise_cons.mp hleftTail).2
    have htermRight :
        term.erasedShape = right.erasedShape ∨
          term.decorated.shapeBefore right.decorated :=
      (List.pairwise_append.mp hmiddleTail).2.2 term hterm right (by simp)
    rcases hleftTerm with hleftTerm | hleftTerm
    · exact hleftTerm.symm
    · rcases htermRight with htermRight | htermRight
      · exact False.elim
          ((not_before_erased
            (hleftRight.trans htermRight.symm)) hleftTerm)
      · exact False.elim
          ((not_before_erased hleftRight)
            (shapeBefore_trans hleftTerm htermRight))

/--
Pairwise primary shape sorting also resolves the exact complete-fiber law
consumed by multiplicity compression.  The proof uses maximality of the
canonical `splitBy` runs: a matching term outside one chosen run would force
strict shape precedence between two terms with the same erased shape.
-/
noncomputable def shapeFiberKernel
    (kernel : OESorted) :
    OperationalShapeFiber where
  filter_eq collected block hblock := by
    let shape : CWord HPAtom :=
      Classical.choose
        (same_erased_blocks
          collected.factors block hblock)
    have hsame :
        ∀ term ∈ block, term.erasedShape = shape :=
      Classical.choose_spec
        (same_erased_blocks
          collected.factors block hblock)
    have hblockSplit :
        block ∈ collected.factors.splitBy
          fun left right => decide (left.erasedShape = right.erasedShape) := by
      simpa [sameErasedBlocks] using hblock
    have hblockNe : block ≠ [] :=
      List.ne_nil_of_mem_splitBy hblockSplit
    let pivot := block.head hblockNe
    have hpivotMem : pivot ∈ block := by
      exact List.head_mem hblockNe
    have hpivotShape : pivot.erasedShape = shape :=
      hsame pivot hpivotMem
    rcases List.mem_iff_append.mp hblock with
      ⟨beforeBlocks, afterBlocks, hblocks⟩
    let before := beforeBlocks.flatten
    let after := afterBlocks.flatten
    have hfactors :
        collected.factors = before ++ (block ++ after) := by
      rw [← flatten_same_blocks collected.factors, hblocks]
      simp [before, after]
    have hsorted :
        (before ++ (block ++ after)).Pairwise fun left right =>
          left.erasedShape = right.erasedShape ∨
            left.decorated.shapeBefore right.decorated := by
      rw [← hfactors]
      exact kernel.sorted collected
    have hblocksChain :
        (beforeBlocks ++ block :: afterBlocks).IsChain fun left right =>
          ∃ hleft hright,
            decide
              ((left.getLast hleft).erasedShape =
                (right.head hright).erasedShape) = false := by
      rw [← hblocks]
      simpa [sameErasedBlocks] using
        (List.isChain_getLast_head_splitBy
          (fun left right =>
            decide (left.erasedShape = right.erasedShape))
          collected.factors)
    have hbeforeFilter :
        before.filter (fun term => term.family.recipe.erasedShape = shape) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro term hterm htermShape
      have htermShape' : term.family.recipe.erasedShape = shape := by
        simpa using htermShape
      have hbeforeNe : before ≠ [] :=
        List.ne_nil_of_mem hterm
      have hbeforeBlocksNe : beforeBlocks ≠ [] := by
        intro hnil
        simp [before, hnil] at hterm
      have hpreviousBlockMem :
          beforeBlocks.getLast hbeforeBlocksNe ∈
            sameErasedBlocks collected.factors := by
        rw [hblocks]
        simp
      have hpreviousBlockNe :
          beforeBlocks.getLast hbeforeBlocksNe ≠ [] := by
        apply List.ne_nil_of_mem_splitBy
        simpa [sameErasedBlocks] using hpreviousBlockMem
      have hchain := hblocksChain
      rw [← List.dropLast_concat_getLast hbeforeBlocksNe] at hchain
      simp only [List.append_assoc, List.singleton_append] at hchain
      have hboundary :=
        (List.isChain_append_cons_cons.mp hchain).2.1
      rcases hboundary with ⟨_hpreviousBlockNe, _hblockNe, hboundary⟩
      have hpreviousEq :
          before.getLast hbeforeNe =
            (beforeBlocks.getLast hbeforeBlocksNe).getLast hpreviousBlockNe := by
        apply List.getLast_flatten_eq_getLast_getLast
      have hpreviousPivotNe :
          (before.getLast hbeforeNe).erasedShape ≠ pivot.erasedShape := by
        intro hpreviousPivot
        rw [← hpreviousEq] at hboundary
        change
          decide
            ((before.getLast hbeforeNe).erasedShape =
              pivot.erasedShape) = false at hboundary
        simp [hpreviousPivot] at hboundary
      have hbeforeSorted :
          before.Pairwise fun left right =>
            left.erasedShape = right.erasedShape ∨
              left.decorated.shapeBefore right.decorated :=
        (List.pairwise_append.mp hsorted).1
      have hbeforeRestCross :
          ∀ left ∈ before, ∀ right ∈ block ++ after,
            left.erasedShape = right.erasedShape ∨
              left.decorated.shapeBefore right.decorated :=
        (List.pairwise_append.mp hsorted).2.2
      have hpreviousPivot :
          (before.getLast hbeforeNe).erasedShape = pivot.erasedShape ∨
            (before.getLast hbeforeNe).decorated.shapeBefore pivot.decorated :=
        hbeforeRestCross (before.getLast hbeforeNe)
          (List.getLast_mem hbeforeNe) pivot (by simp [hpivotMem])
      have hpreviousBeforePivot :
          (before.getLast hbeforeNe).decorated.shapeBefore pivot.decorated := by
        rcases hpreviousPivot with hpreviousPivot | hpreviousPivot
        · exact False.elim (hpreviousPivotNe hpreviousPivot)
        · exact hpreviousPivot
      have htermPrevious :
          term.erasedShape = (before.getLast hbeforeNe).erasedShape ∨
            term.decorated.shapeBefore
              (before.getLast hbeforeNe).decorated :=
        hbeforeSorted.rel_getLast_of_rel_getLast_getLast hterm (Or.inl rfl)
      have htermPivot : term.erasedShape = pivot.erasedShape := by
        rw [term.erased_shape_family, htermShape', hpivotShape]
      rcases htermPrevious with htermPrevious | htermPrevious
      · exact hpreviousPivotNe (htermPrevious.symm.trans htermPivot)
      · exact
          (not_before_erased htermPivot)
            (shapeBefore_trans htermPrevious hpreviousBeforePivot)
    have hblockFilter :
        block.filter (fun term => term.family.recipe.erasedShape = shape) =
          block := by
      apply List.filter_eq_self.mpr
      intro term hterm
      rw [← term.erased_shape_family]
      simpa using hsame term hterm
    have hafterFilter :
        after.filter (fun term => term.family.recipe.erasedShape = shape) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro term hterm htermShape
      have htermShape' : term.family.recipe.erasedShape = shape := by
        simpa using htermShape
      have hafterNe : after ≠ [] :=
        List.ne_nil_of_mem hterm
      have hafterBlocksNe : afterBlocks ≠ [] := by
        intro hnil
        simp [after, hnil] at hterm
      have hnextBlockMem :
          afterBlocks.head hafterBlocksNe ∈
            sameErasedBlocks collected.factors := by
        rw [hblocks]
        simp
      have hnextBlockNe :
          afterBlocks.head hafterBlocksNe ≠ [] := by
        apply List.ne_nil_of_mem_splitBy
        simpa [sameErasedBlocks] using hnextBlockMem
      have hchain := hblocksChain
      rw [← List.cons_head_tail hafterBlocksNe] at hchain
      have hboundary :=
        (List.isChain_append_cons_cons.mp hchain).2.1
      rcases hboundary with ⟨_hblockNe, _hnextBlockNe, hboundary⟩
      have hnextEq :
          after.head hafterNe =
            (afterBlocks.head hafterBlocksNe).head hnextBlockNe := by
        apply List.head_flatten_eq_head_head
      have hlastNextNe :
          (block.getLast hblockNe).erasedShape ≠
            (after.head hafterNe).erasedShape := by
        intro hlastNext
        rw [← hnextEq] at hboundary
        change
          decide
            ((block.getLast hblockNe).erasedShape =
              (after.head hafterNe).erasedShape) = false at hboundary
        simp [hlastNext] at hboundary
      have hprefixAfterSorted :
          ((before ++ block) ++ after).Pairwise fun left right =>
            left.erasedShape = right.erasedShape ∨
              left.decorated.shapeBefore right.decorated := by
        simpa [List.append_assoc] using hsorted
      have hafterSorted :
          after.Pairwise fun left right =>
            left.erasedShape = right.erasedShape ∨
              left.decorated.shapeBefore right.decorated :=
        (List.pairwise_append.mp hprefixAfterSorted).2.1
      have hprefixAfterCross :
          ∀ left ∈ before ++ block, ∀ right ∈ after,
            left.erasedShape = right.erasedShape ∨
              left.decorated.shapeBefore right.decorated :=
        (List.pairwise_append.mp hprefixAfterSorted).2.2
      have hlastNext :
          (block.getLast hblockNe).erasedShape =
              (after.head hafterNe).erasedShape ∨
            (block.getLast hblockNe).decorated.shapeBefore
              (after.head hafterNe).decorated :=
        hprefixAfterCross (block.getLast hblockNe)
          (by simp [List.getLast_mem hblockNe])
          (after.head hafterNe) (List.head_mem hafterNe)
      have hlastBeforeNext :
          (block.getLast hblockNe).decorated.shapeBefore
            (after.head hafterNe).decorated := by
        rcases hlastNext with hlastNext | hlastNext
        · exact False.elim (hlastNextNe hlastNext)
        · exact hlastNext
      have hnextTerm :
          (after.head hafterNe).erasedShape = term.erasedShape ∨
            (after.head hafterNe).decorated.shapeBefore term.decorated :=
        hafterSorted.rel_head_of_rel_head_head hterm (Or.inl rfl)
      have hlastShape : (block.getLast hblockNe).erasedShape = shape :=
        hsame (block.getLast hblockNe) (List.getLast_mem hblockNe)
      have hlastTerm : (block.getLast hblockNe).erasedShape = term.erasedShape := by
        rw [hlastShape, term.erased_shape_family, htermShape']
      rcases hnextTerm with hnextTerm | hnextTerm
      · exact hlastNextNe (hlastTerm.trans hnextTerm.symm)
      · exact
          (not_before_erased hlastTerm)
            (shapeBefore_trans hlastBeforeNext hnextTerm)
    refine ⟨shape, ?_⟩
    rw [hfactors, List.filter_append, List.filter_append, hbeforeFilter,
      hblockFilter, hafterFilter]
    simp

end OESorted

end FORed
end TCTex
end Submission

-- Merged from FamilyOperationalMultiplicityTraceRoutingCompletion.lean

/-!
# Finite completion of opened full multiplicity-routing states

Every pending slot of a full heterogeneous multiplicity worklist still
remembers one concrete Cartesian parent pair.  Consequently, the arithmetic
worklist drain lifts to a concrete routed drain: any already-opened routing
state extends through finitely many routed corrections to a closed state.

This isolates the remaining global recollection problem.  It is enough to
open the correct Cartesian batches; once opened, their concrete exhaustion is
automatic.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace MTRoute

open HACoeff
open IMWork

namespace MRStatea

/-- Every arithmetic full-worklist emission lifts to one concrete routed correction. -/
lemma route_worklist_step
    {M N K : ℕ}
    (state : MRStatea M N K)
    {nextWorklist : MBWork M N K}
    (hstep :
      MBWork.Step state.worklist nextWorklist) :
    ∃ next : MRStatea M N K,
      next.worklist = nextWorklist ∧
        next.worklist.pendingSlots < state.worklist.pendingSlots := by
  generalize hworklist : state.worklist = worklist at hstep
  cases hstep with
  | emit pre post item before term after hpending =>
      have hterm : term ∈ item.ledger.pending := by
        rw [hpending]
        simp
      rcases item.ledger.parent_terms_pending hterm with
        ⟨leftTerm, hleft, rightTerm, hright, htermEq⟩
      subst term
      let emission : MBEmissi item := {
        emission := {
          leftTerm := leftTerm
          rightTerm := rightTerm
          left_mem := hleft
          right_mem := hright
          pendingPrefix := before
          pendingSuffix := after
          pending_eq := hpending } }
      let next := state.route pre post item hworklist emission
      refine ⟨next, ?_, ?_⟩
      · simp [next, route, MBEmissi.emitItem,
          emission]
      simpa [next, hworklist] using state.pending_slots_route
        pre post item hworklist emission

/-- Every nonclosed full routing state admits one concrete routed step. -/
lemma route_not_closed
    {M N K : ℕ}
    (state : MRStatea M N K)
    (hclosed : ¬ state.worklist.Closed) :
    ∃ next : MRStatea M N K,
      next.worklist.pendingSlots < state.worklist.pendingSlots := by
  rcases MBWork.step_not_closed
      state.worklist hclosed with
    ⟨nextWorklist, hstep⟩
  rcases state.route_worklist_step hstep with
    ⟨next, _hworklist, hlt⟩
  exact ⟨next, hlt⟩

/--
Any already-opened full routing state extends through finitely many concrete
emissions to a closed state, preserving its routed operational prefix.
-/
lemma exists_closedExtension
    {M N K : ℕ}
    (state : MRStatea M N K) :
    ∃ final : MRStatea M N K,
      final.worklist.Closed ∧
        state.routedTerms <+: final.routedTerms := by
  by_cases hclosed : state.worklist.Closed
  · exact ⟨state, hclosed, List.prefix_rfl⟩
  · simp only [MBWork.Closed, not_forall] at hclosed
    rcases hclosed with ⟨item, hitem, hopen⟩
    rcases List.mem_iff_append.mp hitem with ⟨pre, post, hworklist⟩
    simp only [MWItem.Closed] at hopen
    cases hpending : item.ledger.pending with
    | nil =>
        exact False.elim (hopen hpending)
    | cons term after =>
        have hterm : term ∈ item.ledger.pending := by
          rw [hpending]
          simp
        rcases item.ledger.parent_terms_pending hterm with
          ⟨leftTerm, hleft, rightTerm, hright, htermEq⟩
        subst term
        let emission : MBEmissi item :=
          MBEmissi.ofMemPending
            item leftTerm rightTerm hleft hright hterm
        let next := state.route pre post item hworklist emission
        rcases exists_closedExtension next with
          ⟨final, hfinalClosed, hprefix⟩
        refine ⟨final, hfinalClosed, ?_⟩
        apply (List.prefix_append state.routedTerms
          [leftTerm.correction rightTerm]).trans
        simpa [next, route] using hprefix
termination_by state.worklist.pendingSlots
decreasing_by
  exact state.pending_slots_route pre post item hworklist emission

end MRStatea

end MTRoute
end TCTex
end Submission

-- Merged from FamilyOperationalRepresented.lean

/-!
# Represented correction routing for operational Hall collection

The truncated router can consume one selected correction slot once exact
inventories for both parent terms are known.  This file constructs those
parent inventories compositionally.

An inverse-raw occurrence starts with the exact raw inventory filtered to its
represented one-block family.  A generated correction then carries the full
Cartesian correction grid of its two represented parent inventories.  Thus a
retained concrete More3 obstruction can open the complete licensed grid and
route its selected occurrence without treating a singleton occurrence as a
complete family packet.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace RCRoutea

open HACoeff
open FIFilter.MIBlock
open IMPropag
open OCClos
open OCPartit
open TMRoutea
open RHRecipe

/--
One concrete decorated-family occurrence together with an exact inventory
block containing its realization slot.
-/
structure RTInv
    {M N K : ℕ}
    (term : DFTerm M N K) where
  terms :
    List (DFTerm M N K)
  inventory :
    MIBlock terms
  term_mem :
    term ∈ terms

namespace RTInv

/--
Initialize one inverse-raw occurrence with the complete exact inventory of its
represented one-block family.
-/
noncomputable def ofInverseRaw
    {M N : ℕ}
    {term : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hterm : term ∈ inverseDecoratedTerms M N) :
    RTInv term := by
  classical
  exact {
    terms :=
      (inverseDecoratedTerms M N).filter fun candidate =>
        decide (candidate.family = term.family)
    inventory :=
      FIFilter.MIBlock.filterFamilies
        (MIBlock.inverseRaw M N) fun family =>
          family = term.family
    term_mem := by
      simp [hterm] }

/--
Pairwise correction of represented terms carries the complete Cartesian grid
of both represented parent inventories.
-/
noncomputable def correction
    {M N K : ℕ}
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm) :
    RTInv (leftTerm.correction rightTerm) where
  terms :=
    HSPacket.DFTerm.correctionGrid
      left.terms right.terms
  inventory :=
    left.inventory.correctionGrid right.inventory
  term_mem := by
    apply List.mem_flatMap.mpr
    exact
      ⟨leftTerm, left.term_mem,
        List.mem_map.mpr ⟨rightTerm, right.term_mem, rfl⟩⟩

/-- The represented occurrence belongs to one retained family of its inventory. -/
lemma term_family_mem
    {M N K : ℕ}
    {term : DFTerm M N K}
    (represented : RTInv term) :
    term.family ∈ represented.inventory.families :=
  represented.inventory.family_mem represented.term_mem

/--
Every finite correction tree whose leaves have represented inventories has a
represented inventory at its root.
-/
lemma nonempty_correction_generated
    {M N K : ℕ}
    {source : List (DFTerm M N K)}
    (hsource :
      ∀ sourceTerm ∈ source,
        Nonempty (RTInv sourceTerm))
    {term : DFTerm M N K}
    (hterm : DFTerm.CGFrom source term) :
    Nonempty (RTInv term) := by
  induction hterm with
  | source hmem =>
      exact hsource _ hmem
  | correction _ _ ihleft ihright =>
      rcases ihleft with ⟨left⟩
      rcases ihright with ⟨right⟩
      exact ⟨left.correction right⟩

/--
Every term generated from the inverse raw trace has a recursively constructed
exact represented inventory.
-/
lemma nonempty_generated_raw
    {M N : ℕ}
    {term : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hterm :
      DFTerm.CGFrom
        (inverseDecoratedTerms M N) term) :
    Nonempty (RTInv term) := by
  apply nonempty_correction_generated
    (source := inverseDecoratedTerms M N) _ hterm
  intro sourceTerm hsourceTerm
  exact ⟨ofInverseRaw hsourceTerm⟩

/-- Choose the recursively constructed represented inventory of one generated term. -/
noncomputable def correctionGeneratedRaw
    {M N : ℕ}
    {term : DFTerm M N
      (inverseLabelledCollection M N).factors.length}
    (hterm :
      DFTerm.CGFrom
        (inverseDecoratedTerms M N) term) :
    RTInv term :=
  Classical.choice (nonempty_generated_raw hterm)

end RTInv

namespace MRState

/--
Open the complete filtered Cartesian grid licensed by two represented parent
inventories and route their selected retained correction occurrence.
-/
noncomputable def batchRouteRepresented
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
          (leftTerm.correction rightTerm) < n) :
    MRState
      M N K n leftWeight rightWeight :=
  state.openBatchRoute
    left.inventory right.inventory leftTerm rightTerm
    left.term_mem right.term_mem hweight

@[simp]
lemma routed_batch_represented
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
          (leftTerm.correction rightTerm) < n) :
    (batchRouteRepresented state left right hweight).routedTerms =
      state.routedTerms ++ [leftTerm.correction rightTerm] :=
  rfl

end MRState

end RCRoutea
end TCTex
end Submission

/-!
# Reuse-first represented correction routing

The first represented-routing prototype opens a fresh filtered Cartesian batch
for every retained concrete correction occurrence.  A global scheduler instead
has to consume an already-open matching slot whenever one exists, opening a
new represented batch only when no existing pending slot can route the
occurrence.

This file adds that local state transition.  It intentionally does not claim
the global closure theorem: closure still requires proving that the
reuse-first traversal of the operational trace exhausts every opened grid.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace CRRouted

open HACoeff
open IMPropag
open OCPartit
open RCRoutea
open TMWork
open TMRoutea
open RCRoutea.MRState

namespace MRState

/--
One already-open truncated worklist item whose pending grid can route the
specified concrete correction occurrence.
-/
structure EPRoute
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    (leftTerm rightTerm : DFTerm M N K) where
  pre :
    TBWork M N K n leftWeight rightWeight
  post :
    TBWork M N K n leftWeight rightWeight
  item :
    TWItem M N K n leftWeight rightWeight
  worklist_eq :
    state.worklist = pre ++ item :: post
  left_mem :
    leftTerm ∈ item.leftTerms
  right_mem :
    rightTerm ∈ item.rightTerms
  correction_mem_pending :
    leftTerm.correction rightTerm ∈ item.ledger.pending

namespace EPRoute

/-- Consume the selected correction occurrence from its already-open batch. -/
noncomputable def consume
    {M N K n leftWeight rightWeight : ℕ}
    {state :
      MRState
        M N K n leftWeight rightWeight}
    {leftTerm rightTerm : DFTerm M N K}
    (route : EPRoute state leftTerm rightTerm) :
    MRState
      M N K n leftWeight rightWeight :=
  state.route route.pre route.post route.item route.worklist_eq
    (CBEmissia.ofMemPending
      route.item leftTerm rightTerm route.left_mem route.right_mem
      route.correction_mem_pending)

@[simp]
lemma routedTerms_consume
    {M N K n leftWeight rightWeight : ℕ}
    {state :
      MRState
        M N K n leftWeight rightWeight}
    {leftTerm rightTerm : DFTerm M N K}
    (route : EPRoute state leftTerm rightTerm) :
    route.consume.routedTerms =
      state.routedTerms ++ [leftTerm.correction rightTerm] :=
  rfl

/-- Reusing one already-open pending slot strictly decreases open-slot count. -/
lemma pendin_slots_consu
    {M N K n leftWeight rightWeight : ℕ}
    {state :
      MRState
        M N K n leftWeight rightWeight}
    {leftTerm rightTerm : DFTerm M N K}
    (route : EPRoute state leftTerm rightTerm) :
    route.consume.worklist.pendingSlots < state.worklist.pendingSlots := by
  let emission :=
    CBEmissia.ofMemPending
      route.item leftTerm rightTerm route.left_mem route.right_mem
      route.correction_mem_pending
  unfold consume
  apply TBWork.pending_slots_step
  rw [route.worklist_eq]
  exact
    TBWork.stepConcreteEmission
      route.pre route.post route.item emission

end EPRoute

/--
Route one represented correction occurrence by consuming an existing pending
slot when possible.  Only a genuinely new represented grid is opened.
-/
noncomputable def representedReusingPending
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
          (leftTerm.correction rightTerm) < n) :
    MRState
      M N K n leftWeight rightWeight := by
  classical
  exact
    if hroute :
        Nonempty (EPRoute state leftTerm rightTerm) then
      (Classical.choice hroute).consume
    else
      batchRouteRepresented state left right hweight

/-- If a compatible pending slot exists, reuse-first routing consumes it. -/
lemma represented_reusing_consume
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
          (leftTerm.correction rightTerm) < n)
    (hroute :
      Nonempty (EPRoute state leftTerm rightTerm)) :
    representedReusingPending state left right hweight =
      (Classical.choice hroute).consume := by
  classical
  simp [representedReusingPending, hroute]

/-- Without a compatible pending slot, reuse-first routing opens one grid. -/
lemma represented_reusing_nonempty
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
          (leftTerm.correction rightTerm) < n)
    (hroute :
      ¬Nonempty (EPRoute state leftTerm rightTerm)) :
    representedReusingPending state left right hweight =
      batchRouteRepresented state left right hweight := by
  classical
  simp [representedReusingPending, hroute]

/-- Reuse-first routing strictly decreases open slots whenever it reuses. -/
lemma slots_represented_reusing
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
          (leftTerm.correction rightTerm) < n)
    (hroute :
      Nonempty (EPRoute state leftTerm rightTerm)) :
    (representedReusingPending
      state left right hweight).worklist.pendingSlots <
        state.worklist.pendingSlots := by
  rw [represented_reusing_consume
    state left right hweight hroute]
  exact (Classical.choice hroute).pendin_slots_consu

@[simp]
lemma routed_represented_reusing
    {M N K n leftWeight rightWeight : ℕ}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm)
    (hweight :
      decoratedFamilyWeight leftWeight rightWeight
          (leftTerm.correction rightTerm) < n) :
    (representedReusingPending state left right hweight).routedTerms =
      state.routedTerms ++ [leftTerm.correction rightTerm] := by
  classical
  by_cases hroute :
      Nonempty (EPRoute state leftTerm rightTerm)
  · simp [representedReusingPending, hroute]
  · simp [representedReusingPending, hroute,
      routed_batch_represented]

end MRState

end CRRouted
end TCTex
end Submission

/-!
# Reuse-first routing of represented operational corrections

Each retained More3 obstruction first consumes a compatible pending slot from
an already-open represented grid.  Only an obstruction with no compatible
pending slot opens a new filtered Cartesian batch.

This file lifts that local transition through the actual insertion and
collection recurrences.  The resulting prefix is the appropriate input for
the remaining global closure theorem: unlike the earlier fresh-grid prefix,
it performs the required coalescing while the operational trace is traversed.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace RTRoute

open HACoeff
open ICFilter
open ICFilter.CCPartit
open IMPropag
open OCClos
open OCPartit
open OEAccoun
open FMEnd
open CRRouted
open RCRoutea
open TMRoutea

namespace FInsert.ECorrec

/--
Route every retained correction occurrence emitted by one insertion, reusing
matching pending represented-grid slots whenever possible.
-/
lemma route_retained_reuse
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {hinsert : DFTerm.IInsert L A R}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    (hemits : FInsert.ECorrec hinsert corrections)
    (hrepresented :
      ∀ term ∈ L ++ [A],
        Nonempty (RTInv term)) :
    ∃ final :
        MRState
          M N K n leftWeight rightWeight,
      final.routedTerms =
        state.routedTerms ++
          belowCutoffTerms n leftWeight rightWeight corrections := by
  induction hemits generalizing state with
  | nil A =>
      exact ⟨state, by simp [belowCutoffTerms]⟩
  | append P B A hAB =>
      exact ⟨state, by simp [belowCutoffTerms]⟩
  | @obstruction P B A hAB Q R hcorrection hinsert
      correctionTerms insertTerms hcorrectionTerms hinsertTerms
      ihcorrection ihinsert =>
      have hB : Nonempty (RTInv B) :=
        hrepresented B (by simp)
      have hA : Nonempty (RTInv A) :=
        hrepresented A (by simp)
      rcases hB with ⟨left⟩
      rcases hA with ⟨right⟩
      have hBA : Nonempty (RTInv (B.correction A)) :=
        ⟨left.correction right⟩
      have hcorrectionRepresented :
          ∀ term ∈ P ++ [B.correction A],
            Nonempty (RTInv term) := by
        intro term hterm
        rcases List.mem_append.mp hterm with hterm | hterm
        · exact hrepresented term (by simp [hterm])
        · rcases List.mem_singleton.mp hterm with rfl
          exact hBA
      have hQRepresented :
          ∀ term ∈ Q,
            Nonempty (RTInv term) := by
        intro term hterm
        exact
          RTInv.nonempty_correction_generated
            hcorrectionRepresented
            (FInsert.ECorrec.result_corre_gener
              hcorrectionTerms term hterm)
      have hinsertRepresented :
          ∀ term ∈ Q ++ [A],
            Nonempty (RTInv term) := by
        intro term hterm
        rcases List.mem_append.mp hterm with hterm | hterm
        · exact hQRepresented term hterm
        · rcases List.mem_singleton.mp hterm with rfl
          exact ⟨right⟩
      by_cases hweight :
          decoratedFamilyWeight leftWeight rightWeight
              (B.correction A) < n
      · let root :=
          MRState.representedReusingPending
            state left right hweight
        rcases ihcorrection root hcorrectionRepresented with
          ⟨afterCorrection, hafterCorrection⟩
        rcases ihinsert afterCorrection hinsertRepresented with
          ⟨afterInsert, hafterInsert⟩
        refine ⟨afterInsert, ?_⟩
        rw [hafterInsert, hafterCorrection]
        simp [root, belowCutoffTerms, hweight, List.filter_append,
          List.append_assoc]
      · rcases ihcorrection state hcorrectionRepresented with
          ⟨afterCorrection, hafterCorrection⟩
        rcases ihinsert afterCorrection hinsertRepresented with
          ⟨afterInsert, hafterInsert⟩
        refine ⟨afterInsert, ?_⟩
        rw [hafterInsert, hafterCorrection]
        simp [belowCutoffTerms, hweight, List.filter_append,
          List.append_assoc]

end FInsert.ECorrec

namespace FCollec.ECorrec

/--
Route every retained correction occurrence emitted by one complete
collection derivation, reusing compatible pending represented-grid slots.
-/
lemma route_retained_reuse
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {hcollect : DFTerm.ICollec L R}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    (hemits : FCollec.ECorrec hcollect corrections)
    (hrepresented :
      ∀ term ∈ L,
        Nonempty (RTInv term)) :
    ∃ final :
        MRState
          M N K n leftWeight rightWeight,
      final.routedTerms =
        state.routedTerms ++
          belowCutoffTerms n leftWeight rightWeight corrections := by
  induction hemits generalizing state with
  | nil =>
      exact ⟨state, by simp [belowCutoffTerms]⟩
  | @snoc P A C R hcollect hinsert collectTerms insertTerms
      hcollectTerms hinsertTerms ihcollect =>
      have hPRepresented :
          ∀ term ∈ P,
            Nonempty (RTInv term) := by
        intro term hterm
        exact hrepresented term (by simp [hterm])
      rcases ihcollect state hPRepresented with
        ⟨afterCollect, hafterCollect⟩
      have hCRepresented :
          ∀ term ∈ C,
            Nonempty (RTInv term) := by
        intro term hterm
        exact
          RTInv.nonempty_correction_generated
            hPRepresented
            (FCollec.ECorrec.result_corre_gener
              hcollectTerms term hterm)
      have hARepresented : Nonempty (RTInv A) :=
        hrepresented A (by simp)
      have hinsertRepresented :
          ∀ term ∈ C ++ [A],
            Nonempty (RTInv term) := by
        intro term hterm
        rcases List.mem_append.mp hterm with hterm | hterm
        · exact hCRepresented term hterm
        · rcases List.mem_singleton.mp hterm with rfl
          exact hARepresented
      rcases
          FInsert.ECorrec.route_retained_reuse
            afterCollect hinsertTerms hinsertRepresented with
        ⟨afterInsert, hafterInsert⟩
      refine ⟨afterInsert, ?_⟩
      rw [hafterInsert, hafterCollect]
      simp [belowCutoffTerms, List.filter_append, List.append_assoc]

end FCollec.ECorrec

/--
The reuse-first retained routing prefix of one operational cutoff partition.
Its routed terms are exactly the retained partition up to permutation.
-/
structure RRRoute
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint
        n leftWeight rightWeight) where
  state :
    MRState M N
      (inverseLabelledCollection M N).factors.length
      n leftWeight rightWeight
  routed_perm :
    List.Perm state.routedTerms partition.retained

/-- Construct the reuse-first prefix directly from the More3 trace. -/
noncomputable def representedReuseRouting
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint
        n leftWeight rightWeight) :
    RRRoute partition := by
  let initial :=
    MRState.nil M N
      (inverseLabelledCollection M N).factors.length
      n leftWeight rightWeight
  let routed :=
    FCollec.ECorrec.route_retained_reuse
      initial endpoint.emits
      (fun _term hterm =>
        ⟨RTInv.ofInverseRaw hterm⟩)
  let state := Classical.choose routed
  have hrouted := Classical.choose_spec routed
  exact {
    state := state
    routed_perm := by
      rw [hrouted]
      simpa [initial, MRState.nil] using
        belowTermsPerm partition }

namespace RRRoute

/--
If the reuse-first prefix is closed, its retained terms carry the exact
multiplicity inventory required by polynomial compression.
-/
noncomputable def retainedInventoryClosed
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    {partition :
      CCPartit endpoint
        n leftWeight rightWeight}
    (routing : RRRoute partition)
    (hclosed : routing.state.worklist.Closed) :
    MIBlock partition.retained :=
  (routing.state.closedInventoryBlock hclosed).permTerms routing.routed_perm

end RRRoute

end RTRoute
end TCTex
end Submission

/-!
# Reuse-first represented-grid closure boundary

The operational trace now consumes an already-open matching represented slot
before opening a new filtered Cartesian batch.  The remaining global
combinatorial theorem is that this reuse-first traversal exhausts every batch
it opens.

This file packages that precise closure boundary and proves its downstream
retained-inventory consumers.  It intentionally does not assume closure of the
older fresh-grid routing prototype.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace RRGrid

open IMPropag
open OCPartit
open FMEnd
open RTRoute
open TMPlanni
open TMRoutea

/--
Global reuse-first represented-grid closure law: after traversing every
retained operational correction, every opened filtered grid is exhausted.
-/
structure ORReuse : Prop where
  closed :
    ∀ {M N n leftWeight rightWeight : ℕ}
      {endpoint : ODEmissi M N}
      (partition :
        CCPartit endpoint
          n leftWeight rightWeight),
      (representedReuseRouting
        partition).state.worklist.Closed

namespace ORReuse

/--
Reuse-first represented-grid closure constructs an exact retained correction
router at every nilpotent cutoff.
-/
noncomputable def truncMultRouting
    (kernel : ORReuse)
    (n leftWeight rightWeight : ℕ) :
    OMRoute
      n leftWeight rightWeight where
  route endpoint partition := by
    let routingPrefix :=
      representedReuseRouting partition
    let routedState :=
      MRState.permRoutedTerms
        routingPrefix.state routingPrefix.routed_perm
    refine ⟨routedState, ?_, ?_⟩
    · simpa [routedState] using kernel.closed partition
    · rfl

/--
Reuse-first represented-grid closure supplies the exact retained inventory
consumed by cutoff-level symbolic compression.
-/
noncomputable def retainedInventory
    (kernel : ORReuse)
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint
        n leftWeight rightWeight) :
    MIBlock partition.retained :=
  Classical.choice <|
    (kernel.truncMultRouting
      n leftWeight rightWeight).nonempty_retainedInventory partition

end ORReuse

end RRGrid
end TCTex
end Submission

/-!
# Open-prefix routing of represented operational corrections

Each actual More3 obstruction emits one concrete pairwise correction.  The
represented-inventory constructor attaches complete parent packets to both
parents, opens their filtered Cartesian grid, and consumes the selected
retained slot.

This file lifts that local operation through the genuine
`IInsert` and `ICollec` emission recurrences.  The
result is an exact open routing prefix for every retained operational
correction occurrence.  Fresh grids are intentionally not coalesced here:
proving that the remaining pending slots can be identified with later
operational occurrences is the subsequent packet-closure theorem.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace ORRoute

open HACoeff
open ICFilter
open ICFilter.CCPartit
open IMPropag
open OCClos
open OCPartit
open OEAccoun
open FMEnd
open RCRoutea
open TMRoutea

namespace FInsert.ECorrec

/--
Route every retained correction occurrence emitted by one actual insertion.
The resulting open worklist may still contain slots of complete represented
grids that have not yet appeared in the operational trace.
-/
lemma route_retained_prefix
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {hinsert : DFTerm.IInsert L A R}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    (hemits : FInsert.ECorrec hinsert corrections)
    (hrepresented :
      ∀ term ∈ L ++ [A],
        Nonempty (RTInv term)) :
    ∃ final :
        MRState
          M N K n leftWeight rightWeight,
      final.routedTerms =
        state.routedTerms ++
          belowCutoffTerms n leftWeight rightWeight corrections := by
  induction hemits generalizing state with
  | nil A =>
      exact ⟨state, by simp [belowCutoffTerms]⟩
  | append P B A hAB =>
      exact ⟨state, by simp [belowCutoffTerms]⟩
  | @obstruction P B A hAB Q R hcorrection hinsert
      correctionTerms insertTerms hcorrectionTerms hinsertTerms
      ihcorrection ihinsert =>
      have hB : Nonempty (RTInv B) :=
        hrepresented B (by simp)
      have hA : Nonempty (RTInv A) :=
        hrepresented A (by simp)
      rcases hB with ⟨left⟩
      rcases hA with ⟨right⟩
      have hBA : Nonempty (RTInv (B.correction A)) :=
        ⟨left.correction right⟩
      have hcorrectionRepresented :
          ∀ term ∈ P ++ [B.correction A],
            Nonempty (RTInv term) := by
        intro term hterm
        rcases List.mem_append.mp hterm with hterm | hterm
        · exact hrepresented term (by simp [hterm])
        · rcases List.mem_singleton.mp hterm with rfl
          exact hBA
      have hQRepresented :
          ∀ term ∈ Q,
            Nonempty (RTInv term) := by
        intro term hterm
        exact
          RTInv.nonempty_correction_generated
            hcorrectionRepresented
            (FInsert.ECorrec.result_corre_gener
              hcorrectionTerms term hterm)
      have hinsertRepresented :
          ∀ term ∈ Q ++ [A],
            Nonempty (RTInv term) := by
        intro term hterm
        rcases List.mem_append.mp hterm with hterm | hterm
        · exact hQRepresented term hterm
        · rcases List.mem_singleton.mp hterm with rfl
          exact ⟨right⟩
      by_cases hweight :
          decoratedFamilyWeight leftWeight rightWeight
              (B.correction A) < n
      · let root :=
          MRState.batchRouteRepresented
            state left right hweight
        rcases ihcorrection root hcorrectionRepresented with
          ⟨afterCorrection, hafterCorrection⟩
        rcases ihinsert afterCorrection hinsertRepresented with
          ⟨afterInsert, hafterInsert⟩
        refine ⟨afterInsert, ?_⟩
        rw [hafterInsert, hafterCorrection]
        simp [root, belowCutoffTerms, hweight, List.filter_append,
          List.append_assoc]
      · rcases ihcorrection state hcorrectionRepresented with
          ⟨afterCorrection, hafterCorrection⟩
        rcases ihinsert afterCorrection hinsertRepresented with
          ⟨afterInsert, hafterInsert⟩
        refine ⟨afterInsert, ?_⟩
        rw [hafterInsert, hafterCorrection]
        simp [belowCutoffTerms, hweight, List.filter_append,
          List.append_assoc]

end FInsert.ECorrec

namespace FCollec.ECorrec

/--
Route every retained correction occurrence emitted by one actual complete
collection derivation.
-/
lemma route_retained_prefix
    {M N K n leftWeight rightWeight : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {hcollect : DFTerm.ICollec L R}
    (state :
      MRState
        M N K n leftWeight rightWeight)
    (hemits : FCollec.ECorrec hcollect corrections)
    (hrepresented :
      ∀ term ∈ L,
        Nonempty (RTInv term)) :
    ∃ final :
        MRState
          M N K n leftWeight rightWeight,
      final.routedTerms =
        state.routedTerms ++
          belowCutoffTerms n leftWeight rightWeight corrections := by
  induction hemits generalizing state with
  | nil =>
      exact ⟨state, by simp [belowCutoffTerms]⟩
  | @snoc P A C R hcollect hinsert collectTerms insertTerms
      hcollectTerms hinsertTerms ihcollect =>
      have hPRepresented :
          ∀ term ∈ P,
            Nonempty (RTInv term) := by
        intro term hterm
        exact hrepresented term (by simp [hterm])
      rcases ihcollect state hPRepresented with
        ⟨afterCollect, hafterCollect⟩
      have hCRepresented :
          ∀ term ∈ C,
            Nonempty (RTInv term) := by
        intro term hterm
        exact
          RTInv.nonempty_correction_generated
            hPRepresented
            (FCollec.ECorrec.result_corre_gener
              hcollectTerms term hterm)
      have hARepresented : Nonempty (RTInv A) :=
        hrepresented A (by simp)
      have hinsertRepresented :
          ∀ term ∈ C ++ [A],
            Nonempty (RTInv term) := by
        intro term hterm
        rcases List.mem_append.mp hterm with hterm | hterm
        · exact hCRepresented term hterm
        · rcases List.mem_singleton.mp hterm with rfl
          exact hARepresented
      rcases
          FInsert.ECorrec.route_retained_prefix
            afterCollect hinsertTerms hinsertRepresented with
        ⟨afterInsert, hafterInsert⟩
      refine ⟨afterInsert, ?_⟩
      rw [hafterInsert, hafterCollect]
      simp [belowCutoffTerms, List.filter_append, List.append_assoc]

end FCollec.ECorrec

/--
One sound open routing prefix for the retained side of an operational cutoff
partition.  Its routed concrete terms are exactly the retained partition up to
permutation.  Closure of the open represented grids is a separate theorem.
-/
structure RRPrefix
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint
        n leftWeight rightWeight) where
  state :
    MRState M N
      (inverseLabelledCollection M N).factors.length
      n leftWeight rightWeight
  routed_perm :
    List.Perm state.routedTerms partition.retained

/-- Construct the sound retained routing prefix directly from the More3 trace. -/
noncomputable def representedRoutingPrefix
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint
        n leftWeight rightWeight) :
    RRPrefix partition := by
  let initial :=
    MRState.nil M N
      (inverseLabelledCollection M N).factors.length
      n leftWeight rightWeight
  let routed :=
    FCollec.ECorrec.route_retained_prefix
      initial endpoint.emits
      (fun _term hterm =>
        ⟨RTInv.ofInverseRaw hterm⟩)
  let state := Classical.choose routed
  have hrouted := Classical.choose_spec routed
  exact {
    state := state
    routed_perm := by
      rw [hrouted]
      simpa [initial, MRState.nil] using
        belowTermsPerm partition }

namespace RRPrefix

/--
If grid coalescing closes the sound open prefix, its routed retained terms
already carry the exact multiplicity inventory required by polynomial
compression.
-/
noncomputable def retainedInventoryClosed
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    {partition :
      CCPartit endpoint
        n leftWeight rightWeight}
    (routing : RRPrefix partition)
    (hclosed : routing.state.worklist.Closed) :
    MIBlock partition.retained :=
  (routing.state.closedInventoryBlock hclosed).permTerms routing.routed_perm

end RRPrefix

end ORRoute
end TCTex
end Submission

/-!
# Full-grid reuse-first represented correction routing

The natural scheduler should route complete represented Cartesian correction
grids before any nilpotent cutoff is imposed.  Filtering a closed full-grid
schedule then gives every truncated schedule through the existing adapters.

This file adds the full-grid analogue of reuse-first represented routing:
consume a compatible already-open pending slot whenever possible and open a
new represented grid only when no such slot exists.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace FRRoutea

open HACoeff
open IMWork
open IMPropag
open MTRoute
open RCRoutea
open HSPacket

namespace MRStatea

/--
One already-open full worklist item whose pending grid can route the specified
concrete correction occurrence.
-/
structure EPRoute
    {M N K : ℕ}
    (state : MRStatea M N K)
    (leftTerm rightTerm : DFTerm M N K) where
  pre :
    MBWork M N K
  post :
    MBWork M N K
  item :
    MWItem M N K
  worklist_eq :
    state.worklist = pre ++ item :: post
  left_mem :
    leftTerm ∈ item.leftTerms
  right_mem :
    rightTerm ∈ item.rightTerms
  correction_mem_pending :
    leftTerm.correction rightTerm ∈ item.ledger.pending

namespace EPRoute

/-- Consume the selected correction occurrence from its already-open batch. -/
noncomputable def consume
    {M N K : ℕ}
    {state : MRStatea M N K}
    {leftTerm rightTerm : DFTerm M N K}
    (route : EPRoute state leftTerm rightTerm) :
    MRStatea M N K :=
  state.route route.pre route.post route.item route.worklist_eq
    (MBEmissi.ofMemPending
      route.item leftTerm rightTerm route.left_mem route.right_mem
      route.correction_mem_pending)

@[simp]
lemma routedTerms_consume
    {M N K : ℕ}
    {state : MRStatea M N K}
    {leftTerm rightTerm : DFTerm M N K}
    (route : EPRoute state leftTerm rightTerm) :
    route.consume.routedTerms =
      state.routedTerms ++ [leftTerm.correction rightTerm] :=
  rfl

/-- Reusing one already-open pending slot strictly decreases open-slot count. -/
lemma pendin_slots_consu
    {M N K : ℕ}
    {state : MRStatea M N K}
    {leftTerm rightTerm : DFTerm M N K}
    (route : EPRoute state leftTerm rightTerm) :
    route.consume.worklist.pendingSlots < state.worklist.pendingSlots := by
  let emission :=
    MBEmissi.ofMemPending
      route.item leftTerm rightTerm route.left_mem route.right_mem
      route.correction_mem_pending
  unfold consume
  exact state.pending_slots_route
    route.pre route.post route.item route.worklist_eq emission

end EPRoute

/--
The selected represented parent pair belongs to the freshly opened complete
Cartesian grid.
-/
lemma represented_initial_pending
    {M N K : ℕ}
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm) :
    leftTerm.correction rightTerm ∈
      (MWItem.initial
        left.inventory right.inventory).ledger.pending := by
  change leftTerm.correction rightTerm ∈
    DFTerm.correctionGrid left.terms right.terms
  apply List.mem_flatMap.mpr
  exact
    ⟨leftTerm, left.term_mem,
      List.mem_map.mpr ⟨rightTerm, right.term_mem, rfl⟩⟩

/-- Open one complete represented grid and route its selected occurrence. -/
noncomputable def batchRouteRepresented
    {M N K : ℕ}
    (state : MRStatea M N K)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm) :
    MRStatea M N K :=
  state.batchRoute left.inventory right.inventory
    (MBEmissi.ofMemPending
      (MWItem.initial left.inventory right.inventory)
      leftTerm rightTerm left.term_mem right.term_mem
      (represented_initial_pending left right))

@[simp]
lemma routed_batch_represented
    {M N K : ℕ}
    (state : MRStatea M N K)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm) :
    (batchRouteRepresented state left right).routedTerms =
      state.routedTerms ++ [leftTerm.correction rightTerm] :=
  rfl

/--
Route one represented correction occurrence by consuming an existing pending
slot when possible.  Only a genuinely new represented grid is opened.
-/
noncomputable def representedReusingPending
    {M N K : ℕ}
    (state : MRStatea M N K)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm) :
    MRStatea M N K := by
  classical
  exact
    if hroute :
        Nonempty (EPRoute state leftTerm rightTerm) then
      (Classical.choice hroute).consume
    else
      batchRouteRepresented state left right

/-- If a compatible pending slot exists, reuse-first routing consumes it. -/
lemma represented_reusing_consume
    {M N K : ℕ}
    (state : MRStatea M N K)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm)
    (hroute :
      Nonempty (EPRoute state leftTerm rightTerm)) :
    representedReusingPending state left right =
      (Classical.choice hroute).consume := by
  classical
  simp [representedReusingPending, hroute]

/-- Without a compatible pending slot, reuse-first routing opens one grid. -/
lemma represented_reusing_nonempty
    {M N K : ℕ}
    (state : MRStatea M N K)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm)
    (hroute :
      ¬Nonempty (EPRoute state leftTerm rightTerm)) :
    representedReusingPending state left right =
      batchRouteRepresented state left right := by
  classical
  simp [representedReusingPending, hroute]

/-- Reuse-first routing strictly decreases open slots whenever it reuses. -/
lemma slots_represented_reusing
    {M N K : ℕ}
    (state : MRStatea M N K)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm)
    (hroute :
      Nonempty (EPRoute state leftTerm rightTerm)) :
    (representedReusingPending
      state left right).worklist.pendingSlots <
        state.worklist.pendingSlots := by
  rw [represented_reusing_consume
    state left right hroute]
  exact (Classical.choice hroute).pendin_slots_consu

@[simp]
lemma routed_represented_reusing
    {M N K : ℕ}
    (state : MRStatea M N K)
    {leftTerm rightTerm : DFTerm M N K}
    (left : RTInv leftTerm)
    (right : RTInv rightTerm) :
    (representedReusingPending state left right).routedTerms =
      state.routedTerms ++ [leftTerm.correction rightTerm] := by
  classical
  by_cases hroute :
      Nonempty (EPRoute state leftTerm rightTerm)
  · simp [representedReusingPending, hroute]
  · simp [representedReusingPending, hroute]

end MRStatea

end FRRoutea
end TCTex
end Submission

/-!
# Full-grid reuse-first routing of represented operational corrections

Every actual More3 obstruction emits one concrete correction.  This file
traverses that genuine operational recurrence while consuming an already-open
matching represented-grid slot whenever possible.  A fresh complete Cartesian
grid is opened only as a fallback.

The resulting full-grid prefix routes the emitted-correction list exactly.
The remaining scheduler theorem is that every batch opened by this traversal
is exhausted when the operational trace ends.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace RTRoutea

open HACoeff
open OCClos
open OEAccoun
open FMEnd
open MTRoute
open RCRoutea
open FRRoutea

namespace FInsert.ECorrec

/--
Route every correction occurrence emitted by one actual insertion, reusing
matching pending represented-grid slots whenever possible.
-/
lemma route_reuse
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {A : DFTerm M N K}
    {hinsert : DFTerm.IInsert L A R}
    (state : MRStatea M N K)
    (hemits : FInsert.ECorrec hinsert corrections)
    (hrepresented :
      ∀ term ∈ L ++ [A],
        Nonempty (RTInv term)) :
    ∃ final : MRStatea M N K,
      final.routedTerms = state.routedTerms ++ corrections := by
  induction hemits generalizing state with
  | nil A =>
      exact ⟨state, by simp⟩
  | append P B A hAB =>
      exact ⟨state, by simp⟩
  | @obstruction P B A hAB Q R hcorrection hinsert
      correctionTerms insertTerms hcorrectionTerms hinsertTerms
      ihcorrection ihinsert =>
      have hB : Nonempty (RTInv B) :=
        hrepresented B (by simp)
      have hA : Nonempty (RTInv A) :=
        hrepresented A (by simp)
      rcases hB with ⟨left⟩
      rcases hA with ⟨right⟩
      have hBA : Nonempty (RTInv (B.correction A)) :=
        ⟨left.correction right⟩
      have hcorrectionRepresented :
          ∀ term ∈ P ++ [B.correction A],
            Nonempty (RTInv term) := by
        intro term hterm
        rcases List.mem_append.mp hterm with hterm | hterm
        · exact hrepresented term (by simp [hterm])
        · rcases List.mem_singleton.mp hterm with rfl
          exact hBA
      have hQRepresented :
          ∀ term ∈ Q,
            Nonempty (RTInv term) := by
        intro term hterm
        exact
          RTInv.nonempty_correction_generated
            hcorrectionRepresented
            (FInsert.ECorrec.result_corre_gener
              hcorrectionTerms term hterm)
      have hinsertRepresented :
          ∀ term ∈ Q ++ [A],
            Nonempty (RTInv term) := by
        intro term hterm
        rcases List.mem_append.mp hterm with hterm | hterm
        · exact hQRepresented term hterm
        · rcases List.mem_singleton.mp hterm with rfl
          exact ⟨right⟩
      let root :=
        MRStatea.representedReusingPending
          state left right
      rcases ihcorrection root hcorrectionRepresented with
        ⟨afterCorrection, hafterCorrection⟩
      rcases ihinsert afterCorrection hinsertRepresented with
        ⟨afterInsert, hafterInsert⟩
      refine ⟨afterInsert, ?_⟩
      rw [hafterInsert, hafterCorrection]
      simp [root, List.append_assoc]

end FInsert.ECorrec

namespace FCollec.ECorrec

/--
Route every correction occurrence emitted by one complete collection
derivation, reusing matching pending represented-grid slots whenever possible.
-/
lemma route_reuse
    {M N K : ℕ}
    {L R corrections : List (DFTerm M N K)}
    {hcollect : DFTerm.ICollec L R}
    (state : MRStatea M N K)
    (hemits : FCollec.ECorrec hcollect corrections)
    (hrepresented :
      ∀ term ∈ L,
        Nonempty (RTInv term)) :
    ∃ final : MRStatea M N K,
      final.routedTerms = state.routedTerms ++ corrections := by
  induction hemits generalizing state with
  | nil =>
      exact ⟨state, by simp⟩
  | @snoc P A C R hcollect hinsert collectTerms insertTerms
      hcollectTerms hinsertTerms ihcollect =>
      have hPRepresented :
          ∀ term ∈ P,
            Nonempty (RTInv term) := by
        intro term hterm
        exact hrepresented term (by simp [hterm])
      rcases ihcollect state hPRepresented with
        ⟨afterCollect, hafterCollect⟩
      have hCRepresented :
          ∀ term ∈ C,
            Nonempty (RTInv term) := by
        intro term hterm
        exact
          RTInv.nonempty_correction_generated
            hPRepresented
            (FCollec.ECorrec.result_corre_gener
              hcollectTerms term hterm)
      have hARepresented : Nonempty (RTInv A) :=
        hrepresented A (by simp)
      have hinsertRepresented :
          ∀ term ∈ C ++ [A],
            Nonempty (RTInv term) := by
        intro term hterm
        rcases List.mem_append.mp hterm with hterm | hterm
        · exact hCRepresented term hterm
        · rcases List.mem_singleton.mp hterm with rfl
          exact hARepresented
      rcases
          FInsert.ECorrec.route_reuse
            afterCollect hinsertTerms hinsertRepresented with
        ⟨afterInsert, hafterInsert⟩
      refine ⟨afterInsert, ?_⟩
      rw [hafterInsert, hafterCollect]
      simp [List.append_assoc]

end FCollec.ECorrec

/--
The full-grid reuse-first routing prefix of one operational emitted-correction
endpoint.
-/
structure RepresentedReusePrefix
    {M N : ℕ}
    (endpoint : ODEmissi M N) where
  state :
    MRStatea M N
      (inverseLabelledCollection M N).factors.length
  routed_eq :
    state.routedTerms = endpoint.corrections

/-- Construct the full reuse-first prefix directly from the More3 trace. -/
noncomputable def operationalRepresentedReuse
    {M N : ℕ}
    (endpoint : ODEmissi M N) :
    RepresentedReusePrefix endpoint := by
  let initial :=
    MRStatea.nil M N
      (inverseLabelledCollection M N).factors.length
  let routed :=
    FCollec.ECorrec.route_reuse
      initial endpoint.emits
      (fun _term hterm =>
        ⟨RTInv.ofInverseRaw hterm⟩)
  let state := Classical.choose routed
  have hrouted := Classical.choose_spec routed
  exact {
    state := state
    routed_eq := by
      simpa [initial, MRStatea.nil] using hrouted }

end RTRoutea
end TCTex
end Submission

/-!
# Full reuse-first represented-grid closure boundary

The full operational trace now consumes an already-open matching represented
slot before opening a new complete Cartesian batch.  The remaining global
combinatorial theorem is that this full reuse-first traversal exhausts every
batch it opens.

One proof of that theorem supplies the established full trace-routing kernel.
The existing filtering adapter then yields exact retained routing at every
nilpotent cutoff.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace RRClos

open FMEnd
open MTRoute
open RTRoutea
open TMRoutea
open TMPlanni.TRKern

/--
Global full reuse-first represented-grid closure law: after traversing every
operational correction, every opened Cartesian grid is exhausted.
-/
structure RFReuse : Prop where
  closed :
    ∀ {M N : ℕ}
      (endpoint : ODEmissi M N),
      (operationalRepresentedReuse
        endpoint).state.worklist.Closed

namespace RFReuse

/--
Full reuse-first represented-grid closure constructs the established exact
full correction router.
-/
noncomputable def operationalMultiplicityRouting
    (kernel : RFReuse) :
    ORKern where
  route endpoint := by
    let routingPrefix :=
      operationalRepresentedReuse endpoint
    exact ⟨routingPrefix.state, kernel.closed endpoint, routingPrefix.routed_eq⟩

/--
Filtering a closed full reuse-first schedule gives exact retained correction
routing at every nilpotent cutoff.
-/
noncomputable def retainedRoutingKernel
    (kernel : RFReuse)
    (n leftWeight rightWeight : ℕ) :
    OMRoute
      n leftWeight rightWeight :=
  truncMultRouting
    kernel.operationalMultiplicityRouting
      n leftWeight rightWeight

end RFReuse

end RRClos
end TCTex
end Submission

/-!
# Represented-grid closure as the remaining retained scheduler law

The operational emission recursion already opens a complete represented
Cartesian grid at every retained obstruction and routes the selected concrete
occurrence.  The only remaining issue is coalescing those opened grids: after
all retained occurrences have been routed, no represented slot may remain
pending.

This file packages that exact global law and proves its consumers.  Grid
closure yields a closed truncated trace router, hence an exact retained
multiplicity inventory, at every nilpotent cutoff and every pair of input
weights.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace RGClos

open IMPropag
open OCPartit
open FMEnd
open ORRoute
open TMPlanni
open TMRoutea

/--
Global represented-grid coalescing law: the sound operational prefix opened
from every retained correction trace is already closed.
-/
structure ORGrid : Prop where
  closed :
    ∀ {M N n leftWeight rightWeight : ℕ}
      {endpoint : ODEmissi M N}
      (partition :
        CCPartit endpoint
          n leftWeight rightWeight),
      (representedRoutingPrefix partition).state.worklist.Closed

namespace ORGrid

/--
Represented-grid coalescing constructs an exact retained correction router at
every nilpotent cutoff.
-/
noncomputable def truncMultRouting
    (kernel : ORGrid)
    (n leftWeight rightWeight : ℕ) :
    OMRoute
      n leftWeight rightWeight where
  route endpoint partition := by
    let routingPrefix := representedRoutingPrefix partition
    let routedState :=
      MRState.permRoutedTerms
        routingPrefix.state routingPrefix.routed_perm
    refine ⟨routedState, ?_, ?_⟩
    · simpa [routedState] using kernel.closed partition
    · rfl

/--
Represented-grid coalescing supplies the exact retained multiplicity inventory
consumed by cutoff-level symbolic compression.
-/
noncomputable def retainedInventory
    (kernel : ORGrid)
    {M N n leftWeight rightWeight : ℕ}
    {endpoint : ODEmissi M N}
    (partition :
      CCPartit endpoint
        n leftWeight rightWeight) :
    MIBlock partition.retained :=
  Classical.choice <|
    (kernel.truncMultRouting
      n leftWeight rightWeight).nonempty_retainedInventory partition

end ORGrid

end RGClos
end TCTex
end Submission

-- Merged from FamilyOperationalIndependentCollectorShapeSortingObstruction.lean

/-!
# Independent collector shape-sorting obstruction

The support-sensitive independent collector only interchanges histories whose
supports are disjoint.  Consequently, its generic derivation type does not
force primary erased-shape sorting: an overlapping-support pair may remain in
reverse primary-shape order.

This file records a concrete two-term witness.  Any proof of operational
erased-shape sorting must therefore use an additional invariant of the
inverse-oriented raw trace, rather than only the retained
`DTerm.ICollec` derivation.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace ISObstru

open HACoeff
open FORed

/-- A degree-two positive Hall-pair term with one occupied history slot. -/
def overlappingLowTerm :
    DTerm 1 1 1 where
  word :=
    .commutator
      (.atom (.inl 0))
      (.atom (.inr 0))
  support := {0}

/-- A higher-degree correction occupying the same history slot. -/
def overlappingHighTerm :
    DTerm 1 1 1 :=
  DTerm.correction overlappingLowTerm overlappingLowTerm

lemma overlapping_low_positive :
    overlappingLowTerm.erasedShape.PBPos := by
  simp [overlappingLowTerm, DTerm.erasedShape,
    collapseWord, collapseLabel, CWord.PBPos]

/-- The correction has strict primary precedence over its parent. -/
lemma overlapping_high_low :
    overlappingHighTerm.shapeBefore overlappingLowTerm := by
  exact Or.inl
    (DTerm.higher_before_left
      overlapping_low_positive)

/--
The higher-degree term cannot be moved across its parent by the independent
collector, because their supports overlap.
-/
lemma overlapping_before_low :
    ¬ overlappingHighTerm.independentBefore overlappingLowTerm := by
  apply independent_before_subset
  · simp [overlappingHighTerm, overlappingLowTerm,
      DTerm.correction]
  · simp [overlappingHighTerm, overlappingLowTerm,
      DTerm.correction]

/-- The independent collector therefore leaves the reverse-shape pair intact. -/
lemma overlapping_independent_inserts :
    IInsert
      [overlappingLowTerm]
      overlappingHighTerm
      [overlappingLowTerm, overlappingHighTerm] := by
  simpa using
    IInsert.append
      []
      overlappingLowTerm
      overlappingHighTerm
      overlapping_before_low

/-- The retained endpoint is not sorted by primary erased-shape order. -/
lemma overlapping_pairwise_sorted :
    ¬ [overlappingLowTerm, overlappingHighTerm].Pairwise
      fun left right =>
        left.erasedShape = right.erasedShape ∨
          left.shapeBefore right := by
  intro hsorted
  have hpair :
      overlappingLowTerm.erasedShape =
          overlappingHighTerm.erasedShape ∨
        overlappingLowTerm.shapeBefore overlappingHighTerm :=
    (List.pairwise_cons.mp hsorted).1
      overlappingHighTerm
      (by simp)
  rcases hpair with hshape | hbefore
  · exact
      (not_before_erased hshape.symm)
        overlapping_high_low
  · exact
      (DTerm.shapeBefore_asymm
        overlapping_high_low)
        hbefore

/--
Generic independent collection does not imply pairwise erased-shape sorting.
The witness already occurs in one append step after collecting its singleton
prefix.
-/
theorem independent_collects_sorted :
    ∃ input endpoint : List (DTerm 1 1 1),
      ICollec input endpoint ∧
        ¬ endpoint.Pairwise fun left right =>
          left.erasedShape = right.erasedShape ∨
            left.shapeBefore right := by
  refine
    ⟨[overlappingLowTerm, overlappingHighTerm],
      [overlappingLowTerm, overlappingHighTerm], ?_, ?_⟩
  · simpa using
      ICollec.snoc
        [overlappingLowTerm]
        overlappingHighTerm
        (ICollec.snoc
          []
          overlappingLowTerm
          ICollec.nil
          (IInsert.nil overlappingLowTerm))
        overlapping_independent_inserts
  · exact overlapping_pairwise_sorted

end ISObstru
end TCTex
end Submission

-- Merged from FamilyOperationalShapeFiberSortedCompletion.lean

/-!
# Shape-fiber completion from operational sorting

The operational collector splits its output into maximal adjacent runs of equal
erased Hall shape.  Pairwise sorting already implies that every erased-shape
fiber is interval-convex.  This file closes the remaining list-theoretic gap:
an interval-convex key fiber is exactly its unique maximal `splitBy` run.

Consequently, the primary erased-shape sorting statement constructs the
`OperationalShapeFiber` consumed by multiplicity compression and the
complete pending-presentation route.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace FSComp

open HACoeff
open HOCollec
open MSCompre
open FORed

/--
If equal-key occurrences form intervals, every maximal adjacent equal-key run
is the complete filtered fiber of its key.
-/
lemma List.exists_eqmem_keyfi
    {α β : Type*}
    [DecidableEq β]
    (key : α → β)
    (terms block : List α)
    (fiberConvex :
      ∀ (routingPrefix middle routingSuffix : List α)
        (left right : α),
        terms =
            routingPrefix ++ (left :: middle ++ (right :: routingSuffix)) →
          key left = key right →
            ∀ term ∈ middle, key term = key left)
    (hblock :
      block ∈ terms.splitBy
        fun left right => decide (key left = key right)) :
    ∃ shape : β,
      terms.filter (fun term => key term = shape) = block := by
  have hblockNe : block ≠ [] :=
    List.ne_nil_of_mem_splitBy hblock
  let shape := key (block.head hblockNe)
  have hblockChainBool :
      block.IsChain fun left right =>
        decide (key left = key right) :=
    List.isChain_of_mem_splitBy hblock
  have hblockChain :
      block.IsChain fun left right =>
        key left = key right :=
    hblockChainBool.imp (by
      intro left right hleftRight
      simpa using hleftRight)
  letI : Trans
      (fun left right : α => key left = key right)
      (fun left right : α => key left = key right)
      (fun left right : α => key left = key right) :=
    ⟨fun hleftMiddle hmiddleRight =>
      hleftMiddle.trans hmiddleRight⟩
  have hblockAll :
      ∀ term ∈ block, key term = shape := by
    intro term hterm
    exact
      (hblockChain.pairwise.rel_head_of_rel_head_head
        hterm rfl).symm
  rcases List.mem_iff_append.mp hblock with
    ⟨beforeBlocks, afterBlocks, hblocks⟩
  have hterms :
      terms =
        beforeBlocks.flatten ++ block ++ afterBlocks.flatten := by
    calc
      terms =
          (terms.splitBy
            fun left right => decide (key left = key right)).flatten :=
        (List.flatten_splitBy _ _).symm
      _ = beforeBlocks.flatten ++ block ++ afterBlocks.flatten := by
        rw [hblocks]
        simp
  have hblocksChain :
      (beforeBlocks ++ block :: afterBlocks).IsChain
        fun leftBlock rightBlock =>
          ∃ hleft hright,
            decide
              (key (leftBlock.getLast hleft) =
                key (rightBlock.head hright)) = false := by
    rw [← hblocks]
    exact List.isChain_getLast_head_splitBy
      (fun left right => decide (key left = key right)) terms
  have hbeforeFilter :
      beforeBlocks.flatten.filter (fun term => key term = shape) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro term hterm
    have htermShapeNe :
        key term ≠ shape := by
      intro htermShape
      have hbeforeBlocksNe :
          beforeBlocks ≠ [] := by
        intro hnil
        simp [hnil] at hterm
      have hboundary :=
        (List.isChain_append.mp hblocksChain).2.2
          (beforeBlocks.getLast hbeforeBlocksNe)
          (List.getLast?_eq_getLast_of_ne_nil hbeforeBlocksNe)
          block
          (by simp)
      rcases hboundary with
        ⟨hlastBlockNe, _hblockNe, hboundary⟩
      have hbeforeFlattenNe :
          beforeBlocks.flatten ≠ [] :=
        List.flatten_ne_nil_iff.mpr
          ⟨beforeBlocks.getLast hbeforeBlocksNe,
            List.getLast_mem hbeforeBlocksNe,
            hlastBlockNe⟩
      rcases List.mem_iff_append.mp hterm with
        ⟨beforeTerm, afterTerm, hbeforeFlatten⟩
      have hmiddleShape :
          ∀ middleTerm ∈ afterTerm,
            key middleTerm = key term := by
        apply fiberConvex beforeTerm afterTerm
          (block.tail ++ afterBlocks.flatten)
          term (block.head hblockNe)
        · rw [hterms, hbeforeFlatten]
          cases block with
          | nil =>
              contradiction
          | cons blockHead blockTail =>
              simp only [List.head_cons, List.tail_cons, List.cons_append,
                List.append_assoc]
        · exact htermShape
      have hbeforeLastShape :
          key (beforeBlocks.flatten.getLast hbeforeFlattenNe) =
            shape := by
        have hlastEq :
            beforeBlocks.flatten.getLast hbeforeFlattenNe =
              (term :: afterTerm).getLast (by simp) := by
          calc
            beforeBlocks.flatten.getLast hbeforeFlattenNe =
                (beforeTerm ++ term :: afterTerm).getLast (by simp) :=
              List.getLast_congr hbeforeFlattenNe (by simp)
                hbeforeFlatten
            _ = (term :: afterTerm).getLast (by simp) :=
              List.getLast_append_of_right_ne_nil
                beforeTerm (term :: afterTerm) (by simp)
        rw [hlastEq]
        rcases List.mem_cons.mp
            (List.getLast_mem (by simp : term :: afterTerm ≠ [])) with
          hlast | hlast
        · rw [hlast]
          exact htermShape
        · exact (hmiddleShape _ hlast).trans htermShape
      have hlastEq :
          (beforeBlocks.getLast hbeforeBlocksNe).getLast hlastBlockNe =
            beforeBlocks.flatten.getLast hbeforeFlattenNe :=
        List.getLast_getLast_eq_getLast_flatten
          hbeforeBlocksNe hlastBlockNe
      have hboundaryEq :
          key
              ((beforeBlocks.getLast hbeforeBlocksNe).getLast
                hlastBlockNe) =
            key (block.head hblockNe) := by
        rw [hlastEq]
        exact hbeforeLastShape
      exact
        (by simp [hboundaryEq] at hboundary)
    simpa using htermShapeNe
  have hafterFilter :
      afterBlocks.flatten.filter (fun term => key term = shape) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro term hterm
    have htermShapeNe :
        key term ≠ shape := by
      intro htermShape
      have hafterBlocksNe :
          afterBlocks ≠ [] := by
        intro hnil
        simp [hnil] at hterm
      have htailChain :
          (block :: afterBlocks).IsChain
            fun leftBlock rightBlock =>
              ∃ hleft hright,
                decide
                  (key (leftBlock.getLast hleft) =
                    key (rightBlock.head hright)) = false :=
        (List.isChain_append.mp hblocksChain).2.1
      have hboundary :=
        (List.isChain_cons.mp htailChain).1
          (afterBlocks.head hafterBlocksNe)
          (List.head?_eq_some_head hafterBlocksNe)
      rcases hboundary with
        ⟨_hblockNe, hfirstBlockNe, hboundary⟩
      have hafterFlattenNe :
          afterBlocks.flatten ≠ [] :=
        List.flatten_ne_nil_iff.mpr
          ⟨afterBlocks.head hafterBlocksNe,
            List.head_mem hafterBlocksNe,
            hfirstBlockNe⟩
      rcases List.mem_iff_append.mp hterm with
        ⟨beforeTerm, afterTerm, hafterFlatten⟩
      have hblockLastShape :
          key (block.getLast hblockNe) = shape :=
        hblockAll _ (List.getLast_mem hblockNe)
      have hmiddleShape :
          ∀ middleTerm ∈ beforeTerm,
            key middleTerm = key (block.getLast hblockNe) := by
        apply fiberConvex
          (beforeBlocks.flatten ++ block.dropLast)
          beforeTerm afterTerm
          (block.getLast hblockNe) term
        · calc
            terms =
                beforeBlocks.flatten ++ block ++
                  afterBlocks.flatten :=
              hterms
            _ =
                beforeBlocks.flatten ++
                  (block.dropLast ++ [block.getLast hblockNe]) ++
                    afterBlocks.flatten := by
              rw [List.dropLast_append_getLast hblockNe]
            _ =
                (beforeBlocks.flatten ++ block.dropLast) ++
                  (block.getLast hblockNe ::
                    beforeTerm ++ (term :: afterTerm)) := by
              rw [hafterFlatten]
              simp only [List.append_assoc, List.cons_append,
                List.nil_append]
        · exact hblockLastShape.trans htermShape.symm
      have hafterHeadShape :
          key (afterBlocks.flatten.head hafterFlattenNe) =
            shape := by
        cases beforeTerm with
        | nil =>
            have hheadEq :
                afterBlocks.flatten.head hafterFlattenNe = term := by
              have hheadOption :=
                congrArg List.head? hafterFlatten
              simpa [List.head?_eq_some_head hafterFlattenNe] using
                hheadOption
            rw [hheadEq]
            exact htermShape
        | cons firstTerm remainingTerms =>
            have hheadEq :
                afterBlocks.flatten.head hafterFlattenNe =
                  firstTerm := by
              have hheadOption :=
                congrArg List.head? hafterFlatten
              simpa [List.head?_eq_some_head hafterFlattenNe] using
                hheadOption
            rw [hheadEq]
            exact
              (hmiddleShape firstTerm (by simp)).trans
                hblockLastShape
      have hheadEq :
          (afterBlocks.head hafterBlocksNe).head hfirstBlockNe =
            afterBlocks.flatten.head hafterFlattenNe :=
        List.head_head_eq_head_flatten
          hafterBlocksNe hfirstBlockNe
      have hboundaryEq :
          key (block.getLast hblockNe) =
            key
              ((afterBlocks.head hafterBlocksNe).head
                hfirstBlockNe) := by
        rw [hheadEq]
        exact hblockLastShape.trans hafterHeadShape.symm
      exact
        (by simp [hboundaryEq] at hboundary)
    simpa using htermShapeNe
  refine ⟨shape, ?_⟩
  rw [hterms, List.filter_append, List.filter_append,
    hbeforeFilter, hafterFilter,
    List.filter_eq_self.mpr (by
      intro term hterm
      simpa using hblockAll term hterm)]
  simp

namespace EIConvex

/--
Interval-convex erased-shape fibers make every maximal adjacent same-shape run
the complete filtered fiber required by multiplicity compression.
-/
def shapeFiberKernel
    (kernel : EIConvex) :
    OperationalShapeFiber where
  filter_eq collected block hblock := by
    rcases
        List.exists_eqmem_keyfi
          (fun term => term.erasedShape) collected.factors block
          (by
            intro routingPrefix middle routingSuffix left right
              hfactors hleftRight
            exact
              kernel.convex collected routingPrefix middle routingSuffix
                left right hfactors hleftRight)
          (by simpa [sameErasedBlocks] using hblock) with
      ⟨shape, hshape⟩
    refine ⟨shape, ?_⟩
    simpa only [DFTerm.erased_shape_family] using hshape

end EIConvex

namespace OESorted

/--
Primary erased-shape sorting supplies the complete shape-fiber law consumed by
the downstream operational Hall-Petresco compiler.
-/
def shapeFiberKernel
    (kernel : OESorted) :
    OperationalShapeFiber :=
  FSComp.EIConvex.shapeFiberKernel
    kernel.operationalIntervalConvex

end OESorted

end FSComp
end TCTex
end Submission

-- Merged from FamilyFullDecoratedCollectorShapeSortingBridge.lean

/-!
# Shape sorting from the full decorated collector

The support-sensitive operational route retains an independent-collector
derivation.  The older full decorated collector has a stronger endpoint law:
its output is `Collected`, hence nondecreasing in the complete deterministic
collector key.

This file proves that the custom erased-shape code is injective and projects
the full collectedness law to the primary erased-shape sorting statement
needed by shape-fiber completion.  It deliberately leaves family-provenance
lifting separate: a future full family collector only has to supply
`Collected (terms.map DFTerm.decorated)`.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace DSBridge

open HACoeff
open FORed
open FSComp

/-- Maximum nesting depth of one erased Hall-pair word. -/
def pairShapeDepth :
    CWord HPAtom → ℕ
  | .atom _ => 0
  | .commutator left right =>
      max (pairShapeDepth left) (pairShapeDepth right) + 1

/--
Fuel-bounded parser for the prefix code used by the decorated collector.
Successful parsing returns one shape and the unconsumed suffix.
-/
def parsePairCode :
    ℕ → List ℕ → Option (CWord HPAtom × List ℕ)
  | 0, _ => none
  | _ + 1, 0 :: suffix => some (.atom .left, suffix)
  | _ + 1, 1 :: suffix => some (.atom .right, suffix)
  | fuel + 1, 2 :: suffix => do
      let (left, suffix) ← parsePairCode fuel suffix
      let 3 :: suffix := suffix | none
      let (right, suffix) ← parsePairCode fuel suffix
      let 4 :: suffix := suffix | none
      some (.commutator left right, suffix)
  | _ + 1, _ => none

/-- Parsing a generated code consumes exactly that code and returns its word. -/
lemma parse_code_append
    (word : CWord HPAtom)
    (suffix : List ℕ)
    (fuel : ℕ)
    (hdepth : pairShapeDepth word < fuel) :
    parsePairCode fuel
        (pairShapeCode word ++ suffix) =
      some (word, suffix) := by
  induction word generalizing fuel suffix with
  | atom atom =>
      cases atom <;>
        cases fuel with
        | zero =>
            simp [pairShapeDepth] at hdepth
        | succ fuel =>
            simp [pairShapeCode, parsePairCode]
  | commutator left right ihleft ihright =>
      cases fuel with
      | zero =>
          simp [pairShapeDepth] at hdepth
      | succ fuel =>
          have hleftDepth : pairShapeDepth left < fuel := by
            simp only [pairShapeDepth] at hdepth
            omega
          have hrightDepth : pairShapeDepth right < fuel := by
            simp only [pairShapeDepth] at hdepth
            omega
          simp [pairShapeCode, parsePairCode,
            ihleft _ _ hleftDepth, ihright _ _ hrightDepth,
            List.append_assoc]

/-- The collector's custom erased-shape prefix code is injective. -/
lemma pair_code_injective :
    Function.Injective pairShapeCode := by
  intro left right hcode
  let fuel :=
    max (pairShapeDepth left) (pairShapeDepth right) + 1
  have hleftDepth : pairShapeDepth left < fuel := by
    simp [fuel]
  have hrightDepth : pairShapeDepth right < fuel := by
    simp [fuel]
  have hleft :=
    parse_code_append left [] fuel hleftDepth
  have hright :=
    parse_code_append right [] fuel hrightDepth
  rw [hcode, hright] at hleft
  exact (congrArg Prod.fst (Option.some.inj hleft)).symm

/-- Equal primary shape codes recover equal erased Hall shapes. -/
lemma erased_code
    {M N K : ℕ}
    {left right : DTerm M N K}
    (hcode : left.erasedShapeCode = right.erasedShapeCode) :
    left.erasedShape = right.erasedShape := by
  apply pair_code_injective
  exact hcode

/--
Nondecreasing full collector keys project to sorted primary erased shapes.
Terms with the same primary code have literally the same erased Hall shape.
-/
lemma or_before_collector
    {M N K : ℕ}
    {left right : DTerm M N K}
    (hle : left.collectorLe right) :
    left.erasedShape = right.erasedShape ∨
      left.shapeBefore right := by
  by_cases hbefore : left.shapeBefore right
  · exact Or.inr hbefore
  by_cases hafter : right.shapeBefore left
  · exact False.elim
      (hle (DTerm.collector_before_shape hafter))
  have hdegree :
      left.erasedDegree = right.erasedDegree := by
    rcases lt_trichotomy left.erasedDegree right.erasedDegree with
      hdegree | hdegree | hdegree
    · exact False.elim (hafter (Or.inl hdegree))
    · exact hdegree
    · exact False.elim (hbefore (Or.inl hdegree))
  have hcode :
      left.erasedShapeCode = right.erasedShapeCode := by
    rcases lt_trichotomy left.erasedShapeCode right.erasedShapeCode with
      hcode | hcode | hcode
    · exact False.elim (hbefore (Or.inr ⟨hdegree, hcode⟩))
    · exact hcode
    · exact False.elim (hafter (Or.inr ⟨hdegree.symm, hcode⟩))
  exact Or.inl (erased_code hcode)

/-- A full decorated collector endpoint is pairwise primary-shape sorted. -/
lemma pairwise_sorted_collected
    {M N K : ℕ}
    {terms : List (DTerm M N K)}
    (hcollected : Collected terms) :
    terms.Pairwise fun left right =>
      left.erasedShape = right.erasedShape ∨
        left.shapeBefore right := by
  exact hcollected.imp fun hle =>
    or_before_collector hle

/--
Family terms whose decorated projection came from the full collector satisfy
the exact shape-sorting predicate used by the operational facade.
-/
lemma pairwise_sorted_decorated
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (hcollected :
      Collected (terms.map DFTerm.decorated)) :
    terms.Pairwise fun left right =>
      left.erasedShape = right.erasedShape ∨
        left.decorated.shapeBefore right.decorated := by
  induction terms with
  | nil =>
      simp
  | cons head tail ih =>
      rw [Collected, List.map_cons, List.pairwise_cons] at hcollected
      rw [List.pairwise_cons]
      constructor
      · intro term hterm
        simpa [DFTerm.erasedShape] using
          or_before_collector
            (hcollected.1 term.decorated
              (List.mem_map.mpr ⟨term, hterm, rfl⟩))
      · exact ih hcollected.2

/--
Pairwise primary sorting makes equal erased-shape occurrences interval-convex
in an arbitrary family-term list.
-/
lemma convex_pairwise_sorted
    {M N K : ℕ}
    {terms : List (DFTerm M N K)}
    (hsorted :
      terms.Pairwise fun left right =>
        left.erasedShape = right.erasedShape ∨
          left.decorated.shapeBefore right.decorated) :
    ∀ (routingPrefix middle routingSuffix :
        List (DFTerm M N K))
      (left right : DFTerm M N K),
      terms =
          routingPrefix ++ (left :: middle ++ (right :: routingSuffix)) →
        left.erasedShape = right.erasedShape →
          ∀ term ∈ middle, term.erasedShape = left.erasedShape := by
  intro routingPrefix middle routingSuffix left right
    hterms hleftRight term hterm
  have hsorted' :
      (routingPrefix ++ (left :: middle ++ (right :: routingSuffix))).Pairwise
        fun earlier later =>
          earlier.erasedShape = later.erasedShape ∨
            earlier.decorated.shapeBefore later.decorated := by
    rw [← hterms]
    exact hsorted
  have hleftTail :
      (left :: middle ++ right :: routingSuffix).Pairwise
        fun earlier later =>
          earlier.erasedShape = later.erasedShape ∨
            earlier.decorated.shapeBefore later.decorated :=
    (List.pairwise_append.mp hsorted').2.1
  have hleftTerm :
      left.erasedShape = term.erasedShape ∨
        left.decorated.shapeBefore term.decorated :=
    (List.pairwise_cons.mp hleftTail).1 term (by simp [hterm])
  have hmiddleTail :
      (middle ++ right :: routingSuffix).Pairwise
        fun earlier later =>
          earlier.erasedShape = later.erasedShape ∨
            earlier.decorated.shapeBefore later.decorated :=
    (List.pairwise_cons.mp hleftTail).2
  have htermRight :
      term.erasedShape = right.erasedShape ∨
        term.decorated.shapeBefore right.decorated :=
    (List.pairwise_append.mp hmiddleTail).2.2 term hterm right (by simp)
  rcases hleftTerm with hleftTerm | hleftTerm
  · exact hleftTerm.symm
  · rcases htermRight with htermRight | htermRight
    · exact False.elim
        ((not_before_erased
          (hleftRight.trans htermRight.symm)) hleftTerm)
    · exact False.elim
        ((not_before_erased hleftRight)
          (shapeBefore_trans hleftTerm htermRight))

/--
Every maximal adjacent same-shape block in a full-collected family endpoint is
the complete filtered fiber of one recipe shape.
-/
lemma same_blocks_decorated
    {M N K : ℕ}
    {terms block : List (DFTerm M N K)}
    (hcollected :
      Collected (terms.map DFTerm.decorated))
    (hblock : block ∈ sameErasedBlocks terms) :
    ∃ shape : CWord HPAtom,
      terms.filter
        (fun term => term.family.recipe.erasedShape = shape) =
          block := by
  have hsorted :=
    pairwise_sorted_decorated hcollected
  rcases
      List.exists_eqmem_keyfi
        (fun term => term.erasedShape) terms block
        (convex_pairwise_sorted hsorted)
        (by simpa [sameErasedBlocks] using hblock) with
    ⟨shape, hshape⟩
  refine ⟨shape, ?_⟩
  simpa only [DFTerm.erased_shape_family] using hshape

/--
Minimal family-provenance target for a future lift of the full decorated
collector.  Its endpoint law already resolves complete recipe-shape fibers.
-/
structure FCDecora
    (M N K : ℕ) where
  factors :
    List (DFTerm M N K)
  decorated_collected :
    Collected (factors.map DFTerm.decorated)

namespace FCDecora

lemma filter_eq
    {M N K : ℕ}
    (collected : FCDecora M N K)
    (block : List (DFTerm M N K))
    (hblock : block ∈ sameErasedBlocks collected.factors) :
    ∃ shape : CWord HPAtom,
      collected.factors.filter
        (fun term => term.family.recipe.erasedShape = shape) =
          block :=
  same_blocks_decorated
    collected.decorated_collected hblock

end FCDecora

end DSBridge
end TCTex
end Submission

-- Merged from FamilyFullDecoratedCollectorProvenanceLift.lean

/-!
# Counted-family provenance for the full decorated collector

The existing recipe-certified family collector follows the support-sensitive
independent-history algorithm.  This file records the parallel derivation type
for the older full deterministic collector.  Every obstruction carries the
same disjointness certificate required by `DTerm.Inserts`, while every
generated correction retains its exact `BFam.correction` provenance.

Forgetting family provenance projects a full family derivation to the full
decorated collector.  Consequently, every positive full family endpoint is
sorted and every maximal adjacent same-shape block is its complete recipe
fiber.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace DPLift

open scoped commutatorElement

open HACoeff
open HACoeff.DFTerm
open DSBridge

namespace DFTerm

/--
One full-order More3 insertion derivation with exact counted-family
provenance.
-/
inductive FullInserts
    {M N K : ℕ} :
    List (DFTerm M N K) →
      DFTerm M N K →
        List (DFTerm M N K) →
          Prop where
  | nil
      (A : DFTerm M N K) :
      FullInserts [] A [A]
  | append
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hBA : B.decorated.collectorLe A.decorated) :
      FullInserts (P ++ [B]) A (P ++ [B, A])
  | obstruction
      (P : List (DFTerm M N K))
      (B A : DFTerm M N K)
      (hAB : A.decorated.collectorBefore B.decorated)
      (hdisjoint :
        Disjoint B.decorated.support A.decorated.support)
      {Q R : List (DFTerm M N K)}
      (hcorrection : FullInserts P (B.correction A) Q)
      (hinsert : FullInserts Q A R) :
      FullInserts (P ++ [B]) A (R ++ [B])

/-- Forgetting recipe provenance recovers one full decorated insertion. -/
lemma decorated_full_inserts
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert : FullInserts L A R) :
    HACoeff.Inserts
      (L.map DFTerm.decorated)
      A.decorated
      (R.map DFTerm.decorated) := by
  induction hinsert with
  | nil A =>
      exact HACoeff.Inserts.nil A.decorated
  | append P B A hBA =>
      simpa [List.map_append] using
        (HACoeff.Inserts.append
          (P.map DFTerm.decorated)
          B.decorated A.decorated hBA)
  | obstruction P B A hAB hdisjoint hcorrection hinsert
      ihcorrection ihinsert =>
      simpa [List.map_append,
        HACoeff.DFTerm.decorated_correction] using
        (HACoeff.Inserts.obstruction
          (P.map DFTerm.decorated)
          B.decorated A.decorated hAB hdisjoint ihcorrection ihinsert)

/-- A full family insertion preserves the exact labelled product. -/
lemma list_full_inserts
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert : FullInserts L A R) :
    DFTerm.listEval R =
      DFTerm.listEval L * A.eval := by
  rw [list_eval_decorated,
    list_eval_decorated]
  exact decorated_list_inserts (decorated_full_inserts hinsert)

/-- One complete full-order family collection derivation. -/
inductive FullCollects
    {M N K : ℕ} :
    List (DFTerm M N K) →
      List (DFTerm M N K) →
        Prop where
  | nil :
      FullCollects [] []
  | snoc
      (P : List (DFTerm M N K))
      (A : DFTerm M N K)
      {C R : List (DFTerm M N K)}
      (hcollect : FullCollects P C)
      (hinsert : FullInserts C A R) :
      FullCollects (P ++ [A]) R

/-- Forgetting recipe provenance recovers one full decorated collection. -/
lemma full_collects
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    (hcollect : FullCollects L R) :
    HACoeff.Collects
      (L.map DFTerm.decorated)
      (R.map DFTerm.decorated) := by
  induction hcollect with
  | nil =>
      exact HACoeff.Collects.nil
  | snoc P A hcollect hinsert ihcollect =>
      simpa [List.map_append] using
        (HACoeff.Collects.snoc
          (P.map DFTerm.decorated)
          A.decorated ihcollect (decorated_full_inserts hinsert))

/-- A complete full family collection preserves exact labelled evaluation. -/
lemma list_full_collects
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    (hcollect : FullCollects L R) :
    DFTerm.listEval R =
      DFTerm.listEval L := by
  rw [list_eval_decorated,
    list_eval_decorated]
  exact decorated_list_collects (full_collects hcollect)

/-- Positive full family endpoints are collected in the complete key order. -/
lemma decorated_full_collects
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    (hcollect : FullCollects L R)
    (hpositive :
      PositiveList (L.map DFTerm.decorated)) :
    Collected (R.map DFTerm.decorated) := by
  exact collected_collects (full_collects hcollect) hpositive

/--
Every maximal adjacent same-shape block in a positive full family endpoint is
the complete filtered fiber of one recipe shape.
-/
lemma same_blocks_collects
    {M N K : ℕ}
    {L R block : List (DFTerm M N K)}
    (hcollect : FullCollects L R)
    (hpositive :
      PositiveList (L.map DFTerm.decorated))
    (hblock : block ∈ sameErasedBlocks R) :
    ∃ shape : CWord HPAtom,
      R.filter
        (fun term => term.family.recipe.erasedShape = shape) =
          block := by
  exact
    same_blocks_decorated
      (decorated_full_collects hcollect hpositive) hblock

end DFTerm

/--
An inverse-raw full family endpoint retaining its complete provenance
derivation.
-/
structure FDTerms
    (M N : ℕ) where
  factors :
    List (DFTerm M N
      (inverseLabelledCollection M N).factors.length)
  family_collects :
    DFTerm.FullCollects
      (inverseDecoratedTerms M N)
      factors

namespace FDTerms

/-- The inverse-raw endpoint retains the universal labelled commutator value. -/
lemma eval_eq
    {M N : ℕ}
    (collected : FDTerms M N) :
    DFTerm.listEval collected.factors =
      ⁅labelledLeft M N, labelledRight M N⁆ := by
  rw [DFTerm.list_full_collects collected.family_collects]
  exact list_decorated_terms M N

/-- The inverse-raw input is positive after forgetting recipe provenance. -/
lemma input_positive
    (M N : ℕ) :
    PositiveList
      ((inverseDecoratedTerms M N).map
        DFTerm.decorated) := by
  rw [decorated_inverse_terms]
  exact (inverseDecoratedCollection M N).factors_positive

/-- Full family collection sorts the inverse-raw endpoint. -/
lemma decorated_collected
    {M N : ℕ}
    (collected : FDTerms M N) :
    Collected
      (collected.factors.map DFTerm.decorated) :=
  DFTerm.decorated_full_collects
    collected.family_collects (input_positive M N)

/-- Every same-shape block in a full inverse-raw endpoint is a complete fiber. -/
lemma filter_eq
    {M N : ℕ}
    (collected : FDTerms M N)
    (block : List (DFTerm M N
      (inverseLabelledCollection M N).factors.length))
    (hblock : block ∈ sameErasedBlocks collected.factors) :
    ∃ shape : CWord HPAtom,
      collected.factors.filter
        (fun term => term.family.recipe.erasedShape = shape) =
          block := by
  exact
    DFTerm.same_blocks_collects
      collected.family_collects (input_positive M N) hblock

end FDTerms

end DPLift
end TCTex
end Submission
