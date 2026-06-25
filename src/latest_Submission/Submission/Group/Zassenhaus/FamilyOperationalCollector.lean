import Submission.Group.Zassenhaus.FamilySlotWorklist

/-!
# Exact labelled-word traces from the More3 family collector

The stable More3 collector already terminates on decorated family terms and
records every generated family correction.  Its existing consumer proves only
that ordered evaluation is preserved.  Product and inverse packet scheduling
needs the stronger operational statement: the collector derivation itself is
a finite sequence of primitive labelled-word rewrites.

This file extracts that sequence from `DFTerm.IInsert`
and lifts it through `DFTerm.ICollec`.  It then
packages an operationally collected inverse raw trace whose endpoint retains
the family-provenance derivation needed by exact realization-slot accounting.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace HOCollec

open scoped commutatorElement
open HACoeff
open BBSched
open PLMoveme

namespace FCTrace

/--
One More3 family insertion derivation is an explicit finite run of primitive
labelled-word swaps.
-/
lemma labelled_rewrites_inserts
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    {A : DFTerm M N K}
    (hinsert :
      HACoeff.DFTerm.IInsert
        L A R) :
    BBSched.LWRw
      (decoratedFamilyList L ++ [A.decorated.word])
      (decoratedFamilyList R) := by
  induction hinsert with
  | nil A =>
      exact Relation.ReflTransGen.refl
  | append P B A _hAB =>
      simpa [decoratedFamilyList, List.map_append, List.append_assoc] using
        (Relation.ReflTransGen.refl :
          BBSched.LWRw
            (decoratedFamilyList P ++
              [B.decorated.word, A.decorated.word])
            (decoratedFamilyList P ++
              [B.decorated.word, A.decorated.word]))
  | @obstruction P B A _hAB Q R hcorrection hinsert
      ihcorrection ihinsert =>
      have hswap :
          BBSched.LWRw
            (decoratedFamilyList P ++
              [B.decorated.word, A.decorated.word])
            (decoratedFamilyList P ++
              [(B.correction A).decorated.word,
                A.decorated.word, B.decorated.word]) := by
        simpa [DTerm.correction] using
          rewrites_single_step
            (decoratedFamilyList P) []
            B.decorated.word A.decorated.word
      have hcorrection' :
          BBSched.LWRw
            (decoratedFamilyList P ++
              [(B.correction A).decorated.word,
                A.decorated.word, B.decorated.word])
            (decoratedFamilyList Q ++
              [A.decorated.word, B.decorated.word]) := by
        simpa [List.append_assoc] using
          ihcorrection.context [] [A.decorated.word, B.decorated.word]
      have hinsert' :
          BBSched.LWRw
            (decoratedFamilyList Q ++
              [A.decorated.word, B.decorated.word])
            (decoratedFamilyList R ++ [B.decorated.word]) := by
        simpa [List.append_assoc] using
          ihinsert.context [] [B.decorated.word]
      simpa [decoratedFamilyList, List.map_append, List.append_assoc] using
        hswap.trans (hcorrection'.trans hinsert')

/--
A complete More3 family collection derivation is an explicit finite run of
primitive labelled-word swaps.
-/
lemma labelled_rewrites_collects
    {M N K : ℕ}
    {L R : List (DFTerm M N K)}
    (hcollect :
      HACoeff.DFTerm.ICollec
        L R) :
    BBSched.LWRw
      (decoratedFamilyList L)
      (decoratedFamilyList R) := by
  induction hcollect with
  | nil =>
      exact Relation.ReflTransGen.refl
  | snoc P A hcollect hinsert ihcollect =>
      simpa [decoratedFamilyList, List.map_append] using
        (ihcollect.context [] [A.decorated.word]).trans
          (labelled_rewrites_inserts hinsert)

end FCTrace

/--
Terminating More3 output that retains its exact family-provenance derivation
and therefore its concrete labelled-word rewrite schedule.
-/
structure ODTerms
    (M N : ℕ) where
  factors :
    List (DFTerm M N
      (inverseLabelledCollection M N).factors.length)
  family_collects :
    HACoeff.DFTerm.ICollec
      (inverseDecoratedTerms M N)
      factors

namespace ODTerms

/-- The operational output has the universal labelled commutator evaluation. -/
lemma eval_eq
    {M N : ℕ}
    (C : ODTerms M N) :
    DFTerm.listEval C.factors =
      ⁅labelledLeft M N, labelledRight M N⁆ := by
  rw [DFTerm.list_independent_collects C.family_collects]
  exact list_decorated_terms M N

/-- The operational output is reached by an explicit concrete rewrite run. -/
lemma labelledWordRewrites
    {M N : ℕ}
    (C : ODTerms M N) :
    BBSched.LWRw
      (decoratedFamilyList (inverseDecoratedTerms M N))
      (decoratedFamilyList C.factors) :=
  FCTrace.labelled_rewrites_collects
    C.family_collects

/-- Forget the retained family derivation and recover the older output carrier. -/
def independentDecoratedTerms
    {M N : ℕ}
    (C : ODTerms M N) :
    IndependentDecoratedTerms M N where
  factors := C.factors
  eval_eq := C.eval_eq
  decorated_collects :=
    DFTerm.independent_collects C.family_collects

end ODTerms

/-- The stable well-founded More3 collector supplies an operational endpoint. -/
lemma nonempty_decorated_terms
    (M N : ℕ) :
    Nonempty (ODTerms M N) := by
  have hinputSupport :
      SupportNonemptyList
        ((inverseDecoratedTerms M N).map
          DFTerm.decorated) := by
    rw [decorated_inverse_terms]
    exact (inverseDecoratedCollection M N).factors_support_nonempty
  rcases DFTerm.independent_collects_ready
      (DFTerm.independentCollectReady
        (inverseDecoratedTerms M N) hinputSupport) with
    ⟨factors, hcollect⟩
  exact ⟨{
    factors := factors
    family_collects := hcollect }⟩

end HOCollec
end TCTex
end Submission
