import Submission.Group.Zassenhaus.AtomParentHistories

/-!
# Canonical recipe endpoints for the operational family collector

The terminating More3 collector now supplies an exact labelled-word rewrite
run, and the inverse raw source has exact realization-slot coverage.  The
remaining propagation theorem must show that the collector endpoint splits
into consecutive complete realization packets.

This file packages that final boundary and proves its consumer: any such
packet decomposition immediately compresses to a canonical block-family
expansion and hence to the polynomial recipe endpoint.

This file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex
namespace HOEnd

open scoped commutatorElement
open HACoeff
open HSPacket
open HOCollec
open PPColl
open PPColl.RCColl.RPAggreg

/--
One operational More3 output together with its consecutive complete-packet
decomposition.
-/
structure CREnd
    (M N : ℕ) where
  collected :
    ODTerms M N
  families :
    List (BFam M N)
  packeted :
    RPBy families collected.factors

namespace CREnd

/-- The inverse raw trace reaches the endpoint by explicit labelled-word swaps. -/
lemma labelledWordRewrites
    {M N : ℕ}
    (E : CREnd M N) :
    BBSched.LWRw
      (decoratedFamilyList (inverseDecoratedTerms M N))
      (decoratedFamilyList E.collected.factors) :=
  E.collected.labelledWordRewrites

/-- Compress one packeted operational endpoint to the canonical block families. -/
def blockExpansion
    {M N : ℕ}
    (E : CREnd M N) :
    BFam.Expansion M N where
  families := E.families
  collapsed_eval_eq := by
    calc
      collapsedListEval (BFam.realizationList E.families) =
          collapsedListEval
            (decoratedFamilyList E.collected.factors) := by
        simpa [collapsedListEval,
          BFTrunc.collapsedList] using
          (E.packeted.collapsed_list_realization
            universalLeft universalRight).symm
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

/-- Retain the polynomial-ready canonical factors of the packet endpoint. -/
def factors
    {M N : ℕ}
    (E : CREnd M N) :
    List (Factor M N) :=
  E.blockExpansion.factors

/-- The compressed factors evaluate to the universal power commutator. -/
lemma listEval_factors
    {M N : ℕ}
    (E : CREnd M N) :
    listEval universalLeft universalRight E.factors =
      ⁅universalLeft ^ M, universalRight ^ N⁆ :=
  E.blockExpansion.listEval_factors

end CREnd

/--
Precise remaining propagation law: every terminating operational More3 output
admits a consecutive exact-slot packet decomposition.
-/
structure EPClos : Prop where
  packeted :
    ∀ {M N : ℕ}
      (collected : ODTerms M N),
      ∃ families : List (BFam M N),
        RPBy families collected.factors

namespace EPClos

/-- A packet-closure kernel resolves every operational More3 output. -/
noncomputable def endpoint
    (kernel : EPClos)
    {M N : ℕ}
    (collected : ODTerms M N) :
    CREnd M N :=
  let families := (kernel.packeted collected).choose
  {
    collected := collected
    families := families
    packeted := (kernel.packeted collected).choose_spec }

/--
The stable terminating collector and one packet-closure propagation kernel
produce the desired canonical block-family expansion.
-/
noncomputable def expansion
    (kernel : EPClos)
    (M N : ℕ) :
    BFam.Expansion M N :=
  let collected :=
    Classical.choice
      (nonempty_decorated_terms M N)
  (kernel.endpoint collected).blockExpansion

end EPClos

end HOEnd
end TCTex
end Submission
