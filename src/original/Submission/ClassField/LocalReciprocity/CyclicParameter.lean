import Submission.ClassField.LocalReciprocity.NormResidueFormula
import Submission.ClassField.LocalBrauer.CohomologyTransport

/-!
# The cyclic parameter used in Proposition III.3.6

For a chosen cyclic coordinate `Multiplicative (ZMod n) ≃ G`, the standard
description of multiplicative `H²(G,M)` sends a normalized cocycle to the
product of its values `(g, s)` as `g` runs through `G`, where `s` is the
chosen generator.  This is the same cyclic product that occurs in the
degree-minus-two formula for the local Artin map.
-/

namespace Submission.CField.LRecip

open Submission.CField.CProduca
open Submission.CField.LBrauer

noncomputable section

variable {n : ℕ} [NeZero n]
variable {G M : Type*} [Group G] [Fintype G]
  [CommGroup M] [MulDistribMulAction G M]

/-- In arbitrary cyclic coordinates, the `H² ≃ Mᴳ/NM` equivalence is
literally evaluation of the cyclic parameter at the chosen generator. -/
theorem cyclic_invariants_mk
    (hn : 1 < n) (e : Multiplicative (ZMod n) ≃* G)
    (c : NMCocycl₂ (G := G) (M := M)) :
    GroupH2.mulInvariantsMod (M := M) e hn
        (MHTwo.mk c) =
      QuotientGroup.mk' (FMAct.norm G M).range
        (NMCocycl₂.cyclicProductInvariant c
          (e (Multiplicative.ofAdd (1 : ZMod n)))) := by
  letI : MulDistribMulAction (Multiplicative (ZMod n)) M :=
    GroupH2.pulledAction e
  simp only [GroupH2.mulInvariantsMod, MulEquiv.trans_apply,
    CyclicH2.mulInvariantsMod, MulEquiv.ofBijective_apply,
    CyclicH2.classParameterHom]
  simp only [GroupH2.hCyclicModel,
    MHTrans.h_2_mk]
  change GroupH2.invariantsModEquiv e
      (CyclicH2.classParameter
        (MHTwo.mk
          (MHTrans.cocycleMap e.symm (MulEquiv.refl M)
            (by
              intro g m
              simp [MulAction.compHom_smul_def]) c))) = _
  rw [CyclicH2.classParameter_mk]
  change QuotientGroup.mk' (FMAct.norm G M).range
      (GroupH2.invariantsMulEquiv e
        (CyclicH2.parameterHom
          (MHTrans.cocycleMap e.symm (MulEquiv.refl M)
            _ c))) = _
  apply congrArg (QuotientGroup.mk' (FMAct.norm G M).range)
  apply Subtype.ext
  change (∏ g : Multiplicative (ZMod n),
      c (e g, e (Multiplicative.ofAdd (1 : ZMod n)))) =
    ∏ g : G, c (g, e (Multiplicative.ofAdd (1 : ZMod n)))
  exact Fintype.prod_equiv e.toEquiv _ _ (fun _ ↦ rfl)

end

end Submission.CField.LRecip
