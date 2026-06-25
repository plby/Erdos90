import Submission.ClassField.NormCorrespondence.InverseLimit
import Submission.ClassField.LocalBrauer.ConcreteInflationBasic

/-!
# The tower of finite levels in the maximal abelian extension

Finite intermediate fields of the maximal abelian extension are lifted into
the chosen separable closure.  This file records monotonicity of that lift
and naturality of the canonical equivalences with respect to restriction.
-/

namespace Submission.CField.LFTheory

open Submission.CField.LBrauer

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

set_option maxHeartbeats 3000000 in
-- Unfolding the bundled finite subextensions exposes the two lifted fields.
omit [NumberField K] in
/-- Inclusion of finite maximal-abelian levels is preserved by their
canonical lifts into the separable closure. -/
theorem maximal_subextension_mono
    {E F : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K)} (hFE : F ≤ E) :
    (maximalAbelianSubextension K F).1 ≤
      (maximalAbelianSubextension K E).1 := by
  change IntermediateField.lift F.toIntermediateField ≤
    IntermediateField.lift E.toIntermediateField
  exact IntermediateField.map_mono
    (maximalAbelianIntermediate K).val hFE

set_option maxHeartbeats 3000000 in
-- The lifted fields need their explicit inclusion algebra for restriction.
set_option synthInstance.maxHeartbeats 500000 in
omit [NumberField K] in
/-- The canonical equivalences from finite maximal-abelian levels to their
lifts commute with finite Galois restriction. -/
theorem maximal_restriction_natural
    {E F : FiniteGaloisIntermediateField K
      (maximalAbelianIntermediate K)} (hFE : F ≤ E) :
    (galoisRestrictionHom K
        (maximal_subextension_mono hFE)).comp
        (maximalAbelianLevel K E).autCongr.toMonoidHom =
      (maximalAbelianLevel K F).autCongr.toMonoidHom.comp
        (galoisRestrictionHom K hFE) := by
  let eE := maximalAbelianLevel K E
  let eF := maximalAbelianLevel K F
  let hLift := maximal_subextension_mono hFE
  letI : Algebra F E :=
    RingHom.toAlgebra (Subsemiring.inclusion hFE)
  letI : IsScalarTower K F E :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  letI : Algebra (maximalAbelianSubextension K F).1
      (maximalAbelianSubextension K E).1 :=
    RingHom.toAlgebra (Subsemiring.inclusion hLift)
  letI : IsScalarTower K (maximalAbelianSubextension K F).1
      (maximalAbelianSubextension K E).1 :=
    IsScalarTower.of_algebraMap_eq' rfl
  apply MonoidHom.ext
  intro sigma
  apply AlgEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := eF.surjective x
  simp only [MonoidHom.comp_apply]
  change (eE.autCongr sigma).restrictNormal
      (maximalAbelianSubextension K F).1 (eF x) =
    eF.autCongr (galoisRestrictionHom K hFE sigma) (eF x)
  apply (algebraMap (maximalAbelianSubextension K F).1
    (maximalAbelianSubextension K E).1).injective
  rw [AlgEquiv.restrictNormal_commutes]
  apply eE.symm.injective
  simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    eE, eF, maximalAbelianLevel,
    AlgEquiv.symm_apply_apply]
  exact (AlgEquiv.restrictNormal_commutes sigma F x).symm

end

end Submission.CField.LFTheory
