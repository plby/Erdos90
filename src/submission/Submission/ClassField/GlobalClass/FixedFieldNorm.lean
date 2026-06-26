import Submission.ClassField.GlobalClass.TateTransport
import Submission.ClassField.GlobalClass.AbsoluteInvariant

open scoped IsMulCommutative

/-!
# The literal source statement of Theorem VIII.4.8

The fixed-field proof works inside a finite Galois closure.  This file
transports both the original extension and its specified maximal abelian
subfield into that closure, proves that the transported maximal field is
the fixed field of `H · G'`, and carries the norm equality back.
-/

namespace Submission.CField.GClass

open NumberField
open Submission.CField.Ideles

noncomputable section

universe u

/-- Commutativity of a Galois group is preserved by an algebra equivalence
of the corresponding extensions. -/
private theorem commutativeGalAlg
    {K A B : Type u} [Field K] [Field A] [Field B]
    [Algebra K A] [Algebra K B]
    [IsGalois K A] [IsGalois K B]
    [IsMulCommutative Gal(A/K)]
    (e : A ≃ₐ[K] B) : IsMulCommutative Gal(B/K) := by
  letI : CommGroup Gal(A/K) := inferInstance
  let eAut : Gal(A/K) ≃* Gal(B/K) := e.autCongr
  refine ⟨⟨fun sigma tau ↦ ?_⟩⟩
  apply eAut.symm.injective
  simpa only [map_mul] using
    mul_comm (eAut.symm sigma) (eAut.symm tau)

set_option maxHeartbeats 4000000 in
-- The normal closure and two transported intermediate-field lattices carry
-- several overlapping algebra and scalar-tower instances.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The fixed-field norm-limitation argument implies the literal statement
for an arbitrary finite extension and its specified maximal abelian Galois
subextension. -/
theorem maximal_abelian_corestriction
    (hcore : CorestrictionCokernelBridge.{u})
    (hindex : GaloisIndexFormula.{u}) :
    MaximalSubextensionEquality.{u} := by
  intro K E _ _ _ _ _ _ M hM
  letI : IsGalois K M := hM.1
  letI : IsMulCommutative Gal(M/K) := hM.2.1
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : IsAlgClosure K (AlgebraicClosure E) := inferInstance
  letI : IsGalois K (AlgebraicClosure E) :=
    IsAlgClosure.isGalois K (AlgebraicClosure E)
  let L := IntermediateField.normalClosure K E (AlgebraicClosure E)
  letI : IsGalois K L :=
    IsGalois.normalClosure K E (AlgebraicClosure E)
  letI : FiniteDimensional K L :=
    normalClosure.is_finiteDimensional K E (AlgebraicClosure E)
  letI : NumberField L := NumberField.of_module_finite K L
  let j : E →ₐ[K] L := IsScalarTower.toAlgHom K E L
  let E' : IntermediateField K L := j.fieldRange
  let eE : E ≃ₐ[K] E' := by
    simpa [E', AlgHom.fieldRange_toSubalgebra j] using
      (AlgEquiv.ofInjectiveField j)
  letI : NumberField E' := NumberField.of_module_finite K E'
  let H : Subgroup Gal(L/K) := E'.fixingSubgroup
  let A : IntermediateField K L :=
    maximalSubfieldInside K L H
  have hfixed : IntermediateField.fixedField H = E' :=
    IsGalois.fixedField_fixingSubgroup E'
  have hAE' : A ≤ E' := by
    rw [← hfixed]
    exact maximal_abelian_inside K L H
  -- View the canonical field `A` and the given field `M` inside the same
  -- intermediate-field lattice over the transported extension `E'`.
  let F : IntermediateField K E' := IntermediateField.restrict hAE'
  let M' : IntermediateField K E' := M.map eE.toAlgHom
  let eM' : M ≃ₐ[K] M' := IntermediateField.intermediateFieldMap eE M
  let eMlift : M ≃ₐ[K] IntermediateField.lift M' :=
    eM'.trans (IntermediateField.liftAlgEquiv M')
  letI : IsGalois K (IntermediateField.lift M') :=
    IsGalois.of_algEquiv eMlift
  letI : IsMulCommutative Gal(IntermediateField.lift M'/K) :=
    commutativeGalAlg eMlift
  have hMliftA : IntermediateField.lift M' ≤ A := by
    apply subfield_inside_fixed K L H
    rw [hfixed]
    exact IntermediateField.lift_le M'
  have hM'F : M' ≤ F := by
    intro x hx
    apply (IntermediateField.mem_restrict hAE' x).2
    apply hMliftA
    exact (IntermediateField.mem_lift x).2 hx
  -- Conversely, pull `A` back to `E`.  It is abelian Galois, so maximality
  -- of the given `M` forces it into `M`; transporting forward gives `F ≤ M'`.
  let Fpre : IntermediateField K E := F.map eE.symm.toAlgHom
  let eFpre : A ≃ₐ[K] Fpre :=
    (IntermediateField.restrict_algEquiv hAE').trans
      (IntermediateField.intermediateFieldMap eE.symm F)
  letI : IsGalois K Fpre := IsGalois.of_algEquiv eFpre
  letI : IsMulCommutative Gal(Fpre/K) :=
    commutativeGalAlg eFpre
  have hFpreM : Fpre ≤ M := hM.2.2 Fpre inferInstance inferInstance
  have hFM' : F ≤ M' := by
    intro x hx
    let y : E := eE.symm x
    have hyFpre : y ∈ Fpre := by
      exact ⟨x, hx, rfl⟩
    have hyM : y ∈ M := hFpreM hyFpre
    exact ⟨y, hyM, eE.apply_symm_apply x⟩
  have hFM : F = M' := le_antisymm hFM' hM'F
  have hAMlift : A = IntermediateField.lift M' := by
    calc
      A = IntermediateField.lift F :=
        (IntermediateField.lift_restrict hAE').symm
      _ = IntermediateField.lift M' := congrArg IntermediateField.lift hFM
  have hEE' :
      (canonicalIdeleNorm (K := K) (L := E)).range =
        (canonicalIdeleNorm (K := K) (L := E')).range :=
    canonical_range_alg eE
  have hE'A :
      (canonicalIdeleNorm (K := K) (L := E')).range =
        (canonicalIdeleNorm (K := K) (L := A)).range := by
    have h := norm_maximal_abelian
      hcore hindex K L H
    rw [hfixed] at h
    exact h
  have hMtransport :
      (canonicalIdeleNorm (K := K) (L := M)).range =
        (canonicalIdeleNorm
          (K := K) (L := IntermediateField.lift M')).range :=
    canonical_range_alg eMlift
  calc
    (canonicalIdeleNorm (K := K) (L := E)).range =
        (canonicalIdeleNorm (K := K) (L := E')).range := hEE'
    _ = (canonicalIdeleNorm (K := K) (L := A)).range := hE'A
    _ = (canonicalIdeleNorm
          (K := K) (L := IntermediateField.lift M')).range := by rw [hAMlift]
    _ = (canonicalIdeleNorm (K := K) (L := M)).range :=
      hMtransport.symm

/-- **Theorem VIII.4.8**, with Tate's theorem transported through the
small model and with the source's corestriction square as the only remaining
compatibility input. -/
theorem abelian_corestriction_square
    (h51 : Submission.CField.CIdeles.IdeleCohomologyClaims.{u})
    (h47 : RelativeInvariantGenerator.{u})
    (hsquare : CorestrictionSquareBridge.{u}) :
    MaximalSubextensionEquality.{u} :=
  maximal_abelian_corestriction
    (corestriction_cokernel_square hsquare)
    (previous_results_small h51 h47)

/-- Theorem VIII.4.8 with Theorem 4.7 expanded into the absolute invariant
and restriction sequence immediately preceding it in the text. -/
theorem maximal_corestriction_square
    (h51 : Submission.CField.CIdeles.IdeleCohomologyClaims.{u})
    (hAbsolute : AbsoluteInvariantBridge.{u})
    (hsquare : CorestrictionSquareBridge.{u}) :
    MaximalSubextensionEquality.{u} :=
  abelian_corestriction_square h51
    (absolute_invariant hAbsolute) hsquare

end

end Submission.CField.GClass
