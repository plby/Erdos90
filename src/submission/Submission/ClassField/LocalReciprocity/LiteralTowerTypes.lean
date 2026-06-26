import Submission.ClassField.LocalReciprocity.GlobalBrauer
import Submission.ClassField.LocalReciprocity.AlgEquiv

/-!
# III.3.3 for a literal tower of field types

The intermediate-field statement of III.3.3 is transported to an arbitrary
literal tower `Ω/F/K`.  This is the form needed when a completed local field
is mapped into a normal closure and represented there by its field range.
-/

namespace Submission.CField.LRecip

open IntermediateField
open Submission.CField.LBrauer
open scoped IsMulCommutative

noncomputable section

variable (K Omega : Type)
  [NontriviallyNormedField K] [IsUltrametricDist K]

local instance towerValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

local instance towerValuationCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := K))

variable [IsNonarchimedeanLocalField K]
  [Field Omega] [Algebra K Omega] [FiniteDimensional K Omega]
  [IsGalois K Omega]
  (F : Type) [Field F] [Algebra K F] [Algebra F Omega]
  [IsScalarTower K F Omega] [FiniteDimensional K F] [IsGalois K F]
  [IsMulCommutative Gal(F/K)]

set_option maxHeartbeats 5000000 in
-- Transporting the literal tower through two intermediate-field models is expensive.
set_option synthInstance.maxHeartbeats 500000 in
-- The same transport requires a larger local typeclass-search budget.
/-- **III.3.3, literal-tower form.**  Abelianized restriction from an
ambient finite Galois extension to a normal abelian subextension carries
the ambient Artin homomorphism to the normalized Artin homomorphism of the
literal lower field. -/
theorem abelianized_restrict_normal :
    (Abelianization.lift (AlgEquiv.restrictNormalHom F)).comp
        (localArtinHom K Omega) =
      abelianArtinHom K F := by
  let i : F →ₐ[K] Omega := IsScalarTower.toAlgHom K F Omega
  let Ffield : IntermediateField K Omega := i.fieldRange
  let eF : F ≃ₐ[K] Ffield :=
    IntermediateField.topEquiv.symm |>.trans
      ((IntermediateField.equivMap (⊤ : IntermediateField K F) i).trans
        (IntermediateField.equivOfEq (AlgHom.fieldRange_eq_map i).symm))
  letI : FiniteDimensional K Ffield :=
    Module.Finite.equiv eF.toLinearEquiv
  letI : IsGalois K Ffield := IsGalois.of_algEquiv eF
  letI : IsMulCommutative Gal(Ffield/K) := by
    refine ⟨⟨fun sigma tau => ?_⟩⟩
    apply eF.autCongr.symm.injective
    simpa only [map_mul] using
      mul_comm (eF.autCongr.symm sigma) (eF.autCongr.symm tau)
  let Ofield : IntermediateField K Omega := ⊤
  let eO : Omega ≃ₐ[K] Ofield := IntermediateField.topEquiv.symm
  letI : FiniteDimensional K Ofield :=
    Module.Finite.equiv eO.toLinearEquiv
  letI : IsGalois K Ofield := IsGalois.of_algEquiv eO
  let Flevel : FiniteGaloisIntermediateField K Omega :=
    { Ffield with
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  let Olevel : FiniteGaloisIntermediateField K Omega :=
    { Ofield with
      finiteDimensional := inferInstance
      isGalois := inferInstance }
  have hOtop : Ofield = (⊤ : IntermediateField K Omega) := rfl
  let hFO : Flevel ≤ Olevel := by
    change Ffield ≤ Ofield
    dsimp only [Ofield]
    exact le_top
  letI : Algebra Ffield Ofield :=
    RingHom.toAlgebra (Subsemiring.inclusion hFO)
  letI : IsScalarTower K Ffield Ofield :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  let restrictionField : Gal(Ofield/K) →* Gal(Ffield/K) :=
    galoisRestrictionHom K hFO
  have hrestriction : restrictionField.comp eO.autCongr.toMonoidHom =
      eF.autCongr.toMonoidHom.comp (AlgEquiv.restrictNormalHom F) := by
    apply MonoidHom.ext
    intro sigma
    apply AlgEquiv.ext
    intro x
    obtain ⟨x, rfl⟩ := eF.surjective x
    simp only [MonoidHom.comp_apply]
    change (eO.autCongr sigma).restrictNormal Ffield (eF x) =
      eF.autCongr (AlgEquiv.restrictNormalHom F sigma) (eF x)
    apply (algebraMap Ffield Ofield).injective
    rw [AlgEquiv.restrictNormal_commutes]
    apply eO.symm.injective
    simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
      eO.symm_apply_apply, eF.symm_apply_apply]
    change sigma (i x) = i ((AlgEquiv.restrictNormalHom F sigma) x)
    exact (AlgEquiv.restrictNormal_commutes sigma F x).symm
  have hrestrictionAb :
      (Abelianization.lift restrictionField).comp
          (Abelianization.map eO.autCongr.toMonoidHom) =
        eF.autCongr.toMonoidHom.comp
          (Abelianization.lift (AlgEquiv.restrictNormalHom F)) := by
    apply Abelianization.hom_ext
    simpa only [MonoidHom.comp_assoc, Abelianization.lift_of_comp,
      Abelianization.map_of] using hrestriction
  have hintermediate := artin_abelianized_restriction
    K Omega hFO
  have htransport := abelian_artin_alg K F Ffield eF
  have hambient := artin_hom_alg K Omega Ofield eO
  apply MonoidHom.ext
  intro a
  apply eF.autCongr.injective
  have hi := DFunLike.congr_fun hintermediate a
  have ht := DFunLike.congr_fun htransport a
  have ha := DFunLike.congr_fun hambient a
  have hr := DFunLike.congr_fun hrestrictionAb
    (localArtinHom K Omega a)
  have ht' : eF.autCongr (abelianArtinHom K F a) =
      abelianArtinHom K Ffield a := by
    simpa only [MonoidHom.comp_apply] using ht
  have ha' : eO.autCongr.abelianizationCongr
      (localArtinHom K Omega a) =
      localArtinHom K Ofield a := by
    simpa only [MonoidHom.comp_apply] using ha
  have hi' : Abelianization.lift restrictionField
      (localArtinHom K Ofield a) =
      abelianArtinHom K Ffield a := by
    simpa only [MonoidHom.comp_apply] using hi
  have hr' : Abelianization.lift restrictionField
        (eO.autCongr.abelianizationCongr
          (localArtinHom K Omega a)) =
      eF.autCongr
        (Abelianization.lift (AlgEquiv.restrictNormalHom F)
          (localArtinHom K Omega a)) := by
    simpa only [MonoidHom.comp_apply] using hr
  change eF.autCongr
      (Abelianization.lift (AlgEquiv.restrictNormalHom F)
        (localArtinHom K Omega a)) =
    eF.autCongr (abelianArtinHom K F a)
  calc
    _ = Abelianization.lift restrictionField
        (eO.autCongr.abelianizationCongr
          (localArtinHom K Omega a)) := hr'.symm
    _ = Abelianization.lift restrictionField
        (localArtinHom K Ofield a) := congrArg _ ha'
    _ = abelianArtinHom K Ffield a := hi'
    _ = eF.autCongr (abelianArtinHom K F a) := ht'.symm

end

end Submission.CField.LRecip
