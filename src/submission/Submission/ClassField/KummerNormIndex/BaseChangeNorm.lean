import Submission.ClassField.NormIndex.NormCompatibility
import Submission.ClassField.CyclicIdeles.FixedField
import Submission.ClassField.KummerNormIndex.IdeleExtensionTower

namespace Submission.CField.KNIndex

open IsDedekindDomain NumberField
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.NIndex
open Submission.CField.CIdeles

noncomputable section

universe u

private abbrev CK (K : Type u) [Field K] [NumberField K] :=
  IdeleClassGroup (NumberField.RingOfIntegers K) K

theorem smul_alg_aut
    {K K' M : Type u} [Field K] [Field K'] [Field M]
    [NumberField K] [NumberField K'] [NumberField M]
    [Algebra K K'] [Algebra K' M] [Algebra K M]
    [IsScalarTower K K' M]
    [FiniteDimensional K K'] [FiniteDimensional K' M]
    [IsGalois K K'] [IsGalois K' M] [IsGalois K M]
    (sigma : Gal(M/K')) (c : CK M) :
    let lift : Gal(M/K) :=
      MulSemiringAction.toAlgAut Gal(M/K') K M sigma
    letI := ideleDistribAction (K := K) (L := M)
    letI := ideleDistribAction (K := K') (L := M)
    (ideleDistribAction (K := K) (L := M)).smul lift c =
      (ideleDistribAction (K := K') (L := M)).smul sigma c := by
  rfl

set_option synthInstance.maxHeartbeats 500000 in
-- Several concrete Galois actions and five class-extension maps coexist here.
set_option maxHeartbeats 5000000 in
/-- In a cartesian Galois field square, extension of idèle classes commutes
with the two corresponding norm maps. -/
theorem canonical_base_change
    {K L K' M : Type u}
    [Field K] [Field L] [Field K'] [Field M]
    [NumberField K] [NumberField L] [NumberField K'] [NumberField M]
    [Algebra K L] [Algebra K K'] [Algebra L M] [Algebra K' M]
    [Algebra K M] [IsScalarTower K L M] [IsScalarTower K K' M]
    [FiniteDimensional K L] [FiniteDimensional K K']
    [FiniteDimensional L M] [FiniteDimensional K' M]
    [IsGalois K L] [IsGalois K K'] [IsGalois L M]
    [IsGalois K' M] [IsGalois K M]
    (rho : Gal(M/K') ≃* Gal(L/K))
    (hrho : ∀ sigma x,
      algebraMap L M (rho sigma x) = sigma (algebraMap L M x)) :
    let iK := (canonicalExtensionData (K := K) (L := K')).classMap
    let iL := (canonicalExtensionData (K := L) (L := M)).classMap
    iK.comp (canonicalIdeleNorm (K := K) (L := L)) =
      (canonicalIdeleNorm (K := K') (L := M)).comp iL := by
  classical
  let EK' := canonicalExtensionData (K := K) (L := K')
  let EL := canonicalExtensionData (K := K) (L := L)
  let EM := canonicalExtensionData (K := K) (L := M)
  let ELM := canonicalExtensionData (K := L) (L := M)
  let EK'M := canonicalExtensionData (K := K') (L := M)
  let liftHom : Gal(M/K') →* Gal(M/K) :=
    MulSemiringAction.toAlgAut Gal(M/K') K M
  letI : Fintype Gal(M/K') := Fintype.ofFinite Gal(M/K')
  letI : Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)
  letI := ideleDistribAction (K := K) (L := L)
  letI := ideleDistribAction (K := K) (L := M)
  letI := ideleDistribAction (K := K') (L := M)
  have hrestrict (sigma : Gal(M/K')) :
      AlgEquiv.restrictNormalHom L (liftHom sigma) = rho sigma := by
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L M).injective
    calc
      algebraMap L M
          ((AlgEquiv.restrictNormalHom L (liftHom sigma)) x) =
          (liftHom sigma) (algebraMap L M x) :=
        AlgEquiv.restrictNormal_commutes (liftHom sigma) L x
      _ = sigma (algebraMap L M x) := rfl
      _ = algebraMap L M (rho sigma x) := (hrho sigma x).symm
  have hequivariant (sigma : Gal(M/K')) (c : CK L) :
      ELM.classMap (rho sigma • c) =
        (ideleDistribAction (K := K') (L := M)).smul
          sigma (ELM.classMap c) := by
    calc
      ELM.classMap (rho sigma • c) =
          ELM.classMap
            ((AlgEquiv.restrictNormalHom L (liftHom sigma)) • c) := by
        rw [hrestrict]
      _ = (liftHom sigma) • ELM.classMap c :=
        canonical_restrict_smul
          (K := K) (L := M) L (liftHom sigma) c
      _ = (ideleDistribAction (K := K') (L := M)).smul
          sigma (ELM.classMap c) :=
        smul_alg_aut sigma (ELM.classMap c)
  have hproduct (c : CK L) :
      (∏ sigma : Gal(M/K'),
          (ideleDistribAction (K := K') (L := M)).smul
            sigma (ELM.classMap c)) =
        ELM.classMap (∏ tau : Gal(L/K), tau • c) := by
    calc
      (∏ sigma : Gal(M/K'),
          (ideleDistribAction (K := K') (L := M)).smul
            sigma (ELM.classMap c)) =
          ∏ sigma : Gal(M/K'), ELM.classMap (rho sigma • c) := by
        apply Finset.prod_congr rfl
        intro sigma _
        exact (hequivariant sigma c).symm
      _ = ELM.classMap (∏ sigma : Gal(M/K'), rho sigma • c) := by
        exact (map_prod ELM.classMap _ Finset.univ).symm
      _ = ELM.classMap (∏ tau : Gal(L/K), tau • c) := by
        congr 1
        exact Fintype.prod_equiv rho.toEquiv
          (fun sigma : Gal(M/K') ↦ rho sigma • c)
          (fun tau : Gal(L/K) ↦ tau • c) (fun _ ↦ rfl)
  have htransK' : EK'M.classMap.comp EK'.classMap = EM.classMap :=
    canonical_extension_trans (K := K) (E := K') (L := M)
  have htransL : ELM.classMap.comp EL.classMap = EM.classMap :=
    canonical_extension_trans (K := K) (E := L) (L := M)
  have htopInjective : Function.Injective EK'M.classMap := by
    intro a b hab
    have hbij := canonical_fixed_bijective
      (K := K') (L := M)
    apply hbij.1
    exact Subtype.ext hab
  apply MonoidHom.ext
  intro c
  apply htopInjective
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  calc
    EK'M.classMap
        (EK'.classMap (canonicalIdeleNorm (K := K) (L := L) c)) =
        EM.classMap (canonicalIdeleNorm (K := K) (L := L) c) :=
      DFunLike.congr_fun htransK'
        (canonicalIdeleNorm (K := K) (L := L) c)
    _ = ELM.classMap
        (EL.classMap (canonicalIdeleNorm (K := K) (L := L) c)) :=
      (DFunLike.congr_fun htransL
        (canonicalIdeleNorm (K := K) (L := L) c)).symm
    _ = ELM.classMap (∏ tau : Gal(L/K), tau • c) := by
      exact congrArg ELM.classMap
        (EL.classmap_canonidele_classnorm
          (canonical_idele_compatible (K := K) (L := L)) c)
    _ = ∏ sigma : Gal(M/K'),
        (ideleDistribAction (K := K') (L := M)).smul
          sigma (ELM.classMap c) := (hproduct c).symm
    _ = EK'M.classMap
        (canonicalIdeleNorm (K := K') (L := M) (ELM.classMap c)) := by
      rw [EK'M.classmap_canonidele_classnorm
        (canonical_idele_compatible (K := K') (L := M))]

end

end Submission.CField.KNIndex
