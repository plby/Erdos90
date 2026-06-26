import Submission.ClassField.NormIndex.IdeleTowerTransitivity
import Submission.ClassField.KummerNormIndex.BaseChangeNorm
import Submission.ClassField.KummerNormIndex.CyclotomicCompositum
import Submission.ClassField.KummerNormIndex.NormExponent

/-!
# The cyclotomic base-change bridge in Lemma VII.6.1

This assembles the cyclotomic compositum, the two canonical idèle-class
extension maps, norm functoriality in towers, and the base-change norm
square into the literal data used by the source-statement diagram chase.
-/

namespace Submission.CField.KNIndex

open IsDedekindDomain NumberField
open Submission.CField.Ideles
open Submission.CField.NIndex

noncomputable section

universe u

private theorem canonical_norm_trans
    {K E L : Type u} [Field K] [Field E] [Field L]
    [NumberField K] [NumberField E] [NumberField L]
    [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    [IsGalois K E] [IsGalois E L] [IsGalois K L] :
    canonicalIdeleNorm (K := K) (L := L) =
      (canonicalIdeleNorm (K := K) (L := E)).comp
        (canonicalIdeleNorm (K := E) (L := L)) := by
  apply MonoidHom.ext
  intro c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (principalIdeles (RingOfIntegers L) L) c
  simp only [canonical_idele_mk]
  rw [ideleNorm_trans (K := K) (E := E) (L := L)]
  rfl

set_option synthInstance.maxHeartbeats 500000 in
-- The constructed compositum carries four overlapping algebra towers.
set_option maxHeartbeats 5000000 in
/-- The actual cyclotomic square and its canonical idèle-class maps. -/
theorem cyclotomicChangeBridge :
    CyclotomicChangeBridge.{u} := by
  intro p hp K L _ _ _ _ _ _ _ _ hdegree
  obtain ⟨F⟩ := cyclotomic_compositum_data
    p hp K L hdegree
  letI : Field F.K' := F.fieldK'
  letI : Field F.L' := F.fieldL'
  letI : NumberField F.K' := F.numberFieldK'
  letI : NumberField F.L' := F.numberFieldL'
  letI : Algebra K F.K' := F.algebraKK'
  letI : Algebra L F.L' := F.algebraLL'
  letI : Algebra F.K' F.L' := F.algebraK'L'
  letI : Algebra K F.L' := F.algebraKL'
  letI : IsScalarTower K F.K' F.L' := F.scalarTowerKK'L'
  letI : IsScalarTower K L F.L' := F.scalarTowerKLL'
  letI : FiniteDimensional K F.K' := F.finiteDimensionalKK'
  letI : FiniteDimensional L F.L' := F.finiteDimensionalLL'
  letI : FiniteDimensional F.K' F.L' := F.finiteDimensionalK'L'
  letI : IsGalois K F.K' := F.isGaloisKK'
  letI : IsGalois L F.L' := F.isGaloisLL'
  letI : IsGalois K F.L' := F.isGaloisKL'
  letI : IsGalois F.K' F.L' := F.isGaloisK'L'
  letI : IsCyclic Gal(F.L'/F.K') := F.isCyclicK'L'
  let EK' := canonicalExtensionData (K := K) (L := F.K')
  let EL' := canonicalExtensionData (K := L) (L := F.L')
  have htop : EK'.classMap.comp
        (canonicalIdeleNorm (K := K) (L := L)) =
      (canonicalIdeleNorm (K := F.K') (L := F.L')).comp
        EL'.classMap :=
    canonical_base_change F.galoisRestriction
      F.galoisRestriction_commutes
  have hbottom :
      (canonicalIdeleNorm (K := K) (L := F.K')).comp
          (canonicalIdeleNorm (K := F.K') (L := F.L')) =
        (canonicalIdeleNorm (K := K) (L := L)).comp
          (canonicalIdeleNorm (K := L) (L := F.L')) :=
    (canonical_norm_trans (K := K) (E := F.K') (L := F.L')).symm.trans
      (canonical_norm_trans (K := K) (E := L) (L := F.L'))
  have hdownK :
      (canonicalIdeleNorm (K := K) (L := F.K')).comp EK'.classMap =
        powMonoidHom F.m := by
    simpa only [F.degreeRight] using
      (canonical_comp_extension
        (K := K) (L := F.K'))
  have hdownL :
      (canonicalIdeleNorm (K := L) (L := F.L')).comp EL'.classMap =
        powMonoidHom F.m := by
    simpa only [F.degreeLeft] using
      (canonical_comp_extension
        (K := L) (L := F.L'))
  exact ⟨{
    K' := F.K'
    L' := F.L'
    fieldK' := inferInstance
    fieldL' := inferInstance
    numberFieldK' := inferInstance
    numberFieldL' := inferInstance
    algebraKK' := inferInstance
    algebraLL' := inferInstance
    algebraK'L' := inferInstance
    algebraKL' := inferInstance
    scalarTowerKK'L' := inferInstance
    scalarTowerKLL' := inferInstance
    finiteDimensionalKK' := inferInstance
    finiteDimensionalLL' := inferInstance
    finiteDimensionalK'L' := inferInstance
    isGaloisK'L' := inferInstance
    isCyclicK'L' := inferInstance
    m := F.m
    primitiveRoot := F.primitiveRoot
    degreeTop := F.degreeTop
    degreeLeft := F.degreeLeft
    degreeRight := F.degreeRight
    m_dvd_pred := F.m_dvd_pred
    iK := EK'.classMap
    iL := EL'.classMap
    topSquare := htop
    bottomSquare := hbottom
    downUpK := hdownK
    downUpL := hdownL }⟩

/-- **Lemma VII.6.1.**  It is enough to prove the second inequality for
prime-degree cyclic extensions whose base contains a primitive `p`th root
of unity. -/
theorem cyclotomicChangeStatement : (∀ (p : ℕ), p.Prime →
      (∀ (K L : Type u) [Field K] [Field L]
        [NumberField K] [NumberField L]
        [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
        [IsCyclic Gal(L/K)],
        (primitiveRoots p K).Nonempty → Module.finrank K L = p →
          SecondInequalityAt K L) →
      ∀ (K L : Type u) [Field K] [Field L]
        [NumberField K] [NumberField L]
        [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
        [IsCyclic Gal(L/K)],
        Module.finrank K L = p → SecondInequalityAt K L) :=
  idele_statement_bridges
    cyclotomicChangeBridge
    normExponentBridge

end

end Submission.CField.KNIndex
