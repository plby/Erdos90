import Submission.ClassField.NormIndex.IndexComparison
import Submission.ClassField.NormIndex.IdeleTowerTransitivity
import Submission.ClassField.CyclicIdeles.NormalSubgroupBridge

/-!
# Chapter VII, Section 5, Lemma 5.4: norm indices in a tower

The norm index in a tower divides the product of the two successive norm
indices.  On idèle classes this is the elementary fact that, for homomorphisms
`A → B → C`, the index of the range of the composite divides the product
of the indices of the two ranges.
-/

namespace Submission.CField.CIdeles

open IsDedekindDomain NumberField
open Submission.CField.Ideles
open Submission.CField.NIndex

noncomputable section

universe u

/-- The range-index inequality for a composite of group homomorphisms. -/
private theorem range_comp_dvd
    {A B C : Type u} [Group A] [Group B] [Group C]
    (f : B →* C) (g : A →* B) :
    (f.comp g).range.index ∣ f.range.index * g.range.index := by
  rw [MonoidHom.range_comp]
  have hle : g.range.map f ≤ f.range := Subgroup.map_le_range _ _
  rw [← Subgroup.relIndex_mul_index hle]
  have hrel : (g.range.map f).relIndex f.range ∣ g.range.index := by
    rw [MonoidHom.range_eq_map f]
    rw [Subgroup.relIndex_map_map]
    rw [top_sup_eq, Subgroup.relIndex_top_right]
    exact Subgroup.index_dvd_of_le le_sup_left
  simpa [mul_comm] using Nat.mul_dvd_mul_right hrel f.range.index

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

private theorem range_index_principal
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    (canonicalIdeleNorm (K := K) (L := L)).range.index =
      (principalIdeles (RingOfIntegers K) K ⊔
        ideleNormSubgroup (K := K) (L := L)).index := by
  rw [Subgroup.index_eq_card]
  exact nat_principal_index K L

set_option maxHeartbeats 1000000 in
-- Fixed-field number-field and norm-map instance synthesis is expensive.
/-- The norm index for `L/K` divides the product of the norm indices in the
tower through an actual normal fixed field. -/
theorem indexTowerBridge : IndexTowerBridge.{u} := by
  intro K L _ _ _ _ _ _ _ H hnormal
  letI : H.Normal := hnormal
  let E := IntermediateField.fixedField H
  letI : IsGalois K E := IsGalois.of_fixedField_normal_subgroup H
  letI : IsGalois E L := inferInstance
  change (principalIdeles (RingOfIntegers K) K ⊔
      ideleNormSubgroup (K := K) (L := L)).index ∣
    (principalIdeles (RingOfIntegers K) K ⊔
        ideleNormSubgroup (K := K) (L := E)).index *
      (principalIdeles (RingOfIntegers E) E ⊔
        ideleNormSubgroup (K := E) (L := L)).index
  rw [← range_index_principal K L,
    ← range_index_principal K E,
    ← range_index_principal E L,
    canonical_norm_trans (K := K) (E := E) (L := L)]
  exact range_comp_dvd
    (canonicalIdeleNorm (K := K) (L := E))
    (canonicalIdeleNorm (K := E) (L := L))

end

end Submission.CField.CIdeles
