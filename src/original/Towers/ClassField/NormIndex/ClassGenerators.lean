import Towers.ClassField.NormIndex.UnitsPlacesIdeles

/-!
# The class-generator input to Theorem VII.4.3

Lemma VII.4.2 turns a finite set of ideal-class generators into generation of
the idèles by principal idèles and idèles integral away from that set. This
file compares that subgroup with the restriction along a base-field set of
places used in Theorem VII.4.3.
-/

namespace Towers.CField.NIndex

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.ICohomo

noncomputable section

universe u

/-- Lemma VII.4.2 supplies the class-generator-to-idèle-generation bridge in
Theorem VII.4.3. Infinite places are adjoined to the selected upper places;
their addition does not alter the finite support condition. -/
theorem ideles_bridge_ideal
    (h42 : (∀ (K : Type u) [Field K] [NumberField K]
          (S : Finset (NumberFieldPlace K)),
          ContainsAllPlaces K S →
            CIGenera K S →
            principalIdeles (NumberField.RingOfIntegers K) K ⊔ idelesAtPlaces K S = ⊤)) :
    GeneratorsIdelesBridge.{u} := by
  intro K L _ _ _ _ _ _ _ S hgenerators
  classical
  obtain ⟨T, hTgenerators, hTcontract⟩ := hgenerators
  let Tinfty : Finset (NumberFieldPlace L) :=
    Finset.univ.map ⟨fun v : InfinitePlace L ↦ Sum.inr v,
      Sum.inr_injective⟩
  let T' : Finset (NumberFieldPlace L) := T ∪ Tinfty
  have hTinfinite : ContainsAllPlaces L T' := by
    intro v
    apply Finset.mem_union_right
    exact Finset.mem_map.mpr ⟨v, Finset.mem_univ v, rfl⟩
  have hsupported :
      fractionalIdealsPlaces L T ≤
        fractionalIdealsPlaces L T' := by
    apply Subgroup.closure_mono
    rintro I ⟨p, hp, rfl⟩
    exact ⟨p, Finset.mem_union_left Tinfty hp, rfl⟩
  have hTgenerators' : CIGenera L T' := by
    unfold CIGenera at hTgenerators ⊢
    apply top_unique
    rw [← hTgenerators]
    exact Subgroup.map_mono
      (f := ClassGroup.mk (R := NumberField.RingOfIntegers L) (K := L))
      hsupported
  have hrestricted :
      idelesAtPlaces L T' ≤
        ICohomo.idelesAtPlaces (K := K) (L := L) S := by
    intro x hx Q hQoutside
    apply hx Q
    intro hQT'
    have hQT : (Sum.inl Q : NumberFieldPlace L) ∈ T := by
      simpa [T', Tinfty] using hQT'
    exact hQoutside (hTcontract Q hQT)
  have htop := h42 L T' hTinfinite hTgenerators'
  apply top_unique
  rw [← htop]
  exact sup_le_sup le_rfl hrestricted

end

end Towers.CField.NIndex
