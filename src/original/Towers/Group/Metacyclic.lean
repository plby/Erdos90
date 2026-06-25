import Mathlib


noncomputable section

namespace Towers

def IMSubgro
    {Q : Type*} [Group Q] (H : Subgroup Q) : Prop :=
  ∃ I : Subgroup H, ∃ _ : I.Normal,
    IsCyclic I ∧ IsCyclic (H ⧸ I)

lemma IMSubgro.map_subgroup_mulequiv
    {Q R : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (H : Subgroup Q)
    (hH : IMSubgro H) :
    IMSubgro (e.mapSubgroup H) := by
  classical
  rcases hH with ⟨I, hI_normal, hI_cyclic, hquot_cyclic⟩
  let eH : H ≃* e.mapSubgroup H := e.subgroupMap H
  let J : Subgroup (e.mapSubgroup H) := I.map eH.toMonoidHom
  have hJ_normal : J.Normal := by
    exact hI_normal.map eH.toMonoidHom eH.surjective
  have hJ_cyclic : IsCyclic J := by
    exact (eH.subgroupMap I).isCyclic.mp hI_cyclic
  have hquot_cyclic' : IsCyclic ((e.mapSubgroup H) ⧸ J) := by
    have hIJ : I ≤ J.comap eH.toMonoidHom := by
      intro x hx
      exact ⟨x, hx, rfl⟩
    let qmap : H ⧸ I →* (e.mapSubgroup H) ⧸ J :=
      QuotientGroup.map I J eH.toMonoidHom hIJ
    have hmk_surjective :
        Function.Surjective
          (QuotientGroup.mk' J ∘ eH.toMonoidHom :
            H → (e.mapSubgroup H) ⧸ J) := by
      intro y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective J y
      obtain ⟨x, rfl⟩ := eH.surjective z
      exact ⟨x, rfl⟩
    exact isCyclic_of_surjective qmap
      (QuotientGroup.map_surjective_of_surjective
        (N := I) (M := J) eH.toMonoidHom hmk_surjective hIJ)
  exact ⟨J, hJ_normal, hJ_cyclic, hquot_cyclic'⟩

end Towers
