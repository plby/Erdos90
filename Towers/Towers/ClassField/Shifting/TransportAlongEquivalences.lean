import Towers.ClassField.Shifting.NormTransitivity
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Milne, Class Field Theory, Theorem II.3.10: transport along group equivalences

The hypothesis of Theorem II.3.10 is stated for subgroups.  During the
inductive proof it is convenient to use arbitrary injective homomorphisms.
This file supplies the equivalence transport which identifies those two
formulations.
-/

namespace Towers.CField.Shifting

open CategoryTheory CategoryTheory.Limits Rep Representation

noncomputable section

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

/-- Restricting successively along a group equivalence and its inverse gives
back the original representation. -/
noncomputable def resCounitIso (e : G ≃* H) (A : Rep.{u} k H) :
    Rep.res e.symm.toMonoidHom (Rep.res e.toMonoidHom A) ≅ A :=
  Rep.mkIso {
    toLinearEquiv := LinearEquiv.refl k A
    isIntertwining' := fun h => by
      change A.ρ (e (e.symm h)) = A.ρ h
      rw [e.apply_symm_apply] }

/-- Group cohomology is invariant under relabelling the acting group by an
equivalence. -/
noncomputable def cohomologyMulIso (e : G ≃* H)
    (A : Rep.{u} k H) (n : ℕ) :
    groupCohomology A n ≅
      groupCohomology (Rep.res e.toMonoidHom A) n where
  hom := groupCohomology.map e.toMonoidHom (𝟙 _) n
  inv := groupCohomology.map e.symm.toMonoidHom
    (resCounitIso e A).hom n
  hom_inv_id := by
    rw [← groupCohomology.map_comp]
    change HomologicalComplex.homologyMap _ n = _
    have hc : groupCohomology.cochainsMap
        (e.toMonoidHom.comp e.symm.toMonoidHom)
        ((Rep.resFunctor e.symm.toMonoidHom).map
          (𝟙 (Rep.res e.toMonoidHom A)) ≫
            (resCounitIso e A).hom) =
        𝟙 (groupCohomology.inhomogeneousCochains A) := by
      ext i x g
      simp [groupCohomology.cochainsMap, resCounitIso]
    rw [hc]
    exact HomologicalComplex.homologyMap_id _ _
  inv_hom_id := by
    rw [← groupCohomology.map_comp]
    change HomologicalComplex.homologyMap _ n = _
    have hc : groupCohomology.cochainsMap
        (e.symm.toMonoidHom.comp e.toMonoidHom)
        ((Rep.resFunctor e.toMonoidHom).map
          (resCounitIso e A).hom ≫
            𝟙 (Rep.res e.toMonoidHom A)) =
        𝟙 (groupCohomology.inhomogeneousCochains
          (Rep.res e.toMonoidHom A)) := by
      ext i x g
      simp [groupCohomology.cochainsMap, resCounitIso]
    rw [hc]
    exact HomologicalComplex.homologyMap_id _ _

/-- A cohomological vanishing hypothesis on literal subgroups implies the
equivalent formulation for arbitrary injective homomorphisms. -/
theorem cohomology_12_subgroups
    (A : Rep.{u} k H)
    (h12 : ∀ S : Subgroup H,
      IsZero (groupCohomology (Rep.res S.subtype A) 1) ∧
      IsZero (groupCohomology (Rep.res S.subtype A) 2)) :
    ∀ {K : Type u} [Group K] (f : K →* H), Function.Injective f →
      IsZero (groupCohomology (Rep.res f A) 1) ∧
      IsZero (groupCohomology (Rep.res f A) 2) := by
  intro K _ f hf
  let e : K ≃* f.range := MonoidHom.ofInjective hf
  have hR := h12 f.range
  constructor
  · have h := hR.1.of_iso
        (cohomologyMulIso e (Rep.res f.range.subtype A) 1).symm
    simpa only [Rep.res, MonoidHom.coe_comp, Function.comp_def, e] using h
  · have h := hR.2.of_iso
        (cohomologyMulIso e (Rep.res f.range.subtype A) 2).symm
    simpa only [Rep.res, MonoidHom.coe_comp, Function.comp_def, e] using h

/-- Tate degree-zero vanishing is preserved when the acting finite group is
relabelled by an equivalence. -/
theorem subsingleton_tate_cohomology [Fintype G] [Fintype H]
    (e : G ≃* H) (A : Rep.{u} k H)
    (hzero : Subsingleton
      (tateCohomologyZero (Rep.res e.toMonoidHom A))) :
    Subsingleton (tateCohomologyZero A) := by
  apply (coinvariants_invariants_surjective A).1
  have hnorm :=
    (coinvariants_invariants_surjective
      (Rep.res e.toMonoidHom A)).2 hzero
  intro x
  let xe : (Rep.res e.toMonoidHom A).ρ.invariants :=
    ⟨x.1, fun g => x.2 (e g)⟩
  obtain ⟨q, hq⟩ := hnorm xe
  obtain ⟨y, rfl⟩ := Coinvariants.mk_surjective
    (Rep.res e.toMonoidHom A).ρ q
  refine ⟨Coinvariants.mk A.ρ y, ?_⟩
  apply Subtype.ext
  have hv := congrArg Subtype.val hq
  rw [coinvariants_invariants_mk] at hv
  change A.ρ.norm y = x.1
  rw [Representation.norm, LinearMap.sum_apply,
    ← e.sum_comp (fun h : H => A.ρ h y)]
  simpa [xe, Representation.norm] using hv

end

end Towers.CField.Shifting
