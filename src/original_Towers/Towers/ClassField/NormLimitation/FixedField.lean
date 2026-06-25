import Towers.ClassField.NormLimitation.FiniteReciprocity

/-!
# The fixed-field step in Lemma VII.9.1

For a subgroup of a finite abelian Galois group, this file realizes its
fixed field inside the chosen separable closure.  This is the literal field
used in Milne's proof of Lemma 9.1.
-/

namespace Towers.CField.NLimita

open scoped IsMulCommutative
open NumberField
open Towers.CField.LFTheory
open Towers.CField.Ideles
open Towers.CField.Recip

noncomputable section

universe u

variable {K : Type u} [Field K]

noncomputable local instance fixedFieldNumberField
    [NumberField K] (L : FASubext K) : NumberField L.1 :=
  NumberField.of_module_finite K L.1

/-- The fixed field of `H ≤ Gal(L/K)`, embedded in the fixed separable
closure already containing `L`. -/
noncomputable def fixedSubextension
    (L : FASubext K) (H : Subgroup Gal(L.1/K)) :
    FASubext K := by
  let F₀ : IntermediateField K L.1 := IntermediateField.fixedField H
  let i : L.1 →ₐ[K] SeparableClosure K := L.1.val
  let F : IntermediateField K (SeparableClosure K) := F₀.map i
  let e : F₀ ≃ₐ[K] F := IntermediateField.equivMap F₀ i
  letI : FiniteDimensional K F :=
    LinearEquiv.finiteDimensional e.toLinearEquiv
  letI : Subgroup.Normal H := inferInstance
  letI : IsGalois K F₀ := IsGalois.of_fixedField_normal_subgroup H
  letI : IsGalois K F := IsGalois.of_algEquiv e
  let q : Gal(L.1/K) ⧸ H ≃* Gal(F₀/K) :=
    IsGalois.normalAutEquivQuotient H
  letI : IsMulCommutative Gal(F₀/K) :=
    ⟨⟨fun sigma tau ↦ by
      apply q.symm.injective
      simpa only [map_mul] using mul_comm (q.symm sigma) (q.symm tau)⟩⟩
  let a : Gal(F₀/K) ≃* Gal(F/K) := e.autCongr
  letI : IsMulCommutative Gal(F/K) :=
    ⟨⟨fun sigma tau ↦ by
      apply a.symm.injective
      simpa only [map_mul] using mul_comm (a.symm sigma) (a.symm tau)⟩⟩
  exact
    { finiteIntermediateField :=
        { F with
          finiteDimensional := inferInstance
          isGalois := inferInstance }
      isAbelian := inferInstance }

/-- The evident equivalence from the fixed field inside `L` to its image in
the chosen separable closure. -/
noncomputable def fixedSubextensionEquiv
    (L : FASubext K) (H : Subgroup Gal(L.1/K)) :
    IntermediateField.fixedField H ≃ₐ[K]
      (fixedSubextension L H).1 :=
  IntermediateField.equivMap (IntermediateField.fixedField H) L.1.val

@[simp]
theorem fixed_subextension_coe
    (L : FASubext K) (H : Subgroup Gal(L.1/K))
    (x : IntermediateField.fixedField H) :
    (((fixedSubextensionEquiv L H x :
      (fixedSubextension L H).1) : SeparableClosure K)) =
        ((x : L.1) : SeparableClosure K) :=
  rfl

/-- On the absolute Galois group, restriction to the fixed subextension has
kernel equal to the inverse image of `H` under restriction to `L`. -/
theorem fixed_subextension_restriction
    (L : FASubext K) (H : Subgroup Gal(L.1/K)) :
    (AlgEquiv.restrictNormalHom (fixedSubextension L H).1 :
      LocalAbsoluteGalois K →*
        Gal((fixedSubextension L H).1/K)).ker =
      H.comap (AlgEquiv.restrictNormalHom L.1 :
        LocalAbsoluteGalois K →* Gal(L.1/K)) := by
  ext sigma
  rw [IntermediateField.restrictNormalHom_ker]
  change sigma ∈
      (fixedSubextension L H).1.fixingSubgroup ↔
    (AlgEquiv.restrictNormalHom L.1 sigma) ∈ H
  rw [IntermediateField.mem_fixingSubgroup_iff]
  have hright :
      (AlgEquiv.restrictNormalHom L.1 sigma) ∈ H ↔
        ∀ x : L.1, x ∈ IntermediateField.fixedField H →
          (AlgEquiv.restrictNormalHom L.1 sigma) x = x := by
    constructor
    · intro h
      rw [← IntermediateField.fixingSubgroup_fixedField H] at h
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 h
    · intro h
      rw [← IntermediateField.fixingSubgroup_fixedField H]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).2 h
  rw [hright]
  constructor
  · intro hsigma x hx
    apply Subtype.ext
    have h := hsigma
      (fixedSubextensionEquiv L H ⟨x, hx⟩)
      (fixedSubextensionEquiv L H ⟨x, hx⟩).property
    simpa only [AlgEquiv.restrictNormalHom_apply,
      fixed_subextension_coe] using h
  · intro hsigma y hy
    let e := fixedSubextensionEquiv L H
    obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
    have hfixed := hsigma (x : L.1) x.property
    have hfixedSep :
        sigma (((x : IntermediateField.fixedField H) : L.1) :
          SeparableClosure K) = ((x : L.1) : SeparableClosure K) :=
      by
        calc
          sigma (((x : IntermediateField.fixedField H) : L.1) :
              SeparableClosure K) =
            (((AlgEquiv.restrictNormalHom L.1 sigma) (x : L.1) :
              L.1) : SeparableClosure K) :=
                (AlgEquiv.restrictNormal_commutes sigma L.1 (x : L.1)).symm
          _ = ((x : L.1) : SeparableClosure K) :=
            congrArg (fun z : L.1 ↦ (z : SeparableClosure K)) hfixed
    have hxy :
        ((e x : (fixedSubextension L H).1) :
          SeparableClosure K) = y := congrArg Subtype.val hx
    calc
      sigma y = sigma
          ((e x : (fixedSubextension L H).1) :
            SeparableClosure K) := congrArg sigma hxy.symm
      _ = ((e x : (fixedSubextension L H).1) :
          SeparableClosure K) := by
            simpa only [e, fixed_subextension_coe] using hfixedSep
      _ = y := hxy

/-- The same kernel formula after passing to the abelianized absolute Galois
group.  Thus the quotient layer attached to the fixed field is exactly the
quotient of the `L`-layer by `H`. -/
theorem subextension_restriction_ker
    (L : FASubext K) (H : Subgroup Gal(L.1/K)) :
    (localAbelianRestriction (fixedSubextension L H)).ker =
      H.comap (localAbelianRestriction L) := by
  ext q
  obtain ⟨sigma, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.topologicalClosure
      (commutator (LocalAbsoluteGalois K))) q
  have h := SetLike.ext_iff.mp
    (fixed_subextension_restriction L H) sigma
  simpa only [MonoidHom.mem_ker, Subgroup.mem_comap,
    abelian_restriction_quotient] using h

/-- Finite reciprocity transports the preceding restriction-kernel formula
to idèle classes. -/
theorem fixed_subextension_ker
    [NumberField K]
    (phi : IdeleGroup (RingOfIntegers K) K →*
      AbsoluteAbelianGalois K)
    (hphi : ContinuousGlobalArtin phi)
    (hrec : IdeleReciprocityLaw (K := K))
    (L : FASubext K) (H : Subgroup Gal(L.1/K)) :
    let M := fixedSubextension L H
    let hL := (hrec phi hphi).2 L
    let hM := (hrec phi hphi).2 M
    (ideleClassArtin M phi hM).ker =
      H.comap (ideleClassArtin L phi hL) := by
  dsimp only
  let hL := (hrec phi hphi).2 L
  let M := fixedSubextension L H
  let hM := (hrec phi hphi).2 M
  ext c
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (principalIdeles (RingOfIntegers K) K) c
  have h := SetLike.ext_iff.mp
    (subextension_restriction_ker L H) (phi x)
  simpa only [MonoidHom.mem_ker, Subgroup.mem_comap,
    ideleClassArtin, MonoidHom.comp_apply,
    idele_reciprocity_mk] using h

end

end Towers.CField.NLimita
