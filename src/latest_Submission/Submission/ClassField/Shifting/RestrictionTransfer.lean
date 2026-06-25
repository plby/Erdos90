import Submission.ClassField.TateCohomology.AddEquivAbelianization
import Submission.ClassField.Shifting.ShapiroUnitGenerator
import Submission.ClassField.Shifting.TransferBridge

/-!
# Proposition II.3.2(b): homological restriction is transfer

For a finite-index subgroup `H ≤ G`, the standard restriction in group
homology is the unit `A ⟶ Indᴳₕ(Resᴳₕ A)` followed by Shapiro's
isomorphism.  In degree one with integral trivial coefficients, it is the
Verlag `Gᵃᵇ ⟶ Hᵃᵇ`.
-/

namespace Submission.CField.Shifting

open Additive CategoryTheory Finsupp

variable {G : Type} [Group G]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- The standard degree-one homological restriction associated to a
finite-index subgroup. -/
noncomputable def restriction1Int (H : Subgroup G) [H.FiniteIndex] :
    groupHomology (Rep.trivial ℤ G ℤ) 1 →+
      groupHomology (Rep.trivial ℤ H ℤ) 1 := by
  classical
  exact (groupHomology.map (MonoidHom.id G)
      ((Rep.resIndAdjunction ℤ H).unit.app (Rep.trivial ℤ G ℤ)) 1 ≫
    (groupHomology.indIso H (Rep.trivial ℤ H ℤ) 1).hom).hom.toAddMonoidHom

/-- The inhomogeneous chain map inducing `restriction1Int`. -/
noncomputable def subgroupRestrictionChain
    (H : Subgroup G) [H.FiniteIndex] :
    groupHomology.inhomogeneousChains (Rep.trivial ℤ G ℤ) ⟶
      groupHomology.inhomogeneousChains (Rep.trivial ℤ H ℤ) := by
  classical
  exact groupHomology.chainsMap
      (A := Rep.trivial ℤ G ℤ)
      (B := Rep.ind H.subtype (Rep.trivial ℤ H ℤ))
      (MonoidHom.id G)
      ((Rep.resIndAdjunction ℤ H).unit.app (Rep.trivial ℤ G ℤ)) ≫
    Rep.indShapiroChain H (Rep.trivial ℤ H ℤ)

theorem restriction_int_homology
    (H : Subgroup G) [H.FiniteIndex] :
    restriction1Int H =
      (HomologicalComplex.homologyMap (subgroupRestrictionChain H) 1).hom.toAddMonoidHom := by
  classical
  simp only [restriction1Int, subgroupRestrictionChain,
    Rep.ind_iso_explicit, HomologicalComplex.homologyMap_comp]
  rfl

open scoped Classical in
theorem restriction_chain_generator
    (H : Subgroup G) [H.FiniteIndex] (g : G) :
    ((subgroupRestrictionChain H).f 1).hom
        (single (fun _ : Fin 1 => g) 1) =
      ∑ q : Quotient (QuotientGroup.rightRel H),
        single
          (fun _ : Fin 1 =>
            Rep.rightCosetCorrection H (Quotient.out q * g)) 1 := by
  simp only [subgroupRestrictionChain, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [groupHomology.chainsMap_f_single]
  change
    ((Rep.indShapiroChain H (Rep.trivial ℤ H ℤ)).f 1).hom
      (single (fun _ : Fin 1 => g)
        (((Rep.resIndAdjunction ℤ H).unit.app
          (Rep.trivial ℤ G ℤ)).hom (1 : ℤ))) = _
  exact Rep.ind_shapiro_chain H g

set_option maxRecDepth 10000 in
theorem restriction_1_intπ_single
    (H : Subgroup G) [H.FiniteIndex] (g : G) :
    restriction1Int H
        (groupHomology.H1π (Rep.trivial ℤ G ℤ)
          ((groupHomology.cycles₁IsoOfIsTrivial
            (Rep.trivial ℤ G ℤ)).inv (single g 1))) =
      ∑ q : Quotient (QuotientGroup.rightRel H),
        groupHomology.H1π (Rep.trivial ℤ H ℤ)
          ((groupHomology.cycles₁IsoOfIsTrivial
            (Rep.trivial ℤ H ℤ)).inv
              (single (Rep.rightCosetCorrection H (Quotient.out q * g)) 1)) := by
  classical
  rw [restriction_int_homology]
  let xG := (groupHomology.cycles₁IsoOfIsTrivial
    (Rep.trivial ℤ G ℤ)).inv (single g 1)
  let yG := (groupHomology.isoCycles₁ (Rep.trivial ℤ G ℤ)).inv xG
  let fH : H →₀ ℤ :=
    ∑ q : Quotient (QuotientGroup.rightRel H),
      single (Rep.rightCosetCorrection H (Quotient.out q * g)) 1
  let cH : (Fin 1 → H) →₀ ℤ :=
    ∑ q : Quotient (QuotientGroup.rightRel H),
      single
        (fun _ : Fin 1 => Rep.rightCosetCorrection H (Quotient.out q * g)) 1
  let xH := (groupHomology.cycles₁IsoOfIsTrivial
    (Rep.trivial ℤ H ℤ)).inv fH
  let yH := (groupHomology.isoCycles₁ (Rep.trivial ℤ H ℤ)).inv xH
  have hiG :
      groupHomology.iCycles (Rep.trivial ℤ G ℤ) 1 yG =
        single (fun _ : Fin 1 => g) 1 := by
    have hz := congrArg (fun f => f.hom xG)
      (groupHomology.isoCycles₁_inv_comp_iCycles
        (A := Rep.trivial ℤ G ℤ))
    change
      groupHomology.iCycles (Rep.trivial ℤ G ℤ) 1 yG =
        (groupHomology.chainsIso₁ (Rep.trivial ℤ G ℤ)).inv xG.1 at hz
    rw [hz]
    dsimp only [xG]
    change
      (groupHomology.chainsIso₁ (Rep.trivial ℤ G ℤ)).inv
        (single g 1) = _
    apply (ModuleCat.mono_iff_injective
      (groupHomology.chainsIso₁ (Rep.trivial ℤ G ℤ)).hom).1 inferInstance
    rw [Iso.inv_hom_id_apply]
    change
      single g (1 : ℤ) =
        (Finsupp.domLCongr (Equiv.funUnique (Fin 1) G) :
          ((Fin 1 → G) →₀ ℤ) ≃ₗ[ℤ] (G →₀ ℤ))
            (single (fun _ : Fin 1 => g) (1 : ℤ))
    rw [Finsupp.domLCongr_single]
    rfl
  have hiH :
      groupHomology.iCycles (Rep.trivial ℤ H ℤ) 1 yH = cH := by
    have hz := congrArg (fun f => f.hom xH)
      (groupHomology.isoCycles₁_inv_comp_iCycles
        (A := Rep.trivial ℤ H ℤ))
    change
      groupHomology.iCycles (Rep.trivial ℤ H ℤ) 1 yH =
        (groupHomology.chainsIso₁ (Rep.trivial ℤ H ℤ)).inv xH.1 at hz
    rw [hz]
    dsimp only [xH]
    change
      (groupHomology.chainsIso₁ (Rep.trivial ℤ H ℤ)).inv fH = cH
    dsimp only [fH, cH]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro q hq
    apply (ModuleCat.mono_iff_injective
      (groupHomology.chainsIso₁ (Rep.trivial ℤ H ℤ)).hom).1 inferInstance
    rw [Iso.inv_hom_id_apply]
    change
      single (Rep.rightCosetCorrection H (Quotient.out q * g)) (1 : ℤ) =
        (Finsupp.domLCongr (Equiv.funUnique (Fin 1) H) :
          ((Fin 1 → H) →₀ ℤ) ≃ₗ[ℤ] (H →₀ ℤ))
            (single
              (fun _ : Fin 1 =>
                Rep.rightCosetCorrection H (Quotient.out q * g)) (1 : ℤ))
    rw [Finsupp.domLCongr_single]
    rfl
  have hcycles :
      HomologicalComplex.cyclesMap (subgroupRestrictionChain H) 1 yG = yH := by
    apply (ModuleCat.mono_iff_injective
      (groupHomology.iCycles (Rep.trivial ℤ H ℤ) 1)).1 inferInstance
    have hc := congrArg (fun f => f.hom yG)
      (HomologicalComplex.cyclesMap_i (subgroupRestrictionChain H) 1)
    change
      groupHomology.iCycles (Rep.trivial ℤ H ℤ) 1
          (HomologicalComplex.cyclesMap (subgroupRestrictionChain H) 1 yG) =
        ((subgroupRestrictionChain H).f 1)
          (groupHomology.iCycles (Rep.trivial ℤ G ℤ) 1 yG) at hc
    have hmap :
        ((subgroupRestrictionChain H).f 1)
            (groupHomology.iCycles (Rep.trivial ℤ G ℤ) 1 yG) = cH := by
      rw [hiG]
      exact restriction_chain_generator H g
    exact hc.trans (hmap.trans hiH.symm)
  have hnat := congrArg (fun f => f.hom yG)
    (HomologicalComplex.homologyπ_naturality (subgroupRestrictionChain H) 1)
  change
    HomologicalComplex.homologyMap (subgroupRestrictionChain H) 1
        (groupHomology.π (Rep.trivial ℤ G ℤ) 1 yG) =
      groupHomology.π (Rep.trivial ℤ H ℤ) 1
        (HomologicalComplex.cyclesMap (subgroupRestrictionChain H) 1 yG) at hnat
  rw [hcycles] at hnat
  change
    HomologicalComplex.homologyMap (subgroupRestrictionChain H) 1
        (groupHomology.H1π (Rep.trivial ℤ G ℤ) xG) =
      groupHomology.H1π (Rep.trivial ℤ H ℤ) xH at hnat
  change
    HomologicalComplex.homologyMap (subgroupRestrictionChain H) 1
        (groupHomology.H1π (Rep.trivial ℤ G ℤ) xG) = _
  rw [hnat]
  dsimp only [xH, fH]
  rw [map_sum, map_sum]

/-- **Proposition II.3.2(b).** Under the canonical identifications
`H₁(G, ℤ) ≃ Gᵃᵇ` and `H₁(H, ℤ) ≃ Hᵃᵇ`, homological restriction
is the Verlag. -/
theorem restriction_1_verlagerung
    (H : Subgroup G) [H.FiniteIndex] :
    (TCohomo.homology1Abelianization H).toAddMonoidHom.comp
        (restriction1Int H) =
      (ARecip.verlagerung H).toAdditive.comp
        (TCohomo.homology1Abelianization G).toAddMonoidHom := by
  classical
  apply AddMonoidHom.ext
  intro x
  obtain ⟨g, hg⟩ : ∃ g : G,
      TCohomo.homology1Abelianization G x =
        Additive.ofMul (Abelianization.of g) := by
    rcases TCohomo.homology1Abelianization G x with ⟨g⟩
    exact ⟨g, rfl⟩
  have hgenG :
      TCohomo.homology1Abelianization G
          (groupHomology.H1π (Rep.trivial ℤ G ℤ)
            ((groupHomology.cycles₁IsoOfIsTrivial
              (Rep.trivial ℤ G ℤ)).inv (single g 1))) =
        Additive.ofMul (Abelianization.of g) := by
    simp only [TCohomo.homology1Abelianization,
      AddEquiv.trans_apply]
    rw [groupHomology.H1AddEquivOfIsTrivial_single]
    have hrid :
        (TensorProduct.rid ℤ (Additive (Abelianization G))).toAddEquiv
            (Additive.ofMul (Abelianization.of g) ⊗ₜ[ℤ] (1 : ℤ)) =
          TensorProduct.rid ℤ (Additive (Abelianization G))
            (Additive.ofMul (Abelianization.of g) ⊗ₜ[ℤ] (1 : ℤ)) := rfl
    rw [hrid, TensorProduct.rid_tmul, one_smul]
  have hx : x =
      groupHomology.H1π (Rep.trivial ℤ G ℤ)
        ((groupHomology.cycles₁IsoOfIsTrivial
          (Rep.trivial ℤ G ℤ)).inv (single g 1)) := by
    apply (TCohomo.homology1Abelianization G).injective
    rw [hg, hgenG]
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [hx, restriction_1_intπ_single, map_sum, hgenG]
  have hterm (q : Quotient (QuotientGroup.rightRel H)) :
      TCohomo.homology1Abelianization H
          (groupHomology.H1π (Rep.trivial ℤ H ℤ)
            ((groupHomology.cycles₁IsoOfIsTrivial
              (Rep.trivial ℤ H ℤ)).inv
                (single (Rep.rightCosetCorrection H (Quotient.out q * g)) 1))) =
        Additive.ofMul
          (Abelianization.of (Rep.rightCosetCorrection H (Quotient.out q * g))) := by
    simp only [TCohomo.homology1Abelianization,
      AddEquiv.trans_apply]
    rw [groupHomology.H1AddEquivOfIsTrivial_single]
    have hrid :
        (TensorProduct.rid ℤ (Additive (Abelianization H))).toAddEquiv
            (Additive.ofMul
                (Abelianization.of
                  (Rep.rightCosetCorrection H (Quotient.out q * g))) ⊗ₜ[ℤ]
              (1 : ℤ)) =
          TensorProduct.rid ℤ (Additive (Abelianization H))
            (Additive.ofMul
                (Abelianization.of
                  (Rep.rightCosetCorrection H (Quotient.out q * g))) ⊗ₜ[ℤ]
              (1 : ℤ)) := rfl
    rw [hrid, TensorProduct.rid_tmul, one_smul]
  calc
    _ = ∑ q : Quotient (QuotientGroup.rightRel H),
        Additive.ofMul
          (Abelianization.of
            (Rep.rightCosetCorrection H (Quotient.out q * g))) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hterm q
    _ = Additive.ofMul
        (MonoidHom.transfer (Abelianization.of : H →* Abelianization H) g) :=
      (transfer_coset_correction H g).symm
    _ = (ARecip.verlagerung H).toAdditive
        (Additive.ofMul (Abelianization.of g)) := by
      simp only [MonoidHom.coe_toAdditive, Function.comp_apply, toMul_ofMul,
        ARecip.verlagerung_apply_of,
        ARecip.transferToAbelianization]

end Submission.CField.Shifting
