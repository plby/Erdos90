import Towers.ClassField.LocalReciprocity.LocalUnitsRep

/-!
# The degree-minus-two Tate shift on a cyclic generator

This file computes the two exceptional connecting maps used by Tate's
degree-minus-two shift.  With Mathlib's inhomogeneous-chain convention, the
class of `g⁻¹` first maps to the coinvariant class of `g - 1`; the norm in
the splitting module then has coefficient equal to the cyclic product of the
chosen two-cocycle along `g`.
-/

namespace Towers.CField.Shifting

open AddSubgroup CategoryTheory CategoryTheory.Limits Rep Representation
open Towers.CField.TCohomo

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- Elementwise form of the norm snake connecting isomorphism. -/
theorem iso_short_exact
    (X : ShortComplex (Rep.{u} k G)) (hX : X.ShortExact)
    (hneg : Subsingleton (tateCohomologyOne X.X₂))
    (hzero : Subsingleton (tateCohomologyZero X.X₂))
    (z : tateCohomologyOne X.X₃)
    (x₂ : X.X₂.ρ.Coinvariants) (x₁ : X.X₁.ρ.invariants)
    (h₂ : (Rep.coinvariantsFunctor k G).map X.g x₂ = z.1)
    (h₁ : (Rep.invariantsFunctor k G).map X.f x₁ =
      normCoinvariantsInvariants X.X₂ x₂) :
    isoShortExact X hX hneg hzero z =
      Submodule.Quotient.mk x₁ := by
  let S := normSnakeInput X hX
  letI : Subsingleton (tateCohomologyOne X.X₂) := hneg
  letI : Subsingleton (tateCohomologyZero X.X₂) := hzero
  let h₀ : IsZero S.L₀.X₂ :=
    (ModuleCat.isZero_of_subsingleton
      (ModuleCat.of k (tateCohomologyOne X.X₂))).of_iso
        (ModuleCat.kernelIsoKer S.v₁₂.τ₂)
  let h₃ : IsZero S.L₃.X₂ :=
    (ModuleCat.isZero_of_subsingleton
      (ModuleCat.of k (tateCohomologyZero X.X₂))).of_iso
        (ModuleCat.cokernelIsoRangeQuotient S.v₁₂.τ₂)
  let a : S.L₀.X₃ :=
    (ModuleCat.kernelIsoKer S.v₁₂.τ₃).inv z
  have ha : S.v₀₁.τ₃ a = z.1 := by
    exact ModuleCat.kernelIsoKer_inv_kernel_ι_apply S.v₁₂.τ₃ z
  have hδ : S.δ a = S.v₂₃.τ₁ x₁ := by
    apply S.δ_apply a x₂ x₁
    · change (Rep.coinvariantsFunctor k G).map X.g x₂ = S.v₀₁.τ₃ a
      rw [ha]
      exact h₂
    · simpa [S, normSnakeInput] using h₁
  change (ModuleCat.cokernelIsoRangeQuotient S.v₁₂.τ₁).hom
      ((S.δIso h₀ h₃).hom a) = Submodule.Quotient.mk x₁
  change (ModuleCat.cokernelIsoRangeQuotient S.v₁₂.τ₁).hom
      (S.δ a) = Submodule.Quotient.mk x₁
  rw [hδ]
  exact ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom_apply
    S.v₁₂.τ₁ x₁

/-- Elementwise form of the low homology connecting isomorphism. -/
theorem homology_short_exact
    (X : ShortComplex (Rep.{u} k G)) (hX : X.ShortExact)
    (hH₁ : IsZero (groupHomology X.X₂ 1))
    (hneg : Subsingleton (tateCohomologyOne X.X₂))
    (z : groupHomology.cycles₁ X.X₃) (y : G →₀ X.X₂)
    (hy : Finsupp.mapRange.linearMap X.g.hom.toLinearMap y = z.1)
    (x : X.X₁) (hx : X.f.hom x = groupHomology.d₁₀ X.X₂ y) :
    (homologyNegShort X hX hH₁ hneg
      (groupHomology.H1π X.X₃ z)).1 = Coinvariants.mk X.X₁.ρ x := by
  change (groupHomology.H0Iso X.X₁).hom
      (groupHomology.δ hX 1 0 rfl (groupHomology.H1π X.X₃ z)) = _
  rw [groupHomology.δ₀_apply hX z y hy x hx]
  exact groupHomology.H0π_comp_H0Iso_hom_apply X.X₁ x

end


section IntegralCyclic

variable {G M : Type} [Group G] [Fintype G]
  [CommGroup M] [MulDistribMulAction G M]

/-- The invariant coefficient obtained by taking the norm of the standard
splitting-module lift of `g - 1`. -/
noncomputable def splittingParameterInvariant
    (φ : groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction G M))
    (hφ : φ (1, 1) = 0) (g : G) :
    (Rep.ofMulDistribMulAction G M).ρ.invariants := by
  let C := Rep.ofMulDistribMulAction G M
  let X := splittingModule C φ hφ
  let b := augmentationClass G g
  let N : X.ρ.invariants :=
    ⟨X.ρ.norm (0, b), fun h ↦ X.ρ.self_norm_apply h (0, b)⟩
  have hN₂ : N.1.2 = 0 := by
    dsimp only [N]
    simp only [Representation.norm, LinearMap.sum_apply]
    let sndHom : (C × augmentationIdeal G) →+ augmentationIdeal G :=
      { toFun := Prod.snd, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
    change sndHom (∑ h : G, X.ρ h (0, b)) = 0
    rw [map_sum]
    change (∑ h : G, augmentationLeftAction h b) = 0
    simp only [b, augmentation_action_class, Finset.sum_sub_distrib]
    have heq : (∑ h : G, augmentationClass G (h * g)) =
        ∑ h : G, augmentationClass G h :=
      Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ ↦ rfl)
    rw [heq, sub_self]
  refine ⟨N.1.1, ?_⟩
  intro h
  have hN := N.2 h
  have hN' := congrArg Prod.fst hN
  change C.ρ h N.1.1 + splittingTwist C φ h N.1.2 = N.1.1 at hN'
  rw [hN₂, map_zero, add_zero] at hN'
  exact hN'

theorem splitting_parameter_coe
    (φ : groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction G M))
    (hφ : φ (1, 1) = 0) (g : G) :
    (splittingParameterInvariant φ hφ g).1 =
      ∑ h : G, φ (h, g) := by
  let C := Rep.ofMulDistribMulAction G M
  change ((splittingModule C φ hφ).ρ.norm
      (0, augmentationClass G g)).1 = _
  simp only [Representation.norm, LinearMap.sum_apply,
    splittingModule_action, map_zero, zero_add,
    splittingTwist_class C φ hφ]
  let fstHom : (C × augmentationIdeal G) →+ C :=
    { toFun := Prod.fst, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  change fstHom (∑ h : G,
    (φ (h, g), augmentationLeftAction h (augmentationClass G g))) = _
  rw [map_sum]
  rfl

/-- Unfolding lemma for the degree-minus-two field of Tate's assembled
two-shift. -/
theorem neg_two_explicit
    (C : Rep ℤ G) (gamma : groupCohomology C 2)
    (hgamma : ∀ x : groupCohomology C 2, x ∈ zmultiples gamma)
    (hcard : Nat.card (groupCohomology C 2) = Fintype.card G)
    (hC1self : IsZero (groupCohomology C 1))
    (hC1 : ∀ H : Subgroup G,
      IsZero (groupCohomology (Rep.res H.subtype C) 1))
    (hboundary : ∀ H : Subgroup G,
      IsIso (groupCohomology.δ
        ((splitting_sequence_short C
          (normalizedCocycleClass C gamma)
          (normalized_cocycle_class C gamma)).map_of_exact
            (Rep.resFunctor H.subtype)) 1 2 rfl))
    (a : groupHomology (Rep.trivial ℤ G ℤ) 1) :
    (restricted_boundary_iso C gamma hgamma hcard hC1self
      hC1 hboundary).negTwo a =
      let φ := normalizedCocycleClass C gamma
      let hφ := normalized_cocycle_class C gamma
      let X := splittingModuleSequence C φ hφ
      let Y := augmentationSequence (G := G)
      let hX := splitting_sequence_short C φ hφ
      let hY := augmentation_short_exact (G := G)
      let hE12 : ∀ H : Subgroup G,
          IsZero (groupCohomology
              (Rep.res H.subtype (splittingModule C φ hφ)) 1) ∧
            IsZero (groupCohomology
              (Rep.res H.subtype (splittingModule C φ hφ)) 2) := by
        apply splitting_12_iso C φ hφ hC1
          cohomology_restrict_ideal
        simpa [φ, hφ] using hboundary
      let hE := allDegrees (splittingModule C φ hφ) hE12
      let hregular12 : ∀ H : Subgroup G,
          IsZero (groupCohomology
              (Rep.res H.subtype (Rep.leftRegular ℤ G)) 1) ∧
          IsZero (groupCohomology
              (Rep.res H.subtype (Rep.leftRegular ℤ G)) 2) := fun H ↦
        ⟨restrict_int_acyclic H 1 Nat.zero_lt_one,
          restrict_int_acyclic H 2 (by omega)⟩
      let hregular := allDegrees (Rep.leftRegular ℤ G) hregular12
      (isoShortExact X hX hE.2.2.1 hE.2.1)
        (homologyNegShort Y hY
          (hregular.2.2.2 1 Nat.zero_lt_one) hregular.2.2.1 a) := by
  rfl

/-- The assembled negative Tate shift sends the homology class represented
by `g⁻¹` to the splitting-module cyclic parameter along `g`. -/
theorem neg_generator_inv
    (gamma : groupCohomology (Rep.ofMulDistribMulAction G M) 2)
    (hgamma : ∀ x : groupCohomology (Rep.ofMulDistribMulAction G M) 2,
      x ∈ zmultiples gamma)
    (hcard : Nat.card
      (groupCohomology (Rep.ofMulDistribMulAction G M) 2) = Fintype.card G)
    (hC1self : IsZero
      (groupCohomology (Rep.ofMulDistribMulAction G M) 1))
    (hC1 : ∀ H : Subgroup G,
      IsZero (groupCohomology
        (Rep.res H.subtype (Rep.ofMulDistribMulAction G M)) 1))
    (hboundary : ∀ H : Subgroup G,
      IsIso (groupCohomology.δ
        ((splitting_sequence_short (Rep.ofMulDistribMulAction G M)
          (normalizedCocycleClass (Rep.ofMulDistribMulAction G M) gamma)
          (normalized_cocycle_class
            (Rep.ofMulDistribMulAction G M) gamma)).map_of_exact
              (Rep.resFunctor H.subtype)) 1 2 rfl))
    (g : G) :
    (restricted_boundary_iso
      (Rep.ofMulDistribMulAction G M) gamma hgamma hcard hC1self
        hC1 hboundary).negTwo
        (groupHomology.H1π (Rep.trivial ℤ G ℤ)
          ((groupHomology.cycles₁IsoOfIsTrivial
            (Rep.trivial ℤ G ℤ)).inv (Finsupp.single g⁻¹ 1))) =
      Submodule.Quotient.mk
        (splittingParameterInvariant
          (normalizedCocycleClass (Rep.ofMulDistribMulAction G M) gamma)
          (normalized_cocycle_class
            (Rep.ofMulDistribMulAction G M) gamma) g) := by
  let C := Rep.ofMulDistribMulAction G M
  let φ := normalizedCocycleClass C gamma
  let hφ := normalized_cocycle_class C gamma
  let X := splittingModuleSequence C φ hφ
  let Y := augmentationSequence (G := G)
  let hX := splitting_sequence_short C φ hφ
  let hY := augmentation_short_exact (G := G)
  let hE12 : ∀ H : Subgroup G,
      IsZero (groupCohomology
          (Rep.res H.subtype (splittingModule C φ hφ)) 1) ∧
        IsZero (groupCohomology
          (Rep.res H.subtype (splittingModule C φ hφ)) 2) := by
    apply splitting_12_iso C φ hφ hC1
      cohomology_restrict_ideal
    simpa [C, φ, hφ] using hboundary
  let hE := allDegrees (splittingModule C φ hφ) hE12
  let hregular12 : ∀ H : Subgroup G,
      IsZero (groupCohomology
          (Rep.res H.subtype (Rep.leftRegular ℤ G)) 1) ∧
      IsZero (groupCohomology
          (Rep.res H.subtype (Rep.leftRegular ℤ G)) 2) := fun H ↦
    ⟨restrict_int_acyclic H 1 Nat.zero_lt_one,
      restrict_int_acyclic H 2 (by omega)⟩
  let hregular := allDegrees (Rep.leftRegular ℤ G) hregular12
  letI : Y.X₃.IsTrivial := by
    dsimp [Y, augmentationSequence]
    infer_instance
  let zc : groupHomology.cycles₁ (Rep.trivial ℤ G ℤ) :=
    (groupHomology.cycles₁IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).inv
      (Finsupp.single g⁻¹ (1 : ℤ))
  let yc : G →₀ IntegralGroupRing G :=
    Finsupp.single g⁻¹ (MonoidAlgebra.single 1 1)
  let b : augmentationIdeal G := augmentationClass G g
  have hy : Finsupp.mapRange.linearMap Y.g.hom.toLinearMap yc = zc.1 := by
    change Finsupp.mapRange.linearMap (augmentation G) yc = zc.1
    rw [show zc.1 = Finsupp.single g⁻¹ (1 : ℤ) by
      exact groupHomology.cycles₁IsoOfIsTrivial_inv_apply _]
    ext t
    simp [yc, augmentation_single]
  have hx : Y.f.hom b = groupHomology.d₁₀ Y.X₂ yc := by
    calc
      Y.f.hom b =
          (show IntegralGroupRing G from
            (Rep.leftRegular ℤ G).ρ (g⁻¹)⁻¹
              (MonoidAlgebra.single 1 1 : IntegralGroupRing G)) -
            (MonoidAlgebra.single 1 1 : IntegralGroupRing G) := by
        change (b : IntegralGroupRing G) = _
        rw [inv_inv]
        have ha : (show IntegralGroupRing G from
            (Rep.leftRegular ℤ G).ρ g
              (MonoidAlgebra.single 1 1 : IntegralGroupRing G)) =
            MonoidAlgebra.single g 1 := by
          exact (regular_int_action g
            (MonoidAlgebra.single 1 1 : IntegralGroupRing G)).trans <| by
              rw [← MonoidAlgebra.one_def]
              exact mul_one (MonoidAlgebra.single g (1 : ℤ))
        rw [ha]
        exact augmentationClass_coe (G := G) g
      _ = (show IntegralGroupRing G from
          groupHomology.d₁₀ (Rep.leftRegular ℤ G)
            (Finsupp.single g⁻¹
              (MonoidAlgebra.single 1 1 : IntegralGroupRing G))) :=
        (groupHomology.d₁₀_single (A := Rep.leftRegular ℤ G) g⁻¹
          (MonoidAlgebra.single 1 1 : IntegralGroupRing G)).symm
      _ = (show IntegralGroupRing G from
          groupHomology.d₁₀ Y.X₂ yc) := rfl
  let e1 := homologyNegShort Y hY
    (hregular.2.2.2 1 Nat.zero_lt_one) hregular.2.2.1
  let z := e1 (groupHomology.H1π Y.X₃ zc)
  have hz : z.1 = Coinvariants.mk Y.X₁.ρ b := by
    exact homology_short_exact
      Y hY (hregular.2.2.2 1 Nat.zero_lt_one) hregular.2.2.1
        zc yc hy b hx
  let x₂ : X.X₂.ρ.Coinvariants :=
    Coinvariants.mk X.X₂.ρ (0, augmentationClass G g)
  let x₁ := splittingParameterInvariant φ hφ g
  have h₂ : (Rep.coinvariantsFunctor ℤ G).map X.g x₂ = z.1 := by
    rw [hz]
    rfl
  have h₁ : (Rep.invariantsFunctor ℤ G).map X.f x₁ =
      normCoinvariantsInvariants X.X₂ x₂ := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp only [x₁, splittingParameterInvariant]
      rfl
    · symm
      change ((splittingModule C φ hφ).ρ.norm
          (0, augmentationClass G g)).2 = 0
      simp only [Representation.norm, LinearMap.sum_apply]
      let sndHom : (C × augmentationIdeal G) →+ augmentationIdeal G :=
        { toFun := Prod.snd, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
      change sndHom (∑ h : G,
        (splittingModule C φ hφ).ρ h (0, augmentationClass G g)) = 0
      rw [map_sum]
      change (∑ h : G, augmentationLeftAction h
        (augmentationClass G g)) = 0
      simp only [augmentation_action_class, Finset.sum_sub_distrib]
      have heq : (∑ h : G, augmentationClass G (h * g)) =
          ∑ h : G, augmentationClass G h :=
        Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ ↦ rfl)
      rw [heq, sub_self]
  rw [neg_two_explicit]
  change (isoShortExact X hX hE.2.2.1 hE.2.1)
      (e1 (groupHomology.H1π Y.X₃ zc)) = Submodule.Quotient.mk x₁
  exact iso_short_exact X hX hE.2.2.1
    hE.2.1 z x₂ x₁ h₂ h₁

end IntegralCyclic

end Towers.CField.Shifting
