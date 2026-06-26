import Submission.FieldTheory.CentralEmbeddingExtension

/-!
# Cohomology class of a finite tame-pair extension

This file constructs the normalized factor set of a `GroupExtension` in
arbitrary universe and applies the unramified local `H²` vanishing theorem to
the tame-pair extension.
-/

noncomputable section

namespace Submission
namespace TBluepr

open Submission.CField.CProduca
open Submission.CField.LBrauer

attribute [local instance] Units.mulDistribMulActionRight

universe u

/-- The normalized set-theoretic section of a group extension. -/
noncomputable def normalizedExtensionSection
    {N E Q : Type u} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q) : S.Section where
  toFun := normalizedSurjInv S.rightHom S.rightHom_surjective
  rightInverse_rightHom := normalized_surj_maps
    S.rightHom S.rightHom_surjective

@[simp]
theorem normalized_extension_section
    {N E Q : Type u} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q) :
    normalizedExtensionSection S 1 = 1 := by
  simp [normalizedExtensionSection, normalizedSurjInv]

/-- The kernel-valued normalized factor set of a group extension. -/
noncomputable def extensionNormalizedValue
    {N E Q : Type u} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q) (g h : Q) : N :=
  Function.invFun S.inl
    (normalizedExtensionSection S g *
      normalizedExtensionSection S h *
      (normalizedExtensionSection S (g * h))⁻¹)

theorem extension_normalized_section
    {N E Q : Type u} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q) (g h : Q) :
    S.inl (extensionNormalizedValue S g h) *
        normalizedExtensionSection S (g * h) =
      normalizedExtensionSection S g *
        normalizedExtensionSection S h := by
  let s := normalizedExtensionSection S
  have hmem := s.mul_mul_mul_inv_mem_range_inl g h
  have hinl : S.inl (extensionNormalizedValue S g h) =
      s g * s h * (s (g * h))⁻¹ := Function.invFun_eq hmem
  change S.inl (extensionNormalizedValue S g h) * s (g * h) =
    s g * s h
  rw [hinl]
  group

theorem extension_normalized_left
    {N E Q : Type u} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q) (g : Q) :
    extensionNormalizedValue S 1 g = 1 := by
  apply S.inl_injective
  apply mul_right_cancel (b := normalizedExtensionSection S g)
  simpa using extension_normalized_section S 1 g

theorem extension_normalized_right
    {N E Q : Type u} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q) (g : Q) :
    extensionNormalizedValue S g 1 = 1 := by
  apply S.inl_injective
  apply mul_right_cancel (b := normalizedExtensionSection S g)
  have h := extension_normalized_section S g 1
  simpa using h

/-- Moving a kernel element across the normalized section applies the
quotient action. -/
theorem normalized_section_inl
    {N E Q : Type u} [CommGroup N] [Group E] [Group Q]
    [MulDistribMulAction Q N]
    (S : GroupExtension N E Q)
    (hS : ∀ e : E, ∀ n : N, S.conjAct e n = S.rightHom e • n)
    (g : Q) (n : N) :
    normalizedExtensionSection S g * S.inl n =
      S.inl (g • n) * normalizedExtensionSection S g := by
  let s := normalizedExtensionSection S
  have haction : S.conjAct (s g) n = g • n := by
    rw [hS]
    exact congrArg (fun q : Q => q • n) (s.rightInverse_rightHom g)
  calc
    s g * S.inl n = (s g * S.inl n * (s g)⁻¹) * s g := by group
    _ = S.inl (S.conjAct (s g) n) * s g := by
      rw [S.inl_conjAct_comm]
    _ = S.inl (g • n) * s g := by rw [haction]

/-- The normalized factor set as a normalized multiplicative two-cocycle. -/
noncomputable def extensionNormalizedCocycle
    {N E Q : Type u} [CommGroup N] [Group E] [Group Q]
    [MulDistribMulAction Q N]
    (S : GroupExtension N E Q)
    (hS : ∀ e : E, ∀ n : N, S.conjAct e n = S.rightHom e • n) :
    NMCocycl₂ (G := Q) (M := N) where
  toFun p := extensionNormalizedValue S p.1 p.2
  map_one_fst := extension_normalized_left S
  map_one_snd := extension_normalized_right S
  isMulCocycle₂ g h j := by
    let s := normalizedExtensionSection S
    let c := extensionNormalizedValue S
    apply S.inl_injective
    simp only [map_mul]
    apply mul_right_cancel (b := s ((g * h) * j))
    calc
      (S.inl (c (g * h) j) * S.inl (c g h)) * s ((g * h) * j) =
          S.inl (c g h) * (S.inl (c (g * h) j) * s ((g * h) * j)) := by
            have hcomm : S.inl (c (g * h) j) * S.inl (c g h) =
                S.inl (c g h) * S.inl (c (g * h) j) := by
              rw [← map_mul, ← map_mul, mul_comm]
            rw [hcomm, mul_assoc]
      _ = S.inl (c g h) * (s (g * h) * s j) := by
            rw [extension_normalized_section]
      _ = (s g * s h) * s j := by
            rw [← mul_assoc,
              extension_normalized_section]
      _ = s g * (s h * s j) := mul_assoc _ _ _
      _ = s g * (S.inl (c h j) * s (h * j)) := by
            rw [extension_normalized_section]
      _ = (S.inl (g • c h j) * s g) * s (h * j) := by
            rw [← mul_assoc, normalized_section_inl S hS]
      _ = S.inl (g • c h j) * (s g * s (h * j)) := by rw [mul_assoc]
      _ = S.inl (g • c h j) *
          (S.inl (c g (h * j)) * s (g * (h * j))) := by
            rw [extension_normalized_section]
      _ = (S.inl (g • c h j) * S.inl (c g (h * j))) *
          s ((g * h) * j) := by rw [mul_assoc, mul_assoc]

set_option maxHeartbeats 10000000 in
-- The tame-pair quotient and canonical unramified level are dependent types.
set_option synthInstance.maxHeartbeats 1000000 in
/-- After embedding inertia as roots of unity, the tame-pair extension class
vanishes in the unit-valued `H²` of the canonical unramified level. -/
theorem tame_pair_mapped
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [CharZero K]
    {G : Type u} [Group G] [Finite G] (x y : G)
    (hcoprime : (localResidueCard K).Coprime (orderOf x))
    (hconj : y * x * y⁻¹ = x ^ localResidueCard K) :
    let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
    let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
    letI : I.Normal := tame_inertia_closure
      x y (localResidueCard K) hcoprime hconj
    let f := Nat.card (H ⧸ I)
    let e := orderOf x
    letI : NeZero f := ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
    letI : NeZero e := ⟨(orderOf_pos x).ne'⟩
    let eI : Multiplicative (ZMod e) ≃* I :=
      (tameZMod x).trans
        (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr
          (Subgroup.subset_closure (Set.mem_insert x {y})))).symm
    letI : CommGroup I :=
      eI.symm.toMonoidHom.commGroupOfInjective eI.symm.injective
    letI : MulDistribMulAction Gal(canonicalUnramifiedLevel K f/K) I :=
      tameInertiaAction K x y hcoprime hconj
    ∀ (c : NMCocycl₂
        (G := Gal(canonicalUnramifiedLevel K f/K)) (M := I))
      (zeta : canonicalUnramifiedLevel K f)
      (hzeta : IsPrimitiveRoot zeta e),
      let phi := tameInertiaUnits K x y hcoprime zeta hzeta
      MHTwo.mapCoefficientsHom phi
          (fun sigma i => tame_inertia_equivariant
            K x y hcoprime hconj zeta hzeta sigma i)
          (MHTwo.mk c) = 1 := by
  let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
  let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  letI : I.Normal := tame_inertia_closure
    x y (localResidueCard K) hcoprime hconj
  let f := Nat.card (H ⧸ I)
  let e := orderOf x
  letI : NeZero f := ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
  letI : NeZero e := ⟨(orderOf_pos x).ne'⟩
  let eI : Multiplicative (ZMod e) ≃* I :=
    (tameZMod x).trans
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr
        (Subgroup.subset_closure (Set.mem_insert x {y})))).symm
  letI : CommGroup I :=
    eI.symm.toMonoidHom.commGroupOfInjective eI.symm.injective
  letI : MulDistribMulAction Gal(canonicalUnramifiedLevel K f/K) I :=
    tameInertiaAction K x y hcoprime hconj
  change ∀ (c : NMCocycl₂
      (G := Gal(canonicalUnramifiedLevel K f/K)) (M := I)),
    ∀ (zeta : canonicalUnramifiedLevel K f)
    (hzeta : IsPrimitiveRoot zeta e), _
  intro c zeta hzeta
  let phi := tameInertiaUnits K x y hcoprime zeta hzeta
  have hcard : Nat.card I = e := by
    calc
      Nat.card I = Nat.card (Multiplicative (ZMod e)) :=
        (Nat.card_congr eI.toEquiv).symm
      _ = e := by simp
  exact canonical_unramified_level K f e
    phi
    (fun sigma i => tame_inertia_equivariant
      K x y hcoprime hconj zeta hzeta sigma i)
    (fun i => by
      rw [← map_pow, ← hcard, pow_card_eq_one', map_one])
    (MHTwo.mk c)

/-- A vanishing finite-order unit-valued cocycle supplies the cochain and
Hilbert-90 radical used in the Kummer realization. -/
theorem normalized_cocycle_kummer
    {C L K : Type u} [CommGroup C]
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [MulDistribMulAction Gal(L/K) C]
    (e : ℕ)
    (c : NMCocycl₂ (G := Gal(L/K)) (M := C))
    (phi : C →* Lˣ)
    (hphi : ∀ sigma : Gal(L/K), ∀ z : C,
      phi (sigma • z) =
        Units.map sigma.toRingEquiv.toMonoidHom (phi z))
    (hpow : ∀ z : C, phi z ^ e = 1)
    (hzero : MHTwo.mapCoefficientsHom phi hphi
      (MHTwo.mk c) = 1) :
    ∃ b : Gal(L/K) → Lˣ,
      (∀ sigma tau : Gal(L/K),
        Units.map sigma.toRingEquiv.toMonoidHom (b tau) /
            b (sigma * tau) * b sigma = phi (c (sigma, tau))) ∧
      ∃ a : Lˣ, ∀ sigma : Gal(L/K),
        Units.map sigma.toRingEquiv.toMonoidHom a / a = b sigma ^ e := by
  let cL : NMCocycl₂ (G := Gal(L/K)) (M := Lˣ) :=
    NMCocycl₂.mapCoefficients phi hphi c
  have hcLclass : MHTwo.mk cL = 1 := by
    simpa [cL] using hzero
  have hcoh : MHTwo.IsCohomologous cL 1 :=
    (MHTwo.mk_eq_iff cL 1).1 (by simpa using hcLclass)
  obtain ⟨b, hb⟩ := hcoh
  have hb' : ∀ sigma tau : Gal(L/K),
      Units.map sigma.toRingEquiv.toMonoidHom (b tau) /
          b (sigma * tau) * b sigma = cL (sigma, tau) := by
    intro sigma tau
    simpa [MHTwo.IsCohomologous] using hb sigma tau
  have heTorsion : ∀ sigma tau : Gal(L/K), cL (sigma, tau) ^ e = 1 := by
    intro sigma tau
    exact hpow (c (sigma, tau))
  have hbCocycle : groupCohomology.IsMulCocycle₁
      (fun sigma => b sigma ^ e) :=
    groupCohomology.isMulCocycle₁_pow_of_coboundary_eq_torsion
      e cL b hb' heTorsion
  obtain ⟨a, ha⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
      (fun sigma => b sigma ^ e) hbCocycle
  refine ⟨b, ?_, a, ?_⟩
  · intro sigma tau
    simpa [cL] using hb' sigma tau
  · intro sigma
    simpa using ha sigma

set_option maxHeartbeats 3000000 in
-- The local extension, quotient action, and radical field share a dependent degree.
set_option synthInstance.maxHeartbeats 1000000 in
theorem tame_kummer_data
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [CharZero K]
    {G : Type u} [Group G] [Finite G] (x y : G)
    (hcoprime : (localResidueCard K).Coprime (orderOf x))
    (hconj : y * x * y⁻¹ = x ^ localResidueCard K) :
    let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
    let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
    letI : I.Normal := tame_inertia_closure
      x y (localResidueCard K) hcoprime hconj
    let f := Nat.card (H ⧸ I)
    let e := orderOf x
    letI : NeZero f := ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
    letI : NeZero e := ⟨(orderOf_pos x).ne'⟩
    letI : MulDistribMulAction Gal(canonicalUnramifiedLevel K f/K) I :=
      tameInertiaAction K x y hcoprime hconj
    ∀ (zeta : canonicalUnramifiedLevel K f)
      (hzeta : IsPrimitiveRoot zeta e),
      let phi := tameInertiaUnits K x y hcoprime zeta hzeta
      let S := tamePairExtension K x y hcoprime hconj
      ∃ b : Gal(canonicalUnramifiedLevel K f/K) →
          (canonicalUnramifiedLevel K f)ˣ,
        (∀ sigma tau,
          Units.map sigma.toRingEquiv.toMonoidHom (b tau) /
              b (sigma * tau) * b sigma =
            phi (extensionNormalizedValue S sigma tau)) ∧
        ∃ a : (canonicalUnramifiedLevel K f)ˣ, ∀ sigma,
          Units.map sigma.toRingEquiv.toMonoidHom a / a = b sigma ^ e := by
  let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
  let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  letI : I.Normal := tame_inertia_closure
    x y (localResidueCard K) hcoprime hconj
  let f := Nat.card (H ⧸ I)
  let e := orderOf x
  letI : NeZero f := ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
  letI : NeZero e := ⟨(orderOf_pos x).ne'⟩
  let eI : Multiplicative (ZMod e) ≃* I :=
    (tameZMod x).trans
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr
        (Subgroup.subset_closure (Set.mem_insert x {y})))).symm
  letI : CommGroup I :=
    eI.symm.toMonoidHom.commGroupOfInjective eI.symm.injective
  letI : MulDistribMulAction Gal(canonicalUnramifiedLevel K f/K) I :=
    tameInertiaAction K x y hcoprime hconj
  change ∀ (zeta : canonicalUnramifiedLevel K f)
    (hzeta : IsPrimitiveRoot zeta e), _
  intro zeta hzeta
  let phi := tameInertiaUnits K x y hcoprime zeta hzeta
  let S := tamePairExtension K x y hcoprime hconj
  have hS : ∀ h : H, ∀ i : I,
      S.conjAct h i = S.rightHom h • i := by
    intro h i
    exact extension_action_smul S h i
  let c := extensionNormalizedCocycle S hS
  exact normalized_cocycle_kummer e c phi
    (fun sigma i => tame_inertia_equivariant
      K x y hcoprime hconj zeta hzeta sigma i)
    (fun i => tame_pair_inertia
      K x y hcoprime zeta hzeta i)
    (tame_pair_mapped
      K x y hcoprime hconj c zeta hzeta)

end TBluepr
end Submission
