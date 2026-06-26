import Submission.FieldTheory.CentralEmbeddingLocal


/-!
# The abelian-kernel extension attached to a finite tame pair

This file identifies tame inertia with roots of unity in the canonical
unramified level and checks the Frobenius compatibility needed to transport
the tame extension class into field-unit-valued cohomology.
-/

noncomputable section

namespace Submission
namespace TBluepr

open Submission.CField.LBrauer

attribute [local instance] Units.mulDistribMulActionRight

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [CharZero K]

/-- The tame inertia subgroup embedded as the powers of a chosen primitive
root in the canonical unramified level. -/
noncomputable def tameInertiaUnits
    {G : Type u} [Group G] [Finite G] (x y : G)
    (_hcoprime : (localResidueCard K).Coprime (orderOf x))
    (zeta : canonicalUnramifiedLevel K
      (Nat.card
        (let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
         let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
         H ⧸ I)))
    (hzeta : IsPrimitiveRoot zeta (orderOf x)) :
    let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
    let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
    I →* (canonicalUnramifiedLevel K (Nat.card (H ⧸ I)))ˣ := by
  let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
  have hxH : x ∈ H := Subgroup.subset_closure (Set.mem_insert x {y})
  let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  let e := orderOf x
  letI : NeZero e := ⟨(orderOf_pos x).ne'⟩
  let eI : Multiplicative (ZMod e) ≃* I :=
    (tameZMod x).trans
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxH)).symm
  let zetaUnit : (canonicalUnramifiedLevel K (Nat.card (H ⧸ I)))ˣ :=
    (hzeta.isUnit (orderOf_pos x).ne').unit
  have hzetaUnit : IsPrimitiveRoot zetaUnit e :=
    hzeta.isUnit_unit (orderOf_pos x).ne'
  let eZeta : Multiplicative (ZMod e) ≃* Subgroup.zpowers zetaUnit :=
    hzetaUnit.zmodEquivZPowers.toMultiplicativeLeft
  exact (Subgroup.zpowers zetaUnit).subtype.comp
    (eZeta.toMonoidHom.comp eI.symm.toMonoidHom)

omit [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] [CharZero K] in
@[simp]
theorem tame_inertia_generator
    {G : Type u} [Group G] [Finite G] (x y : G)
    (hcoprime : (localResidueCard K).Coprime (orderOf x))
    (zeta : canonicalUnramifiedLevel K
      (Nat.card
        (let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
         let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
         H ⧸ I)))
    (hzeta : IsPrimitiveRoot zeta (orderOf x)) :
    let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
    let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
    tameInertiaUnits K x y hcoprime zeta hzeta
        (⟨⟨x, Subgroup.subset_closure (Set.mem_insert x {y})⟩,
          Subgroup.mem_zpowers x⟩ : I) =
      (hzeta.isUnit (orderOf_pos x).ne').unit := by
  let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
  have hxH : x ∈ H := Subgroup.subset_closure (Set.mem_insert x {y})
  let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  let e := orderOf x
  let xI : I := ⟨⟨x, hxH⟩, Subgroup.mem_zpowers x⟩
  let eSub : I ≃* Subgroup.zpowers x :=
    Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxH)
  let eI : Multiplicative (ZMod e) ≃* I :=
    (tameZMod x).trans eSub.symm
  let zetaUnit : (canonicalUnramifiedLevel K (Nat.card (H ⧸ I)))ˣ :=
    (hzeta.isUnit (orderOf_pos x).ne').unit
  have hzetaUnit : IsPrimitiveRoot zetaUnit e :=
    hzeta.isUnit_unit (orderOf_pos x).ne'
  let eZeta : Multiplicative (ZMod e) ≃* Subgroup.zpowers zetaUnit :=
    hzetaUnit.zmodEquivZPowers.toMultiplicativeLeft
  change ((eZeta (eI.symm xI) : Subgroup.zpowers zetaUnit) :
      (canonicalUnramifiedLevel K (Nat.card (H ⧸ I)))ˣ) = zetaUnit
  have hxcoord : eI.symm xI = Multiplicative.ofAdd 1 := by
    apply eI.injective
    rw [MulEquiv.apply_symm_apply]
    symm
    change eSub.symm
      (tameZMod x (Multiplicative.ofAdd 1)) = xI
    rw [tame_inertia_z]
    apply Subtype.ext
    rfl
  rw [hxcoord]
  change (hzetaUnit.zmodEquivZPowers 1).toMul = zetaUnit
  have hz := hzetaUnit.zmodEquivZPowers_apply_coe_nat 1
  have hz' := congrArg
    (fun z : Additive (Subgroup.zpowers zetaUnit) =>
      (z.toMul : (canonicalUnramifiedLevel K (Nat.card (H ⧸ I)))ˣ)) hz
  simpa using hz'

omit [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] [CharZero K] in
theorem tame_inertia_injective
    {G : Type u} [Group G] [Finite G] (x y : G)
    (hcoprime : (localResidueCard K).Coprime (orderOf x))
    (zeta : canonicalUnramifiedLevel K
      (Nat.card
        (let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
         let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
         H ⧸ I)))
    (hzeta : IsPrimitiveRoot zeta (orderOf x)) :
    Function.Injective (tameInertiaUnits K x y hcoprime zeta hzeta) := by
  let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
  have hxH : x ∈ H := Subgroup.subset_closure (Set.mem_insert x {y})
  let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  let e := orderOf x
  let eI : Multiplicative (ZMod e) ≃* I :=
    (tameZMod x).trans
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxH)).symm
  let zetaUnit : (canonicalUnramifiedLevel K (Nat.card (H ⧸ I)))ˣ :=
    (hzeta.isUnit (orderOf_pos x).ne').unit
  have hzetaUnit : IsPrimitiveRoot zetaUnit e :=
    hzeta.isUnit_unit (orderOf_pos x).ne'
  let eZeta : Multiplicative (ZMod e) ≃* Subgroup.zpowers zetaUnit :=
    hzetaUnit.zmodEquivZPowers.toMultiplicativeLeft
  exact (Subgroup.zpowers zetaUnit).subtype_injective.comp
    (eZeta.injective.comp eI.symm.injective)

omit [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] [CharZero K] in
theorem tame_pair_inertia
    {G : Type u} [Group G] [Finite G] (x y : G)
    (hcoprime : (localResidueCard K).Coprime (orderOf x))
    (zeta : canonicalUnramifiedLevel K
      (Nat.card
        (let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
         let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
         H ⧸ I)))
    (hzeta : IsPrimitiveRoot zeta (orderOf x))
    (i : let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
         let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
         I) :
    tameInertiaUnits K x y hcoprime zeta hzeta i ^ orderOf x = 1 := by
  let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
  have hxH : x ∈ H := Subgroup.subset_closure (Set.mem_insert x {y})
  let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  let e := orderOf x
  letI : NeZero e := ⟨(orderOf_pos x).ne'⟩
  let eI : Multiplicative (ZMod e) ≃* I :=
    (tameZMod x).trans
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxH)).symm
  let zetaUnit : (canonicalUnramifiedLevel K (Nat.card (H ⧸ I)))ˣ :=
    (hzeta.isUnit (orderOf_pos x).ne').unit
  have hzetaUnit : IsPrimitiveRoot zetaUnit e :=
    hzeta.isUnit_unit (orderOf_pos x).ne'
  let eZeta : Multiplicative (ZMod e) ≃* Subgroup.zpowers zetaUnit :=
    hzetaUnit.zmodEquivZPowers.toMultiplicativeLeft
  let psi : Multiplicative (ZMod e) →*
      (canonicalUnramifiedLevel K (Nat.card (H ⧸ I)))ˣ :=
    (Subgroup.zpowers zetaUnit).subtype.comp eZeta.toMonoidHom
  let w := eI.symm i
  have hw : w ^ e = 1 := by
    apply Multiplicative.toAdd.injective
    simp
  change psi w ^ e = 1
  rw [← map_pow, hw, map_one]

omit [CharZero K] in
theorem arithmetic_primitive_root
    (f e m : ℕ) [NeZero f] [NeZero e]
    (zeta : canonicalUnramifiedLevel K f)
    (hzeta : IsPrimitiveRoot zeta e)
    (hcoprime : (localResidueCard K).Coprime e) :
    (canonicalArithmeticFrobenius K f ^ m) zeta =
      zeta ^ (localResidueCard K ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, AlgEquiv.mul_apply,
        arithmetic_frobenius_primitive
          K f e zeta hzeta hcoprime, map_pow, ih, ← pow_mul, pow_succ]

/-- The quotient Galois group acts on tame inertia through conjugation in
the tame-pair extension. -/
@[implicit_reducible]
noncomputable def tameInertiaAction
    {G : Type u} [Group G] [Finite G] (x y : G)
    (hcoprime : (localResidueCard K).Coprime (orderOf x))
    (hconj : y * x * y⁻¹ = x ^ localResidueCard K) :
    let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
    let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
    letI : I.Normal := tame_inertia_closure
      x y (localResidueCard K) hcoprime hconj
    MulDistribMulAction
      Gal(canonicalUnramifiedLevel K (Nat.card (H ⧸ I))/K) I := by
  let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
  have hxH : x ∈ H := Subgroup.subset_closure (Set.mem_insert x {y})
  let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  letI : I.Normal := tame_inertia_closure
    x y (localResidueCard K) hcoprime hconj
  let eI : Multiplicative (ZMod (orderOf x)) ≃* I :=
    (tameZMod x).trans
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxH)).symm
  letI : CommGroup I :=
    eI.symm.toMonoidHom.commGroupOfInjective eI.symm.injective
  exact groupExtensionAction
    (tamePairExtension K x y hcoprime hconj)

set_option maxHeartbeats 1000000 in
-- Normalizing the dependent quotient action is instance-heavy in builds.
set_option synthInstance.maxHeartbeats 1000000 in
omit [CharZero K] in
theorem tame_frobenius_generator
    {G : Type u} [Group G] [Finite G] (x y : G)
    (hcoprime : (localResidueCard K).Coprime (orderOf x))
    (hconj : y * x * y⁻¹ = x ^ localResidueCard K) :
    let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
    let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
    letI : I.Normal := tame_inertia_closure
      x y (localResidueCard K) hcoprime hconj
    letI : NeZero (Nat.card (H ⧸ I)) :=
      ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
    letI : MulDistribMulAction
        Gal(canonicalUnramifiedLevel K (Nat.card (H ⧸ I))/K) I :=
      tameInertiaAction K x y hcoprime hconj
    canonicalArithmeticFrobenius K (Nat.card (H ⧸ I)) •
        (⟨⟨x, Subgroup.subset_closure (Set.mem_insert x {y})⟩,
          Subgroup.mem_zpowers x⟩ : I) =
      (⟨⟨x, Subgroup.subset_closure (Set.mem_insert x {y})⟩,
          Subgroup.mem_zpowers x⟩ : I) ^ localResidueCard K := by
  let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
  have hxH : x ∈ H := Subgroup.subset_closure (Set.mem_insert x {y})
  have hyH : y ∈ H := Subgroup.subset_closure
    (Set.mem_insert_of_mem x (Set.mem_singleton y))
  let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  letI : I.Normal := tame_inertia_closure
    x y (localResidueCard K) hcoprime hconj
  letI : NeZero (Nat.card (H ⧸ I)) :=
    ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
  let eI : Multiplicative (ZMod (orderOf x)) ≃* I :=
    (tameZMod x).trans
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxH)).symm
  letI : CommGroup I :=
    eI.symm.toMonoidHom.commGroupOfInjective eI.symm.injective
  let S := tamePairExtension K x y hcoprime hconj
  letI : MulDistribMulAction
      Gal(canonicalUnramifiedLevel K (Nat.card (H ⧸ I))/K) I :=
    tameInertiaAction K x y hcoprime hconj
  let xI : I := ⟨⟨x, hxH⟩, Subgroup.mem_zpowers x⟩
  let yH : H := ⟨y, hyH⟩
  have hbase : S.rightHom yH =
      canonicalArithmeticFrobenius K (Nat.card (H ⧸ I)) := by
    exact tame_pair_frobenius K x y hcoprime hconj
  have haction := extension_action_smul S yH xI
  rw [hbase] at haction
  calc
    canonicalArithmeticFrobenius K (Nat.card (H ⧸ I)) • xI =
        S.conjAct yH xI := haction.symm
    _ = xI ^ localResidueCard K := by
      apply S.inl_injective
      rw [S.inl_conjAct_comm, map_pow]
      apply Subtype.ext
      exact hconj

set_option maxHeartbeats 1000000 in
-- Normalizing the dependent quotient action is instance-heavy in builds.
set_option synthInstance.maxHeartbeats 1000000 in
omit [CharZero K] in
theorem tame_action_generator
    {G : Type u} [Group G] [Finite G] (x y : G)
    (hcoprime : (localResidueCard K).Coprime (orderOf x))
    (hconj : y * x * y⁻¹ = x ^ localResidueCard K)
    (m : ℕ) :
    let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
    let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
    letI : I.Normal := tame_inertia_closure
      x y (localResidueCard K) hcoprime hconj
    letI : NeZero (Nat.card (H ⧸ I)) :=
      ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
    letI : MulDistribMulAction
        Gal(canonicalUnramifiedLevel K (Nat.card (H ⧸ I))/K) I :=
      tameInertiaAction K x y hcoprime hconj
    (canonicalArithmeticFrobenius K (Nat.card (H ⧸ I)) ^ m) •
        (⟨⟨x, Subgroup.subset_closure (Set.mem_insert x {y})⟩,
          Subgroup.mem_zpowers x⟩ : I) =
      (⟨⟨x, Subgroup.subset_closure (Set.mem_insert x {y})⟩,
          Subgroup.mem_zpowers x⟩ : I) ^ (localResidueCard K ^ m) := by
  let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
  let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  letI : I.Normal := tame_inertia_closure
    x y (localResidueCard K) hcoprime hconj
  letI : NeZero (Nat.card (H ⧸ I)) :=
    ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
  letI : MulDistribMulAction
      Gal(canonicalUnramifiedLevel K (Nat.card (H ⧸ I))/K) I :=
    tameInertiaAction K x y hcoprime hconj
  let xI : I :=
    ⟨⟨x, Subgroup.subset_closure (Set.mem_insert x {y})⟩,
      Subgroup.mem_zpowers x⟩
  change (canonicalArithmeticFrobenius K (Nat.card (H ⧸ I)) ^ m) • xI =
    xI ^ (localResidueCard K ^ m)
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, mul_smul,
        tame_frobenius_generator
          K x y hcoprime hconj, smul_pow', ih, ← pow_mul, pow_succ]

set_option maxHeartbeats 3000000 in
-- The repeated dependent tame-pair telescope is expensive to normalize.
set_option synthInstance.maxHeartbeats 500000 in
omit [CharZero K] in
theorem tame_inertia_equivariant
    {G : Type u} [Group G] [Finite G] (x y : G)
    (hcoprime : (localResidueCard K).Coprime (orderOf x))
    (hconj : y * x * y⁻¹ = x ^ localResidueCard K) :
    let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
    let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
    letI : I.Normal := tame_inertia_closure
      x y (localResidueCard K) hcoprime hconj
    letI : NeZero (Nat.card (H ⧸ I)) :=
      ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
    letI : MulDistribMulAction
        Gal(canonicalUnramifiedLevel K (Nat.card (H ⧸ I))/K) I :=
      tameInertiaAction K x y hcoprime hconj
    ∀ (zeta : canonicalUnramifiedLevel K (Nat.card (H ⧸ I)))
      (hzeta : IsPrimitiveRoot zeta (orderOf x))
      (sigma : Gal(canonicalUnramifiedLevel K (Nat.card (H ⧸ I))/K))
      (i : I),
      tameInertiaUnits K x y hcoprime zeta hzeta (sigma • i) =
        Units.map sigma.toRingEquiv.toMonoidHom
          (tameInertiaUnits K x y hcoprime zeta hzeta i) := by
  let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
  have hxH : x ∈ H := Subgroup.subset_closure (Set.mem_insert x {y})
  let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  letI : I.Normal := tame_inertia_closure
    x y (localResidueCard K) hcoprime hconj
  let f := Nat.card (H ⧸ I)
  letI : NeZero f := ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
  letI : MulDistribMulAction Gal(canonicalUnramifiedLevel K f/K) I :=
    tameInertiaAction K x y hcoprime hconj
  let xI : I := ⟨⟨x, hxH⟩, Subgroup.mem_zpowers x⟩
  change ∀ (zeta : canonicalUnramifiedLevel K f)
    (hzeta : IsPrimitiveRoot zeta (orderOf x))
    (sigma : Gal(canonicalUnramifiedLevel K f/K)) (i : I),
    tameInertiaUnits K x y hcoprime zeta hzeta (sigma • i) =
      Units.map sigma.toRingEquiv.toMonoidHom
        (tameInertiaUnits K x y hcoprime zeta hzeta i)
  intro zeta hzeta sigma i
  letI : NeZero (orderOf x) := ⟨(orderOf_pos x).ne'⟩
  let zetaUnit : (canonicalUnramifiedLevel K f)ˣ :=
    (hzeta.isUnit (orderOf_pos x).ne').unit
  obtain ⟨m, _hm, hSigma⟩ :=
    canonical_arithmetic_frobenius K f sigma
  obtain ⟨j, hj⟩ := i.property
  have hi : i = xI ^ j := by
    apply Subtype.ext
    apply Subtype.ext
    exact hj.symm
  have hsource :
      (canonicalArithmeticFrobenius K f ^ m) • xI =
        xI ^ (localResidueCard K ^ m) :=
    tame_action_generator
      K x y hcoprime hconj m
  have htarget :
      Units.map (canonicalArithmeticFrobenius K f ^ m).toRingEquiv.toMonoidHom
          zetaUnit =
        zetaUnit ^ (localResidueCard K ^ m) := by
    apply Units.ext
    simpa [zetaUnit] using
      arithmetic_primitive_root
        K f (orderOf x) m zeta hzeta hcoprime
  have hmapgen :
      tameInertiaUnits K x y hcoprime zeta hzeta xI = zetaUnit :=
    tame_inertia_generator K x y hcoprime zeta hzeta
  rw [← hSigma, hi]
  calc
    tameInertiaUnits K x y hcoprime zeta hzeta
          ((canonicalArithmeticFrobenius K f ^ m) • (xI ^ j)) =
        tameInertiaUnits K x y hcoprime zeta hzeta
          (((canonicalArithmeticFrobenius K f ^ m) • xI) ^ j) := by
            rw [smul_zpow']
    _ = (tameInertiaUnits K x y hcoprime zeta hzeta
          ((canonicalArithmeticFrobenius K f ^ m) • xI)) ^ j := by
            rw [map_zpow]
    _ = (tameInertiaUnits K x y hcoprime zeta hzeta
          (xI ^ (localResidueCard K ^ m))) ^ j := by rw [hsource]
    _ = ((tameInertiaUnits K x y hcoprime zeta hzeta xI) ^
          (localResidueCard K ^ m)) ^ j := by rw [map_pow]
    _ = (zetaUnit ^ (localResidueCard K ^ m)) ^ j := by rw [hmapgen]
    _ = (Units.map
          (canonicalArithmeticFrobenius K f ^ m).toRingEquiv.toMonoidHom
          zetaUnit) ^ j := by rw [htarget]
    _ = Units.map
          (canonicalArithmeticFrobenius K f ^ m).toRingEquiv.toMonoidHom
          (zetaUnit ^ j) := by rw [map_zpow]
    _ = Units.map
          (canonicalArithmeticFrobenius K f ^ m).toRingEquiv.toMonoidHom
          (tameInertiaUnits K x y hcoprime zeta hzeta
            (xI ^ j)) := by rw [← hmapgen, ← map_zpow]

end TBluepr
end Submission
