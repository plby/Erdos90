import Towers.FieldTheory.CentralEmbeddingAction


/-!
# Local Galois realization of finite tame pairs

A finite tame pair in a finite `3`-group is realized as the complete Galois
group of an explicit Kummer extension of the canonical unramified field.
-/

noncomputable section

namespace Towers
namespace TBluepr

open Towers.CField.LBrauer

universe u

set_option maxHeartbeats 3000000 in
-- The realization carries the dependent inertia subgroup and unramified degree.
set_option synthInstance.maxHeartbeats 1000000 in
theorem tame_pair_realization
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [CharZero K]
    {G : Type u} [Group G] [Finite G] (hG : IsPGroup 3 G)
    (x y : G)
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
    ∃ (zeta : canonicalUnramifiedLevel K f)
      (hzeta : IsPrimitiveRoot zeta e),
      let phi := tameInertiaUnits K x y hcoprime zeta hzeta
      let S := tamePairExtension K x y hcoprime hconj
      ∃ b : Gal(canonicalUnramifiedLevel K f/K) →
          (canonicalUnramifiedLevel K f)ˣ,
        ∃ _hb : (∀ sigma tau,
          Units.map sigma.toRingEquiv.toMonoidHom (b tau) /
              b (sigma * tau) * b sigma =
            phi (extensionNormalizedValue S sigma tau)),
        ∃ a : (canonicalUnramifiedLevel K f)ˣ,
          ∃ _ha : (∀ sigma,
            Units.map sigma.toRingEquiv.toMonoidHom a / a =
              b sigma ^ e),
          ∃ hirr : Irreducible (tameKummerPolynomial e a),
            letI : Fact (Irreducible (tameKummerPolynomial e a)) := ⟨hirr⟩
            ∃ _hGal : IsGalois K (TameKummerAdjoin e a),
              ∃ action : H →* Gal(TameKummerAdjoin e a/K),
                Function.Bijective action := by
  let H : Subgroup G := Subgroup.closure ({x, y} : Set G)
  have hxH : x ∈ H := Subgroup.subset_closure (Set.mem_insert x {y})
  let I : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  letI : I.Normal := tame_inertia_closure
    x y (localResidueCard K) hcoprime hconj
  let f := Nat.card (H ⧸ I)
  let e := orderOf x
  letI : NeZero f := ⟨(Nat.card_pos : 0 < Nat.card (H ⧸ I)).ne'⟩
  letI : NeZero e := ⟨(orderOf_pos x).ne'⟩
  let eI : Multiplicative (ZMod e) ≃* I :=
    (tameZMod x).trans
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxH)).symm
  letI : CommGroup I :=
    eI.symm.toMonoidHom.commGroupOfInjective eI.symm.injective
  letI : MulDistribMulAction Gal(canonicalUnramifiedLevel K f/K) I :=
    tameInertiaAction K x y hcoprime hconj
  change ∃ (zeta : canonicalUnramifiedLevel K f)
    (hzeta : IsPrimitiveRoot zeta e), _
  obtain ⟨zeta, hzetaMem⟩ :=
    tame_level_primitive
      K x y hcoprime hconj
  have hzeta : IsPrimitiveRoot zeta e :=
    (mem_primitiveRoots (orderOf_pos x)).1 hzetaMem
  refine ⟨zeta, hzeta, ?_⟩
  let phi := tameInertiaUnits K x y hcoprime zeta hzeta
  let S := tamePairExtension K x y hcoprime hconj
  let hS : ∀ h : H, ∀ i : I,
      S.conjAct h i = S.rightHom h • i := by
    intro h i
    exact extension_action_smul S h i
  obtain ⟨b, hb, a, ha, hirr⟩ :=
    tame_irreducible_kummer K hG x y hcoprime hconj zeta hzeta
  refine ⟨b, hb, a, ha, hirr, ?_⟩
  have hcardI : Nat.card I = e := by
    calc
      Nat.card I = Nat.card (Multiplicative (ZMod e)) :=
        Nat.card_congr eI.symm.toEquiv
      _ = e := by simp
  obtain ⟨hGal, hbij⟩ := extension_kummer_bijective
    (K := K) (L := canonicalUnramifiedLevel K f)
    (C := I) (E := H) S
    hS
    phi
    (tame_inertia_injective K x y hcoprime zeta hzeta)
    (fun sigma i => tame_inertia_equivariant
      K x y hcoprime hconj zeta hzeta sigma i)
    e hcardI
    (fun i => tame_pair_inertia
      K x y hcoprime zeta hzeta i)
    b hb a ha hirr
  exact ⟨hGal, _, hbij⟩

end TBluepr
end Towers
