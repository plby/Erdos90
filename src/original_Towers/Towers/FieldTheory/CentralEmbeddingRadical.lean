import Towers.FieldTheory.CentralEmbeddingCohomology
import Towers.FieldTheory.CentralTameKummer

/-!
# Irreducible radicals for finite tame pair extensions

The Hilbert--90 radical obtained from the tame factor set can be multiplied by
an element of the base field without changing its coboundary.  We choose that
element so that the adjusted radical has normalized order one.  For a
`3`-power inertia degree this makes the corresponding Kummer polynomial
irreducible.
-/

noncomputable section

namespace Towers
namespace TBluepr

open Polynomial
open Towers.CField.LBrauer

universe u

/-- A radical over an unramified extension can be rescaled from the base so
that its normalized order is one. -/
theorem base_rescaling_order
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (horder : ∀ x : Kˣ,
      localUnitOrder L
          (Additive.ofMul (Units.map (algebraMap K L) x)) =
        localUnitOrder K (Additive.ofMul x))
    (a : Lˣ) :
    ∃ t : Kˣ,
      localUnitOrder L
          (Additive.ofMul (a * Units.map (algebraMap K L) t)) = 1 := by
  obtain ⟨t, ht⟩ := local_order_surjective K
    (1 - localUnitOrder L (Additive.ofMul a))
  refine ⟨t.toMul, ?_⟩
  change localUnitOrder L
      (Additive.ofMul a +
        Additive.ofMul (Units.map (algebraMap K L) t.toMul)) = 1
  rw [map_add, horder]
  change localUnitOrder L (Additive.ofMul a) +
      localUnitOrder K t = 1
  rw [ht]
  omega

/-- Multiplying a radical by a scalar from the fixed field leaves its Galois
coboundary unchanged. -/
theorem rescaling_preserves_coboundary
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (e : ℕ) (a : Lˣ) (b : Gal(L/K) → Lˣ)
    (ha : ∀ sigma : Gal(L/K),
      Units.map sigma.toRingEquiv.toMonoidHom a / a = b sigma ^ e)
    (t : Kˣ) :
    ∀ sigma : Gal(L/K),
      Units.map sigma.toRingEquiv.toMonoidHom
          (a * Units.map (algebraMap K L) t) /
          (a * Units.map (algebraMap K L) t) =
        b sigma ^ e := by
  intro sigma
  have ht : Units.map sigma.toRingEquiv.toMonoidHom
      (Units.map (algebraMap K L) t) =
        Units.map (algebraMap K L) t := by
    ext
    simp
  calc
    Units.map sigma.toRingEquiv.toMonoidHom
          (a * Units.map (algebraMap K L) t) /
          (a * Units.map (algebraMap K L) t) =
        Units.map sigma.toRingEquiv.toMonoidHom a / a := by
          rw [map_mul, ht]
          simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    _ = b sigma ^ e := ha sigma

/-- A local-field unit of normalized order one cannot be a cube. -/
theorem not_cube_order
    (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    (a : Lˣ)
    (ha : localUnitOrder L (Additive.ofMul a) = 1) :
    ∀ b : L, b ^ 3 ≠ (a : L) := by
  intro b hb
  have hb0 : b ≠ 0 := by
    intro h
    subst b
    apply a.ne_zero
    simpa using hb.symm
  let bu : Lˣ := Units.mk0 b hb0
  have hbu : bu ^ 3 = a := by
    ext
    simpa [bu] using hb
  have hbuAdd : 3 • Additive.ofMul bu = Additive.ofMul a := by
    apply Additive.toMul.injective
    simpa using hbu
  have hord := congrArg (localUnitOrder L) hbuAdd
  rw [map_nsmul, ha] at hord
  have hord' : 3 * localUnitOrder L (Additive.ofMul bu) = 1 := by
    simpa [nsmul_eq_mul] using hord
  omega

/-- For a `3`-power exponent, order one of the radical gives the standard
Kummer irreducibility criterion. -/
theorem tame_kummer_irreducible
    (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    (e r : ℕ) (he : e = 3 ^ r) (a : Lˣ)
    (ha : localUnitOrder L (Additive.ofMul a) = 1) :
    Irreducible (tameKummerPolynomial e a) := by
  subst e
  simpa [tameKummerPolynomial] using
    X_pow_sub_C_irreducible_of_prime_pow (K := L)
      (p := 3) (by norm_num) (by norm_num) r
      (not_cube_order L a ha)

set_option maxHeartbeats 3000000 in
-- The canonical unramified level and its tame quotient share a dependent degree.
set_option synthInstance.maxHeartbeats 1000000 in
/-- Kummer data for a finite tame pair in a `3`-group, with an irreducible
radical polynomial. -/
theorem tame_irreducible_kummer
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
        ∃ a : (canonicalUnramifiedLevel K f)ˣ,
          (∀ sigma,
            Units.map sigma.toRingEquiv.toMonoidHom a / a =
              b sigma ^ e) ∧
          Irreducible (tameKummerPolynomial e a) := by
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
  change ∀ (zeta : canonicalUnramifiedLevel K f)
    (hzeta : IsPrimitiveRoot zeta e), _
  intro zeta hzeta
  let U := canonicalUnramifiedLevel K f
  letI : Algebra.IsAlgebraic K U := Algebra.IsAlgebraic.of_finite K U
  letI : NontriviallyNormedField U :=
    FLExt.nontriviallyNormedField K U
  letI : NormedAlgebra K U := spectralNorm.normedAlgebra K U
  letI : IsUltrametricDist U := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel U := FLExt.valuativeRel K U
  letI : Valuation.Compatible (NormedField.valuation (K := U)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := U))
  letI : IsNonarchimedeanLocalField U :=
    FLExt.nonarchimedeanLocalField K U
  obtain ⟨_hResidueAlgebra, _hUnit, horder, _hIntegerData⟩ :=
    unramified_level_data K f
  obtain ⟨b, hb, a, ha⟩ :=
    tame_kummer_data K x y hcoprime hconj zeta hzeta
  obtain ⟨t, ht⟩ := base_rescaling_order K U horder a
  let a' : Uˣ := a * Units.map (algebraMap K U) t
  have ha' : ∀ sigma : Gal(U/K),
      Units.map sigma.toRingEquiv.toMonoidHom a' / a' = b sigma ^ e := by
    exact rescaling_preserves_coboundary K U e a b ha t
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨r, hr⟩ := (IsPGroup.iff_orderOf.mp hG) x
  refine ⟨b, hb, a', ha', ?_⟩
  exact tame_kummer_irreducible U e r hr a' ht

end TBluepr
end Towers
