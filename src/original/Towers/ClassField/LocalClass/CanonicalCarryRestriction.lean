import Towers.ClassField.LocalBrauer.GaloisCarryRestriction
import Towers.ClassField.LocalBrauer.CanonicalUnramifiedTower

/-!
# Carry restriction between arbitrary canonical unramified levels

For `U_f ⊆ U_{m f}`, the unique order-`m` subgroup of the cyclic Galois
group of `U_{m f}/K` is the Galois group over `U_f`.  This file packages its
cyclic coordinate so that the concrete carry-restriction theorem applies.
-/

namespace Towers.CField.LClass

noncomputable section

universe u

open CProduca LBrauer

variable (K : Type u)
  [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

private abbrev lowerLevel (f : ℕ) := canonicalUnramifiedLevel K f
private abbrev upperLevel (m f : ℕ) := canonicalUnramifiedLevel K (m * f)

private def lowerUpperInclusion (m f : ℕ) [NeZero m] [NeZero f] :
    lowerLevel K f ≤ upperLevel K m f :=
  unramified_level K
    (NeZero.pos f) (mul_pos (NeZero.pos m) (NeZero.pos f))
    (dvd_mul_left f m)

set_option synthInstance.maxHeartbeats 1000000 in
-- The algebra structure is defined through nested intermediate-field coercions.
local instance lowerUpperAlgebra (m f : ℕ) [NeZero m] [NeZero f] :
    Algebra (lowerLevel K f) (upperLevel K m f) :=
  RingHom.toAlgebra (IntermediateField.inclusion (lowerUpperInclusion K m f))

set_option synthInstance.maxHeartbeats 1000000 in
-- The scalar tower compares the same nested intermediate-field coercions.
local instance lowerUpperScalarTower (m f : ℕ) [NeZero m] [NeZero f] :
    IsScalarTower K (lowerLevel K f) (upperLevel K m f) :=
  IsScalarTower.of_algebraMap_eq' rfl

set_option maxHeartbeats 1000000 in
-- Finiteness is inherited from the ambient canonical finite level.
set_option synthInstance.maxHeartbeats 1000000 in
-- Finiteness is inherited from the ambient canonical finite level.
local instance lowerUpperFiniteDimensional (m f : ℕ)
    [NeZero m] [NeZero f] :
    FiniteDimensional (lowerLevel K f) (upperLevel K m f) :=
  FiniteDimensional.right K (lowerLevel K f) (upperLevel K m f)

set_option maxHeartbeats 1000000 in
-- Galoisness descends to the top part of the canonical field tower.
set_option synthInstance.maxHeartbeats 1000000 in
-- Galoisness descends to the top part of the canonical field tower.
local instance lowerUpperIsGalois (m f : ℕ) [NeZero m] [NeZero f] :
    IsGalois (lowerLevel K f) (upperLevel K m f) :=
  IsGalois.tower_top_of_isGalois K (lowerLevel K f) (upperLevel K m f)

set_option maxHeartbeats 1000000 in
-- The two nested finite Galois intermediate-field structures are dependent.
set_option synthInstance.maxHeartbeats 100000 in
-- Nested intermediate fields require a larger typeclass-search budget.
/-- Cyclic coordinates on `Gal(U_{mf}/U_f)` compatible with the ambient
coordinates on `Gal(U_{mf}/K)`. -/
theorem compatible_tower_gal
    (m f : ℕ) [NeZero m] [NeZero f] :
    ∃ eF : Multiplicative (ZMod m) ≃*
        Gal(upperLevel K m f/lowerLevel K f),
      ∀ z, galoisTowerInclusion K (lowerLevel K f) (upperLevel K m f)
          (eF z) =
        galZMod K (m * f)
          (CCarry.subgroupHom m f z) := by
  let F := lowerLevel K f
  let U := upperLevel K m f
  let hFU : F ≤ U := lowerUpperInclusion K m f
  letI : IsGalois F U := IsGalois.tower_top_of_isGalois K F U
  letI : FiniteDimensional F U := FiniteDimensional.right K F U
  let eK := galZMod K (m * f)
  let res := galoisRestrictionHom K hFU
  have hcardF : Nat.card Gal(F/K) = f := by
    rw [IsGalois.card_aut_eq_finrank,
      unramified_level_finrank K f]
  have hresGeneratorPow :
      res (eK (CyclicH2.generator (n := m * f))) ^ f = 1 := by
    have hpow :
        (res (eK (CyclicH2.generator (n := m * f)))) ^
          Nat.card Gal(F/K) = 1 := pow_card_eq_one'
    simpa only [hcardF] using hpow
  have hsubgroupGenerator :
      CCarry.subgroupHom m f (CyclicH2.generator (n := m)) =
        CyclicH2.generator (n := m * f) ^ f := by
    apply Multiplicative.ext
    simpa [CyclicH2.generator] using
      CCarry.subgroup_nat_cast m f 1
  have hfixGenerator :
      res (eK (CCarry.subgroupHom m f
        (CyclicH2.generator (n := m)))) = 1 := by
    rw [hsubgroupGenerator, map_pow, map_pow, hresGeneratorPow]
  have hfix (z : Multiplicative (ZMod m)) :
      res (eK (CCarry.subgroupHom m f z)) = 1 := by
    rw [CyclicH2.generator_pow_val z, map_pow, map_pow, map_pow,
      hfixGenerator, one_pow]
  let qFun : Multiplicative (ZMod m) → Gal(U/F) := fun z ↦ by
      let sigma : Gal(U/K) := eK (CCarry.subgroupHom m f z)
      let tau : Gal(U/F) :=
        { sigma with
          commutes' := by
            intro x
            have hx : res sigma x = x := by
              rw [show res sigma = 1 by simpa [sigma] using hfix z]
              rfl
            change sigma (IntermediateField.inclusion hFU x) =
              IntermediateField.inclusion hFU x
            rw [← galois_restriction_hom K hFU sigma x, hx] }
      exact tau
  let q : Multiplicative (ZMod m) →* Gal(U/F) :=
    { toFun := qFun
      map_one' := by
        ext x
        simp [qFun, eK]
      map_mul' := by
        intro z w
        ext x
        simp [qFun, eK] }
  have hqcompat (z : Multiplicative (ZMod m)) :
      galoisTowerInclusion K F U (q z) =
        eK (CCarry.subgroupHom m f z) := by
    ext x
    rfl
  have hqInjective : Function.Injective q := by
    intro z w hzw
    apply CCarry.subgroupHom_injective (m := m) (f := f)
    apply eK.injective
    rw [← hqcompat, ← hqcompat, hzw]
  have hfinrankFU : Module.finrank F U = m := by
    have htower := Module.finrank_mul_finrank K F U
    rw [unramified_level_finrank K f,
      unramified_level_finrank K (m * f)] at htower
    apply Nat.eq_of_mul_eq_mul_left (NeZero.pos f)
    calc
      f * Module.finrank F U = m * f := htower
      _ = f * m := Nat.mul_comm _ _
  have hcardq : Nat.card (Multiplicative (ZMod m)) =
      Nat.card Gal(U/F) := by
    rw [show Nat.card (Multiplicative (ZMod m)) = Nat.card (ZMod m) by rfl,
      Nat.card_zmod, IsGalois.card_aut_eq_finrank, hfinrankFU]
  let eF : Multiplicative (ZMod m) ≃* Gal(U/F) :=
    MulEquiv.ofBijective q
      ((Nat.bijective_iff_injective_and_card q).2 ⟨hqInjective, hcardq⟩)
  exact ⟨eF, fun z ↦ hqcompat z⟩

set_option maxHeartbeats 1000000 in
-- The finite Galois structures on the two canonical levels are dependent.
set_option synthInstance.maxHeartbeats 100000 in
/-- Restricting a canonical unramified carry class from level `m * f` to
level `f` gives a carry class for the degree-`m` relative level. -/
theorem relative_brauer_carry
    (m f : ℕ) [NeZero m] [NeZero f] (a : Kˣ) :
    ∃ eF : Multiplicative (ZMod m) ≃*
        Gal(upperLevel K m f/lowerLevel K f),
      (∀ z, galoisTowerInclusion K (lowerLevel K f) (upperLevel K m f)
          (eF z) =
        galZMod K (m * f)
          (CCarry.subgroupHom m f z)) ∧
      relativeBrauerChange K (lowerLevel K f) (upperLevel K m f)
          (CProduc.relativeBrauerClass K (upperLevel K m f)
            (galoisCarryCocycle K
              (galZMod K (m * f)) a)) =
        CProduc.relativeBrauerClass (lowerLevel K f)
          (upperLevel K m f)
          (galoisCarryCocycle (lowerLevel K f) eF
            (Units.map (algebraMap K (lowerLevel K f)) a)) := by
  let F := lowerLevel K f
  let U := upperLevel K m f
  letI : IsGalois F U := IsGalois.tower_top_of_isGalois K F U
  letI : FiniteDimensional F U := FiniteDimensional.right K F U
  obtain ⟨eF, hcompat⟩ :=
    compatible_tower_gal K m f
  refine ⟨eF, hcompat, ?_⟩
  exact brauer_change_carry K F U
    (galZMod K (m * f)) eF hcompat a

set_option maxHeartbeats 1000000 in
-- The relative Brauer comparison unfolds two cohomology quotient maps.
set_option synthInstance.maxHeartbeats 100000 in
/-- The same canonical restriction calculation for every power of the carry
cocycle. -/
theorem relative_change_carry
    (m f : ℕ) [NeZero m] [NeZero f] (a : Kˣ) (j : ℕ) :
    ∃ eF : Multiplicative (ZMod m) ≃*
        Gal(upperLevel K m f/lowerLevel K f),
      (∀ z, galoisTowerInclusion K (lowerLevel K f) (upperLevel K m f)
          (eF z) =
        galZMod K (m * f)
          (CCarry.subgroupHom m f z)) ∧
      relativeBrauerChange K (lowerLevel K f) (upperLevel K m f)
          (CProduc.relativeBrauerClass K (upperLevel K m f)
            ((galoisCarryCocycle K
              (galZMod K (m * f)) a) ^ j)) =
        CProduc.relativeBrauerClass (lowerLevel K f)
          (upperLevel K m f)
          ((galoisCarryCocycle (lowerLevel K f) eF
            (Units.map (algebraMap K (lowerLevel K f)) a)) ^ j) := by
  let F := lowerLevel K f
  let U := upperLevel K m f
  let eK := galZMod K (m * f)
  let cK := galoisCarryCocycle K eK a
  obtain ⟨eF, hcompat, hbase⟩ :=
    relative_brauer_carry K m f a
  let cF := galoisCarryCocycle F eF (Units.map (algebraMap K F) a)
  have hpowK : CProduc.relativeBrauerClass K U (cK ^ j) =
      (CProduc.relativeBrauerClass K U cK) ^ j := by
    change (CProduc.hRelativeBrauer K U)
        (MHTwo.mk (cK ^ j)) =
      ((CProduc.hRelativeBrauer K U)
        (MHTwo.mk cK)) ^ j
    rw [← map_pow, MHTwo.mk_pow]
  have hpowF : CProduc.relativeBrauerClass F U (cF ^ j) =
      (CProduc.relativeBrauerClass F U cF) ^ j := by
    change (CProduc.hRelativeBrauer F U)
        (MHTwo.mk (cF ^ j)) =
      ((CProduc.hRelativeBrauer F U)
        (MHTwo.mk cF)) ^ j
    rw [← map_pow, MHTwo.mk_pow]
  refine ⟨eF, hcompat, ?_⟩
  rw [hpowK, map_pow, hbase, hpowF]

end

end Towers.CField.LClass
