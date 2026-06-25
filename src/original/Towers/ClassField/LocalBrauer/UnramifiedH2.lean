import Mathlib.Data.ZMod.QuotientGroup
import Towers.ClassField.CrossedProducts.Cohomology
import Towers.ClassField.LocalBrauer.CohomologyTransport
import Towers.ClassField.LocalBrauer.LocalFieldOrder
import Towers.ClassField.LocalBrauer.UnramifiedNormSurjectivity


/-!
# Cyclic cohomology and Brauer classes of an unramified local extension

For an unramified cyclic extension `L/K` of degree `n`, unit norms are
surjective and normalized valuations of arbitrary norms are multiples of
`n`.  Thus `Kˣ / N(Lˣ)` is `ZMod n`; cyclic `H²` and the crossed-product
equivalence transport this calculation to the relative Brauer group.
-/

namespace Towers.CField.LBrauer

noncomputable section

universe u

open ValuativeRel
open BGroups
open CProduca

attribute [local instance] Units.mulDistribMulActionRight

variable (K L : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [NontriviallyNormedField L] [IsUltrametricDist L] [ValuativeRel L]
  [IsNonarchimedeanLocalField L]
  [Valuation.Compatible (NormedField.valuation (K := L))]
  [Algebra K L] [Module.Finite K L] [IsGalois K L]
  [Algebra 𝓀[K] 𝓀[L]]

/-- The norm homomorphism on field unit groups. -/
def localNormUnits : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K)

/-- Normalized valuation modulo `n`. -/
def localOrderMod (n : ℕ) : Kˣ →* Multiplicative (ZMod n) where
  toFun x := Multiplicative.ofAdd
    (localUnitOrder K (Additive.ofMul x) : ZMod n)
  map_one' := by simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp [add_comm]

omit [IsUltrametricDist K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
theorem local_mod_surjective (n : ℕ) [NeZero n] :
    Function.Surjective (localOrderMod K n) := by
  intro z
  obtain ⟨x, hx⟩ := local_order_surjective K (z.toAdd.val : ℤ)
  refine ⟨x.toMul, ?_⟩
  apply Multiplicative.toAdd.injective
  change (localUnitOrder K x : ZMod n) = z.toAdd
  rw [hx]
  simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val z.toAdd

omit [IsUltrametricDist K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
/-- A field unit of normalized order zero comes from an integer-ring unit. -/
theorem integer_order_zero
    (x : Kˣ) (hx : localUnitOrder K (Additive.ofMul x) = 0) :
    ∃ u : 𝒪[K]ˣ, Units.map (𝒪[K]).subtype u = x := by
  have hxval : valuation K (x : K) = 1 := by
    apply le_antisymm
    · have hle : localUnitOrder K (0 : Additive Kˣ) ≤
          localUnitOrder K (Additive.ofMul x) := by simp [hx]
      simpa using
        (local_order_valuation K (1 : Kˣ) x).1 hle
    · have hle : localUnitOrder K (Additive.ofMul x) ≤
          localUnitOrder K (0 : Additive Kˣ) := by simp [hx]
      simpa using
        (local_order_valuation K x (1 : Kˣ)).1 hle
  let r : 𝒪[K] := ⟨(x : K), hxval.le⟩
  have hrUnit : IsUnit r :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).2 hxval
  refine ⟨hrUnit.unit, ?_⟩
  apply Units.ext
  change ((hrUnit.unit : 𝒪[K]) : K) = (x : K)
  simp [r]

variable {n : ℕ} [NeZero n]

omit [NeZero n] [Module.Finite K L] [IsGalois K L] in
/-- For unramified local norm data, the norm subgroup consists exactly of
the field units whose normalized order is divisible by `n`. -/
theorem ker_mod_range
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x)) :
    (localOrderMod K n).ker =
      (localNormUnits K L).range := by
  apply le_antisymm
  · intro x hx
    have hxmod :
        (localUnitOrder K (Additive.ofMul x) : ZMod n) = 0 := by
      exact congrArg Multiplicative.toAdd hx
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hxmod
    obtain ⟨z, hz⟩ := local_order_surjective L t
    let z' : Lˣ := z.toMul
    let e : Kˣ := x / localNormUnits K L z'
    have heOrder : localUnitOrder K (Additive.ofMul e) = 0 := by
      change localUnitOrder K
        (Additive.ofMul x - Additive.ofMul (localNormUnits K L z')) = 0
      rw [map_sub, horderNorm, show localUnitOrder L
        (Additive.ofMul z') = t from hz]
      change localUnitOrder K (Additive.ofMul x) - (n : ℤ) * t = 0
      rw [← ht]
      simp
    obtain ⟨eu, heu⟩ := integer_order_zero K e heOrder
    obtain ⟨w, hw⟩ := unramified_units_surjective K L N hN eu
    let w' : Lˣ := Units.map (𝒪[L]).subtype w
    refine ⟨z' * w', ?_⟩
    rw [map_mul]
    have hwNorm : localNormUnits K L w' = e := by
      apply Units.ext
      change Algebra.norm K (((w : 𝒪[L]) : L)) = (e : K)
      rw [← hN.coe_norm w, hw, ← heu]
      rfl
    rw [hwNorm]
    simp [e]
  · intro x hx
    obtain ⟨y, rfl⟩ := hx
    apply MonoidHom.mem_ker.mpr
    apply Multiplicative.toAdd.injective
    change ((localUnitOrder K
      (Additive.ofMul (localNormUnits K L y)) : ℤ) : ZMod n) = 0
    rw [horderNorm]
    simp

/-- For unramified local norm data, normalized valuation identifies the
quotient of field units by norms with `ZMod n`. -/
noncomputable def localZMod
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x)) :
    Kˣ ⧸ (localNormUnits K L).range ≃* Multiplicative (ZMod n) := by
  have hker := ker_mod_range
    K L N hN horderNorm
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (localOrderMod K n)
      (local_mod_surjective K n))

/-- Base-field units are exactly the Galois-invariant units of `L`. -/
def baseGaloisInvariants :
    Kˣ →* FMAct.invariants Gal(L/K) Lˣ where
  toFun x := ⟨Units.map (algebraMap K L) x, by
    intro σ
    apply Units.ext
    simp⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K]
  [ValuativeRel K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsUltrametricDist L] [IsNonarchimedeanLocalField L]
  [ValuativeRel L]
  [Valuation.Compatible (NormedField.valuation (K := L))]
  [Algebra 𝓀[K] 𝓀[L]] in
theorem base_invariants_bijective :
    Function.Bijective (baseGaloisInvariants K L) := by
  constructor
  · intro x y hxy
    apply Units.ext
    apply (algebraMap K L).injective
    have h := congrArg
      (fun z : FMAct.invariants Gal(L/K) Lˣ ↦ ((z.1 : Lˣ) : L)) hxy
    simpa [baseGaloisInvariants] using h
  · intro x
    have hfixed : ∀ σ : Gal(L/K), σ (x.1 : L) = (x.1 : L) := by
      intro σ
      have h := x.2 σ
      exact congrArg Units.val h
    obtain ⟨a, ha⟩ :=
      (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L) (x.1 : L)).2 hfixed
    have ha0 : a ≠ 0 := by
      intro ha0
      rw [ha0, map_zero] at ha
      exact x.1.ne_zero ha.symm
    let a' : Kˣ := Units.mk0 a ha0
    refine ⟨a', ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact ha

/-- Multiplicative equivalence between base units and Galois invariants. -/
noncomputable def baseUnitsInvariants :
    Kˣ ≃* FMAct.invariants Gal(L/K) Lˣ :=
  MulEquiv.ofBijective (baseGaloisInvariants K L)
    (base_invariants_bijective K L)

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K]
  [ValuativeRel K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsUltrametricDist L] [IsNonarchimedeanLocalField L]
  [ValuativeRel L]
  [Valuation.Compatible (NormedField.valuation (K := L))]
  [Algebra 𝓀[K] 𝓀[L]] in
/-- The finite-action norm corresponds to the field norm under the fixed-unit
equivalence. -/
theorem base_units_invariants (x : Lˣ) :
    baseUnitsInvariants K L (localNormUnits K L x) =
      FMAct.norm Gal(L/K) Lˣ x := by
  apply Subtype.ext
  apply Units.ext
  simpa [baseUnitsInvariants,
    baseGaloisInvariants, localNormUnits,
    FMAct.norm] using
      (Algebra.norm_eq_prod_automorphisms K (x : L))

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K]
  [ValuativeRel K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsUltrametricDist L] [IsNonarchimedeanLocalField L]
  [ValuativeRel L]
  [Valuation.Compatible (NormedField.valuation (K := L))]
  [Algebra 𝓀[K] 𝓀[L]] in
private theorem galois_comap_units :
    (FMAct.norm Gal(L/K) Lˣ).range ≤
      (localNormUnits K L).range.comap
        (baseUnitsInvariants K L).symm.toMonoidHom := by
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  refine ⟨x, ?_⟩
  change localNormUnits K L x =
    (baseUnitsInvariants K L).symm
      (FMAct.norm Gal(L/K) Lˣ x)
  exact (baseUnitsInvariants K L).eq_symm_apply.mpr
    (base_units_invariants K L x)

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K]
  [ValuativeRel K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsUltrametricDist L] [IsNonarchimedeanLocalField L]
  [ValuativeRel L]
  [Valuation.Compatible (NormedField.valuation (K := L))]
  [Algebra 𝓀[K] 𝓀[L]] in
private theorem base_comap_units :
    (localNormUnits K L).range ≤
      (FMAct.norm Gal(L/K) Lˣ).range.comap
        (baseUnitsInvariants K L).toMonoidHom := by
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨x, (base_units_invariants K L x).symm⟩

/-- Galois-invariants modulo the finite-action norm are base-field units
modulo the field norm. -/
noncomputable def galoisInvariantsBase :
    FMAct.invariantsModNorm Gal(L/K) Lˣ ≃*
      Kˣ ⧸ (localNormUnits K L).range where
  toFun := QuotientGroup.map
    (FMAct.norm Gal(L/K) Lˣ).range
    (localNormUnits K L).range
    (baseUnitsInvariants K L).symm.toMonoidHom
    (galois_comap_units K L)
  invFun := QuotientGroup.map
    (localNormUnits K L).range
    (FMAct.norm Gal(L/K) Lˣ).range
    (baseUnitsInvariants K L).toMonoidHom
    (base_comap_units K L)
  left_inv q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (FMAct.norm Gal(L/K) Lˣ).range q
    apply congrArg (QuotientGroup.mk'
      (FMAct.norm Gal(L/K) Lˣ).range)
    exact (baseUnitsInvariants K L).apply_symm_apply x
  right_inv q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (localNormUnits K L).range q
    apply congrArg (QuotientGroup.mk' (localNormUnits K L).range)
    exact (baseUnitsInvariants K L).symm_apply_apply x
  map_mul' x y := map_mul _ x y

/-- For a cyclic unramified extension of degree `n`, normalized valuation
identifies multiplicative `H²` with `ZMod n`. -/
noncomputable def hZMod
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x)) :
    MHTwo Gal(L/K) Lˣ ≃* Multiplicative (ZMod n) :=
  (GroupH2.mulInvariantsMod eGal hn).trans <|
    (galoisInvariantsBase K L).trans <|
      localZMod K L N hN horderNorm

/-- Consequently the local cyclic `H²` group has exactly `n` elements. -/
theorem nat_multiplicative_2
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x)) :
    Nat.card (MHTwo Gal(L/K) Lˣ) = n := by
  rw [Nat.card_congr
    (hZMod K L eGal hn N hN horderNorm).toEquiv]
  change Nat.card (ZMod n) = n
  exact Nat.card_zmod n

/-- A base uniformizer, viewed as an invariant coefficient in the pulled-back
cyclic model. -/
def cyclicUniformizerInvariant
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (varpiK : Kˣ) :
    letI : MulDistribMulAction (Multiplicative (ZMod n)) Lˣ :=
      GroupH2.pulledAction eGal
    CyclicH2.invariants (n := n) (M := Lˣ) := by
  letI : MulDistribMulAction (Multiplicative (ZMod n)) Lˣ :=
    GroupH2.pulledAction eGal
  refine ⟨Units.map (algebraMap K L) varpiK, ?_⟩
  intro g
  apply Units.ext
  simp [MulAction.compHom_smul_def]

/-- Milne's carry class for a chosen cyclic generator of the Galois group
and a base uniformizer. -/
noncomputable def unramifiedCarryH
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (varpiK : Kˣ) :
    MHTwo Gal(L/K) Lˣ := by
  letI : MulDistribMulAction (Multiplicative (ZMod n)) Lˣ :=
    GroupH2.pulledAction eGal
  let pi := cyclicUniformizerInvariant K L eGal varpiK
  exact (GroupH2.hCyclicModel eGal).symm
    (MHTwo.mk (CCarry.factorSet pi.1 pi.2))

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K]
  [ValuativeRel K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsUltrametricDist L] [IsNonarchimedeanLocalField L]
  [ValuativeRel L]
  [Valuation.Compatible (NormedField.valuation (K := L))]
  [Algebra 𝓀[K] 𝓀[L]] in
private theorem cyclic_h_carry
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (varpiK : Kˣ) :
    GroupH2.mulInvariantsMod eGal hn
        (unramifiedCarryH K L eGal varpiK) =
      QuotientGroup.mk' (FMAct.norm Gal(L/K) Lˣ).range
        (baseUnitsInvariants K L varpiK) := by
  letI : MulDistribMulAction (Multiplicative (ZMod n)) Lˣ :=
    GroupH2.pulledAction eGal
  let pi := cyclicUniformizerInvariant K L eGal varpiK
  have hcarry :
      CyclicH2.mulInvariantsMod (n := n) (M := Lˣ) hn
          (MHTwo.mk (CCarry.factorSet pi.1 pi.2)) =
        QuotientGroup.mk' (CyclicH2.norm (n := n) (M := Lˣ)).range pi := by
    have h := CyclicH2.symm_mk_carry
      (n := n) (M := Lˣ) hn pi
    simpa using (congrArg
      (CyclicH2.mulInvariantsMod (n := n) (M := Lˣ) hn) h).symm
  change GroupH2.invariantsModEquiv eGal
      (CyclicH2.mulInvariantsMod (n := n) (M := Lˣ) hn
        (GroupH2.hCyclicModel eGal
          (unramifiedCarryH K L eGal varpiK))) = _
  rw [unramifiedCarryH, MulEquiv.apply_symm_apply, hcarry]
  apply congrArg (QuotientGroup.mk'
    (FMAct.norm Gal(L/K) Lˣ).range)
  apply Subtype.ext
  apply Units.ext
  rfl

/-- The carry cocycle attached to an arbitrary base-field unit maps to its
normalized order modulo `n`. -/
theorem z_mod_carry
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x))
    (a : Kˣ) :
    hZMod K L eGal hn N hN horderNorm
        (unramifiedCarryH K L eGal a) =
      Multiplicative.ofAdd
        (localUnitOrder K (Additive.ofMul a) : ZMod n) := by
  change localZMod K L N hN horderNorm
      (galoisInvariantsBase K L
        (GroupH2.mulInvariantsMod eGal hn
          (unramifiedCarryH K L eGal a))) = _
  rw [cyclic_h_carry K L eGal hn a]
  rw [show galoisInvariantsBase K L
      (QuotientGroup.mk' (FMAct.norm Gal(L/K) Lˣ).range
        (baseUnitsInvariants K L a)) =
      QuotientGroup.mk' (localNormUnits K L).range a by
    apply congrArg (QuotientGroup.mk' (localNormUnits K L).range)
    exact (baseUnitsInvariants K L).symm_apply_apply a]
  rfl

/-- The carry cocycle attached to a normalized base uniformizer maps to the
standard generator of `ZMod n`. -/
theorem h_z_carry
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x))
    (varpiK : Kˣ)
    (hvarpiK : localUnitOrder K (Additive.ofMul varpiK) = 1) :
    hZMod K L eGal hn N hN horderNorm
        (unramifiedCarryH K L eGal varpiK) =
      Multiplicative.ofAdd (1 : ZMod n) := by
  rw [z_mod_carry
    K L eGal hn N hN horderNorm varpiK, hvarpiK]
  apply Multiplicative.toAdd.injective
  simp

/-- Every class in local cyclic `H²` is a power of Milne's carry class. -/
theorem unramified_carry_h
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x))
    (varpiK : Kˣ)
    (hvarpiK : localUnitOrder K (Additive.ofMul varpiK) = 1)
    (x : MHTwo Gal(L/K) Lˣ) :
    ∃ i : ZMod n, x = (unramifiedCarryH K L eGal varpiK) ^ i.val := by
  let e := hZMod K L eGal hn N hN horderNorm
  let i : ZMod n := (e x).toAdd
  have hi : Multiplicative.ofAdd (1 : ZMod n) ^ i.val =
      Multiplicative.ofAdd i := by
    apply Multiplicative.toAdd.injective
    simp
  refine ⟨i, e.injective ?_⟩
  rw [map_pow, h_z_carry
    K L eGal hn N hN horderNorm varpiK hvarpiK, hi]
  rfl

/-- The explicit Galois cocycle obtained by transporting Milne's carry
cocycle from the chosen `ZMod n` model. -/
noncomputable def unramifiedCarryCocycle
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (varpiK : Kˣ) :
    NMCocycl₂ (G := Gal(L/K)) (M := Lˣ) := by
  letI : MulDistribMulAction (Multiplicative (ZMod n)) Lˣ :=
    GroupH2.pulledAction eGal
  let pi := cyclicUniformizerInvariant K L eGal varpiK
  exact MHTrans.cocycleMap eGal (MulEquiv.refl Lˣ)
    (by intro g x; rfl) (CCarry.factorSet pi.1 pi.2)

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K]
  [ValuativeRel K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
  [IsUltrametricDist L] [IsNonarchimedeanLocalField L]
  [ValuativeRel L]
  [Valuation.Compatible (NormedField.valuation (K := L))]
  [Module.Finite K L] [IsGalois K L] [Algebra 𝓀[K] 𝓀[L]] in
/-- The explicit transported cocycle represents the carry class used above. -/
theorem mk_carry_cocycle
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (varpiK : Kˣ) :
    MHTwo.mk (unramifiedCarryCocycle K L eGal varpiK) =
      unramifiedCarryH K L eGal varpiK := by
  letI : MulDistribMulAction (Multiplicative (ZMod n)) Lˣ :=
    GroupH2.pulledAction eGal
  let pi := cyclicUniformizerInvariant K L eGal varpiK
  apply (GroupH2.hCyclicModel eGal).injective
  rw [unramifiedCarryH, MulEquiv.apply_symm_apply]
  change MHTwo.mk
      (MHTrans.cocycleMap eGal.symm (MulEquiv.refl Lˣ)
        (by
          intro g x
          change g • x = eGal (eGal.symm g) • x
          rw [eGal.apply_symm_apply])
        (MHTrans.cocycleMap eGal (MulEquiv.refl Lˣ)
          (by intro g x; rfl) (CCarry.factorSet pi.1 pi.2))) =
    MHTwo.mk (CCarry.factorSet pi.1 pi.2)
  apply congrArg MHTwo.mk
  exact (MHTrans.cocycleMulEquiv eGal
    (MulEquiv.refl Lˣ) (by intro g x; rfl)).left_inv
      (CCarry.factorSet pi.1 pi.2)

/-- Crossed products identify the relative Brauer group with `ZMod n`. -/
noncomputable def unramifiedZMod
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x)) :
    relativeBrauerGroup K L ≃* Multiplicative (ZMod n) :=
  (CProduc.hRelativeBrauer K L).symm.trans
    (hZMod K L eGal hn N hN horderNorm)

/-- The crossed-product class of the carry cocycle. -/
def unramifiedCarryRelative
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (varpiK : Kˣ) :
    relativeBrauerGroup K L :=
  CProduc.relativeBrauerClass K L
    (unramifiedCarryCocycle K L eGal varpiK)

/-- The crossed product attached to an arbitrary base-field unit maps to its
normalized order modulo `n`. -/
theorem unramified_z_carry
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x))
    (a : Kˣ) :
    unramifiedZMod K L eGal hn N hN horderNorm
        (unramifiedCarryRelative K L eGal a) =
      Multiplicative.ofAdd
        (localUnitOrder K (Additive.ofMul a) : ZMod n) := by
  change hZMod K L eGal hn N hN horderNorm
      ((CProduc.hRelativeBrauer K L).symm
        (CProduc.relativeBrauerClass K L
          (unramifiedCarryCocycle K L eGal a))) = _
  rw [show CProduc.relativeBrauerClass K L
      (unramifiedCarryCocycle K L eGal a) =
        CProduc.hRelativeBrauer K L
          (MHTwo.mk
            (unramifiedCarryCocycle K L eGal a)) by rfl,
    MulEquiv.symm_apply_apply,
    mk_carry_cocycle K L eGal a]
  exact z_mod_carry
    K L eGal hn N hN horderNorm a

/-- The carry crossed product is the standard generator of the cyclic
relative Brauer group. -/
theorem relative_z_carry
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x))
    (varpiK : Kˣ)
    (hvarpiK : localUnitOrder K (Additive.ofMul varpiK) = 1) :
    unramifiedZMod K L eGal hn N hN horderNorm
        (unramifiedCarryRelative K L eGal varpiK) =
      Multiplicative.ofAdd (1 : ZMod n) := by
  rw [unramified_z_carry
    K L eGal hn N hN horderNorm varpiK, hvarpiK]
  apply Multiplicative.toAdd.injective
  simp

/-- Every relative Brauer class is a power of the crossed-product carry
class. -/
theorem unramified_carry_brauer
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x))
    (varpiK : Kˣ)
    (hvarpiK : localUnitOrder K (Additive.ofMul varpiK) = 1)
    (x : relativeBrauerGroup K L) :
    ∃ i : ZMod n,
      x = (unramifiedCarryRelative K L eGal varpiK) ^ i.val := by
  let e := unramifiedZMod K L eGal hn N hN horderNorm
  let i : ZMod n := (e x).toAdd
  have hi : Multiplicative.ofAdd (1 : ZMod n) ^ i.val =
      Multiplicative.ofAdd i := by
    apply Multiplicative.toAdd.injective
    simp
  refine ⟨i, e.injective ?_⟩
  rw [map_pow, relative_z_carry
    K L eGal hn N hN horderNorm varpiK hvarpiK, hi]
  rfl

/-- The relative Brauer group of the unramified cyclic extension has order
`n`. -/
theorem nat_relative_brauer
    (eGal : Multiplicative (ZMod n) ≃* Gal(L/K)) (hn : 1 < n)
    (N : 𝒪[L]ˣ →* 𝒪[K]ˣ) (hN : UnramifiedLocalData K L N)
    (horderNorm : ∀ x : Lˣ,
      localUnitOrder K
          (Additive.ofMul (localNormUnits K L x)) =
        (n : ℤ) * localUnitOrder L (Additive.ofMul x)) :
    Nat.card (relativeBrauerGroup K L) = n := by
  rw [Nat.card_congr
    (unramifiedZMod K L eGal hn N hN horderNorm).toEquiv]
  change Nat.card (ZMod n) = n
  exact Nat.card_zmod n

end

end Towers.CField.LBrauer
