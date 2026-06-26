import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.GroupTheory.NoncommCoprod

/-!
# Class Field Theory, Chapter I, the local Artin map

This file formalizes the algebraic setup immediately after Example 3.8.  A
chosen uniformizer gives the unique decomposition `a = u * pi^m`.  Hence a
unit action and a Frobenius action define a homomorphism on the whole
multiplicative group, provided that their images commute.
-/

namespace Submission.CField.LTate

variable {K Gamma : Type*} [Field K]
  [LinearOrderedCommGroupWithZero Gamma]

/-- Every nonzero element is a valuation unit times an integral power of a
chosen uniformizer. -/
theorem unit_uniformizer_zpow
    (v : Valuation K Gamma) [v.IsRankOneDiscrete]
    (pi : K) (hpi : v.IsUniformizer pi) (x : Kˣ) :
    ∃ (u : Kˣ) (m : ℤ), v (u : K) = 1 ∧
      x = u * (Units.mk0 pi hpi.ne_zero) ^ m := by
  let p : Kˣ := Units.mk0 pi hpi.ne_zero
  have hvx0 : v (x : K) ≠ 0 := (map_ne_zero v).2 x.ne_zero
  let vx : Gammaˣ := Units.mk0 (v (x : K)) hvx0
  have hvx : vx ∈ MonoidWithZeroHom.valueGroup v := by
    apply MonoidWithZeroHom.mem_valueGroup v
    exact Set.mem_range_self (x : K)
  rw [hpi.zpowers_eq_valueGroup] at hvx
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hvx
  have hvalx : v (x : K) = v pi ^ m := by
    have h := congrArg ((↑) : Gammaˣ → Gamma) hm
    simpa [vx, Units.val_zpow_eq_zpow_val] using h.symm
  let u : Kˣ := x * p ^ (-m)
  have hvalu : v (u : K) = 1 := by
    simp only [u, p, Units.val_mul, Units.val_zpow_eq_zpow_val,
      Units.val_mk0, map_mul, map_zpow₀]
    rw [hvalx, zpow_neg]
    exact mul_inv_cancel₀ (zpow_ne_zero _ hpi.val_ne_zero)
  refine ⟨u, m, hvalu, ?_⟩
  simp only [u]
  change x = x * p ^ (-m) * p ^ m
  group

/-- The unit and exponent in the uniformizer decomposition are unique. -/
theorem uniformizer_zpow_injective
    (v : Valuation K Gamma) [v.IsRankOneDiscrete]
    (pi : K) (hpi : v.IsUniformizer pi)
    {u u' : Kˣ} (hu : v (u : K) = 1) (hu' : v (u' : K) = 1)
    {m n : ℤ}
    (h : u * (Units.mk0 pi hpi.ne_zero) ^ m =
      u' * (Units.mk0 pi hpi.ne_zero) ^ n) :
    u = u' ∧ m = n := by
  let p : Kˣ := Units.mk0 pi hpi.ne_zero
  have hval := congrArg (fun z : Kˣ ↦ v (z : K)) h
  have hpow : v pi ^ m = v pi ^ n := by
    simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val,
      Units.val_mk0, map_mul, map_zpow₀, hu, hu', one_mul] using hval
  have hmn : m = n :=
    zpow_right_injective₀ hpi.val_pos (ne_of_lt hpi.val_lt_one) hpow
  subst n
  refine ⟨?_, rfl⟩
  change u * p ^ m = u' * p ^ m at h
  exact mul_right_cancel h

/-- Multiplication of a valuation unit by an integral power of a fixed
uniformizer, as a group homomorphism. -/
noncomputable def timesUniformizerHom
    (v : Valuation K Gamma) [v.IsRankOneDiscrete]
    (pi : K) (hpi : v.IsUniformizer pi) :
    v.valuationSubring.unitGroup × Multiplicative ℤ →* Kˣ where
  toFun z := z.1.1 * (Units.mk0 pi hpi.ne_zero) ^ z.2.toAdd
  map_one' := by simp
  map_mul' x y := by
    change (x.1 : Kˣ) * (y.1 : Kˣ) *
        (Units.mk0 pi hpi.ne_zero) ^ (x.2.toAdd + y.2.toAdd) = _
    rw [zpow_add]
    ac_rfl

/-- A chosen uniformizer splits the multiplicative group into valuation
units and its integral valuation exponent. -/
noncomputable def unitTimesUniformizer
    (v : Valuation K Gamma) [v.IsRankOneDiscrete]
    (pi : K) (hpi : v.IsUniformizer pi) :
    v.valuationSubring.unitGroup × Multiplicative ℤ ≃* Kˣ :=
  MulEquiv.ofBijective (timesUniformizerHom v pi hpi) ⟨by
    rintro ⟨u, m⟩ ⟨u', n⟩ h
    have hu : v (((u : Kˣ) : K)) = 1 :=
      (Valuation.mem_unitGroup_iff K v (u : Kˣ)).mp u.2
    have hu' : v (((u' : Kˣ) : K)) = 1 :=
      (Valuation.mem_unitGroup_iff K v (u' : Kˣ)).mp u'.2
    have h' : (u : Kˣ) * (Units.mk0 pi hpi.ne_zero) ^ m.toAdd =
        (u' : Kˣ) * (Units.mk0 pi hpi.ne_zero) ^ n.toAdd := h
    obtain ⟨huu, hmn⟩ :=
      uniformizer_zpow_injective v pi hpi hu hu' h'
    apply Prod.ext
    · exact Subtype.ext huu
    · exact Multiplicative.toAdd.injective hmn
  , by
    intro x
    obtain ⟨u, m, hu, rfl⟩ := unit_uniformizer_zpow v pi hpi x
    refine ⟨⟨⟨u, (Valuation.mem_unitGroup_iff K v u).mpr hu⟩,
      Multiplicative.ofAdd m⟩, ?_⟩
    rfl
  ⟩

/-- Integral powers of a chosen group element as a homomorphism from the
multiplicative copy of `ℤ`. -/
def frobeniusPowers {G : Type*} [Group G] (sigma : G) :
    Multiplicative ℤ →* G where
  toFun m := sigma ^ m.toAdd
  map_one' := by simp
  map_mul' m n := by
    change sigma ^ (m.toAdd + n.toAdd) = _
    exact zpow_add sigma m.toAdd n.toAdd

/-- The purely algebraic gluing step in the local Artin-map construction.
An action of valuation units which commutes with the chosen Frobenius extends
across the uniformizer decomposition. -/
noncomputable def artinCommutingActions
    (v : Valuation K Gamma) [v.IsRankOneDiscrete]
    (pi : K) (hpi : v.IsUniformizer pi)
    {G : Type*} [Group G]
    (unitAction : v.valuationSubring.unitGroup →* G) (sigma : G)
    (hcomm : ∀ u, Commute (unitAction u) sigma) : Kˣ →* G :=
  (unitAction.noncommCoprod (frobeniusPowers sigma)
    (fun u m ↦ (hcomm u).zpow_right m.toAdd)).comp
      (unitTimesUniformizer v pi hpi).symm.toMonoidHom

theorem commuting_actions_decomposition
    (v : Valuation K Gamma) [v.IsRankOneDiscrete]
    (pi : K) (hpi : v.IsUniformizer pi)
    {G : Type*} [Group G]
    (unitAction : v.valuationSubring.unitGroup →* G) (sigma : G)
    (hcomm : ∀ u, Commute (unitAction u) sigma)
    (u : v.valuationSubring.unitGroup) (m : ℤ) :
    artinCommutingActions v pi hpi unitAction sigma hcomm
        ((u : Kˣ) * (Units.mk0 pi hpi.ne_zero) ^ m) =
      unitAction u * sigma ^ m := by
  change artinCommutingActions v pi hpi unitAction sigma hcomm
      (unitTimesUniformizer v pi hpi (u, Multiplicative.ofAdd m)) = _
  simp [artinCommutingActions, frobeniusPowers]

/-- The setup exactly as it appears before Theorem 3.9: the unit action and
the Frobenius-power action live on separate factors. -/
noncomputable def localArtinProduct
    (v : Valuation K Gamma) [v.IsRankOneDiscrete]
    (pi : K) (hpi : v.IsUniformizer pi)
    {Gpi Gun : Type*} [Group Gpi] [Group Gun]
    (unitAction : v.valuationSubring.unitGroup →* Gpi) (frob : Gun) :
    Kˣ →* Gpi × Gun :=
  (unitAction.prodMap (frobeniusPowers frob)).comp
    (unitTimesUniformizer v pi hpi).symm.toMonoidHom

theorem artin_product_decomposition
    (v : Valuation K Gamma) [v.IsRankOneDiscrete]
    (pi : K) (hpi : v.IsUniformizer pi)
    {Gpi Gun : Type*} [Group Gpi] [Group Gun]
    (unitAction : v.valuationSubring.unitGroup →* Gpi) (frob : Gun)
    (u : v.valuationSubring.unitGroup) (m : ℤ) :
    localArtinProduct v pi hpi unitAction frob
        ((u : Kˣ) * (Units.mk0 pi hpi.ne_zero) ^ m) =
      (unitAction u, frob ^ m) := by
  change localArtinProduct v pi hpi unitAction frob
      (unitTimesUniformizer v pi hpi (u, Multiplicative.ofAdd m)) = _
  simp [localArtinProduct, frobeniusPowers]

/-- Milne's sign convention for the local Artin map: the unit factor acts
through its inverse, while the uniformizer exponent gives the corresponding
power of Frobenius. -/
noncomputable def localArtinUnit
    (v : Valuation K Gamma) [v.IsRankOneDiscrete]
    (pi : K) (hpi : v.IsUniformizer pi)
    {Gpi Gun : Type*} [Group Gpi] [Group Gun]
    (unitAction : v.valuationSubring.unitGroup →* Gpi) (frob : Gun) :
    Kˣ →* Gpi × Gun :=
  localArtinProduct v pi hpi
    (unitAction.comp invMonoidHom) frob

theorem local_artin_decomposition
    (v : Valuation K Gamma) [v.IsRankOneDiscrete]
    (pi : K) (hpi : v.IsUniformizer pi)
    {Gpi Gun : Type*} [Group Gpi] [Group Gun]
    (unitAction : v.valuationSubring.unitGroup →* Gpi) (frob : Gun)
    (u : v.valuationSubring.unitGroup) (m : ℤ) :
    localArtinUnit v pi hpi unitAction frob
        ((u : Kˣ) * (Units.mk0 pi hpi.ne_zero) ^ m) =
      (unitAction u⁻¹, frob ^ m) := by
  simpa [localArtinUnit] using
    artin_product_decomposition v pi hpi
      (unitAction.comp invMonoidHom) frob u m

end Submission.CField.LTate
