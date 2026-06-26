import Mathlib.RingTheory.Valuation.Discrete.Basic
import Towers.ClassField.NormCorrespondence.SubgroupOpenClosed
import Towers.ClassField.NormCorrespondence.LocalStatement
import Towers.ClassField.LocalBrauer.DivisionAlgebraOrder

/-!
# Class Field Theory, Theorem I.1.13: prime elements generate

The proof of uniqueness in Theorem 1.13 ends by observing that the prime
elements of a local field generate its multiplicative group.  Here a prime
element is represented by a uniformizer for an explicit rank-one discrete
valuation.  The full uniqueness theorem still requires the maximal abelian
and maximal unramified extensions, but this final group-theoretic step is
unconditional.
-/

namespace Towers.CField.NCorr

open Towers.CField.LBrauer
open Towers.CField.LFTheory

variable {K Gamma : Type*} [Field K]
  [LinearOrderedCommGroupWithZero Gamma]

/-- The elements of `K^x` which are uniformizers for `v`. -/
def valuationUniformizers (v : Valuation K Gamma) [v.IsRankOneDiscrete] :
    Set Kˣ :=
  {x | v.IsUniformizer (x : K)}

/-- The prime elements of a discretely valued field generate its
multiplicative group.  This is the final generation argument in the proof of
Theorem 1.13. -/
theorem valuation_uniformizers_top
    (v : Valuation K Gamma) [v.IsRankOneDiscrete] :
    Subgroup.closure (valuationUniformizers v) = ⊤ := by
  apply top_unique
  intro x _
  let pi : v.Uniformizer := Classical.choice inferInstance
  let p : Kˣ := Units.mk0 (pi.val : K) pi.ne_zero
  have hpUniformizer : v.IsUniformizer (p : K) := by
    simpa [p] using pi.2
  have hp : p ∈ Subgroup.closure (valuationUniformizers v) :=
    Subgroup.subset_closure hpUniformizer
  have hvx0 : v (x : K) ≠ 0 := (map_ne_zero v).2 x.ne_zero
  let vx : Gammaˣ := Units.mk0 (v (x : K)) hvx0
  have hvx : vx ∈ MonoidWithZeroHom.valueGroup v := by
    apply MonoidWithZeroHom.mem_valueGroup v
    exact Set.mem_range_self (x : K)
  rw [hpUniformizer.zpowers_eq_valueGroup] at hvx
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hvx
  have hvalx : v (x : K) = v (p : K) ^ m := by
    have h := congrArg ((↑) : Gammaˣ → Gamma) hm
    simpa [vx, Units.val_zpow_eq_zpow_val] using h.symm
  let u : Kˣ := x * p ^ (-m)
  have hvalu : v (u : K) = 1 := by
    simp only [u, Units.val_mul, Units.val_zpow_eq_zpow_val,
      map_mul, map_zpow₀]
    rw [hvalx, zpow_neg]
    exact mul_inv_cancel₀ (zpow_ne_zero _ hpUniformizer.val_ne_zero)
  have hupUniformizer : v.IsUniformizer ((u * p : Kˣ) : K) := by
    change v ((u : K) * (p : K)) = _
    rw [map_mul, hvalu, one_mul]
    exact hpUniformizer
  have hup : u * p ∈ Subgroup.closure (valuationUniformizers v) :=
    Subgroup.subset_closure hupUniformizer
  have hu : u ∈ Subgroup.closure (valuationUniformizers v) := by
    rw [show u = (u * p) * p⁻¹ by group]
    exact (Subgroup.closure (valuationUniformizers v)).mul_mem hup
      ((Subgroup.closure (valuationUniformizers v)).inv_mem hp)
  rw [show x = u * p ^ m by simp [u]]
  exact (Subgroup.closure (valuationUniformizers v)).mul_mem hu
    ((Subgroup.closure (valuationUniformizers v)).zpow_mem hp m)

/-- The generation step used in paragraph 1.14: two multiplicative
homomorphisms which agree on every prime element agree everywhere. -/
theorem monoid_valuation_uniformizers
    (v : Valuation K Gamma) [v.IsRankOneDiscrete]
    {G : Type*} [Group G] (f g : Kˣ →* G)
    (hfg : ∀ x ∈ valuationUniformizers v, f x = g x) :
    f = g := by
  apply MonoidHom.ext
  intro x
  have hclosure : Subgroup.closure (valuationUniformizers v) ≤ f.eqLocus g :=
    (Subgroup.closure_le _).2 hfg
  apply hclosure
  rw [valuation_uniformizers_top v]
  trivial

section LocalField

open ValuativeRel
open scoped WithZero

variable (K : Type*) [NontriviallyNormedField K]
  [IsUltrametricDist K] [ValuativeRel K]
  [IsNonarchimedeanLocalField K]

omit [IsUltrametricDist K] in
/-- Under the normalized identification of the local value group with
WithZero (Multiplicative integers), the largest value below one is exp(-1). -/
theorem local_int_uniformizer :
    local_value_int K (uniformizer K) =
      WithZero.exp (-1 : ℤ) := by
  let e := local_value_int K
  apply le_antisymm
  · apply (WithZero.lt_mul_exp_iff_le
      (WithZero.exp_pos (G := ℤ) (a := -1)).ne').1
    have hlt : e (uniformizer K) < e 1 :=
      (map_lt_map_iff e).2 (uniformizer_lt_one (R := K))
    simpa [e, ← WithZero.exp_add] using hlt
  · have hprelt : e.symm (WithZero.exp (-1 : ℤ)) < 1 := by
      apply (map_lt_map_iff e).1
      have hexp :
          WithZero.exp (-1 : ℤ) < WithZero.exp (0 : ℤ) :=
        (WithZero.exp_lt_exp).2 (by omega)
      simpa [e] using hexp
    have hprele :
        e.symm (WithZero.exp (-1 : ℤ)) ≤ uniformizer K :=
      (le_uniformizer_iff (R := K)).2 hprelt
    have hmap := (map_le_map_iff e).2 hprele
    simpa using hmap

/-- The prime-element predicate used in Theorem I.1.1 is equivalently the
condition that normalized additive order is one. -/
theorem local_element_order
    (π : Kˣ) :
    LocalPrimeElement K π ↔
      localUnitOrder K (Additive.ofMul π) = 1 := by
  let e := local_value_int K
  have he :
      e (uniformizer K) = WithZero.exp (-1 : ℤ) :=
    local_int_uniformizer K
  constructor
  · intro hπ
    change valuation K (π : K) = uniformizer K at hπ
    change -WithZero.log (e (valuation K (π : K))) = 1
    rw [hπ, he]
    simp
  · intro hπ
    change valuation K (π : K) = uniformizer K
    apply e.injective
    change e (valuation K (π : K)) = e (uniformizer K)
    rw [he]
    have hne : e (valuation K (π : K)) ≠ 0 := by
      rw [ne_eq, map_eq_zero, map_eq_zero]
      exact π.ne_zero
    have hlog :
        WithZero.log (e (valuation K (π : K))) = (-1 : ℤ) := by
      rw [local_field_order] at hπ
      change -WithZero.log (e (valuation K (π : K))) = 1 at hπ
      omega
    calc
      e (valuation K (π : K)) =
          WithZero.exp (WithZero.log (e (valuation K (π : K)))) :=
        (WithZero.exp_log hne).symm
      _ = WithZero.exp (-1 : ℤ) := by rw [hlog]

/-- An element is a local unit exactly when its normalized additive order
is zero. -/
theorem local_order_zero
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (x : Kˣ) :
    x ∈ localUnitSubgroup K ↔
      localUnitOrder K (Additive.ofMul x) = 0 := by
  constructor
  · intro hx
    have hxval : valuation K (x : K) = 1 :=
      (local_subgroup K x).1 hx
    apply le_antisymm
    · have h := (local_order_valuation K x 1).2
          (by simp [hxval])
      simpa using h
    · have h := (local_order_valuation K 1 x).2
          (by simp [hxval])
      simpa using h
  · intro hx
    apply (local_subgroup K x).2
    apply le_antisymm
    · have hle : localUnitOrder K (Additive.ofMul (1 : Kˣ)) ≤
          localUnitOrder K (Additive.ofMul x) := by simp [hx]
      simpa using
        (local_order_valuation K (1 : Kˣ) x).1 hle
    · have hle : localUnitOrder K (Additive.ofMul x) ≤
          localUnitOrder K (Additive.ofMul (1 : Kˣ)) := by simp [hx]
      simpa using
        (local_order_valuation K x (1 : Kˣ)).1 hle

/-- The set of prime elements in the intrinsic normalization used by local
reciprocity. -/
def localPrimeElements : Set Kˣ :=
  {π | LocalPrimeElement K π}

/-- A nonarchimedean local field has a prime element in the normalization
used by Theorem I.1.1. -/
theorem local_prime_element :
    ∃ π : Kˣ, LocalPrimeElement K π := by
  obtain ⟨π, hπ⟩ :=
    ValuativeRel.valuation_surjective (K := K) (uniformizer K)
  have hπ0 : π ≠ 0 := by
    intro hzero
    subst π
    rw [map_zero] at hπ
    exact (uniformizer_pos (R := K)).ne' hπ.symm
  exact ⟨Units.mk0 π hπ0, hπ⟩

/-- The prime elements appearing in Theorem I.1.13 generate the
multiplicative group of K.

Writing ord(x) = m, the element u = x times pi^(-m) has order zero, so both
pi and u*pi are prime elements and x = (u*pi)*pi^(m-1). -/
theorem elements_closure_top :
    Subgroup.closure (localPrimeElements K) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨π, hπ⟩ := local_prime_element K
  have hπorder :
      localUnitOrder K (Additive.ofMul π) = 1 :=
    (local_element_order K π).1 hπ
  have hπmem : π ∈ Subgroup.closure (localPrimeElements K) :=
    Subgroup.subset_closure hπ
  let m : ℤ := localUnitOrder K (Additive.ofMul x)
  let u : Kˣ := x * π ^ (-m)
  have huorder :
      localUnitOrder K (Additive.ofMul u) = 0 := by
    change localUnitOrder K
      (Additive.ofMul x + (-m) • Additive.ofMul π) = 0
    rw [map_add, map_zsmul, hπorder]
    simp [m]
  have huporder :
      localUnitOrder K (Additive.ofMul (u * π)) = 1 := by
    change localUnitOrder K
      (Additive.ofMul u + Additive.ofMul π) = 1
    rw [map_add, huorder, hπorder, zero_add]
  have hup : u * π ∈ localPrimeElements K :=
    (local_element_order K (u * π)).2
      huporder
  have hupmem : u * π ∈ Subgroup.closure (localPrimeElements K) :=
    Subgroup.subset_closure hup
  rw [show x = (u * π) * π ^ (m - 1) by simp [u]; group]
  exact (Subgroup.closure (localPrimeElements K)).mul_mem hupmem
    ((Subgroup.closure (localPrimeElements K)).zpow_mem hπmem (m - 1))

/-- Two homomorphisms agreeing on every prime element in the intrinsic
normalization of Theorem I.1.1 agree everywhere.  This is the final
generation step in Theorem I.1.13 with no normalization bridge left as a
hypothesis. -/
theorem monoid_hom_elements
    {G : Type*} [Group G] (f g : Kˣ →* G)
    (hfg : ∀ π : Kˣ, LocalPrimeElement K π → f π = g π) :
    f = g := by
  apply MonoidHom.ext
  intro x
  have hclosure : Subgroup.closure (localPrimeElements K) ≤ f.eqLocus g :=
    (Subgroup.closure_le _).2 hfg
  apply hclosure
  rw [elements_closure_top K]
  trivial

end LocalField

end Towers.CField.NCorr
