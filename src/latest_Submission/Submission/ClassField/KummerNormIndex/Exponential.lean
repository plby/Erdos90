import Submission.ClassField.LubinTate.RingUnitsCard
import Submission.ClassField.LocalClass.ExpUnitHom
import Submission.ClassField.KummerNormIndex.TrivialTate

/-!
# The exponential calculation in Proposition VII.6.8

This file implements the last paragraph of Milne's proof.  A sufficiently
small principal lattice `d 𝒪_K` is carried by the local exponential to an
open finite-index subgroup of the local units.  The trivial-cyclic Herbrand
quotient is invariant under this passage, and the remaining index is the
cardinality of `𝒪_K / n 𝒪_K`.
-/

namespace Submission.CField.KNIndex

open CategoryTheory
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.LTate
open Submission.CField.LClass
open Submission.CField.LExist
open Submission.CField.LBrauer
open ValuativeRel
open scoped NormedField Pointwise Topology

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [ValuativeRel K] :=
  Valuation.integer (valuation K)

/-- Multiplication by an integral scalar, viewed as an additive map into the
local field. -/
def scaledIntegerHom
    (K : Type u) [Field K] [ValuativeRel K] (d : OK K) :
    OK K →+ K where
  toFun x := (d : K) * (x : K)
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

/-- The principal additive lattice `d 𝒪_K`. -/
def scaledIntegerLattice
    (K : Type u) [Field K] [ValuativeRel K] (d : OK K) :
    AddSubgroup K :=
  (scaledIntegerHom K d).range

/-- Multiplication by a nonzero scalar identifies `𝒪_K` additively with
the principal lattice `d 𝒪_K`. -/
noncomputable def scaledIntegerAdd
    (K : Type u) [Field K] [ValuativeRel K]
    (d : OK K) (hd : d ≠ 0) :
    OK K ≃+ scaledIntegerLattice K d := by
  let f := scaledIntegerHom K d
  apply AddEquiv.ofBijective f.rangeRestrict
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hdK : (d : K) ≠ 0 := by
      intro h
      exact hd (Subtype.ext h)
    exact mul_left_cancel₀ hdK (congrArg Subtype.val hxy)
  · exact f.rangeRestrict_surjective

theorem scaled_lattice_open
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (d : OK K) (hd : d ≠ 0) :
    IsOpen (scaledIntegerLattice K d : Set K) := by
  have hdK : (d : K) ≠ 0 := by
    intro h
    exact hd (Subtype.ext h)
  have hopen : IsOpen ((d : K) • (OK K : Set K)) :=
    (Valuation.isOpen_integer (v := valuation K)).smul₀ hdK
  convert hopen using 1
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(a : K), a.2, by simp [scaledIntegerHom]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, by simp [scaledIntegerHom]⟩

/-- A nonzero principal integral lattice can be chosen inside any
neighborhood of zero. -/
theorem scaled_lattice_subset
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (N : Set K) (hN : N ∈ nhds (0 : K)) :
    ∃ d : OK K, d ≠ 0 ∧
      (scaledIntegerLattice K d : Set K) ⊆ N := by
  rw [Metric.mem_nhds_iff] at hN
  obtain ⟨ε, hε, hεN⟩ := hN
  obtain ⟨dK, hdKpos, hdKlt⟩ :=
    NormedField.exists_norm_lt K (lt_min hε zero_lt_one)
  have hdKle : ‖dK‖ ≤ 1 :=
    (hdKlt.trans_le (min_le_right _ _)).le
  let d : OK K := ⟨dK, by
    apply (Valuation.mem_integer_iff (valuation K) dK).2
    have hdNorm : (NormedField.valuation (K := K)) dK ≤
        (NormedField.valuation (K := K)) 1 := by
      simpa only [NormedField.valuation_apply, map_one] using
        (show ‖dK‖₊ ≤ 1 by exact_mod_cast hdKle)
    have hdRel : dK ≤ᵥ (1 : K) :=
      (Valuation.Compatible.vle_iff_le
        (v := NormedField.valuation (K := K)) dK 1).2 hdNorm
    exact (Valuation.Compatible.vle_iff_le
      (v := valuation K) dK 1).1 hdRel⟩
  have hd : d ≠ 0 := by
    intro h
    have : dK = 0 := congrArg Subtype.val h
    simp [this] at hdKpos
  refine ⟨d, hd, ?_⟩
  rintro x ⟨a, rfl⟩
  apply hεN
  have ha : ‖(a : K)‖ ≤ 1 := by
    have haVal : valuation K (a : K) ≤ valuation K 1 := by
      simpa only [map_one] using
        (Valuation.mem_integer_iff (valuation K) (a : K)).1 a.2
    have haRel : (a : K) ≤ᵥ (1 : K) :=
      (Valuation.Compatible.vle_iff_le
        (v := valuation K) (a : K) 1).2 haVal
    have haNorm : (NormedField.valuation (K := K)) (a : K) ≤
        (NormedField.valuation (K := K)) 1 :=
      (Valuation.Compatible.vle_iff_le
        (v := NormedField.valuation (K := K)) (a : K) 1).1 haRel
    change ‖(a : K)‖₊ ≤ ‖(1 : K)‖₊ at haNorm
    exact_mod_cast (by simpa using haNorm)
  have hnorm : ‖(d : K) * (a : K)‖ < ε := by
    rw [norm_mul]
    calc
      ‖(d : K)‖ * ‖(a : K)‖ ≤ ‖(d : K)‖ * 1 :=
        mul_le_mul_of_nonneg_left ha (norm_nonneg _)
      _ < ε := by
        simpa [d] using hdKlt.trans_le (min_le_left _ _)
  simpa [Metric.mem_ball, dist_zero_right,
    scaledIntegerHom] using hnorm

/-- For the additive group of a ring, the image of multiplication by `n`
is the principal ideal generated by `n`. -/
def untwistAddEquiv (A : Type u) [AddCommGroup A] :
    Additive (Multiplicative A) ≃+ A where
  toFun x := x.toMul.toAdd
  invFun x := Additive.ofMul (Multiplicative.ofAdd x)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem integer_ns_span
    (A : Type u) [CommRing A] (n : ℕ) :
    AddSubgroup.map (untwistAddEquiv A).toAddMonoidHom
      (nSRange n (Additive (Multiplicative A))) =
      (Ideal.span {(n : A)}).toAddSubgroup := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz⟩, rfl⟩
    apply (Ideal.mem_span_singleton).2
    refine ⟨z.toMul.toAdd, ?_⟩
    have h := congrArg (untwistAddEquiv A) hz
    simpa [nsmul_eq_mul] using h.symm
  · intro hx
    obtain ⟨y, hy⟩ := (Ideal.mem_span_singleton).1 hx
    let x' := (untwistAddEquiv A).symm x
    let y' := (untwistAddEquiv A).symm y
    refine ⟨x', ⟨y', ?_⟩, by simp [x']⟩
    apply (untwistAddEquiv A).injective
    simpa [nsmul_eq_mul, x', y'] using hy.symm

/-- The `n`th-power quotient of the multiplicative copy of `A` is the
ordinary additive quotient `A / nA`. -/
noncomputable def integerPowerEquiv
    (A : Type u) [CommRing A] (n : ℕ) :
    A ⧸ Ideal.span {(n : A)} ≃
      Multiplicative A ⧸
        (powMonoidHom n : Multiplicative A →* Multiplicative A).range := by
  let e₂ := nSPower
    n (Multiplicative A)
  let e₁' := QuotientAddGroup.congr
    (nSRange n (Additive (Multiplicative A)))
    (Ideal.span {(n : A)}).toAddSubgroup
    (untwistAddEquiv A)
    (integer_ns_span A n)
  exact (e₁'.symm.trans e₂).toEquiv.trans Additive.toMul

/-- Quotients of local integers by a nonzero rational integer are finite. -/
@[reducible]
noncomputable def integerQuotientFinite
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [CharZero K]
    (n : ℕ) (hn : 0 < n) :
    Finite (OK K ⧸ Ideal.span {(n : OK K)}) := by
  let A := OK K
  let I : Ideal A := Ideal.span {(n : A)}
  have hI : I ≠ ⊥ := by
    intro h
    have hnA : (n : A) = 0 := by
      exact Ideal.span_singleton_eq_bot.mp h
    have hnK : (n : K) = 0 := congrArg Subtype.val hnA
    exact hn.ne' (Nat.cast_eq_zero.mp hnK)
  apply IsLocalRing.finite_quotient_iff.mpr
  obtain ⟨m, hm⟩ := exists_maximalIdeal_pow_eq_of_principal A
    (IsPrincipalIdealRing.principal (IsLocalRing.maximalIdeal A)) I hI
  exact ⟨m, hm ▸ le_rfl⟩

/-- The normalized nonarchimedean value of the rational integer `n`, in
the exact form used by Milne: `|n|⁻¹ = #(𝒪_K / n𝒪_K)`. -/
noncomputable def normalizedAbsoluteValue
    (K : Type u) [Field K] [ValuativeRel K]
    (n : ℕ) : ℝ :=
  ((Nat.card (OK K ⧸ Ideal.span {(n : OK K)}) : ℕ) : ℝ)⁻¹

/-- A characteristic-zero integral domain has no nontrivial additive
`n`-torsion. -/
theorem integer_kernel_card
    (A : Type u) [CommRing A] [IsDomain A] [CharZero A]
    (n : ℕ) (hn : 0 < n) :
    Nat.card (powMonoidHom n : Multiplicative A →*
      Multiplicative A).ker = 1 := by
  have hsub : Subsingleton
      (powMonoidHom n : Multiplicative A →* Multiplicative A).ker := by
    constructor
    intro x y
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    apply (nsmul_right_injective hn.ne').eq_iff.mp
    have hx : n • x.1.toAdd = 0 := congrArg Multiplicative.toAdd x.2
    have hy : n • y.1.toAdd = 0 := congrArg Multiplicative.toAdd y.2
    rw [hx, hy]
  exact Nat.card_unique

/-- The exponential image of a sufficiently small principal lattice.  It
is an open subgroup of the local units and is multiplicatively equivalent
to the additive group of the local integer ring. -/
theorem open_unit_integer
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [CharZero K] :
    ∃ H : Subgroup Kˣ,
      H ≤ localUnitSubgroup K ∧ IsOpen (H : Set Kˣ) ∧
        Nonempty (Multiplicative (OK K) ≃* H) := by
  let eK := localExpHomeomorph K
  let N : Set K := eK.source ∩ NormedSpace.exp ⁻¹' Metric.ball 1 1
  have hNopen : IsOpen N :=
    eK.isOpen_inter_preimage Metric.isOpen_ball
  have h0N : (0 : K) ∈ N := by
    refine ⟨exp_partial_homeomorph K, ?_⟩
    simp [Metric.mem_ball]
  obtain ⟨d, hd, hWN⟩ :=
    scaled_lattice_subset K N
      (hNopen.mem_nhds h0N)
  let W := scaledIntegerLattice K d
  have hsource : (W : Set K) ⊆ eK.source :=
    fun x hx ↦ (hWN hx).1
  let H := localExpSubgroup K W hsource
  have hopenW : IsOpen (W : Set K) :=
    scaled_lattice_open K d hd
  have hopenH : IsOpen (H : Set Kˣ) :=
    open_exp_subgroup K W hsource hopenW
  have hnear : Units.val '' (H : Set Kˣ) ⊆ Metric.ball 1 1 := by
    rintro y ⟨u, hu, rfl⟩
    let uu : H := ⟨u, hu⟩
    let x : W := (localExpUnit K W hsource).symm
      (Additive.ofMul uu)
    have hxN : (x : K) ∈ N := hWN x.2
    have hval := local_exp_val K W hsource x
    have hux : (u : K) = NormedSpace.exp (x : K) := by
      simpa [x, uu] using hval
    simpa only [hux] using hxN.2
  have hHle : H ≤ localUnitSubgroup K := by
    intro u hu
    apply (local_subgroup K u).2
    have hnorm := norm_one_ball K u
      (hnear ⟨u, hu, rfl⟩)
    have hnnnorm : ‖(u : K)‖₊ = 1 := NNReal.eq hnorm
    apply le_antisymm
    · change valuation K (u : K) ≤ valuation K (1 : K)
      apply (Valuation.Compatible.vle_iff_le
        (v := valuation K) (u : K) 1).1
      apply (Valuation.Compatible.vle_iff_le
        (v := NormedField.valuation (K := K)) (u : K) 1).2
      change ‖(u : K)‖₊ ≤ ‖(1 : K)‖₊
      simp [hnnnorm]
    · change valuation K (1 : K) ≤ valuation K (u : K)
      apply (Valuation.Compatible.vle_iff_le
        (v := valuation K) 1 (u : K)).1
      apply (Valuation.Compatible.vle_iff_le
        (v := NormedField.valuation (K := K)) 1 (u : K)).2
      change ‖(1 : K)‖₊ ≤ ‖(u : K)‖₊
      simp [hnnnorm]
  let eScale := scaledIntegerAdd K d hd
  let eExp := localExpUnit K W hsource
  let e : Multiplicative (OK K) ≃* H :=
    (eScale.trans eExp).toMultiplicativeLeft
  exact ⟨H, hHle, hopenH, ⟨e⟩⟩

/-- Regard a subgroup `H ≤ U` as a group equivalent to its `subgroupOf`
copy inside `U`. -/
noncomputable def subgroupSubgroupOf
    {M : Type u} [CommGroup M] (H U : Subgroup M) (hHU : H ≤ U) :
    H ≃* H.subgroupOf U where
  toFun x := ⟨⟨x.1, hHU x.2⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Milne's `h_n(U)=#(𝒪_K/n𝒪_K)`, expressed as an equality of rational
cardinality ratios. -/
theorem local_card_ratio
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [CharZero K]
    (n : ℕ) (hn : 0 < n) :
    (Nat.card (localUnitSubgroup K ⧸
          (powMonoidHom n : localUnitSubgroup K →*
            localUnitSubgroup K).range) : ℚ) /
        Nat.card (powMonoidHom n : localUnitSubgroup K →*
          localUnitSubgroup K).ker =
      Nat.card (OK K ⧸ Ideal.span {(n : OK K)}) := by
  obtain ⟨H, hHU, hopenH, ⟨eOH⟩⟩ :=
    open_unit_integer K
  let U := localUnitSubgroup K
  let V := H.subgroupOf U
  let eHV := subgroupSubgroupOf H U hHU
  let eOV : Multiplicative (OK K) ≃* V := eOH.trans eHV
  have hcompact : IsCompact (U : Set Kˣ) :=
    Submission.CField.LExist.local_unit_compact K
  letI : CompactSpace U := isCompact_iff_compactSpace.mp hcompact
  have hopenV : IsOpen (V : Set U) := U.subgroupOf_isOpen H hopenH
  letI : Finite (U ⧸ V) := V.quotient_finite_of_isOpen hopenV
  letI : Finite (OK K ⧸ Ideal.span {(n : OK K)}) :=
    integerQuotientFinite K n hn
  let eOQ := integerPowerEquiv (OK K) n
  letI : Finite (Multiplicative (OK K) ⧸
      (powMonoidHom n : Multiplicative (OK K) →*
        Multiplicative (OK K)).range) :=
    Finite.of_equiv (OK K ⧸ Ideal.span {(n : OK K)}) eOQ
  let eVQ := powerMulEquiv eOV n
  letI : Finite (V ⧸ (powMonoidHom n : V →* V).range) :=
    Finite.of_equiv
      (Multiplicative (OK K) ⧸
        (powMonoidHom n : Multiplicative (OK K) →*
          Multiplicative (OK K)).range) eVQ.toEquiv
  have hOKer : Nat.card
      (powMonoidHom n : Multiplicative (OK K) →*
        Multiplicative (OK K)).ker = 1 :=
    integer_kernel_card (OK K) n hn
  haveI : Subsingleton
      (powMonoidHom n : Multiplicative (OK K) →*
        Multiplicative (OK K)).ker := by
    rw [Nat.card_eq_one_iff_unique] at hOKer
    exact hOKer.1
  let eVK := powerKernelEquiv eOV n
  letI : Finite (powMonoidHom n : V →* V).ker :=
    Finite.of_equiv
      (powMonoidHom n : Multiplicative (OK K) →*
        Multiplicative (OK K)).ker eVK.toEquiv
  have hratio := card_ratio_index
    n hn U V
  rw [Nat.card_congr eVQ.symm.toEquiv,
    Nat.card_congr eVK.symm.toEquiv,
    Nat.card_congr eOQ.symm] at hratio
  rw [hOKer, Nat.cast_one, div_one] at hratio
  exact hratio

end

end Submission.CField.KNIndex
