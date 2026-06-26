import Submission.NumberTheory.Valuations.DiscreteValuations
import Submission.ClassField.LocalClass.ValuationSequence
import Submission.ClassField.LocalBrauer.FieldNormExtension
import Submission.ClassField.LocalBrauer.UnramifiedH2
import Submission.ClassField.KummerNormIndex.SubgroupIndex
import Submission.ClassField.KummerNormIndex.PowerIndex
import Submission.ClassField.KummerNormIndex.Exponential

/-!
# Chapter VII, Section 6, Proposition 6.8

Milne computes the index of the `n`th-power subgroup of a characteristic-zero
local field.  The archimedean cases are proved outright.  In the
nonarchimedean case we isolate exactly the two inputs in the printed proof:

* the exponential-map computation of the Herbrand quotient of the local
  unit group; and
* the valuation decomposition `K× ≃ U × ℤ`.

The roots-of-unity comparison is proved here for the actual local-unit
subgroup.  The nonarchimedean value is normalized exactly as in the source by
`|n|⁻¹ = #(𝒪_K / n𝒪_K)`.  Formulas are written after multiplication by this
nonzero value; this is equivalent to the displayed quotients in the source
and avoids representing a natural-number index by a real quotient.
-/

namespace Submission.CField.KNIndex

open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.LClass
open Submission.CField.LBrauer
open ValuativeRel

noncomputable section

universe u

/-- Milne's normalized complex absolute value, for which a complex place
occurs with multiplicity two. -/
def complexAbsoluteValue (z : ℂ) : ℝ := ‖z‖ ^ 2

/-- Milne's normalized real absolute value. -/
def realAbsoluteValue (x : ℝ) : ℝ := ‖x‖

/-- Every root of unity in a nonarchimedean local field is a local unit, so
the `n`-torsion of `U` is exactly `μ_n`. -/
noncomputable def rootsUnityKernel
    (K : Type u) [Field K] [ValuativeRel K]
    (n : ℕ) (hn : n ≠ 0) :
    rootsOfUnity n K ≃*
      (powMonoidHom n : localUnitSubgroup K →* localUnitSubgroup K).ker where
  toFun z := by
    let u : localUnitSubgroup K :=
      ⟨(z : Kˣ), valuation_one_pow
        (valuation K) hn ((mem_rootsOfUnity' n (z : Kˣ)).mp z.property)⟩
    exact ⟨u, by
      apply Subtype.ext
      exact z.property⟩
  invFun z :=
    ⟨(z.1 : localUnitSubgroup K).1, by
      change ((z.1 : localUnitSubgroup K).1 : Kˣ) ^ n = 1
      exact congrArg Subtype.val z.property⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Intersecting the field's `n`th powers with the local units gives exactly
the `n`th powers of local units.  This is the kernel comparison in the
decomposition `K× ≃ U × ℤ`. -/
theorem field_comap_units
    (K : Type u) [Field K] [ValuativeRel K]
    (n : ℕ) (hn : 0 < n) :
    (powMonoidHom n : Kˣ →* Kˣ).range.comap
        (localUnitSubgroup K).subtype =
      (powMonoidHom n : localUnitSubgroup K →*
        localUnitSubgroup K).range := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    have hyUnit : y ∈ localUnitSubgroup K := by
      have hy' : (y : K) ^ n = ((x : Kˣ) : K) := by
        exact congrArg Units.val hy
      apply (local_subgroup K y).2
      apply (pow_eq_one_iff_left hn.ne').mp
      rw [← map_pow, hy']
      exact (local_subgroup K x).1 x.property
    refine ⟨⟨y, hyUnit⟩, ?_⟩
    apply Subtype.ext
    exact hy
  · rintro ⟨y, hy⟩
    exact ⟨(y : localUnitSubgroup K).1,
      congrArg Subtype.val hy⟩

private theorem local_unit_zero
    (F : Type u) [NontriviallyNormedField F] [IsUltrametricDist F]
    [ValuativeRel F] [IsNonarchimedeanLocalField F]
    [Valuation.Compatible (NormedField.valuation (K := F))]
    (x : Fˣ) :
    x ∈ localUnitSubgroup F ↔
      localUnitOrder F (Additive.ofMul x) = 0 := by
  constructor
  · intro hx
    have hxval : valuation F (x : F) = 1 :=
      (local_subgroup F x).1 hx
    apply le_antisymm
    · have h := (local_order_valuation F x 1).2
          (by simp [hxval])
      simpa using h
    · have h := (local_order_valuation F 1 x).2
          (by simp [hxval])
      simpa using h
  · intro hx
    apply (local_subgroup F x).2
    apply le_antisymm
    · have hle : localUnitOrder F (Additive.ofMul (1 : Fˣ)) ≤
          localUnitOrder F (Additive.ofMul x) := by simp [hx]
      simpa using
        (local_order_valuation F (1 : Fˣ) x).1 hle
    · have hle : localUnitOrder F (Additive.ofMul x) ≤
          localUnitOrder F (Additive.ofMul (1 : Fˣ)) := by simp [hx]
      simpa using
        (local_order_valuation F x (1 : Fˣ)).1 hle

/-- Modulo normalized order, the kernel consists of a field `n`th power
times a local unit. -/
theorem order_sup_units
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (n : ℕ) [NeZero n] :
    (localOrderMod K n).ker =
      (powMonoidHom n : Kˣ →* Kˣ).range ⊔ localUnitSubgroup K := by
  apply le_antisymm
  · intro x hx
    have hxmod :
        (localUnitOrder K (Additive.ofMul x) : ZMod n) = 0 :=
      congrArg Multiplicative.toAdd hx
    obtain ⟨t, ht⟩ :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hxmod
    obtain ⟨z, hz⟩ := local_order_surjective K t
    let y : Kˣ := z.toMul
    let e : Kˣ := x / y ^ n
    have heOrder : localUnitOrder K (Additive.ofMul e) = 0 := by
      change localUnitOrder K
        (Additive.ofMul x - n • Additive.ofMul y) = 0
      rw [map_sub, map_nsmul, show localUnitOrder K
        (Additive.ofMul y) = t from hz]
      change localUnitOrder K (Additive.ofMul x) - (n : ℤ) * t = 0
      rw [← ht]
      simp
    have heUnit : e ∈ localUnitSubgroup K :=
      (local_unit_zero K e).2 heOrder
    apply Subgroup.mem_sup.mpr
    refine ⟨y ^ n, ⟨y, rfl⟩, e, heUnit, ?_⟩
    simp [e]
  · apply sup_le
    · rintro _ ⟨y, rfl⟩
      change Multiplicative.ofAdd
        (localUnitOrder K (Additive.ofMul (y ^ n)) : ZMod n) = 1
      apply Multiplicative.toAdd.injective
      simp
    · intro y hy
      change Multiplicative.ofAdd
        (localUnitOrder K (Additive.ofMul y) : ZMod n) = 1
      apply Multiplicative.toAdd.injective
      rw [show localUnitOrder K (Additive.ofMul y) = 0 from
        (local_unit_zero K y).1 hy]
      simp

/-- The quotient by field powers and local units is the cyclic order
quotient of cardinality `n`. -/
theorem sup_units_index
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (n : ℕ) [NeZero n] :
    ((powMonoidHom n : Kˣ →* Kˣ).range ⊔
      localUnitSubgroup K).index = n := by
  rw [← order_sup_units K n,
    Subgroup.index_ker]
  rw [MonoidHom.range_eq_top.mpr (local_mod_surjective K n)]
  simp

/-- The valuation decomposition gives the field power index as `n` times
the local-unit power index. -/
theorem valuation_index
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (n : ℕ) (hn : 0 < n) :
    (powMonoidHom n : Kˣ →* Kˣ).range.index =
      n * (powMonoidHom n : localUnitSubgroup K →*
        localUnitSubgroup K).range.index := by
  letI : NeZero n := ⟨hn.ne'⟩
  let B := (powMonoidHom n : Kˣ →* Kˣ).range
  let U := localUnitSubgroup K
  have hinter : (B ⊓ U).subgroupOf U =
      (powMonoidHom n : localUnitSubgroup K →*
        localUnitSubgroup K).range := by
    rw [← field_comap_units K n hn]
    ext x
    simp [B, U]
  have hindex := subgroup_relIndex (⊤ : Subgroup Kˣ) B U le_top
  rw [top_sup_eq, top_inf_eq] at hindex
  rw [Subgroup.relIndex_top_right] at hindex
  rw [show (B ⊓ U).relIndex U =
      (powMonoidHom n : localUnitSubgroup K →*
        localUnitSubgroup K).range.index by
        change ((B ⊓ U).subgroupOf U).index = _
        rw [hinter]] at hindex
  rw [show (B ⊔ U).index = n by
    exact sup_units_index K n] at hindex
  simpa [B] using hindex.symm

/-- The precise exponential-map input in the source: `h_n(U)=|n|⁻¹`,
written as `index(nU) * |n| = |U_n|`.  It does not mention roots of unity or
the desired field-level formula. -/
def ExponentialHerbrandBridge : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [CharZero K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (n : ℕ), 0 < n →
      (((powMonoidHom n : localUnitSubgroup K →*
          localUnitSubgroup K).range.index : ℕ) : ℝ) *
          normalizedAbsoluteValue K n =
        Nat.card ((powMonoidHom n : localUnitSubgroup K →*
          localUnitSubgroup K).ker)

/-- The local exponential and the DVR quotient computation prove the
Herbrand-quotient input without any additional hypothesis. -/
theorem exponentialHerbrandBridge :
    ExponentialHerbrandBridge.{u} := by
  intro K _ _ _ _ _ _ n hn
  let A := Valuation.integer (valuation K)
  let Q := A ⧸ Ideal.span {(n : A)}
  let U := localUnitSubgroup K
  let P := (powMonoidHom n : U →* U).range
  let T := (powMonoidHom n : U →* U).ker
  letI : NeZero n := ⟨hn.ne'⟩
  letI : Finite Q := integerQuotientFinite K n hn
  letI : Finite T :=
    Finite.of_equiv (rootsOfUnity n K)
      (rootsUnityKernel
        K n hn.ne').toEquiv
  have hqCard : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have htorsCard : Nat.card T ≠ 0 := Nat.card_pos.ne'
  have hratio := local_card_ratio K n hn
  change (Nat.card (U ⧸ P) : ℚ) / Nat.card T = Nat.card Q at hratio
  have hquotient : (Nat.card (U ⧸ P) : ℚ) =
      (Nat.card Q : ℚ) * Nat.card T :=
    (div_eq_iff (Nat.cast_ne_zero.mpr htorsCard)).mp hratio
  have hreal : (Nat.card (U ⧸ P) : ℝ) =
      (Nat.card Q : ℝ) * Nat.card T := by
    exact_mod_cast hquotient
  change (Nat.card (U ⧸ P) : ℝ) *
      normalizedAbsoluteValue K n = Nat.card T
  rw [hreal]
  change ((Nat.card Q : ℝ) * Nat.card T) *
      (Nat.card Q : ℝ)⁻¹ = Nat.card T
  rw [mul_assoc, mul_comm (Nat.card T : ℝ) (Nat.card Q : ℝ)⁻¹,
    ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hqCard), one_mul]

/-- The valuation-sequence input `K× ≃ U × ℤ`, in precisely the
index form used by Proposition 6.8. -/
def ValuationIndexBridge : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [CharZero K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (n : ℕ), 0 < n →
      (powMonoidHom n : Kˣ →* Kˣ).range.index =
        n * (powMonoidHom n : localUnitSubgroup K →*
          localUnitSubgroup K).range.index

/-- The formalized normalized valuation sequence proves the valuation-index
input without an additional hypothesis. -/
theorem valuationIndexBridge :
    ValuationIndexBridge.{u} := by
  intro K _ _ _ _ _ _ n hn
  exact valuation_index K n hn

/-- The nonarchimedean unit formula of Proposition 6.8, deduced from the
exponential Herbrand-quotient calculation. -/
theorem nonarchimedean_unit_formula
    (hexp : ExponentialHerbrandBridge.{u})
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [CharZero K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (n : ℕ) (hn : 0 < n) :
    (((powMonoidHom n : localUnitSubgroup K →*
        localUnitSubgroup K).range.index : ℕ) : ℝ) *
        normalizedAbsoluteValue K n =
      Nat.card (rootsOfUnity n K) := by
  rw [hexp K n hn]
  exact_mod_cast Nat.card_congr
    (rootsUnityKernel K n hn.ne').toEquiv.symm

/-- The nonarchimedean field formula of Proposition 6.8. -/
theorem nonarchimedean_field_formula
    (hexp : ExponentialHerbrandBridge.{u})
    (hvaluation : ValuationIndexBridge.{u})
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K] [CharZero K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    (n : ℕ) (hn : 0 < n) :
    (((powMonoidHom n : Kˣ →* Kˣ).range.index : ℕ) : ℝ) *
        normalizedAbsoluteValue K n =
      (n : ℝ) * Nat.card (rootsOfUnity n K) := by
  rw [hvaluation K n hn, Nat.cast_mul, mul_assoc,
    nonarchimedean_unit_formula hexp K n hn]

/-- For odd `n`, the only real `n`th root of unity is `1`. -/
theorem odd_roots_unity
    {n : ℕ} (hn : Odd n) : Nat.card (rootsOfUnity n ℝ) = 1 := by
  have hsubsingleton : Subsingleton (rootsOfUnity n ℝ) :=
    ⟨fun x y ↦ by
      apply Subtype.ext
      apply Units.ext
      apply hn.pow_injective
      change (((x : rootsOfUnity n ℝ) : ℝˣ) : ℝ) ^ n =
        (((y : rootsOfUnity n ℝ) : ℝˣ) : ℝ) ^ n
      rw [(mem_rootsOfUnity' n (x : ℝˣ)).mp x.property,
        (mem_rootsOfUnity' n (y : ℝˣ)).mp y.property]⟩
  exact Nat.card_unique

/-- For positive even `n`, the real `n`th roots of unity are `±1`. -/
theorem even_roots_unity
    {n : ℕ} (hn : Even n) (hn0 : n ≠ 0) :
    Nat.card (rootsOfUnity n ℝ) = 2 := by
  let e : rootsOfUnity n ℝ ≃ rootsOfUnity 2 ℝ :=
    { toFun := fun z ↦ ⟨z.1, by
        apply Units.ext
        have hz := (mem_rootsOfUnity' n (z : ℝˣ)).mp z.property
        rcases (pow_eq_one_iff_of_ne_zero hn0).mp hz with hz | ⟨hz, _⟩
        · simp [hz]
        · simp [hz]
      ⟩
      invFun := fun z ↦ ⟨z.1, by
        apply Units.ext
        have hz := (mem_rootsOfUnity' 2 (z : ℝˣ)).mp z.property
        rcases (pow_eq_one_iff_of_ne_zero (by omega : 2 ≠ 0)).mp hz with
          hz | ⟨hz, _⟩
        · simp [hz]
        · simpa [hz] using hn.neg_one_pow
      ⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Nat.card_congr e]
  have hprimitive : IsPrimitiveRoot (-1 : ℝ) 2 :=
    IsPrimitiveRoot.neg_one 0 (by norm_num)
  rw [Nat.card_eq_fintype_card]
  exact hprimitive.card_rootsOfUnity

/-- The complex case of Proposition 6.8, with the normalized squared
absolute value at a complex place. -/
theorem complex_formula (n : ℕ) (hn : 0 < n) :
    (((powMonoidHom n : ℂˣ →* ℂˣ).range.index : ℕ) : ℝ) *
        complexAbsoluteValue (n : ℂ) =
      (n : ℝ) * Nat.card (rootsOfUnity n ℂ) := by
  letI : NeZero n := ⟨hn.ne'⟩
  rw [complex_power_index n hn,
    complex_roots_unity n]
  simp [complexAbsoluteValue]
  ring

/-- The real case of Proposition 6.8. -/
theorem real_formula (n : ℕ) (hn : 0 < n) :
    (((powMonoidHom n : ℝˣ →* ℝˣ).range.index : ℕ) : ℝ) *
        realAbsoluteValue (n : ℝ) =
      (n : ℝ) * Nat.card (rootsOfUnity n ℝ) := by
  rcases Nat.even_or_odd n with heven | hodd
  · rw [real_even_index heven hn.ne',
      even_roots_unity heven hn.ne']
    simp [realAbsoluteValue]
    ring
  · rw [real_odd_index hodd,
      odd_roots_unity hodd]
    simp [realAbsoluteValue]

/-- Proposition 6.8 from the two exact nonarchimedean inputs in its printed
proof. -/
theorem complex_statement_bridges
    (hexp : ExponentialHerbrandBridge.{u})
    (hvaluation : ValuationIndexBridge.{u}) :
    ((∀ n : ℕ, 0 < n →
          (((powMonoidHom n : ℂˣ →* ℂˣ).range.index : ℕ) : ℝ) *
              complexAbsoluteValue (n : ℂ) =
            (n : ℝ) * Nat.card (rootsOfUnity n ℂ)) ∧
        (∀ n : ℕ, 0 < n →
          (((powMonoidHom n : ℝˣ →* ℝˣ).range.index : ℕ) : ℝ) *
              realAbsoluteValue (n : ℝ) =
            (n : ℝ) * Nat.card (rootsOfUnity n ℝ)) ∧
        ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
          [ValuativeRel K] [IsNonarchimedeanLocalField K] [CharZero K]
          [Valuation.Compatible (NormedField.valuation (K := K))]
          (n : ℕ), 0 < n →
            ((((powMonoidHom n : Kˣ →* Kˣ).range.index : ℕ) : ℝ) *
                normalizedAbsoluteValue K n =
              (n : ℝ) * Nat.card (rootsOfUnity n K)) ∧
            ((((powMonoidHom n : localUnitSubgroup K →*
                localUnitSubgroup K).range.index : ℕ) : ℝ) *
                normalizedAbsoluteValue K n =
              Nat.card (rootsOfUnity n K))) := by
  refine ⟨complex_formula, real_formula, ?_⟩
  intro K _ _ _ _ _ _ n hn
  exact ⟨nonarchimedean_field_formula
      hexp hvaluation K n hn,
    nonarchimedean_unit_formula hexp K n hn⟩

/-- Proposition 6.8 with only the exponential/Herbrand-quotient computation
left as the analytic input from Lemma III.2.4. -/
theorem complex_absolute_exponential
    (hexp : ExponentialHerbrandBridge.{u}) :
    ((∀ n : ℕ, 0 < n →
          (((powMonoidHom n : ℂˣ →* ℂˣ).range.index : ℕ) : ℝ) *
              complexAbsoluteValue (n : ℂ) =
            (n : ℝ) * Nat.card (rootsOfUnity n ℂ)) ∧
        (∀ n : ℕ, 0 < n →
          (((powMonoidHom n : ℝˣ →* ℝˣ).range.index : ℕ) : ℝ) *
              realAbsoluteValue (n : ℝ) =
            (n : ℝ) * Nat.card (rootsOfUnity n ℝ)) ∧
        ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
          [ValuativeRel K] [IsNonarchimedeanLocalField K] [CharZero K]
          [Valuation.Compatible (NormedField.valuation (K := K))]
          (n : ℕ), 0 < n →
            ((((powMonoidHom n : Kˣ →* Kˣ).range.index : ℕ) : ℝ) *
                normalizedAbsoluteValue K n =
              (n : ℝ) * Nat.card (rootsOfUnity n K)) ∧
            ((((powMonoidHom n : localUnitSubgroup K →*
                localUnitSubgroup K).range.index : ℕ) : ℝ) *
                normalizedAbsoluteValue K n =
              Nat.card (rootsOfUnity n K))) :=
  complex_statement_bridges
    hexp valuationIndexBridge

/-- **Proposition VII.6.8.** -/
theorem complexAbsoluteStatement : ((∀ n : ℕ, 0 < n →
      (((powMonoidHom n : ℂˣ →* ℂˣ).range.index : ℕ) : ℝ) *
          complexAbsoluteValue (n : ℂ) =
        (n : ℝ) * Nat.card (rootsOfUnity n ℂ)) ∧
    (∀ n : ℕ, 0 < n →
      (((powMonoidHom n : ℝˣ →* ℝˣ).range.index : ℕ) : ℝ) *
          realAbsoluteValue (n : ℝ) =
        (n : ℝ) * Nat.card (rootsOfUnity n ℝ)) ∧
    ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
      [ValuativeRel K] [IsNonarchimedeanLocalField K] [CharZero K]
      [Valuation.Compatible (NormedField.valuation (K := K))]
      (n : ℕ), 0 < n →
        ((((powMonoidHom n : Kˣ →* Kˣ).range.index : ℕ) : ℝ) *
            normalizedAbsoluteValue K n =
          (n : ℝ) * Nat.card (rootsOfUnity n K)) ∧
        ((((powMonoidHom n : localUnitSubgroup K →*
            localUnitSubgroup K).range.index : ℕ) : ℝ) *
            normalizedAbsoluteValue K n =
          Nat.card (rootsOfUnity n K))) :=
  complex_absolute_exponential
    exponentialHerbrandBridge

end

end Submission.CField.KNIndex
