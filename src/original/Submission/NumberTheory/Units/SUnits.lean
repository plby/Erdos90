import Submission.NumberTheory.Units.UnitTheorem
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Milne, Algebraic Number Theory, Theorem 5.11

The finite generation and rank formula for the group of `S`-units of a number field.
-/

namespace Submission.NumberTheory.Milne

open IsDedekindDomain
open scoped NumberField nonZeroDivisors

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

abbrev FinitePrime (K : Type*) [Field K] [NumberField K] :=
  HeightOneSpectrum (NumberField.RingOfIntegers K)

/-- The group of `S`-units, using Mathlib's valuation-theoretic definition. -/
abbrev SUnits (S : Set (FinitePrime K)) := S.unit K

/-- The ring of `S`-integers, using Mathlib's valuation-theoretic definition. -/
abbrev SIntegers (S : Set (FinitePrime K)) := S.integer K

/-- The torsion subgroup of the `S`-units is the group of roots of unity in `K`.

Both sides are expressed as subgroups of `Kˣ`: the right-hand side is the pullback of the
torsion subgroup of `Kˣ` along the inclusion of the `S`-units. -/
theorem s_roots_unity (S : Set (FinitePrime K)) :
    CommGroup.torsion (SUnits K S) =
      (CommGroup.torsion Kˣ).comap (Set.unit S K).subtype := by
  ext x
  exact ((Set.unit S K).subtype_injective.isOfFinOrder_iff).symm

/-- `S`-units are precisely the units of the ring of `S`-integers. -/
def sUnitsIntegers (S : Set (FinitePrime K)) :
    SUnits K S ≃* (SIntegers K S)ˣ :=
  Set.unitEquivUnitsInteger S K

/-- For `S = ∅`, the valuation-theoretic unit group is the usual unit group. -/
def emptySIntegers :
    SUnits K (∅ : Set (FinitePrime K)) ≃* (NumberField.RingOfIntegers K)ˣ := by
  let e : SIntegers K (∅ : Set (FinitePrime K)) ≃+*
      NumberField.RingOfIntegers K := by
    rw [SIntegers, IsDedekindDomain.integer_empty]
    exact (Algebra.botEquivOfInjective
      (IsFractionRing.injective (NumberField.RingOfIntegers K) K)).toRingEquiv
  exact (sUnitsIntegers K ∅).trans (Units.mapEquiv e.toMulEquiv)

/-- The vector of additive valuations at the primes in `S`. -/
def sUnitValuation (S : Set (FinitePrime K)) :
    SUnits K S →* (S → Multiplicative ℤ) where
  toFun x v := (v : FinitePrime K).valuationOfNeZero (x : Kˣ)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp]
theorem s_unit_valuation (S : Set (FinitePrime K)) (x : SUnits K S) (v : S) :
    sUnitValuation K S x v = (v : FinitePrime K).valuationOfNeZero (x : Kˣ) := rfl

/-- The ordinary units, embedded in the `S`-units. -/
def ordinaryUnitsS (S : Set (FinitePrime K)) : Subgroup (SUnits K S) :=
  (Set.unit (∅ : Set (FinitePrime K)) K).subgroupOf (Set.unit S K)

/-- The kernel of the valuations at `S` is the group of ordinary units. -/
theorem s_valuation_ker (S : Set (FinitePrime K)) :
    (sUnitValuation K S).ker = ordinaryUnitsS K S := by
  ext x
  constructor
  · intro hx
    rw [ordinaryUnitsS, Subgroup.mem_subgroupOf]
    change ∀ v (_ : v ∉ (∅ : Set (FinitePrime K))), v.valuation K (x : Kˣ) = 1
    intro v _
    by_cases hv : v ∈ S
    · have h := congr_fun hx ⟨v, hv⟩
      rw [s_unit_valuation] at h
      simpa only [HeightOneSpectrum.valuationOfNeZero_eq, WithZero.coe_one] using
        congrArg (fun z : Multiplicative ℤ => (z : WithZero (Multiplicative ℤ))) h
    · exact x.property v hv
  · intro hx
    rw [ordinaryUnitsS, Subgroup.mem_subgroupOf] at hx
    ext v
    change (v : FinitePrime K).valuationOfNeZero (x : Kˣ) = 1
    apply WithZero.coe_injective
    rw [HeightOneSpectrum.valuationOfNeZero_eq]
    exact hx v (Set.notMem_empty v)

/-- The valuation vector as a homomorphism of additive groups. -/
def sValuationHom (S : Set (FinitePrime K)) :
    Additive (SUnits K S) →+ (S → ℤ) where
  toFun x v := Multiplicative.toAdd <|
    (v : FinitePrime K).valuationOfNeZero ((Additive.toMul x : SUnits K S) : Kˣ)
  map_zero' := by
    ext v
    simp
  map_add' x y := by
    ext v
    simp

/-- The valuation vector as a `ℤ`-linear map. -/
def sUnitLinear (S : Set (FinitePrime K)) :
    Additive (SUnits K S) →ₗ[ℤ] (S → ℤ) :=
  (sValuationHom K S).toIntLinearMap

@[simp]
theorem s_valuation_linear (S : Set (FinitePrime K))
    (x : Additive (SUnits K S)) (v : S) :
    sUnitLinear K S x v = Multiplicative.toAdd
      ((v : FinitePrime K).valuationOfNeZero
        ((Additive.toMul x : SUnits K S) : Kˣ)) := rfl

open Classical in
private theorem valuation_ne_power
    (v w : FinitePrime K) (n : ℕ) (a : NumberField.RingOfIntegers K) (ha : a ≠ 0)
    (hspan : Ideal.span {a} = v.asIdeal ^ n) :
    w.valuationOfNeZero
        (Units.mk0 (algebraMap (NumberField.RingOfIntegers K) K a)
          ((map_ne_zero_iff (algebraMap (NumberField.RingOfIntegers K) K)
            (IsFractionRing.injective (NumberField.RingOfIntegers K) K)).2 ha)) =
      Multiplicative.ofAdd (-(if v = w then (n : ℤ) else 0)) := by
  apply WithZero.coe_injective
  rw [HeightOneSpectrum.valuationOfNeZero_eq]
  change w.valuation K (algebraMap (NumberField.RingOfIntegers K) K a) =
    WithZero.exp (-(if v = w then (n : ℤ) else 0))
  rw [w.valuation_of_algebraMap, w.intValuation_if_neg ha]
  congr 2
  rw [hspan]
  have hc := FractionalIdeal.count_coe K w (pow_ne_zero n v.ne_bot)
  rw [FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow,
    FractionalIdeal.count_maximal] at hc
  simpa [mul_ite, mul_one, mul_zero, eq_comm] using hc

/-- A class-number power of every finite prime is principal. -/
theorem generator_class_number (v : FinitePrime K) :
    ∃ a : NumberField.RingOfIntegers K, a ≠ 0 ∧
      Ideal.span {a} = v.asIdeal ^ NumberField.classNumber K := by
  let I : (Ideal (NumberField.RingOfIntegers K))⁰ :=
    ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  have hclass : (ClassGroup.mk0 I) ^ NumberField.classNumber K = 1 := by
    exact pow_card_eq_one
  have hpow0 : v.asIdeal ^ NumberField.classNumber K ≠
      (0 : Ideal (NumberField.RingOfIntegers K)) := pow_ne_zero _ v.ne_bot
  have hprincipal : Submodule.IsPrincipal
      (v.asIdeal ^ NumberField.classNumber K) := by
    apply (ClassGroup.mk0_eq_one_iff
      (mem_nonZeroDivisors_iff_ne_zero.mpr hpow0)).mp
    change ClassGroup.mk0 (I ^ NumberField.classNumber K) = 1
    simpa only [map_pow] using hclass
  letI : Submodule.IsPrincipal (v.asIdeal ^ NumberField.classNumber K) := hprincipal
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal
    (v.asIdeal ^ NumberField.classNumber K)
  refine ⟨a, ?_, ha.symm⟩
  intro ha0
  subst a
  rw [Submodule.span_zero_singleton] at ha
  exact hpow0 ha

/-- An `S`-unit whose principal ideal is the class-number power of a chosen prime in `S`. -/
noncomputable def numberSUnit (S : Set (FinitePrime K)) (v : S) : SUnits K S := by
  let a := Classical.choose (generator_class_number K (v : FinitePrime K))
  have ha : a ≠ 0 :=
    (Classical.choose_spec (generator_class_number K (v : FinitePrime K))).1
  have hspan : Ideal.span {a} =
      (v : FinitePrime K).asIdeal ^ NumberField.classNumber K :=
    (Classical.choose_spec (generator_class_number K (v : FinitePrime K))).2
  let u : Kˣ := Units.mk0 (algebraMap (NumberField.RingOfIntegers K) K a)
    ((map_ne_zero_iff (algebraMap (NumberField.RingOfIntegers K) K)
      (IsFractionRing.injective (NumberField.RingOfIntegers K) K)).2 ha)
  refine ⟨u, ?_⟩
  intro w hw
  have hvw : (v : FinitePrime K) ≠ w := fun h ↦ hw (h ▸ v.property)
  have hval := valuation_ne_power K (v : FinitePrime K) w
    (NumberField.classNumber K) a ha hspan
  rw [if_neg hvw] at hval
  simpa only [u, neg_zero, map_zero,
    HeightOneSpectrum.valuationOfNeZero_eq, WithZero.coe_one] using
      congrArg (fun z : Multiplicative ℤ => (z : WithZero (Multiplicative ℤ))) hval

open Classical in
@[simp]
theorem s_valuation_number
    (S : Set (FinitePrime K)) (v w : S) :
    sUnitLinear K S
        (Additive.ofMul (numberSUnit K S v)) w =
      if (v : FinitePrime K) = (w : FinitePrime K) then
        -(NumberField.classNumber K : ℤ) else 0 := by
  let a := Classical.choose (generator_class_number K (v : FinitePrime K))
  have ha : a ≠ 0 :=
    (Classical.choose_spec (generator_class_number K (v : FinitePrime K))).1
  have hspan : Ideal.span {a} =
      (v : FinitePrime K).asIdeal ^ NumberField.classNumber K :=
    (Classical.choose_spec (generator_class_number K (v : FinitePrime K))).2
  have hmap : algebraMap (NumberField.RingOfIntegers K) K a ≠ 0 :=
    (map_ne_zero_iff (algebraMap (NumberField.RingOfIntegers K) K)
      (IsFractionRing.injective (NumberField.RingOfIntegers K) K)).2 ha
  change Multiplicative.toAdd
      ((w : FinitePrime K).valuationOfNeZero
        (Units.mk0 (algebraMap (NumberField.RingOfIntegers K) K a) hmap)) = _
  rw [valuation_ne_power K (v : FinitePrime K) (w : FinitePrime K)
    (NumberField.classNumber K) a ha hspan]
  split_ifs <;> rfl

/-- The image of the valuation map contains the class number times every integral vector. -/
theorem s_valuation_range
    (S : Set (FinitePrime K)) [Finite S] (y : S → ℤ) :
    (NumberField.classNumber K : ℤ) • y ∈ (sUnitLinear K S).range := by
  classical
  letI := Fintype.ofFinite S
  rw [LinearMap.mem_range]
  refine ⟨∑ v : S, (-y v) • Additive.ofMul (numberSUnit K S v), ?_⟩
  ext w
  simp only [map_sum, LinearMap.map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, s_valuation_number]
  rw [Finset.sum_eq_single w]
  · simp [mul_comm]
  · intro v _ hvw
    have hcoe : (v : FinitePrime K) ≠ (w : FinitePrime K) := fun h ↦ hvw (Subtype.ext h)
    simp [hcoe]
  · simp

/-- The valuation image has full rank `#S`. -/
theorem s_valuation_finrank (S : Set (FinitePrime K)) (hS : S.Finite) :
    Module.finrank ℤ (sUnitLinear K S).range = S.ncard := by
  letI : Fintype S := hS.fintype
  letI : Module.Finite ℤ (S → ℤ) := by infer_instance
  let Q := (S → ℤ) ⧸ (sUnitLinear K S).range
  letI : Module.Finite ℤ Q := Module.Finite.quotient ℤ _
  have hQ : Module.finrank ℤ Q = 0 := by
    apply Module.finrank_eq_zero_iff.mpr
    intro x
    refine Quotient.inductionOn x (fun y ↦ ?_)
    refine ⟨(NumberField.classNumber K : ℤ), ?_, ?_⟩
    · exact Int.ofNat_ne_zero.mpr (NumberField.classNumber_ne_zero K)
    · change Submodule.Quotient.mk
          ((NumberField.classNumber K : ℤ) • y) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact s_valuation_range K S y
  have hrank := Submodule.finrank_quotient_add_finrank
    (sUnitLinear K S).range
  change Module.finrank ℤ Q + Module.finrank ℤ (sUnitLinear K S).range =
    Module.finrank ℤ (S → ℤ) at hrank
  rw [hQ, zero_add, Module.finrank_pi, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] at hrank
  exact hrank

/-- The linear kernel is the additive form of the multiplicative valuation kernel. -/
def sValuationLinear (S : Set (FinitePrime K)) :
    (sUnitLinear K S).ker ≃ₗ[ℤ]
      Additive (sUnitValuation K S).ker :=
  AddEquiv.toIntLinearEquiv
    { toFun := fun x ↦ Additive.ofMul ⟨Additive.toMul x.1, by
          rw [MonoidHom.mem_ker]
          ext v
          apply Multiplicative.toAdd.injective
          simpa only [map_one, s_unit_valuation,
            s_valuation_linear] using congrFun x.2 v⟩
      invFun := fun x ↦ ⟨Additive.ofMul x.toMul.1, by
          ext v
          have h := congrFun x.toMul.2 v
          simpa only [s_valuation_linear, s_unit_valuation, map_one] using
            congrArg Multiplicative.toAdd h⟩
      left_inv := fun x ↦ by ext; rfl
      right_inv := fun x ↦ by ext; rfl
      map_add' := fun x y ↦ by ext; rfl }

/-- The multiplicative valuation kernel is naturally the usual unit group. -/
def sValuationIntegers (S : Set (FinitePrime K)) :
    (sUnitValuation K S).ker ≃* (NumberField.RingOfIntegers K)ˣ := by
  have hle : Set.unit (∅ : Set (FinitePrime K)) K ≤ Set.unit S K := by
    intro x hx v _
    exact hx v (Set.notMem_empty v)
  exact (MulEquiv.subgroupCongr (s_valuation_ker K S)).trans
    ((Subgroup.subgroupOfEquivOfLe hle).trans (emptySIntegers K))

/-- The valuation kernel has the same `ℤ`-rank as the usual unit group. -/
def sValuationUnits (S : Set (FinitePrime K)) :
    (sUnitLinear K S).ker ≃ₗ[ℤ]
      Additive (NumberField.RingOfIntegers K)ˣ :=
  (sValuationLinear K S).trans <|
    AddEquiv.toIntLinearEquiv (sValuationIntegers K S).toAdditive

/-- The quotient map from ordinary units to units modulo torsion, as a `ℤ`-linear map. -/
def modTorsionLinear :
    Additive (NumberField.RingOfIntegers K)ˣ →ₗ[ℤ]
      Additive ((NumberField.RingOfIntegers K)ˣ ⧸ NumberField.Units.torsion K) :=
  (MonoidHom.toAdditive (QuotientGroup.mk' (NumberField.Units.torsion K))).toIntLinearMap

/-- The kernel of the quotient by torsion is the torsion subgroup itself. -/
def unitModTorsion :
    (modTorsionLinear K).ker ≃ₗ[ℤ]
      Additive (NumberField.Units.torsion K) :=
  AddEquiv.toIntLinearEquiv
    { toFun := fun x ↦ Additive.ofMul ⟨Additive.toMul x.1, by
          have h : Additive.ofMul
              (QuotientGroup.mk' (NumberField.Units.torsion K) (Additive.toMul x.1)) =
              Additive.ofMul 1 := by
            simpa [modTorsionLinear] using x.2
          have hxker : Additive.toMul x.1 ∈
              (QuotientGroup.mk' (NumberField.Units.torsion K)).ker := by
            exact Additive.ofMul.injective h
          exact (SetLike.ext_iff.mp
            (QuotientGroup.ker_mk' (NumberField.Units.torsion K)) _).mp hxker⟩
      invFun := fun x ↦ ⟨Additive.ofMul x.toMul.1, by
          have hxker : x.toMul.1 ∈
              (QuotientGroup.mk' (NumberField.Units.torsion K)).ker :=
            (SetLike.ext_iff.mp
              (QuotientGroup.ker_mk' (NumberField.Units.torsion K)) _).mpr x.toMul.2
          have h : QuotientGroup.mk' (NumberField.Units.torsion K) x.toMul.1 = 1 := hxker
          apply Additive.toMul.injective
          exact h⟩
      left_inv := fun x ↦ by ext; rfl
      right_inv := fun x ↦ by ext; rfl
      map_add' := fun x y ↦ by ext; rfl }

/-- The `ℤ`-finrank of the ordinary unit group is Dirichlet's unit rank. -/
theorem ring_integers_finrank :
    Module.finrank ℤ (Additive (NumberField.RingOfIntegers K)ˣ) =
      NumberField.Units.rank K := by
  let f := modTorsionLinear K
  letI : Finite f.ker := Finite.of_equiv (Additive (NumberField.Units.torsion K))
    (unitModTorsion K).symm.toEquiv
  letI : Module.Finite ℤ f.ker := by infer_instance
  have hker : Module.finrank ℤ f.ker = 0 := by
    apply Module.finrank_eq_zero_iff.mpr
    intro x
    refine ⟨(Nat.card f.ker : ℤ), ?_, ?_⟩
    · exact Int.ofNat_ne_zero.mpr (Nat.card_pos.ne')
    · simpa only [Nat.cast_smul_eq_nsmul] using
        (card_nsmul_eq_zero' (G := f.ker) (x := x))
  have hsurj : Function.Surjective f := by
    exact QuotientGroup.mk'_surjective (NumberField.Units.torsion K)
  have hrange : f.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrangeRank : Module.finrank ℤ f.range =
      Module.finrank ℤ (Additive
        ((NumberField.RingOfIntegers K)ˣ ⧸ NumberField.Units.torsion K)) :=
    (LinearEquiv.ofTop f.range hrange).finrank_eq
  have hrank := Submodule.finrank_quotient_add_finrank f.ker
  rw [LinearEquiv.finrank_eq f.quotKerEquivRange, hrangeRank,
    hker, add_zero, NumberField.Units.rank_modTorsion] at hrank
  exact hrank.symm

/-- The additive group underlying the `S`-units is a finite `ℤ`-module. -/
theorem s_units_module (S : Set (FinitePrime K)) (hS : S.Finite) :
    Module.Finite ℤ (Additive (SUnits K S)) := by
  letI : Fintype S := hS.fintype
  let f := sUnitLinear K S
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker f ?_ ?_
  · rw [Submodule.map_top, ← Module.Finite.iff_fg]
    infer_instance
  · rw [top_inf_eq, ← Module.Finite.iff_fg]
    exact @Module.Finite.equiv ℤ
      (Additive (NumberField.RingOfIntegers K)ˣ) f.ker _ _ _ _ _
      (inferInstance : Module.Finite ℤ (Additive (NumberField.RingOfIntegers K)ˣ))
      (sValuationUnits K S).symm

/-- **Milne, Theorem 5.11 (finite generation).** The group of `S`-units is finitely generated. -/
theorem s_finitely_generated (S : Set (FinitePrime K)) (hS : S.Finite) :
    Monoid.FG (SUnits K S) := by
  letI : Module.Finite ℤ (Additive (SUnits K S)) := s_units_module K S hS
  rw [Monoid.fg_iff_add_fg, ← AddGroup.fg_iff_addMonoid_fg,
    ← Module.Finite.iff_addGroup_fg]
  infer_instance

/-- The `ℤ`-rank of the `S`-unit group is the ordinary unit rank plus `#S`. -/
theorem s_rank_ncard (S : Set (FinitePrime K)) (hS : S.Finite) :
    Module.finrank ℤ (Additive (SUnits K S)) =
      NumberField.Units.rank K + S.ncard := by
  letI : Fintype S := hS.fintype
  letI : Module.Finite ℤ (Additive (SUnits K S)) := s_units_module K S hS
  let f := sUnitLinear K S
  have hrank := Submodule.finrank_quotient_add_finrank f.ker
  rw [LinearEquiv.finrank_eq f.quotKerEquivRange,
    s_valuation_finrank K S hS,
    (sValuationUnits K S).finrank_eq,
    ring_integers_finrank] at hrank
  simpa [add_comm] using hrank.symm

/-- **Milne, Theorem 5.11 (rank formula).** The rank is `r + s + #S - 1`. -/
theorem s_complex_ncard
    (S : Set (FinitePrime K)) (hS : S.Finite) :
    Module.finrank ℤ (Additive (SUnits K S)) =
      NumberField.InfinitePlace.nrRealPlaces K +
        NumberField.InfinitePlace.nrComplexPlaces K + S.ncard - 1 := by
  rw [s_rank_ncard K S hS,
    real_places_complex]
  have hplaces : 0 < NumberField.InfinitePlace.nrRealPlaces K +
      NumberField.InfinitePlace.nrComplexPlaces K := by
    rw [← NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  omega

end

end Submission.NumberTheory.Milne
