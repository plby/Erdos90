import Towers.NumberTheory.Locals.NewtonRootLifting
import Towers.NumberTheory.Completions.UnramifiedCompletion
import Towers.ClassField.NormCorrespondence.SubgroupOpenClosed
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Cubes among 3-adic units

This file computes the cubic quotient of the units of `ℤ_[3]`.  The main
Newton-lifting result says that a 3-adic unit congruent to `1` modulo `9` is a
cube.  Consequently every character of `ℤ_[3]ˣ` with exponent-three target
factors through reduction modulo `9`, and in fact through the quotient of
`(ZMod 9)ˣ` by its subgroup of cubes.
-/

namespace Towers.NumberTheory.Milne

open NumberField Polynomial ValuativeRel
open Towers.CField.LFTheory
open Towers.CField.Ideles

noncomputable section

local instance threePrimeFactUnitCubes : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance nineNeZeroUnitCubes : NeZero (3 ^ 2) := ⟨by norm_num⟩

/-- A 3-adic unit congruent to `1` modulo `9` is a cube. -/
theorem padic_cube_z
    (u : ℤ_[3]ˣ) (hu : PadicInt.toZModPow 2 (u : ℤ_[3]) = 1) :
    ∃ z : ℤ_[3]ˣ, z ^ 3 = u := by
  have hmem : (u : ℤ_[3]) - 1 ∈
      (Ideal.span {((3 : ℕ) : ℤ_[3]) ^ 2} : Ideal ℤ_[3]) := by
    rw [← PadicInt.ker_toZModPow 2, RingHom.mem_ker]
    rw [map_sub, hu, map_one, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hmem
  let F : ℤ_[3][X] := C (3 : ℤ_[3]) * X ^ 3 + C (3 : ℤ_[3]) * X ^ 2 + X - C a
  let a0 : ℤ_[3] := ((PadicInt.toZMod (p := 3) a).val : ℕ)
  have ha0 : PadicInt.toZMod a0 = PadicInt.toZMod a := by
    dsimp [a0]
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hFeval : F.aeval a0 = 3 * a0 ^ 3 + 3 * a0 ^ 2 + a0 - a := by
    simp [F]
  have hFsmall : ‖F.aeval a0‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]
    rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
      ← PadicInt.ker_toZMod, RingHom.mem_ker]
    rw [hFeval, map_sub, map_add, map_add, map_mul, map_mul, map_pow, map_pow,
      ha0]
    have hmap3 : PadicInt.toZMod (3 : ℤ_[3]) = 0 := by
      change PadicInt.toZMod (((3 : ℕ) : ℤ_[3])) = 0
      rw [map_natCast]
      decide
    rw [hmap3]
    simp
  have hFderiv : F.derivative.aeval a0 =
      9 * a0 ^ 2 + 6 * a0 + 1 := by
    simp [F]
    ring
  have hderivMod : PadicInt.toZMod (F.derivative.aeval a0) = 1 := by
    rw [hFderiv]
    simp only [map_add, map_mul, map_pow, map_one]
    have hmap9 : PadicInt.toZMod (9 : ℤ_[3]) = 0 := by
      change PadicInt.toZMod (((9 : ℕ) : ℤ_[3])) = 0
      rw [map_natCast]
      decide
    have hmap6 : PadicInt.toZMod (6 : ℤ_[3]) = 0 := by
      change PadicInt.toZMod (((6 : ℕ) : ℤ_[3])) = 0
      rw [map_natCast]
      decide
    rw [hmap9, hmap6]
    simp
  have hderivUnit : IsUnit (F.derivative.aeval a0) := by
    by_contra hn
    rw [PadicInt.not_isUnit_iff, PadicInt.norm_lt_one_iff_dvd,
      ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
      ← PadicInt.ker_toZMod, RingHom.mem_ker] at hn
    rw [hderivMod] at hn
    exact one_ne_zero hn
  have hderivNorm : ‖F.derivative.aeval a0‖ = 1 :=
    PadicInt.isUnit_iff.mp hderivUnit
  have hnewton : ‖F.aeval a0‖ < ‖F.derivative.aeval a0‖ ^ 2 := by
    rw [hderivNorm]
    simpa using hFsmall
  obtain ⟨y, hy, -, -, -⟩ := padic_newton_root F a0 hnewton
  have hyEq : 3 * y ^ 3 + 3 * y ^ 2 + y = a := by
    rw [show F.aeval y = 3 * y ^ 3 + 3 * y ^ 2 + y - a by simp [F]] at hy
    exact sub_eq_zero.mp hy
  let z0 : ℤ_[3] := 1 + 3 * y
  have hz0cube : z0 ^ 3 = (u : ℤ_[3]) := by
    dsimp [z0]
    calc
      (1 + 3 * y) ^ 3 = 1 + 3 ^ 2 * (3 * y ^ 3 + 3 * y ^ 2 + y) := by ring
      _ = 1 + 3 ^ 2 * a := by rw [hyEq]
      _ = (u : ℤ_[3]) := by
        simpa [add_comm] using (sub_eq_iff_eq_add.mp ha).symm
  have hthreeSmall : ‖(3 : ℤ_[3]) * y‖ < 1 := by
    have hnorm3 : ‖(3 : ℤ_[3])‖ = (3 : ℝ)⁻¹ := by
      change ‖(((3 : ℕ) : ℤ_[3]))‖ = (3 : ℝ)⁻¹
      exact PadicInt.norm_p
    rw [norm_mul, hnorm3]
    have hyNorm : ‖y‖ ≤ 1 := PadicInt.norm_le_one y
    nlinarith [norm_nonneg y]
  have hz0Norm : ‖z0‖ = 1 := by
    dsimp [z0]
    rw [PadicInt.norm_add_eq_max_of_ne]
    · rw [max_eq_left]
      · simp
      · simpa using hthreeSmall.le
    · simpa using ne_of_gt hthreeSmall
  have hz0unit : IsUnit z0 := PadicInt.isUnit_iff.mpr hz0Norm
  let z : ℤ_[3]ˣ := hz0unit.unit
  refine ⟨z, ?_⟩
  apply Units.ext
  simpa [z, IsUnit.unit_spec] using hz0cube

/-- Reduction of 3-adic units modulo `9`. -/
noncomputable def padicIntNine : ℤ_[3]ˣ →* (ZMod 9)ˣ :=
  Units.map (PadicInt.toZModPow (p := 3) 2)

private theorem padic_z_surjective :
    Function.Surjective (PadicInt.toZModPow (p := 3) 2) := by
  intro x
  refine ⟨((x.val : ℕ) : ℤ_[3]), ?_⟩
  calc
    PadicInt.toZModPow 2 ((x.val : ℕ) : ℤ_[3]) =
        ((x.val : ℕ) : ZMod (3 ^ 2)) := map_natCast _ _
    _ = x := by simp

/-- Reduction of 3-adic units modulo `9` is surjective. -/
theorem padic_nine_surjective :
    Function.Surjective padicIntNine := by
  letI : Nontrivial (ZMod (3 ^ 2)) := ⟨⟨0, 1, by decide⟩⟩
  apply IsLocalRing.surjective_units_map_of_local_ringHom
      (PadicInt.toZModPow (p := 3) 2) padic_z_surjective
  exact Function.Surjective.isLocalHom _ padic_z_surjective

/-- Every character of the 3-adic units into a group of exponent three
factors through reduction modulo `9`. -/
theorem padic_character_nine
    {A : Type*} [Group A]
    (psi : ℤ_[3]ˣ →* A) (hcube : ∀ a : A, a ^ 3 = 1) :
    ∃ phi : (ZMod 9)ˣ →* A, phi.comp padicIntNine = psi := by
  have hker : padicIntNine.ker ≤ psi.ker := by
    intro u hu
    have huval := congrArg Units.val hu
    have huRed : PadicInt.toZModPow 2 (u : ℤ_[3]) = 1 := by
      simpa [padicIntNine] using huval
    obtain ⟨z, hz⟩ :=
      padic_cube_z u huRed
    rw [MonoidHom.mem_ker, ← hz, map_pow, hcube]
  let phi := MonoidHom.liftOfSurjective padicIntNine
    padic_nine_surjective ⟨psi, hker⟩
  refine ⟨phi, ?_⟩
  exact MonoidHom.liftOfRightInverse_comp padicIntNine
    (Function.surjInv padic_nine_surjective)
    (Function.rightInverse_surjInv padic_nine_surjective)
    ⟨psi, hker⟩

/-- The subgroup of cubes in `(ZMod 9)ˣ`. -/
def zmodNineCubes : Subgroup (ZMod 9)ˣ :=
  (powMonoidHom 3).range

/-- The cubic quotient of `(ZMod 9)ˣ`. -/
abbrev PadicIntCubic :=
  (ZMod 9)ˣ ⧸ zmodNineCubes

/-- The canonical cubic character on the 3-adic units. -/
noncomputable def padicCubicCharacter :
    ℤ_[3]ˣ →* PadicIntCubic :=
  (QuotientGroup.mk' zmodNineCubes).comp padicIntNine

/-- The kernel of the canonical cubic character consists exactly of the
cubes in the 3-adic units. -/
theorem padic_character_ker :
    padicCubicCharacter.ker = (powMonoidHom 3).range := by
  apply le_antisymm
  · intro u hu
    have huQuot : QuotientGroup.mk' zmodNineCubes
        (padicIntNine u) = 1 := by
      exact hu
    have huCubes : padicIntNine u ∈ zmodNineCubes :=
      (QuotientGroup.eq_one_iff (padicIntNine u)).mp huQuot
    obtain ⟨v, hv⟩ := huCubes
    change v ^ 3 = padicIntNine u at hv
    obtain ⟨z, hz⟩ := padic_nine_surjective v
    have hred : padicIntNine (u * (z ^ 3)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hz, ← hv]
      simp
    have hredVal := congrArg Units.val hred
    have hmodNine : PadicInt.toZModPow 2
        ((u * (z ^ 3)⁻¹ : ℤ_[3]ˣ) : ℤ_[3]) = 1 := by
      simpa [padicIntNine] using hredVal
    obtain ⟨w, hw⟩ :=
      padic_cube_z
        (u * (z ^ 3)⁻¹) hmodNine
    refine ⟨w * z, ?_⟩
    change (w * z) ^ 3 = u
    rw [mul_pow, hw]
    group
  · rintro u ⟨z, rfl⟩
    rw [MonoidHom.mem_ker]
    rw [powMonoidHom_apply, map_pow]
    change (QuotientGroup.mk' zmodNineCubes
      (padicIntNine z)) ^ 3 = 1
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff
      ((padicIntNine z) ^ 3)).mpr
    exact ⟨padicIntNine z, rfl⟩

/-- The cubic quotient of the units modulo `9` has order three. -/
theorem padic_cubic_card :
    Nat.card PadicIntCubic = 3 := by
  letI : IsCyclic (ZMod 9)ˣ :=
    ZMod.isCyclic_units_of_prime_pow 3 Nat.prime_three (by decide) 2
  rw [← Subgroup.index_eq_card, zmodNineCubes,
    IsCyclic.index_powMonoidHom_range]
  have hcard : Nat.card (ZMod 9)ˣ = 6 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    decide
  rw [hcard]
  decide

/-- The cubic quotient of the 3-adic units is a cyclic group of order three. -/
noncomputable def padicIntCubic :
    Multiplicative (ZMod 3) ≃* PadicIntCubic := by
  letI : IsCyclic (ZMod 9)ˣ :=
    ZMod.isCyclic_units_of_prime_pow 3 Nat.prime_three (by decide) 2
  letI : IsCyclic PadicIntCubic :=
    isCyclic_of_surjective (QuotientGroup.mk' zmodNineCubes)
      (QuotientGroup.mk'_surjective zmodNineCubes)
  let g := Classical.choose
    (IsCyclic.exists_generator (α := PadicIntCubic))
  exact zmodMulEquivOfGenerator (Classical.choose_spec
    (IsCyclic.exists_generator (α := PadicIntCubic)))
    padic_cubic_card

/-- Every character of the 3-adic units into a group of exponent three
factors through the canonical cubic quotient. -/
theorem padic_character_cubic
    {A : Type*} [Group A]
    (psi : ℤ_[3]ˣ →* A) (hcube : ∀ a : A, a ^ 3 = 1) :
    ∃ chi : PadicIntCubic →* A,
      chi.comp padicCubicCharacter = psi := by
  obtain ⟨phi, hphi⟩ :=
    padic_character_nine psi hcube
  have hcubes : zmodNineCubes ≤ phi.ker := by
    rintro x ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    change phi (y ^ 3) = 1
    rw [map_pow, hcube]
  let chi : PadicIntCubic →* A :=
    QuotientGroup.lift zmodNineCubes phi hcubes
  refine ⟨chi, ?_⟩
  ext u
  change chi (QuotientGroup.mk' zmodNineCubes
    (padicIntNine u)) = psi u
  dsimp [chi]
  exact DFunLike.congr_fun hphi u

/-! ## Transport to the rational finite place above 3 -/

/-- Local units and units in the valuation integer ring are canonically
equivalent. -/
noncomputable def localUnitInteger
    (F : Type*) [Field F] [ValuativeRel F] :
    localUnitSubgroup F ≃* (Valuation.integer (valuation F))ˣ :=
  MonoidHom.toMulEquiv (localInteger F) (integerUnitLocal F)
    (by ext x; rfl)
    (by ext x; rfl)

/-- Equivalent valuations have canonically equivalent integer subrings. -/
noncomputable def integerRingValuation
    {F Gamma Delta : Type*} [Field F]
    [LinearOrderedCommGroupWithZero Gamma]
    [LinearOrderedCommGroupWithZero Delta]
    (v : Valuation F Gamma) (w : Valuation F Delta) (h : v.IsEquiv w) :
    v.integer ≃+* w.integer where
  toFun x := ⟨x, h.le_one_iff_le_one.mp x.property⟩
  invFun x := ⟨x, h.le_one_iff_le_one.mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The rational prime number `3`, including its primality proof. -/
def rationalThreePrime : Nat.Primes := ⟨3, Nat.prime_three⟩

/-- The finite place of `ℚ` corresponding to the prime `3`. -/
noncomputable def rationalThreePlace :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
  Rat.HeightOneSpectrum.primesEquiv.symm rationalThreePrime

/-- The local-unit group in the finite-place completion of `ℚ` at `3`. -/
abbrev RationalPlaceUnits : Type :=
  let P := rationalThreePlace
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion := placeValuativeRel P
  localUnitSubgroup v.Completion

/-- The local units in the rational finite-place completion at `3` are
canonically equivalent to the units of `ℤ_[3]`. -/
noncomputable def rationalPadicInt :
    RationalPlaceUnits ≃* ℤ_[3]ˣ := by
  let P := rationalThreePlace
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion := placeValuativeRel P
  letI : Valuation.Compatible
      (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := v.Completion))
  let eVal : Valuation.integer (valuation v.Completion) ≃+*
      completionIntegerRing v :=
    integerRingValuation _ _
      (ValuativeRel.isEquiv (valuation v.Completion)
        (NormedField.valuation (K := v.Completion)))
  exact (localUnitInteger v.Completion).trans
    ((Units.mapEquiv eVal.toMulEquiv).trans
    ((Units.mapEquiv
      (placeIntegerAdic P).toMulEquiv).trans
    (Units.mapEquiv
      (PadicInt.adicCompletionIntegersEquiv
        (NumberField.RingOfIntegers ℚ) rationalThreePrime).symm.toMulEquiv)))

/-- The canonical cubic character on rational local units at the finite place
above `3`. -/
noncomputable def rationalCubicCharacter :
    RationalPlaceUnits →*
      PadicIntCubic :=
  padicCubicCharacter.comp
    rationalPadicInt.toMonoidHom

/-- Every exponent-three character on rational local units at `3` factors
through the canonical cubic quotient of order three. -/
theorem rational_character_cubic
    {A : Type*} [Group A]
    (psi : RationalPlaceUnits →* A)
    (hcube : ∀ a : A, a ^ 3 = 1) :
    ∃ chi : PadicIntCubic →* A,
      chi.comp rationalCubicCharacter = psi := by
  let e := rationalPadicInt
  obtain ⟨chi, hchi⟩ :=
    padic_character_cubic
      (psi.comp e.symm.toMonoidHom) hcube
  refine ⟨chi, ?_⟩
  ext u
  have hu := DFunLike.congr_fun hchi (e u)
  simpa [rationalCubicCharacter, e] using hu

end

end Towers.NumberTheory.Milne
