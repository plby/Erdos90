import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Submission.NumberTheory.Locals.LocalUnramifiedDecomposition
import Submission.NumberTheory.Completions.TotallyRamifiedBound

/-!
# The different bound through an unramified local stage

This file supplies the tower calculation needed after decomposing a finite
extension of local fields into an unramified extension followed by a totally
ramified extension.  An unramified extension of discrete valuation rings has
unit different and does not change the normalized valuation of integers.
Consequently the totally ramified bound is already a bound for the full
extension.
-/

namespace Submission.NumberTheory.Milne

open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

/-- A finite unramified extension of discrete valuation rings has unit
different. -/
theorem different_top_maximal
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [Algebra.IsUnramifiedAt A (IsLocalRing.maximalIdeal B)] :
    differentIdeal A B = ⊤ := by
  have hD : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal B
    (IsPrincipalIdealRing.principal _) (differentIdeal A B) hD
  by_cases hzero : n = 0
  · simp [hn, hzero]
  have hdivides : IsLocalRing.maximalIdeal B ∣ differentIdeal A B := by
    rw [hn]
    simpa using pow_dvd_pow (IsLocalRing.maximalIdeal B)
      (Nat.one_le_iff_ne_zero.mpr hzero)
  exact False.elim <| (not_dvd_differentIdeal_iff.mpr
    (inferInstance : Algebra.IsUnramifiedAt A (IsLocalRing.maximalIdeal B)))
    hdivides

/-- If the maximal ideal downstairs extends to the maximal ideal upstairs,
then normalized valuations of natural numbers agree.  This is the valuation
part of saying that the intermediate extension is unramified. -/
theorem dvr_valuation_maximal
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CharZero A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CharZero B]
    [Algebra A B]
    [Module.IsTorsionFree A B]
    (hmap : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (n : ℕ) :
    dvrCastValuation B n = dvrCastValuation A n := by
  obtain ⟨Pi, hPi⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hmap' : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      (Ideal.span ({Pi} : Set B)) ^ 1 := by
    simpa [hPi.maximalIdeal_eq] using hmap
  have hvaluation :=
    val_nsmul_maximal
      A B Pi hPi 1 one_ne_zero hmap' (n : A)
  simp only [map_natCast, one_nsmul] at hvaluation
  exact congrArg ENat.toNat hvaluation

/-- The degree-uniform different bound after an unramified/totally-ramified
decomposition.  The unramified stage contributes unit different, while its
normalized valuation on `N!` is the same as that of the original base DVR. -/
theorem different_uniform_tower
    (A U B E L : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A]
    [CommRing U] [IsDomain U] [IsDiscreteValuationRing U] [CharZero U]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CharZero B]
    [Algebra A U] [Algebra U B] [Algebra A B] [IsScalarTower A U B]
    [Module.Finite A U] [Module.Finite U B] [Module.Finite A B]
    [Module.IsTorsionFree A U] [Module.IsTorsionFree U B]
    [Module.IsTorsionFree A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing U)]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [Algebra.IsUnramifiedAt A (IsLocalRing.maximalIdeal U)]
    [Field E] [Algebra U E] [IsFractionRing U E]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra E L] [Algebra U L]
    [IsScalarTower U B L] [IsScalarTower U E L]
    [FiniteDimensional E L] [Algebra.IsSeparable E L]
    [IsIntegralClosure B U L]
    (hmapAU : (IsLocalRing.maximalIdeal A).map (algebraMap A U) =
      IsLocalRing.maximalIdeal U)
    (Pi : B) (hPi : Irreducible Pi) (e N : ℕ) (he : e ≠ 0)
    (heN : e ≤ N)
    (hmapUB : (IsLocalRing.maximalIdeal U).map (algebraMap U B) =
      (Ideal.span ({Pi} : Set B)) ^ e)
    (hdegree : (minpoly U Pi).natDegree = e)
    (hadjoin : Algebra.adjoin U ({Pi} : Set B) = ⊤)
    (hfield : Algebra.adjoin E ({algebraMap B L Pi} : Set L) = ⊤) :
    differentIdeal A B ∣
      (IsLocalRing.maximalIdeal B) ^
        (N * (dvrCastValuation A N.factorial + 1)) := by
  have hDU : differentIdeal A U = ⊤ :=
    different_top_maximal A U
  have htower : differentIdeal A B = differentIdeal U B := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal A U B,
      hDU, Ideal.map_top, Ideal.mul_top]
  have hvaluation : dvrCastValuation U N.factorial =
      dvrCastValuation A N.factorial :=
    dvr_valuation_maximal A U hmapAU N.factorial
  rw [htower, ← hvaluation]
  exact
    different_uniform_totally
      U B E L Pi hPi e N he heN hmapUB hdegree hadjoin hfield

/-- Intrinsic tower form of the local estimate.  Once an intermediate DVR
`U` is unramified over `A` and `B/U` is totally ramified, the full different
is bounded solely in terms of the original base valuation and an upper bound
for the degree of the totally ramified step. -/
theorem different_totally_ramified
    (A U B E L : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A]
    [CommRing U] [IsDomain U] [IsDiscreteValuationRing U] [CharZero U]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CharZero B]
    [Algebra A U] [Algebra U B] [Algebra A B] [IsScalarTower A U B]
    [Module.Finite A U] [Module.Finite U B] [Module.Finite A B]
    [Module.IsTorsionFree A U] [Module.IsTorsionFree U B]
    [Module.IsTorsionFree A B]
    [Algebra.IsSeparable (FractionRing A) (FractionRing U)]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [Algebra.IsUnramifiedAt A (IsLocalRing.maximalIdeal U)]
    [Field E] [Algebra U E] [IsFractionRing U E]
    [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra E L] [Algebra U L]
    [IsScalarTower U B L] [IsScalarTower U E L]
    [FiniteDimensional E L] [Algebra.IsSeparable E L]
    [PerfectField (FractionRing U)] [IsIntegralClosure B U L]
    (hmapAU : (IsLocalRing.maximalIdeal A).map (algebraMap A U) =
      IsLocalRing.maximalIdeal U)
    (htr : TotallyRamified U B (IsLocalRing.maximalIdeal U))
    (N : ℕ) (hN : Module.finrank U B ≤ N) :
    differentIdeal A B ∣
      (IsLocalRing.maximalIdeal B) ^
        (N * (dvrCastValuation A N.factorial + 1)) := by
  have hDU : differentIdeal A U = ⊤ :=
    different_top_maximal A U
  have htower : differentIdeal A B = differentIdeal U B := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal A U B,
      hDU, Ideal.map_top, Ideal.mul_top]
  have hvaluation : dvrCastValuation U N.factorial =
      dvrCastValuation A N.factorial :=
    dvr_valuation_maximal A U hmapAU N.factorial
  rw [htower, ← hvaluation]
  exact
    different_uniform_ramified
      U B E L htr N hN

/-- The unconditional local different bound used in Milne, Theorem 8.42.
The required unramified/totally ramified tower is constructed by lifting a
primitive element of the upper residue field. -/
theorem different_henselian_dvr
    (A B : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A]
    [HenselianLocalRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CharZero B]
    [HenselianLocalRing B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [FiniteDimensional (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B)]
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    (N : ℕ) (hN : Module.finrank A B ≤ N) :
    differentIdeal A B ∣
      (IsLocalRing.maximalIdeal B) ^
        (N * (dvrCastValuation A N.factorial + 1)) := by
  letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  letI : IsLocalHom (algebraMap A B) :=
    Algebra.IsIntegral.isLocalHom A B
  obtain ⟨a₀, f, a, hprimitive, hfmonic, hfmap, _hroot, hresidue,
      haintegral, hminpoly, hlocal, hunramified, hdvr, _hPmax,
      _hsurjective⟩ :=
    unramified_adjoin_prescribed A B
  let U := Algebra.adjoin A ({a} : Set B)
  letI : IsLocalRing U := hlocal
  letI : IsDiscreteValuationRing U := hdvr
  letI : Algebra.FormallyUnramified A U := hunramified
  letI : Module.Finite A U :=
    Algebra.finite_adjoin_simple_of_isIntegral haintegral
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  letI : IsLocalHom (algebraMap A U) :=
    Algebra.IsIntegral.isLocalHom A U
  letI : Module.Finite U B :=
    Module.Finite.of_restrictScalars_finite A U B
  letI : Algebra.IsIntegral U B := Algebra.IsIntegral.of_finite U B
  letI : Module.IsTorsionFree U B :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Subtype.val_injective
  letI : FaithfulSMul U B :=
    (faithfulSMul_iff_algebraMap_injective U B).mpr Subtype.val_injective
  letI : IsLocalHom (algebraMap U B) :=
    Algebra.IsIntegral.isLocalHom U B
  letI : Algebra U (FractionRing B) := U.toAlgebra
  letI : FaithfulSMul U (FractionRing B) := inferInstance
  let uFracAlgebra : Algebra U (FractionRing U) :=
    OreLocalization.instAlgebra
  letI : SMul U (FractionRing U) := uFracAlgebra.toSMul
  letI : Algebra U (FractionRing U) := uFracAlgebra
  letI : Algebra (FractionRing U) (FractionRing B) :=
    FractionRing.liftAlgebra U (FractionRing B)
  letI : IsScalarTower U (FractionRing U) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra U (FractionRing B)
  have hmapAU : (IsLocalRing.maximalIdeal A).map (algebraMap A U) =
      IsLocalRing.maximalIdeal U :=
    Algebra.FormallyUnramified.map_maximalIdeal
  letI : Algebra.IsUnramifiedAt A (IsLocalRing.maximalIdeal U) := by
    change Algebra.FormallyUnramified A
      (Localization.AtPrime (IsLocalRing.maximalIdeal U))
    infer_instance
  letI : IsIntegralClosure B U (FractionRing B) :=
    IsIntegralClosure.of_isIntegrallyClosed B U (FractionRing B)
  letI : FiniteDimensional (FractionRing U) (FractionRing B) :=
    Module.Finite.of_isLocalization
      (Rₚ := FractionRing U) (Sₚ := FractionRing B) U B U⁰
  letI : Algebra.IsSeparable (FractionRing A) (FractionRing U) :=
    Algebra.IsSeparable.of_algHom (FractionRing A) (FractionRing B)
      (IsScalarTower.toAlgHom (FractionRing A) (FractionRing U)
        (FractionRing B))
  letI : Algebra.IsSeparable (FractionRing U) (FractionRing B) :=
    Algebra.isSeparable_tower_top_of_isSeparable
      (FractionRing A) (FractionRing U) (FractionRing B)
  have hres : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField U)
        (IsLocalRing.ResidueField B)) :=
    adjoin_primitive_lift
      A B a₀ f a hprimitive hfmonic hfmap hresidue haintegral hminpoly
  have htr : TotallyRamified U B (IsLocalRing.maximalIdeal U) :=
    totally_ramified_surjective
      U B (FractionRing U) (FractionRing B) hres
  have hUBN : Module.finrank U B ≤ N := by
    calc
      Module.finrank U B = 1 * Module.finrank U B := by simp
      _ ≤ Module.finrank A U * Module.finrank U B := by
        exact Nat.mul_le_mul_right _
          (Nat.one_le_iff_ne_zero.mpr Module.finrank_pos.ne')
      _ = Module.finrank A B := Module.finrank_mul_finrank A U B
      _ ≤ N := hN
  exact
    different_totally_ramified
      A U B (FractionRing U) (FractionRing B) hmapAU htr N hUBN

end Submission.NumberTheory.Milne
