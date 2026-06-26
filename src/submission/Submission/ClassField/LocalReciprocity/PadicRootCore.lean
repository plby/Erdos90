import Submission.ClassField.LubinTate.PadicUniformizerRoot
import Submission.ClassField.LubinTate.RootFieldRamification
import Submission.ClassField.NormCorrespondence.LubinTateGeneration
import Submission.ClassField.LocalBrauer.FieldNormExtension
import Submission.ClassField.LocalBrauer.SpectralIntegerTower
import Submission.ClassField.LocalBrauer.TotallyCanonicalTransport
import Submission.NumberTheory.Locals.UnramifiedExtensions
import Submission.ClassField.LocalExistence.AssembledLocalReciprocity
import Submission.ClassField.LocalReciprocity.MixedCupTransport
import Submission.ClassField.LocalReciprocity.AmbientCompatibility
import Submission.ClassField.LocalReciprocity.CyclotomicComparison
import Submission.ClassField.UnramifiedCohom.NormInteger

open Submission.CField.LFTheory
open Submission.CField.UCohom
open Submission.CField.LRecip
open Submission.CField.LBrauer
open scoped IsMulCommutative

namespace Submission.CField.LRecip.PNProof


theorem spectral_alg_local
    (K E F : Type*) [NormedField K]
    [Field E] [Field F] [Algebra K E] [Algebra K F]
    (e : E ≃ₐ[K] F) (x : E) :
    spectralNorm K E x = spectralNorm K F (e x) := by
  simp only [spectralNorm, minpoly.algEquiv_eq]

noncomputable def absoluteValueRpow
    {F : Type*} [Field F] (v : AbsoluteValue F ℝ)
    (hna : IsNonarchimedean v) (c : ℝ) (hc : 0 < c) :
    AbsoluteValue F ℝ where
  toFun x := v x ^ c
  map_mul' x y := by
    rw [map_mul, Real.mul_rpow (v.nonneg x) (v.nonneg y)]
  nonneg' x := Real.rpow_nonneg (v.nonneg x) c
  eq_zero' x := by
    rw [Real.rpow_eq_zero_iff_of_nonneg (v.nonneg x)]
    simp [hc.ne']
  add_le' x y := by
    have hxy : v (x + y) ≤ max (v x) (v y) := hna x y
    have hp := Real.rpow_le_rpow (v.nonneg _) hxy hc.le
    refine hp.trans ?_
    rw [Real.rpow_max (x := v x) (y := v y) (p := c)
      (v.nonneg x) (v.nonneg y) hc.le]
    exact max_le
      (le_add_of_nonneg_right (Real.rpow_nonneg (v.nonneg y) c))
      (le_add_of_nonneg_left (Real.rpow_nonneg (v.nonneg x) c))

theorem absolute_spectral_restriction
    {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (v : AbsoluteValue L ℝ) (hv : IsNonarchimedean v)
    (hbase : (NormedField.toAbsoluteValue K).IsEquiv
      (v.comp (algebraMap K L).injective)) :
    v.IsEquiv
      (Submission.CField.LBrauer.spectralAbsoluteValue K L) := by
  obtain ⟨c, hc, hpow⟩ :=
    AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hbase
  let w := absoluteValueRpow v hv c⁻¹ (inv_pos.mpr hc)
  have hwext (x : K) : w (algebraMap K L x) = ‖x‖ := by
    change v (algebraMap K L x) ^ c⁻¹ = ‖x‖
    have hx : v (algebraMap K L x) = ‖x‖ ^ c := by
      exact (congrFun hpow x).symm
    rw [hx]
    by_cases hnorm : ‖x‖ = 0
    · rw [hnorm]
      simp [hc.ne']
    · rw [← Real.rpow_mul (norm_nonneg x), mul_inv_cancel₀ hc.ne', Real.rpow_one]
  have hw (x : L) : w x =
      Submission.CField.LBrauer.spectralAbsoluteValue K L x := by
    exact spectralNorm_unique_field_norm_ext hwext x
  apply AbsoluteValue.isEquiv_iff_lt_one_iff.mpr
  intro x
  rw [← hw x]
  change v x < 1 ↔ v x ^ c⁻¹ < 1
  exact (Real.rpow_lt_one_iff' (v.nonneg x) (inv_pos.mpr hc)).symm

/-- An isometric field equivalence restricts to the norm-defined integer
rings. -/
noncomputable def integerIsometricAlg
    {K E F : Type*} [Field K] [NormedField E] [NormedField F]
    [IsUltrametricDist E] [IsUltrametricDist F]
    [Algebra K E] [Algebra K F]
    (e : E ≃ₐ[K] F) (hnorm : ∀ x : E, ‖e x‖ = ‖x‖) :
    Valuation.integer (NormedField.valuation (K := E)) ≃+*
      Valuation.integer (NormedField.valuation (K := F)) :=
  RingEquiv.restrict e.toRingEquiv _ _ fun x ↦ by
    simp only [Valuation.mem_integer_iff, NormedField.valuation_apply]
    rw [← NNReal.coe_le_coe, ← NNReal.coe_le_coe]
    change ‖x‖ ≤ 1 ↔ ‖e x‖ ≤ 1
    rw [hnorm]

theorem integer_isometric_alg
    {K E F : Type*} [Field K] [NormedField E] [NormedField F]
    [IsUltrametricDist E] [IsUltrametricDist F]
    [Algebra K E] [Algebra K F]
    (e : E ≃ₐ[K] F) (hnorm : ∀ x : E, ‖e x‖ = ‖x‖) :
    Nat.card (IsLocalRing.ResidueField
        (Valuation.integer (NormedField.valuation (K := E)))) =
      Nat.card (IsLocalRing.ResidueField
        (Valuation.integer (NormedField.valuation (K := F)))) :=
  Nat.card_congr
    (IsLocalRing.ResidueField.mapEquiv
      (integerIsometricAlg e hnorm)).toEquiv

set_option maxHeartbeats 5000000 in
-- Identifying a finite unramified extension unfolds residue fields and completions.
set_option synthInstance.maxHeartbeats 500000 in
-- The canonical unramified level carries a deep finite-extension instance tower.
/-- A finite intrinsically unramified extension is isomorphic to the
canonical unramified level of the same degree. -/
theorem alg_unramified_level
    (K E : Type)
    [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [Field E] [Algebra K E] [FiniteDimensional K E]
    (hE : Submission.CField.UCohom.FUExt.IsUnramified K E) :
    let n := Module.finrank K E
    letI : NeZero n := ⟨Module.finrank_pos.ne'⟩
    Nonempty (E ≃ₐ[K] canonicalUnramifiedLevel K n) := by
  let n := Module.finrank K E
  letI : NeZero n := ⟨Module.finrank_pos.ne'⟩
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    FLExt.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := FLExt.valuativeRel K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation _
  letI : IsNonarchimedeanLocalField E :=
    FLExt.nonarchimedeanLocalField K E
  letI : IsGalois K E :=
    Submission.CField.UCohom.FUExt.galoisUnramified
      K E hE
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := E)) := spectralValuationExtension K E
  let A := Valuation.integer (ValuativeRel.valuation K)
  let A₀ := Valuation.integer (NormedField.valuation (K := K))
  let U := Valuation.integer (NormedField.valuation (K := E))
  letI : IsDiscreteValuationRing A := discrete_valuation_ring K
  letI : IsDiscreteValuationRing U := by
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (valuativeIntegerNorm E)
  letI : Algebra A K := A.subtype.toAlgebra
  letI : IsFractionRing A K :=
    (Valuation.integer.integers (ValuativeRel.valuation K)).isFractionRing
  letI : Algebra U E := U.subtype.toAlgebra
  letI : IsFractionRing U E :=
    (Valuation.integer.integers (NormedField.valuation (K := E))).isFractionRing
  letI : Algebra A U := valuativeSpectralAlgebra K E
  letI : IsScalarTower A U E := valuativeSpectralTower K E
  letI : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq' rfl
  have hE' : Module.Finite A₀ U ∧ Algebra.FormallyUnramified A₀ U := by
    simpa [Submission.CField.UCohom.FUExt.IsUnramified,
      A₀, U] using hE
  letI : Module.Finite A₀ U := hE'.1
  letI : Algebra.FormallyUnramified A₀ U := hE'.2
  let eA : A ≃+* A₀ := valuativeIntegerNorm K
  letI : Algebra A A₀ := eA.toRingHom.toAlgebra
  let eAA₀ : A ≃ₐ[A] A₀ := AlgEquiv.ofRingEquiv (f := eA) (fun _ ↦ rfl)
  letI : Module.Finite A A₀ := Module.Finite.equiv eAA₀.toLinearEquiv
  letI : Algebra.FormallyUnramified A A₀ :=
    Algebra.FormallyUnramified.of_equiv eAA₀
  letI : IsScalarTower A A₀ U := IsScalarTower.of_algebraMap_eq' <| by
    apply RingHom.ext
    intro a
    rfl
  letI : Module.Finite A U := Module.Finite.trans A₀ U
  letI : Algebra.FormallyUnramified A U :=
    Algebra.FormallyUnramified.comp A A₀ U
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  have hAE : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A K E]
    exact (algebraMap K E).injective.comp (IsFractionRing.injective A K)
  have hAU : Function.Injective (algebraMap A U) := by
    intro x y hxy
    apply hAE
    rw [IsScalarTower.algebraMap_eq A U E]
    exact congrArg (algebraMap U E) hxy
  letI : FaithfulSMul A U :=
    (faithfulSMul_iff_algebraMap_injective A U).mpr hAU
  letI : Module.IsTorsionFree A U :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FaithfulSMul.algebraMap_injective A U)
  letI : Module.Free A U := Module.free_of_finite_type_torsion_free'
  letI : IsLocalHom (algebraMap A U) := inferInstance
  letI : IsAdicComplete (IsLocalRing.maximalIdeal A) A :=
    integer_adic_complete K
  letI : Finite (IsLocalRing.ResidueField A) :=
    local_field_residue K
  have hresidueCard :
      Nat.card (IsLocalRing.ResidueField A) = localResidueCard K := by
    rw [localResidueCard]
    exact Nat.card_congr
      (IsLocalRing.ResidueField.mapEquiv eA).toEquiv
  have hsplit : ((localFrobeniusPolynomial K n).map
      (algebraMap K E)).Splits := by
    simpa [localFrobeniusPolynomial, hresidueCard] using
      (splits_fraction_dvr
        A U K E n rfl)
  exact alg_separable_splits
    K E n rfl hsplit

section GenericArithmeticFrobenius

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

noncomputable local instance genericArithmeticValuativeRel : ValuativeRel K :=
  ValuativeRel.ofValuation (NormedField.valuation (K := K))

noncomputable local instance genericArithmeticCompatible :
    Valuation.Compatible (NormedField.valuation (K := K)) :=
  Valuation.Compatible.ofValuation _

variable [IsNonarchimedeanLocalField K]

/-- The finite Artin map on an arbitrary canonical model of an unramified
extension sends a normalized prime to the automorphism characterized by the
arithmetic residue action. -/
theorem abelian_artin_arithmetic
    (E : Type)
    [Field E] [Algebra K E] [FiniteDimensional K E]
    [IsGalois K E] [IsMulCommutative Gal(E/K)]
    (n : ℕ) [NeZero n]
    (e : E ≃ₐ[K] canonicalUnramifiedLevel K n)
    (sigma : Gal(E/K))
    (hsigma : ∀ x : E, spectralNorm K E x ≤ 1 →
      spectralNorm K E
        (sigma x - x ^ localResidueCardinality K) < 1)
    (varpi : Kˣ)
    (hvarpi : localUnitOrder K (Additive.ofMul varpi) = 1) :
    abelianArtinHom K E varpi = sigma := by
  let U := canonicalUnramifiedLevel K n
  letI : IsMulCommutative Gal(U/K) := by
    letI : IsCyclic Gal(U/K) := unramified_level_cyclic K n
    exact IsCyclic.isMulCommutative
  have hsigmaU :
      (canonicalUnramifiedSubextension K n).IsArithmeticFrobenius K
        (e.autCongr sigma) := by
    unfold FASubext.IsArithmeticFrobenius
    dsimp only [canonicalUnramifiedSubextension]
    intro y hy
    have hx : spectralNorm K E (e.symm y) ≤ 1 := by
      rw [spectral_alg_local K E U e]
      simpa [U] using hy
    have h := hsigma (e.symm y) hx
    change spectralNorm K U
      (e.autCongr sigma y - y ^ localResidueCardinality K) < 1
    have heq :
        e (sigma (e.symm y) - (e.symm y) ^ localResidueCardinality K) =
          e.autCongr sigma y - y ^ localResidueCardinality K := by
      simp [AlgEquiv.autCongr_apply]
    rw [← heq, ← spectral_alg_local K E U e]
    exact h
  have hsigmaCanonical :
      e.autCongr sigma = canonicalArithmeticFrobenius K n :=
    subextension_arithmetic_unique
      K n (e.autCongr sigma) hsigmaU
  have hmap :
      frobeniusNormalizedArtin K n =
        abelianLocalArtin K U :=
    frobenius_normalized_abelian
      K n
  have hvalue :
      abelianArtinHom K U varpi =
        canonicalArithmeticFrobenius K n := by
    change abelianLocalArtin K U
      (QuotientGroup.mk' (normSubgroup K U) varpi) = _
    rw [← hmap]
    exact frobenius_normalized_uniformizer K n varpi hvarpi
  have htransport := DFunLike.congr_fun
    (abelian_artin_alg K E U e) varpi
  apply e.autCongr.injective
  calc
    e.autCongr (abelianArtinHom K E varpi) =
        abelianArtinHom K U varpi := htransport
    _ = canonicalArithmeticFrobenius K n := hvalue
    _ = e.autCongr sigma := hsigmaCanonical.symm

/-- The full normalized formula behind
`abelian_artin_arithmetic`: on an
unramified extension, an arbitrary base-field unit maps to arithmetic
Frobenius raised to its normalized local order.  In particular this is the
identity on valuation-ring units. -/
theorem abelian_arithmetic_zpow
    (E : Type)
    [Field E] [Algebra K E] [FiniteDimensional K E]
    [IsGalois K E] [IsMulCommutative Gal(E/K)]
    (n : ℕ) [NeZero n]
    (e : E ≃ₐ[K] canonicalUnramifiedLevel K n)
    (sigma : Gal(E/K))
    (hsigma : ∀ x : E, spectralNorm K E x ≤ 1 →
      spectralNorm K E
        (sigma x - x ^ localResidueCardinality K) < 1)
    (a : Kˣ) :
    abelianArtinHom K E a =
      sigma ^ localUnitOrder K (Additive.ofMul a) := by
  let U := canonicalUnramifiedLevel K n
  letI : IsMulCommutative Gal(U/K) := by
    letI : IsCyclic Gal(U/K) := unramified_level_cyclic K n
    exact IsCyclic.isMulCommutative
  have hsigmaU :
      (canonicalUnramifiedSubextension K n).IsArithmeticFrobenius K
        (e.autCongr sigma) := by
    unfold FASubext.IsArithmeticFrobenius
    dsimp only [canonicalUnramifiedSubextension]
    intro y hy
    have hx : spectralNorm K E (e.symm y) ≤ 1 := by
      rw [spectral_alg_local K E U e]
      simpa [U] using hy
    have h := hsigma (e.symm y) hx
    change spectralNorm K U
      (e.autCongr sigma y - y ^ localResidueCardinality K) < 1
    have heq :
        e (sigma (e.symm y) - (e.symm y) ^ localResidueCardinality K) =
          e.autCongr sigma y - y ^ localResidueCardinality K := by
      simp [AlgEquiv.autCongr_apply]
    rw [← heq, ← spectral_alg_local K E U e]
    exact h
  have hsigmaCanonical :
      e.autCongr sigma = canonicalArithmeticFrobenius K n :=
    subextension_arithmetic_unique
      K n (e.autCongr sigma) hsigmaU
  have hmap :
      frobeniusNormalizedArtin K n =
        abelianLocalArtin K U :=
    frobenius_normalized_abelian
      K n
  have hvalue :
      abelianArtinHom K U a =
        canonicalArithmeticFrobenius K n ^
          localUnitOrder K (Additive.ofMul a) := by
    change abelianLocalArtin K U
      (QuotientGroup.mk' (normSubgroup K U) a) = _
    rw [← hmap]
    exact frobenius_normalized_unramified K n a
  have htransport := DFunLike.congr_fun
    (abelian_artin_alg K E U e) a
  apply e.autCongr.injective
  rw [map_zpow]
  calc
    e.autCongr (abelianArtinHom K E a) =
        abelianArtinHom K U a := htransport
    _ = canonicalArithmeticFrobenius K n ^
          localUnitOrder K (Additive.ofMul a) := hvalue
    _ = (e.autCongr sigma) ^
          localUnitOrder K (Additive.ofMul a) := by
      rw [hsigmaCanonical]

end GenericArithmeticFrobenius

open Submission.CField.LTate
open Submission.CField.FGroups
open Submission.CField.LBrauer

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (k : Type) [Field k] [CharP k p] [IsAlgClosed k]

local instance : ValuativeRel ℚ_[p] :=
  ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))

local instance : Valuation.Compatible
    (NormedField.valuation (K := ℚ_[p])) :=
  Valuation.Compatible.ofValuation _

local instance : IsNonarchimedeanLocalField ℚ_[p] := by
  haveI htop : IsValuativeTopology ℚ_[p] := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [show s ∈ nhds (0 : ℚ_[p]) ↔
        ∃ γ : (MonoidWithZeroHom.ValueGroup₀
            (NormedField.valuation (K := ℚ_[p])))ˣ,
          {x | (NormedField.valuation (K := ℚ_[p])).restrict x < γ.1} ⊆ s from
      (NormedField.toValued (K := ℚ_[p])).is_topological_valuation s]
    simpa using
      (NormedField.valuation (K := ℚ_[p]))
        |>.exists_setOf_restrict_le_iff 0 s
  haveI hnontrivial : ValuativeRel.IsNontrivial ℚ_[p] :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := ℚ_[p]))).mpr inferInstance
  exact
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := hnontrivial }

private abbrev B (n : ℕ) := PadicWittRing p k n
private abbrev C (n : ℕ) := FractionRing (B p k n)

local instance (n : ℕ) : Algebra ℚ_[p] (C p k n) :=
  (wittRootFraction p k n).toAlgebra

noncomputable def wittAdicAbsolute (n : ℕ) :
    AbsoluteValue (C p k n) ℝ :=
  (IsDiscreteValuationRing.maximalIdeal (B p k n)).adicAbv
    (show (1 : NNReal) < (2 : NNReal) by norm_num)

theorem witt_root_fraction
    (n : ℕ) (x : ℚ_[p]) (hx : ‖x‖ < 1) :
    wittAdicAbsolute p k n
      (wittRootFraction p k n x) < 1 := by
  let z : ℤ_[p] := ⟨x, hx.le⟩
  have hz : ‖z‖ < 1 := hx
  obtain ⟨a, ha⟩ := (PadicInt.norm_lt_one_iff_dvd (p := p) z).mp hz
  have hxrep : x = algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) * a) := by
    change x = ((p : ℤ_[p]) * a : ℤ_[p])
    rw [← ha]
  rw [hxrep, root_fraction_algebra]
  change ((IsDiscreteValuationRing.maximalIdeal (B p k n)).adicAbv
      (show (1 : NNReal) < (2 : NNReal) by norm_num))
    (algebraMap (B p k n) (C p k n)
      (padicWittRing p k n ((p : ℤ_[p]) * a))) < 1
  rw [(IsDiscreteValuationRing.maximalIdeal
    (B p k n)).adicAbv_coe_lt_one_iff]
  change padicWittRing p k n ((p : ℤ_[p]) * a) ∈
    IsLocalRing.maximalIdeal (B p k n)
  rw [padic_witt_maximal]
  change padicWittRing p k n ((p : ℤ_[p]) * a) ∈
    Ideal.span {cyclotomicWittRoot p k n}
  rw [map_mul]
  exact (Ideal.span {cyclotomicWittRoot p k n}).mul_mem_right _
    (by simpa [padicWittRing] using
      padic_witt_p p k n)

theorem padic_fraction_absolute (n : ℕ) :
    (NormedField.toAbsoluteValue ℚ_[p]).IsEquiv
      ((wittAdicAbsolute p k n).comp
        (wittRootFraction p k n).injective) := by
  apply AbsoluteValue.isEquiv_of_lt_one_imp
  · refine ⟨(p : ℚ_[p]), ?_, ?_⟩
    · exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    · exact ne_of_lt Padic.norm_p_lt_one
  · intro x hx
    exact witt_root_fraction p k n x hx

theorem witt_adic_absolute
    (n : ℕ) (x : C p k n) :
    wittAdicAbsolute p k n x ≤ 1 ↔
      ∃ b : B p k n, algebraMap (B p k n) (C p k n) b = x := by
  let v := IsDiscreteValuationRing.maximalIdeal (B p k n)
  have h2 : (1 : NNReal) < (2 : NNReal) := by norm_num
  have habs : wittAdicAbsolute p k n x ≤ 1 ↔
      v.valuation (C p k n) x ≤ 1 := by
    change ((WithZeroMulInt.toNNReal (ne_zero_of_lt h2))
      (v.valuation (C p k n) x) : NNReal) ≤ 1 ↔ _
    exact WithZeroMulInt.toNNReal_le_one_iff h2
  rw [habs]
  constructor
  · exact IsDiscreteValuationRing.exists_lift_of_le_one
  · rintro ⟨b, rfl⟩
    exact v.valuation_le_one b

theorem intermediate_witt_absolute
    (n : ℕ) (L : IntermediateField ℚ_[p] (C p k n))
    [Algebra.IsAlgebraic ℚ_[p] L] :
    ((wittAdicAbsolute p k n).comp L.val.injective).IsEquiv
      (spectralAbsoluteValue ℚ_[p] L) := by
  apply absolute_spectral_restriction
  · intro x y
    exact (IsDiscreteValuationRing.maximalIdeal (B p k n))
      |>.isNonarchimedean_adicAbv
        (show (1 : NNReal) < (2 : NNReal) by norm_num) (x : C p k n) y
  · simpa using padic_fraction_absolute p k n

theorem intermediate_field_spectral
    (n : ℕ) (L : IntermediateField ℚ_[p] (C p k n))
    [Algebra.IsAlgebraic ℚ_[p] L] (x : L) :
    spectralNorm ℚ_[p] L x ≤ 1 ↔
      ∃ b : B p k n,
        algebraMap (B p k n) (C p k n) b = (x : C p k n) := by
  have h := intermediate_witt_absolute p k n L
  change spectralAbsoluteValue ℚ_[p] L x ≤ 1 ↔ _
  rw [← h.le_one_iff]
  exact witt_adic_absolute p k n x

noncomputable def basicWittRoot (n : ℕ) (u : ℤ_[p]ˣ) : B p k n :=
  Classical.choose (padic_witt_root p k n u)

theorem basic_witt_root (n : ℕ) (u : ℤ_[p]ˣ) :
    Polynomial.eval₂ (padicWittRing p k n) (basicWittRoot p k n u)
      (reducedLubinIterate (padicTateDatum p u).f n) = 0 :=
  (Classical.choose_spec
    (padic_witt_root p k n u)).1

theorem basic_witt_fixed (n : ℕ) (u : ℤ_[p]ˣ) :
    wittFrobeniusLift p k n u (basicWittRoot p k n u) =
      basicWittRoot p k n u :=
  (Classical.choose_spec
    (padic_witt_root p k n u)).2.1

theorem basic_witt_associated (n : ℕ) (u : ℤ_[p]ˣ) :
    Associated (basicWittRoot p k n u)
      (cyclotomicWittRoot p k n) :=
  (Classical.choose_spec
    (padic_witt_root p k n u)).2.2

theorem root_value_associated (n : ℕ) (u : ℤ_[p]ˣ) :
    Associated (padicWittValue p k n u)
      (cyclotomicWittRoot p k n) := by
  let epsilon : (WittVector p k)ˣ :=
    Units.map (padicIntWitt p k).toMonoidHom u
  let theta : PowerSeries (WittVector p k) :=
    PowerSeries.map (padicIntWitt p k)
      (padicBinomialEndomorphism p (u : ℤ_[p]))
  have htheta0 : PowerSeries.constantCoeff theta = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      endomorphism_constant_coeff, map_zero]
  have htheta1 : PowerSeries.coeff 1 theta = (epsilon : WittVector p k) := by
    simp [theta, epsilon, padic_binomial_endomorphism]
  have h := witt_theta_associated
    p k n epsilon theta htheta0 htheta1
  rw [show padicWittValue p k n u =
      wittThetaValue p k n theta by
    unfold padicWittValue
    unfold padicWittPoint
    dsimp only
    simp only [id_eq]
    rw [padic_witt_smul p k n (u : ℤ_[p])
      (padicCyclotomicPoint p k n)]
    rfl]
  exact h

noncomputable def basicWittFraction (n : ℕ) (u : ℤ_[p]ˣ) :
    (padicTateDatum p u).RootField ℚ_[p] n →+* C p k n := by
  apply AdjoinRoot.lift (wittRootFraction p k n)
    (algebraMap (B p k n) (C p k n) (basicWittRoot p k n u))
  change Polynomial.eval₂ (wittRootFraction p k n)
      (algebraMap (B p k n) (C p k n) (basicWittRoot p k n u))
      ((reducedLubinIterate (padicTateDatum p u).f n).map
        (algebraMap ℤ_[p] ℚ_[p])) = 0
  rw [Polynomial.eval₂_map]
  have hcoeff :
      (wittRootFraction p k n).comp (algebraMap ℤ_[p] ℚ_[p]) =
        (algebraMap (B p k n) (C p k n)).comp
          (padicWittRing p k n) := by
    ext a
    exact root_fraction_algebra p k n a
  rw [hcoeff, ← Polynomial.hom_eval₂, basic_witt_root]
  exact map_zero _

@[simp] theorem basic_witt_fraction (n : ℕ) (u : ℤ_[p]ˣ) :
    basicWittFraction p k n u
        ((padicTateDatum p u).root ℚ_[p] n) =
      algebraMap (B p k n) (C p k n) (basicWittRoot p k n u) := by
  exact AdjoinRoot.lift_root _

noncomputable def cyclotomicAlgHom (n : ℕ) :
    (cyclotomicLubinDatum p).RootField ℚ_[p] n →ₐ[ℚ_[p]] C p k n :=
  { padicCyclotomicFraction p k n with
    commutes' := fun x ↦ by
      change padicCyclotomicFraction p k n
          (algebraMap ℚ_[p]
            ((cyclotomicLubinDatum p).RootField ℚ_[p] n) x) =
        wittRootFraction p k n x
      exact AdjoinRoot.lift_of _ }

noncomputable def basicAlgHom (n : ℕ) (u : ℤ_[p]ˣ) :
    (padicTateDatum p u).RootField ℚ_[p] n →ₐ[ℚ_[p]] C p k n :=
  { basicWittFraction p k n u with
    commutes' := fun x ↦ by
      change basicWittFraction p k n u
          (algebraMap ℚ_[p]
            ((padicTateDatum p u).RootField ℚ_[p] n) x) =
        wittRootFraction p k n x
      exact AdjoinRoot.lift_of _ }

noncomputable def cyclotomicWittField (n : ℕ) :
    IntermediateField ℚ_[p] (C p k n) :=
  (cyclotomicAlgHom p k n).fieldRange

noncomputable def basicWittField (n : ℕ) (u : ℤ_[p]ˣ) :
    IntermediateField ℚ_[p] (C p k n) :=
  (basicAlgHom p k n u).fieldRange

noncomputable def comparisonWittField (n : ℕ) (u : ℤ_[p]ˣ) :
    IntermediateField ℚ_[p] (C p k n) :=
  cyclotomicWittField p k n ⊔ basicWittField p k n u

noncomputable instance cyclotomic_witt_dimensional (n : ℕ) :
    FiniteDimensional ℚ_[p] (cyclotomicWittField p k n) := by
  let e := AlgEquiv.ofInjectiveField (cyclotomicAlgHom p k n)
  exact FiniteDimensional.of_surjective e.toLinearEquiv.toLinearMap e.surjective

noncomputable instance witt_field_dimensional (n : ℕ) (u : ℤ_[p]ˣ) :
    FiniteDimensional ℚ_[p] (basicWittField p k n u) := by
  let e := AlgEquiv.ofInjectiveField (basicAlgHom p k n u)
  exact FiniteDimensional.of_surjective e.toLinearEquiv.toLinearMap e.surjective

noncomputable instance comparison_witt_dimensional (n : ℕ) (u : ℤ_[p]ˣ) :
    FiniteDimensional ℚ_[p] (comparisonWittField p k n u) := by
  exact IntermediateField.finiteDimensional_sup
    (cyclotomicWittField p k n) (basicWittField p k n u)

noncomputable instance cyclotomic_witt_galois (n : ℕ) :
    IsGalois ℚ_[p] (cyclotomicWittField p k n) := by
  let e := AlgEquiv.ofInjectiveField (cyclotomicAlgHom p k n)
  apply e.transfer_galois.mp
  exact (cyclotomicLubinDatum p).root_field_galois ℚ_[p]
    (padic_int_field p) n

noncomputable instance basic_witt_galois (n : ℕ) (u : ℤ_[p]ˣ) :
    IsGalois ℚ_[p] (basicWittField p k n u) := by
  let e := AlgEquiv.ofInjectiveField (basicAlgHom p k n u)
  apply e.transfer_galois.mp
  apply (padicTateDatum p u).root_field_galois ℚ_[p]
  change IsField (ℤ_[p] ⧸ Ideal.span {((p : ℤ_[p]) * (u : ℤ_[p]))})
  rw [Ideal.span_singleton_mul_right_unit u.isUnit (p : ℤ_[p])]
  exact padic_int_field p

noncomputable instance comparison_field_galois (n : ℕ) (u : ℤ_[p]ˣ) :
    IsGalois ℚ_[p] (comparisonWittField p k n u) := by
  letI hE : Normal ℚ_[p] (cyclotomicWittField p k n) := inferInstance
  letI hF : Normal ℚ_[p] (basicWittField p k n u) := inferInstance
  letI hM : Normal ℚ_[p] (comparisonWittField p k n u) := by
    change Normal ℚ_[p]
      ↑(cyclotomicWittField p k n ⊔ basicWittField p k n u)
    exact IntermediateField.normal_sup (F := ℚ_[p]) (K := C p k n)
      (cyclotomicWittField p k n) (basicWittField p k n u)
  exact isGalois_iff.mpr ⟨inferInstance, hM⟩

noncomputable instance witt_nontrivially_normed
    (n : ℕ) (u : ℤ_[p]ˣ) :
    NontriviallyNormedField (basicWittField p k n u) :=
  spectralNorm.nontriviallyNormedField ℚ_[p] _

noncomputable instance witt_normed_algebra
    (n : ℕ) (u : ℤ_[p]ˣ) :
    NormedAlgebra ℚ_[p] (basicWittField p k n u) :=
  spectralNorm.normedAlgebra ℚ_[p] _

noncomputable instance comparison_nontrivially_normed
    (n : ℕ) (u : ℤ_[p]ˣ) :
    NontriviallyNormedField (comparisonWittField p k n u) :=
  spectralNorm.nontriviallyNormedField ℚ_[p] _

noncomputable instance (priority := 2000) basicWittField_topologicalSpace
    (n : ℕ) (u : ℤ_[p]ˣ) : TopologicalSpace (basicWittField p k n u) :=
  let h := witt_nontrivially_normed p k n u
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _
      (@MetricSpace.toPseudoMetricSpace _ h.toNormedField.toMetricSpace))

noncomputable instance (priority := 2000) comparisonWittField_topologicalSpace
    (n : ℕ) (u : ℤ_[p]ˣ) : TopologicalSpace (comparisonWittField p k n u) :=
  let h := comparison_nontrivially_normed p k n u
  @UniformSpace.toTopologicalSpace _
    (@PseudoMetricSpace.toUniformSpace _
      (@MetricSpace.toPseudoMetricSpace _ h.toNormedField.toMetricSpace))

noncomputable instance comparison_normed_algebra
    (n : ℕ) (u : ℤ_[p]ˣ) :
    NormedAlgebra ℚ_[p] (comparisonWittField p k n u) :=
  spectralNorm.normedAlgebra ℚ_[p] _

noncomputable instance witt_ultrametric_dist
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsUltrametricDist (basicWittField p k n u) :=
  IsUltrametricDist.of_normedAlgebra ℚ_[p]

noncomputable instance comparison_ultrametric_dist
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsUltrametricDist (comparisonWittField p k n u) :=
  IsUltrametricDist.of_normedAlgebra ℚ_[p]

noncomputable instance basic_valuative_rel
    (n : ℕ) (u : ℤ_[p]ˣ) :
    ValuativeRel (basicWittField p k n u) :=
  FLExt.valuativeRel ℚ_[p] _

noncomputable instance witt_valuative_rel
    (n : ℕ) (u : ℤ_[p]ˣ) :
    ValuativeRel (comparisonWittField p k n u) :=
  FLExt.valuativeRel ℚ_[p] _

noncomputable instance basic_witt_local
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsNonarchimedeanLocalField (basicWittField p k n u) :=
  FLExt.nonarchimedeanLocalField ℚ_[p] _

noncomputable instance comparison_witt_local
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsNonarchimedeanLocalField (comparisonWittField p k n u) :=
  FLExt.nonarchimedeanLocalField ℚ_[p] _

noncomputable instance basic_witt_compatible
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Valuation.Compatible
      (NormedField.valuation (K := basicWittField p k n u)) :=
  Valuation.Compatible.ofValuation _

noncomputable instance comparison_witt_compatible
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Valuation.Compatible
      (NormedField.valuation (K := comparisonWittField p k n u)) :=
  Valuation.Compatible.ofValuation _

noncomputable instance witt_complete_space
    (n : ℕ) (u : ℤ_[p]ˣ) : CompleteSpace (basicWittField p k n u) :=
  spectralNorm.completeSpace ℚ_[p] _

noncomputable instance comparison_complete_space
    (n : ℕ) (u : ℤ_[p]ˣ) : CompleteSpace (comparisonWittField p k n u) :=
  spectralNorm.completeSpace ℚ_[p] _

noncomputable instance witt_proper_space
    (n : ℕ) (u : ℤ_[p]ˣ) : ProperSpace (basicWittField p k n u) :=
  FiniteDimensional.proper ℚ_[p] _

set_option maxHeartbeats 8000000 in
-- Computing the residue cardinality unfolds the totally ramified root-field model.
set_option synthInstance.maxHeartbeats 800000 in
-- The root field carries several equivalent finite-dimensional structures.
/-- The basic Lubin--Tate root field is totally ramified over `Q_p`, hence
its residue field still has `p` elements. -/
theorem basic_witt_cardinality
    (n : ℕ) (u : ℤ_[p]ˣ) :
    localResidueCardinality (basicWittField p k n u) = p := by
  let D := lubinTateDatum p u
  let R := D.RootField ℚ_[p] n
  let F := basicWittField p k n u
  letI : Algebra.IsAlgebraic ℚ_[p] R := Algebra.IsAlgebraic.of_finite ℚ_[p] R
  letI : NontriviallyNormedField R := spectralNorm.nontriviallyNormedField ℚ_[p] R
  letI : NormedAlgebra ℚ_[p] R := spectralNorm.normedAlgebra ℚ_[p] R
  letI : IsUltrametricDist R := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : ValuativeRel R :=
    FLExt.valuativeRel ℚ_[p] R
  letI : IsNonarchimedeanLocalField R :=
    FLExt.nonarchimedeanLocalField ℚ_[p] R
  letI : Valuation.Compatible (NormedField.valuation (K := R)) :=
    Valuation.Compatible.ofValuation _
  letI : CompleteSpace R := spectralNorm.completeSpace ℚ_[p] R
  letI : ProperSpace R := FiniteDimensional.proper ℚ_[p] R
  letI : (NormedField.valuation (K := ℚ_[p])).HasExtension
      (NormedField.valuation (K := R)) := spectralValuationExtension ℚ_[p] R
  let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
  let OR := Valuation.integer (NormedField.valuation (K := R))
  have hfield : IsField (A ⧸ Ideal.span {D.pi}) := by
    exact padic_integer_field p u
  letI : IsDiscreteValuationRing A := discreteValuationRing p
  letI : IsDiscreteValuationRing OR :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (valuativeIntegerNorm R)
  letI : Algebra A OR := Valuation.HasExtension.instAlgebraInteger
  letI : IsUniformAddGroup A := A.toAddSubgroup.isUniformAddGroup
  letI : IsUniformAddGroup OR := OR.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace OR := by
    have hset : (↑OR : Set R) = {x : R | ‖x‖ ≤ 1} := by
      ext x
      rw [Set.mem_setOf_eq]
      change (NormedField.valuation (K := R)) x ≤ 1 ↔ ‖x‖ ≤ 1
      rw [NormedField.valuation_apply, ← NNReal.coe_le_coe]
      rfl
    have hclosed : IsClosed (↑OR : Set R) := by
      rw [hset]
      exact isClosed_le continuous_norm continuous_const
    exact hclosed.completeSpace_coe
  letI : IsGalois ℚ_[p] R := D.root_field_galois ℚ_[p] hfield n
  letI : Module.Finite A OR :=
    Submission.NumberTheory.Milne.valued_integer_module ℚ_[p] R
  letI : IsFractionRing OR R :=
    (Valuation.integer.integers
      (NormedField.valuation (K := R))).isFractionRing
  letI : IsScalarTower A OR R := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A ℚ_[p] R := IsScalarTower.of_algebraMap_eq' rfl
  have htotal : Submission.NumberTheory.Milne.TotallyRamified
      A OR (IsLocalRing.maximalIdeal A) := by
    letI : Finite (A ⧸ Ideal.span {D.pi}) := D.finiteResidue
    letI : Fintype (A ⧸ Ideal.span {D.pi}) := Fintype.ofFinite _
    let hI : IsAdic (IsLocalRing.maximalIdeal OR) :=
      Submission.NumberTheory.Milne.valued_integer_adic R
    let rho : A →+* OR := algebraMap A OR
    let FLT := lubinFormalLaw D.pi D.pi_irreducible.ne_zero
      D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
        D.lubin_tate_card
    let point : RelativeLubinPoints hI rho D.pi
        D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
        (D.f : PowerSeries A) D.lubin_tate_card → OR := fun z ↦
      FGLaw.APts.toIdeal hI (FLT.map rho) z
    obtain ⟨y, hy, hyroot⟩ :=
      D.spectral_point_maps ℚ_[p] hfield n
    change OR.subtype (point y) = D.root ℚ_[p] n at hyroot
    let alpha : OR := point y
    let fA : Polynomial A := reducedLubinIterate D.f n
    have hfA_degree : fA.natDegree = (D.q - 1) * D.q ^ n := by
      dsimp only [fA]
      rw [reduced_iterate_degree, D.f_natDegree]
    have hfA_monic : fA.Monic := by
      apply reduced_iterate_monic D.f_monic
      · simpa using D.lubinTateSeries.1
      · rw [D.f_natDegree]
        exact Nat.ne_of_gt (Nat.zero_lt_of_lt D.one_lt_q)
    have hfA_eisenstein :
        fA.IsEisensteinAt (IsLocalRing.maximalIdeal A) := by
      rw [D.pi_irreducible.maximalIdeal_eq]
      exact reduced_iterate_eisenstein
        D.pi_irreducible D.f_monic D.f_natDegree D.one_lt_q
          D.lubinTateSeries n
    have halpha_root : Polynomial.aeval alpha fA = 0 := by
      change Polynomial.eval₂ rho (point y) fA = 0
      exact D.eval₂_reducedLubinTateIterate_eq_zero_of_torsionOf_eq
        hI rho hfield n y hy
    have halpha_gen :
        IntermediateField.adjoin ℚ_[p] ({algebraMap OR R alpha} : Set R) = ⊤ := by
      rw [show algebraMap OR R alpha = D.root ℚ_[p] n by exact hyroot]
      exact D.adjoin_root_top ℚ_[p] n
    have hp0 : IsLocalRing.maximalIdeal A ≠ ⊥ :=
      IsDiscreteValuationRing.not_a_field A
    have hfA_degree_pos : 0 < fA.natDegree := by
      rw [hfA_degree]
      exact Nat.mul_pos (Nat.sub_pos_of_lt D.one_lt_q)
        (pow_pos (Nat.zero_lt_of_lt D.one_lt_q) n)
    have hram :=
      Submission.NumberTheory.Milne.eisenstein_total_ramification
        A OR ℚ_[p] R hp0 hfA_eisenstein hfA_monic
          hfA_degree_pos halpha_root halpha_gen
    let P : Ideal OR :=
      (IsLocalRing.maximalIdeal A).map (algebraMap A OR) ⊔
        Ideal.span {alpha}
    change P.IsPrime ∧
        (IsLocalRing.maximalIdeal A).map (algebraMap A OR) =
          P ^ fA.natDegree ∧
        Ideal.ramificationIdx (IsLocalRing.maximalIdeal A) P =
          fA.natDegree ∧
        ∀ Q : Ideal OR, Q.IsPrime →
          Q.LiesOver (IsLocalRing.maximalIdeal A) → Q = P at hram
    rcases hram with ⟨hPprime, hpow, hidx, hunique⟩
    have hfieldRank : Module.finrank ℚ_[p] R = Module.finrank A OR :=
      Algebra.IsAlgebraic.finrank_of_isFractionRing A ℚ_[p] OR R
    have hdegree : Module.finrank ℚ_[p] R = fA.natDegree := by
      calc
        Module.finrank ℚ_[p] R = (D.q - 1) * D.q ^ n :=
          D.finrank_rootField ℚ_[p] n
        _ = fA.natDegree := hfA_degree.symm
    have hfinrank : Module.finrank A OR = fA.natDegree :=
      hfieldRank.symm.trans hdegree
    have hmap_le :
        (IsLocalRing.maximalIdeal A).map (algebraMap A OR) ≤ P :=
      le_sup_left
    have hcomap_prime : (P.comap (algebraMap A OR)).IsPrime :=
      hPprime.comap (algebraMap A OR)
    have hcomap : P.comap (algebraMap A OR) =
        IsLocalRing.maximalIdeal A := by
      exact ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le
        hcomap_prime.ne_top (Ideal.map_le_iff_le_comap.mp hmap_le)).symm
    refine ⟨P, hPprime, ⟨hcomap.symm⟩, ?_, ?_, hunique⟩
    · rw [hfinrank]
      exact hpow
    · rw [hfinrank]
      exact hidx
  have hcardR : localResidueCard R = localResidueCard ℚ_[p] := by
    let pA := IsLocalRing.maximalIdeal A
    obtain ⟨P, hPprime, hPover, _hmap, hram, hunique⟩ := htotal
    have hp0 : pA ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
    have hPmax : P = IsLocalRing.maximalIdeal OR :=
      IsLocalRing.eq_maximalIdeal (hPprime.isMaximal hP0)
    letI : P.IsPrime := hPprime
    letI : P.IsMaximal := hPprime.isMaximal hP0
    letI : P.LiesOver pA := hPover
    have hprimes : IsDedekindDomain.primesOverFinset pA OR = {P} := by
      ext Q
      constructor
      · intro hQ
        have hQdata := (IsDedekindDomain.mem_primesOverFinset_iff hp0 OR).mp hQ
        rcases hQdata with ⟨hQprime, hQover⟩
        exact Finset.mem_singleton.mpr (hunique Q hQprime hQover)
      · intro hQ
        have hQP : Q = P := Finset.mem_singleton.mp hQ
        subst Q
        exact (IsDedekindDomain.mem_primesOverFinset_iff hp0 OR).mpr ⟨hPprime, hPover⟩
    have hbij : Function.Bijective (algebraMap (A ⧸ pA) (OR ⧸ P)) :=
      Submission.NumberTheory.Milne.bijective_full_idx
        A OR ℚ_[p] R hp0 hprimes hram
    let er : (A ⧸ pA) ≃+* (OR ⧸ P) :=
      RingEquiv.ofBijective (algebraMap (A ⧸ pA) (OR ⧸ P)) hbij
    change Nat.card (IsLocalRing.ResidueField OR) =
      Nat.card (IsLocalRing.ResidueField A)
    simpa [IsLocalRing.ResidueField, pA, hPmax] using
      (Nat.card_congr er.toEquiv).symm
  let e₀ : R ≃ₐ[ℚ_[p]]
      (padicTateDatum p u).RootField ℚ_[p] n :=
    padicIntegerBasic p u n
  let e₁ : (padicTateDatum p u).RootField ℚ_[p] n ≃ₐ[ℚ_[p]] F :=
    AlgEquiv.ofInjectiveField (basicAlgHom p k n u)
  let e : R ≃ₐ[ℚ_[p]] F := e₀.trans e₁
  have heNorm (x : R) : ‖e x‖ = ‖x‖ := by
    rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[p],
      NormedAlgebra.norm_eq_spectralNorm ℚ_[p]]
    exact (spectral_alg_local ℚ_[p] R F e x).symm
  have hcardRF : localResidueCard R = localResidueCard F := by
    exact integer_isometric_alg e heNorm
  have hcardQ : localResidueCard ℚ_[p] = p := by
    change Nat.card (IsLocalRing.ResidueField
      (Valuation.integer (NormedField.valuation (K := ℚ_[p])))) = p
    calc
      _ = Nat.card (IsLocalRing.ResidueField ℤ_[p]) :=
        Nat.card_congr
          (IsLocalRing.ResidueField.mapEquiv
            (padicNormInt p)).toEquiv
      _ = Nat.card (ZMod p) := Nat.card_congr PadicInt.residueField.toEquiv
      _ = p := by simp
  change localResidueCard F = p
  exact hcardRF.symm.trans (hcardR.trans hcardQ)

noncomputable instance comparison_proper_space
    (n : ℕ) (u : ℤ_[p]ˣ) : ProperSpace (comparisonWittField p k n u) :=
  FiniteDimensional.proper ℚ_[p] _

theorem witt_frobenius_injective
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Function.Injective (wittFrobeniusLift p k n u) := by
  let phi := wittFrobeniusLift p k n u
  let root := cyclotomicWittRoot p k n
  have hrootirr : Irreducible root :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer root).mpr
      (padic_witt_maximal p k n)
  intro x y hxy
  have hzero : phi (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  by_contra hne
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨m, hm⟩ :=
    IsDiscreteValuationRing.associated_pow_irreducible hsub hrootirr
  have hmapped := hm.map phi
  have hrootmap : phi root =
      padicWittValue p k n u⁻¹ :=
    padic_frobenius_root p k n u
  have hrootmap0 : phi root ≠ 0 := by
    rw [hrootmap]
    exact (root_value_associated p k n u⁻¹).ne_zero_iff.mpr
      hrootirr.ne_zero
  have hmap0 : phi (x - y) ≠ 0 :=
    hmapped.ne_zero_iff.mpr (by
      rw [map_pow]
      exact pow_ne_zero m hrootmap0)
  exact hmap0 hzero

noncomputable def padicFrobeniusFraction
    (n : ℕ) (u : ℤ_[p]ˣ) : C p k n →+* C p k n :=
  IsFractionRing.lift (A := B p k n) (K := C p k n) (L := C p k n)
    (g := (algebraMap (B p k n) (C p k n)).comp
      (wittFrobeniusLift p k n u))
    ((IsFractionRing.injective (B p k n) (C p k n)).comp
      (witt_frobenius_injective p k n u))

@[simp] theorem padic_fraction_algebra
    (n : ℕ) (u : ℤ_[p]ˣ) (x : B p k n) :
    padicFrobeniusFraction p k n u
        (algebraMap (B p k n) (C p k n) x) =
      algebraMap (B p k n) (C p k n)
        (wittFrobeniusLift p k n u x) := by
  exact IsFractionRing.lift_algebraMap
    (A := B p k n) (K := C p k n) (L := C p k n) _ x

@[simp] theorem padic_witt_int
    (n : ℕ) (u : ℤ_[p]ˣ) (a : ℤ_[p]) :
    wittFrobeniusLift p k n u
        (padicWittRing p k n a) =
      padicWittRing p k n a := by
  change wittFrobeniusLift p k n u
      (algebraMap (WittVector p k) (B p k n) (padicIntWitt p k a)) = _
  rw [padic_witt_coeff,
    frobenius_int_witt]
  rfl

@[simp] theorem padic_frobenius_fraction
    (n : ℕ) (u : ℤ_[p]ˣ) (x : ℚ_[p]) :
    padicFrobeniusFraction p k n u
        (wittRootFraction p k n x) =
      wittRootFraction p k n x := by
  let lhs : ℚ_[p] →+* C p k n :=
    (padicFrobeniusFraction p k n u).comp
      (wittRootFraction p k n)
  have hhom : lhs = wittRootFraction p k n := by
    apply IsFractionRing.ringHom_ext (A := ℤ_[p])
    intro a
    dsimp only [lhs, RingHom.comp_apply]
    rw [root_fraction_algebra,
      padic_fraction_algebra,
      padic_witt_int]
  exact DFunLike.congr_fun hhom x

@[simp] theorem frobenius_fraction_root
    (n : ℕ) (u : ℤ_[p]ˣ) :
    padicFrobeniusFraction p k n u
        (algebraMap (B p k n) (C p k n)
          (cyclotomicWittRoot p k n)) =
      algebraMap (B p k n) (C p k n)
        (padicWittValue p k n u⁻¹) := by
  rw [padic_fraction_algebra,
    padic_frobenius_root]

@[simp] theorem padic_fraction_root
    (n : ℕ) (u : ℤ_[p]ˣ) :
    padicFrobeniusFraction p k n u
        (algebraMap (B p k n) (C p k n) (basicWittRoot p k n u)) =
      algebraMap (B p k n) (C p k n) (basicWittRoot p k n u) := by
  rw [padic_fraction_algebra,
    basic_witt_fixed]

noncomputable def wittFrobeniusFraction
    (n : ℕ) (u : ℤ_[p]ˣ) : C p k n →ₐ[ℚ_[p]] C p k n :=
  { padicFrobeniusFraction p k n u with
    commutes' := padic_frobenius_fraction p k n u }

theorem padic_fraction_comparison
    (n : ℕ) (u : ℤ_[p]ˣ) :
    (comparisonWittField p k n u).map
        (wittFrobeniusFraction p k n u) =
      comparisonWittField p k n u := by
  let phi := wittFrobeniusFraction p k n u
  let E := cyclotomicWittField p k n
  let F := basicWittField p k n u
  have hE : E.map phi = E := by
    rw [← IntermediateField.fieldRange_comp_val]
    exact AlgHom.fieldRange_of_normal (phi.comp E.val)
  have hF : F.map phi = F := by
    rw [← IntermediateField.fieldRange_comp_val]
    exact AlgHom.fieldRange_of_normal (phi.comp F.val)
  change (E ⊔ F).map phi = E ⊔ F
  rw [IntermediateField.map_sup, hE, hF]

noncomputable def comparisonWittAlg
    (n : ℕ) (u : ℤ_[p]ˣ) :
    comparisonWittField p k n u →ₐ[ℚ_[p]] comparisonWittField p k n u := by
  let M := comparisonWittField p k n u
  let phi := wittFrobeniusFraction p k n u
  exact
    { toFun := fun x ↦ ⟨phi x, by
        have hx : phi (x : C p k n) ∈
            (comparisonWittField p k n u).map phi :=
          ⟨x, x.property, rfl⟩
        have heq : (comparisonWittField p k n u).map phi =
            comparisonWittField p k n u := by
          simpa [phi] using
            padic_fraction_comparison p k n u
        rw [heq] at hx
        exact hx⟩
      map_one' := Subtype.ext (map_one phi)
      map_mul' := fun x y ↦ Subtype.ext
        (map_mul phi (x : C p k n) (y : C p k n))
      map_zero' := Subtype.ext (map_zero phi)
      map_add' := fun x y ↦ Subtype.ext
        (map_add phi (x : C p k n) (y : C p k n))
      commutes' := fun x ↦ Subtype.ext (phi.commutes x) }

noncomputable def comparisonWittFrobenius
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Gal(comparisonWittField p k n u/ℚ_[p]) := by
  let f := comparisonWittAlg p k n u
  apply AlgEquiv.ofBijective f
  refine ⟨f.injective, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := ℚ_[p]) (V := comparisonWittField p k n u)
    (V₂ := comparisonWittField p k n u) rfl
    (f := f.toLinearMap)).mp f.injective

@[simp] theorem comparison_frobenius_coe
    (n : ℕ) (u : ℤ_[p]ˣ) (x : comparisonWittField p k n u) :
    ((comparisonWittFrobenius p k n u x : comparisonWittField p k n u) :
        C p k n) =
      padicFrobeniusFraction p k n u (x : C p k n) := by
  rfl

noncomputable def basicFieldComparison
    (n : ℕ) (u : ℤ_[p]ˣ) :
    basicWittField p k n u →+* comparisonWittField p k n u :=
  (IntermediateField.inclusion le_sup_right).toRingHom

noncomputable def cyclotomicWittComparison
    (n : ℕ) (u : ℤ_[p]ˣ) :
    cyclotomicWittField p k n →+* comparisonWittField p k n u :=
  (IntermediateField.inclusion le_sup_left).toRingHom

noncomputable instance cyclotomicComparisonAlgebra
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Algebra (cyclotomicWittField p k n) (comparisonWittField p k n u) :=
  (cyclotomicWittComparison p k n u).toAlgebra

noncomputable instance comparisonScalarTower
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsScalarTower ℚ_[p] (cyclotomicWittField p k n)
      (comparisonWittField p k n u) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable instance wittComparisonAlgebra
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Algebra (basicWittField p k n u) (comparisonWittField p k n u) :=
  (basicFieldComparison p k n u).toAlgebra

noncomputable instance wittScalarTower
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsScalarTower ℚ_[p] (basicWittField p k n u)
      (comparisonWittField p k n u) :=
  IsScalarTower.of_algebraMap_eq' rfl

set_option synthInstance.maxHeartbeats 500000 in
-- Transitivity of finite dimensionality searches through both intermediate fields.
noncomputable instance wittComparisonDimensional
    (n : ℕ) (u : ℤ_[p]ˣ) :
    FiniteDimensional (basicWittField p k n u)
      (comparisonWittField p k n u) :=
  FiniteDimensional.right ℚ_[p] (basicWittField p k n u)
    (comparisonWittField p k n u)

set_option synthInstance.maxHeartbeats 500000 in
-- The relative spectral norm comparison needs the finite-module tower instance.
/-- The spectral absolute value on the comparison field is unchanged when
the fixed basic Lubin--Tate field is used as the base. -/
theorem comparison_spectral_relative
    (n : ℕ) (u : ℤ_[p]ˣ) (x : comparisonWittField p k n u) :
    spectralNorm (basicWittField p k n u)
        (comparisonWittField p k n u) x =
      spectralNorm ℚ_[p] (comparisonWittField p k n u) x := by
  symm
  let v := spectralAbsoluteValue ℚ_[p]
    (comparisonWittField p k n u)
  have hv (a : basicWittField p k n u) :
      v (algebraMap (basicWittField p k n u)
        (comparisonWittField p k n u) a) = ‖a‖ := by
    change spectralNorm ℚ_[p] (comparisonWittField p k n u)
        (algebraMap (basicWittField p k n u)
          (comparisonWittField p k n u) a) = ‖a‖
    calc
      spectralNorm ℚ_[p] (comparisonWittField p k n u)
          (algebraMap (basicWittField p k n u)
            (comparisonWittField p k n u) a) =
          spectralNorm ℚ_[p] (basicWittField p k n u) a :=
        (spectralNorm.eq_of_tower (K := ℚ_[p])
          (L := comparisonWittField p k n u) a).symm
      _ = ‖a‖ := (NormedAlgebra.norm_eq_spectralNorm ℚ_[p] a).symm
  exact spectralNorm_unique_field_norm_ext hv x

theorem witt_frobenius_fraction
    (n : ℕ) (u : ℤ_[p]ˣ) :
    (padicFrobeniusFraction p k n u).comp
        (basicWittFraction p k n u) =
      basicWittFraction p k n u := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro x
    calc
      ((padicFrobeniusFraction p k n u).comp
          (basicWittFraction p k n u))
          (AdjoinRoot.of _ x) =
          padicFrobeniusFraction p k n u
            (wittRootFraction p k n x) := by
        rw [RingHom.comp_apply]
        exact congrArg _ (AdjoinRoot.lift_of _)
      _ = wittRootFraction p k n x :=
        padic_frobenius_fraction p k n u x
      _ = basicWittFraction p k n u
          (AdjoinRoot.of _ x) := by
        exact (AdjoinRoot.lift_of _).symm
  · calc
      ((padicFrobeniusFraction p k n u).comp
          (basicWittFraction p k n u))
          (AdjoinRoot.root _) =
          padicFrobeniusFraction p k n u
            (algebraMap (B p k n) (C p k n)
              (basicWittRoot p k n u)) := by
        rw [RingHom.comp_apply]
        exact congrArg _ (AdjoinRoot.lift_root _)
      _ = algebraMap (B p k n) (C p k n)
            (basicWittRoot p k n u) :=
        padic_fraction_root p k n u
      _ = basicWittFraction p k n u
          (AdjoinRoot.root _) :=
        (AdjoinRoot.lift_root _).symm

theorem comparison_fixes_basic
    (n : ℕ) (u : ℤ_[p]ˣ) (x : basicWittField p k n u) :
    comparisonWittFrobenius p k n u
        (algebraMap (basicWittField p k n u)
          (comparisonWittField p k n u) x) =
      algebraMap (basicWittField p k n u)
        (comparisonWittField p k n u) x := by
  obtain ⟨z, hz⟩ := x.property
  apply Subtype.ext
  change padicFrobeniusFraction p k n u (x : C p k n) = x
  rw [← hz]
  exact DFunLike.congr_fun
    (witt_frobenius_fraction p k n u) z

noncomputable def comparisonRelativeFrobenius
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Gal(comparisonWittField p k n u/basicWittField p k n u) :=
  { (comparisonWittFrobenius p k n u).toRingEquiv with
    commutes' := comparison_fixes_basic p k n u }

noncomputable def wittFieldComparison
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IntermediateField ℚ_[p] (comparisonWittField p k n u) :=
  (basicWittField p k n u).restrict le_sup_right

noncomputable def basicWittComparison
    (n : ℕ) (u : ℤ_[p]ˣ) :
    basicWittField p k n u ≃ₐ[ℚ_[p]] wittFieldComparison p k n u :=
  IntermediateField.restrict_algEquiv le_sup_right

theorem comparison_witt_fixes
    (n : ℕ) (u : ℤ_[p]ˣ) (x : wittFieldComparison p k n u) :
    comparisonWittFrobenius p k n u
        (algebraMap (wittFieldComparison p k n u)
          (comparisonWittField p k n u) x) =
      algebraMap (wittFieldComparison p k n u)
        (comparisonWittField p k n u) x := by
  obtain ⟨y, rfl⟩ := (basicWittComparison p k n u).surjective x
  exact comparison_fixes_basic p k n u y

noncomputable def comparisonWittBasic
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Gal(comparisonWittField p k n u/wittFieldComparison p k n u) :=
  { (comparisonWittFrobenius p k n u).toRingEquiv with
    commutes' := comparison_witt_fixes p k n u }

@[simp] theorem comparison_witt_coe
    (n : ℕ) (u : ℤ_[p]ˣ) (x : comparisonWittField p k n u) :
    ((comparisonRelativeFrobenius p k n u x :
        comparisonWittField p k n u) : C p k n) =
      padicFrobeniusFraction p k n u (x : C p k n) := by
  rfl

/-- The relative Witt Frobenius acts on integral elements as the `p`-power
map modulo the maximal ideal. -/
theorem comparison_witt_relative
    (n : ℕ) (u : ℤ_[p]ˣ) (x : comparisonWittField p k n u)
    (hx : spectralNorm ℚ_[p] (comparisonWittField p k n u) x ≤ 1) :
    spectralNorm ℚ_[p] (comparisonWittField p k n u)
        (comparisonRelativeFrobenius p k n u x - x ^ p) < 1 := by
  obtain ⟨b, hb⟩ :=
    (intermediate_field_spectral p k n
      (comparisonWittField p k n u) x).mp hx
  let phi := wittFrobeniusLift p k n u
  have hresphi := DFunLike.congr_fun
    (padic_witt_lift p k n u) b
  have hresphi' : padicWittResidue p k n
      (phi b) = ((frobenius k p).comp
        (padicWittResidue p k n)) b := by
    exact hresphi
  have hreszero : padicWittResidue p k n
      (phi b - b ^ p) = 0 := by
    rw [map_sub, hresphi', map_pow]
    change ((frobenius k p).comp
        (padicWittResidue p k n)) b -
      (padicWittResidue p k n b) ^ p = 0
    simp [frobenius_def]
  have hbmax : phi b - b ^ p ∈ IsLocalRing.maximalIdeal (B p k n) := by
    rw [padic_witt_maximal,
      ← padic_witt_ker]
    exact hreszero
  have hbabs : wittAdicAbsolute p k n
      (algebraMap (B p k n) (C p k n) (phi b - b ^ p)) < 1 :=
    ((IsDiscreteValuationRing.maximalIdeal (B p k n))
      |>.adicAbv_coe_lt_one_iff
        (show (1 : NNReal) < (2 : NNReal) by norm_num) _).mpr hbmax
  apply (intermediate_witt_absolute p k n
    (comparisonWittField p k n u)).lt_one_iff.mp
  change wittAdicAbsolute p k n
      (((comparisonRelativeFrobenius p k n u x - x ^ p :
        comparisonWittField p k n u) : C p k n)) < 1
  have heq :
      ((comparisonRelativeFrobenius p k n u x - x ^ p :
          comparisonWittField p k n u) : C p k n) =
        algebraMap (B p k n) (C p k n) (phi b - b ^ p) := by
    change
      padicFrobeniusFraction p k n u (x : C p k n) -
          (x : C p k n) ^ p =
        algebraMap (B p k n) (C p k n) (phi b - b ^ p)
    rw [← hb, padic_fraction_algebra,
      map_sub, map_pow]
  rw [heq]
  exact hbabs

set_option maxHeartbeats 3000000 in
-- Rewriting the Witt realization requires normalizing the finite Lubin--Tate orbit.
/-- The Witt realization of a unit translate has the same natural-exponent
formula as the fixed finite Lubin--Tate orbit. -/
theorem padic_witt_pow
    (n : ℕ) (a : ℤ_[p]ˣ) :
    let q := padicIntInteger p (n + 1) a
    let m := (padicZMod p (n + 1) q :
      ZMod (p ^ (n + 1))).val
    algebraMap (B p k n) (C p k n)
        (padicWittValue p k n a) =
      (1 + algebraMap (B p k n) (C p k n)
        (cyclotomicWittRoot p k n)) ^ m - 1 := by
  dsimp only
  rw [padic_z_reduction]
  rw [padic_witt_reduction]
  simp only [map_sub, map_pow, map_add, map_one]
  simp [padicUnitReduction]

noncomputable def comparisonBasicRoot
    (n : ℕ) (u : ℤ_[p]ˣ) : comparisonWittField p k n u :=
  ⟨algebraMap (B p k n) (C p k n) (basicWittRoot p k n u),
    (show basicWittField p k n u ≤ comparisonWittField p k n u from
      le_sup_right) ⟨(padicTateDatum p u).root ℚ_[p] n,
        basic_witt_fraction p k n u⟩⟩

theorem norm_integer_maximal
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [IsLocalRing (Valuation.integer (NormedField.valuation (K := K)))]
    (x : Valuation.integer (NormedField.valuation (K := K)))
    (hx : ‖(x : K)‖ < 1) :
    x ∈ IsLocalRing.maximalIdeal
      (Valuation.integer (NormedField.valuation (K := K))) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hxunit
  rcases hxunit with ⟨v, rfl⟩
  have hinvle :
      ‖(((v⁻¹ :
          (Valuation.integer (NormedField.valuation (K := K)))ˣ) :
        Valuation.integer (NormedField.valuation (K := K))) : K)‖ ≤ 1 := by
    have hv := ((v⁻¹ :
      (Valuation.integer (NormedField.valuation (K := K)))ˣ) :
        Valuation.integer (NormedField.valuation (K := K))).property
    change (NormedField.valuation (K := K))
      ((((v⁻¹ :
          (Valuation.integer (NormedField.valuation (K := K)))ˣ) :
        Valuation.integer (NormedField.valuation (K := K))) : K)) ≤ 1 at hv
    rw [NormedField.valuation_apply, ← NNReal.coe_le_coe] at hv
    exact_mod_cast hv
  have hone :
      ‖(((v : Valuation.integer
          (NormedField.valuation (K := K))) : K))‖ *
        ‖(((v⁻¹ :
            (Valuation.integer (NormedField.valuation (K := K)))ˣ) :
          Valuation.integer (NormedField.valuation (K := K))) : K)‖ = 1 := by
    calc
      _ = ‖(((v : Valuation.integer
              (NormedField.valuation (K := K))) : K) *
          (((v⁻¹ : (Valuation.integer
              (NormedField.valuation (K := K)))ˣ) :
            Valuation.integer (NormedField.valuation (K := K))) : K))‖ := by
        exact (norm_mul _ _).symm
      _ = 1 := by simp
  have hprodle :
      ‖(((v : Valuation.integer
          (NormedField.valuation (K := K))) : K))‖ *
        ‖(((v⁻¹ :
            (Valuation.integer (NormedField.valuation (K := K)))ˣ) :
          Valuation.integer (NormedField.valuation (K := K))) : K)‖ ≤
      ‖(((v : Valuation.integer
          (NormedField.valuation (K := K))) : K))‖ :=
    mul_le_of_le_one_right (norm_nonneg _) hinvle
  rw [hone] at hprodle
  linarith

noncomputable def comparisonRootInteger
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Valuation.integer
      (NormedField.valuation (K := comparisonWittField p k n u)) := by
  refine ⟨comparisonBasicRoot p k n u, ?_⟩
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply,
    ← NNReal.coe_le_coe]
  change ‖comparisonBasicRoot p k n u‖ ≤ 1
  rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[p]]
  apply (intermediate_field_spectral p k n
    (comparisonWittField p k n u) _).mpr
  exact ⟨basicWittRoot p k n u, rfl⟩

set_option synthInstance.maxHeartbeats 500000 in
-- The valuation-integer ideal order is inferred through the comparison field.
theorem comparison_integer_maximal
    (n : ℕ) (u : ℤ_[p]ˣ) :
    comparisonRootInteger p k n u ∈
      IsLocalRing.maximalIdeal
        (Valuation.integer
          (NormedField.valuation (K := comparisonWittField p k n u))) := by
  apply norm_integer_maximal
  change ‖comparisonBasicRoot p k n u‖ < 1
  rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[p]]
  have hequiv := intermediate_witt_absolute p k n
    (comparisonWittField p k n u)
  apply hequiv.lt_one_iff.mp
  change wittAdicAbsolute p k n
      (algebraMap (B p k n) (C p k n) (basicWittRoot p k n u)) < 1
  apply ((IsDiscreteValuationRing.maximalIdeal (B p k n))
    |>.adicAbv_coe_lt_one_iff
      (show (1 : NNReal) < (2 : NNReal) by norm_num) _).mpr
  change basicWittRoot p k n u ∈ IsLocalRing.maximalIdeal (B p k n)
  rw [padic_witt_maximal]
  rw [← Ideal.span_singleton_eq_span_singleton.mpr
    (basic_witt_associated p k n u)]
  exact Ideal.mem_span_singleton_self _

set_option synthInstance.maxHeartbeats 500000 in
-- Principalizing the comparison-field maximal ideal uses its valuation-ring order.
theorem comparison_witt_maximal
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsLocalRing.maximalIdeal
        (Valuation.integer
          (NormedField.valuation (K := comparisonWittField p k n u))) =
      Ideal.span {comparisonRootInteger p k n u} := by
  let M := comparisonWittField p k n u
  let O := Valuation.integer (NormedField.valuation (K := M))
  let yB := basicWittRoot p k n u
  let yM := comparisonBasicRoot p k n u
  let yO := comparisonRootInteger p k n u
  apply le_antisymm
  · intro z hz
    have hznorm : ‖(z : M)‖ ≤ 1 := by
      have hzle := z.property
      change (NormedField.valuation (K := M)) (z : M) ≤ 1 at hzle
      rw [NormedField.valuation_apply] at hzle
      exact_mod_cast hzle
    have hzspec : spectralNorm ℚ_[p] M (z : M) ≤ 1 := by
      rw [← NormedAlgebra.norm_eq_spectralNorm ℚ_[p]]
      exact hznorm
    obtain ⟨b, hb⟩ :=
      (intermediate_field_spectral p k n M z).mp hzspec
    have hzlt : spectralNorm ℚ_[p] M (z : M) < 1 := by
      rw [← NormedAlgebra.norm_eq_spectralNorm ℚ_[p]]
      have hzv :=
        ((NormedField.valuation (K := M)).mem_maximalIdeal_iff).mp hz
      rw [NormedField.valuation_apply] at hzv
      exact_mod_cast hzv
    have hbabs : wittAdicAbsolute p k n
        (algebraMap (B p k n) (C p k n) b) < 1 := by
      rw [hb]
      exact (intermediate_witt_absolute p k n M)
        |>.lt_one_iff.mpr hzlt
    have hbmax : b ∈ IsLocalRing.maximalIdeal (B p k n) := by
      have hb' := ((IsDiscreteValuationRing.maximalIdeal (B p k n))
        |>.adicAbv_coe_lt_one_iff
          (show (1 : NNReal) < (2 : NNReal) by norm_num) _).mp hbabs
      exact hb'
    rw [padic_witt_maximal] at hbmax
    rw [← Ideal.span_singleton_eq_span_singleton.mpr
      (basic_witt_associated p k n u)] at hbmax
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hbmax
    let cC : C p k n := algebraMap (B p k n) (C p k n) c
    have hy0 : (yM : C p k n) ≠ 0 := by
      intro hzero
      have hroot : basicWittRoot p k n u ≠ 0 :=
        (basic_witt_associated p k n u).ne_zero_iff.mpr
          ((IsDiscreteValuationRing.irreducible_iff_uniformizer
            (cyclotomicWittRoot p k n)).mpr
              (padic_witt_maximal p k n)).ne_zero
      apply hroot
      apply IsFractionRing.injective (B p k n) (C p k n)
      simpa [yM, comparisonBasicRoot] using hzero
    have hprod : (z : C p k n) = (yM : C p k n) * cC := by
      rw [← hb, hc, map_mul]
      rfl
    have hcC : cC = (yM : C p k n)⁻¹ * (z : C p k n) := by
      rw [hprod]
      field_simp
    have hcM : cC ∈ M := by
      rw [hcC]
      exact M.mul_mem (M.inv_mem yM.property) z.val.property
    let cM : M := ⟨cC, hcM⟩
    have hcspec : spectralNorm ℚ_[p] M cM ≤ 1 := by
      apply (intermediate_field_spectral p k n M cM).mpr
      exact ⟨c, rfl⟩
    let cO : O := ⟨cM, by
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply,
        ← NNReal.coe_le_coe]
      change ‖cM‖ ≤ 1
      rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[p]]
      exact hcspec⟩
    rw [Ideal.mem_span_singleton]
    refine ⟨cO, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hprod
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact comparison_integer_maximal p k n u

noncomputable def basicFieldRoot
    (n : ℕ) (u : ℤ_[p]ˣ) : basicWittField p k n u :=
  ⟨algebraMap (B p k n) (C p k n) (basicWittRoot p k n u),
    ⟨(padicTateDatum p u).root ℚ_[p] n,
      basic_witt_fraction p k n u⟩⟩

noncomputable def basicRootInteger
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Valuation.integer
      (NormedField.valuation (K := basicWittField p k n u)) := by
  refine ⟨basicFieldRoot p k n u, ?_⟩
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply,
    ← NNReal.coe_le_coe]
  change ‖basicFieldRoot p k n u‖ ≤ 1
  rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[p]]
  exact (intermediate_field_spectral p k n
    (basicWittField p k n u) _).mpr ⟨basicWittRoot p k n u, rfl⟩

set_option maxHeartbeats 3000000 in
-- Showing the distinguished root is nonunit unfolds both Witt-field norms.
set_option synthInstance.maxHeartbeats 500000 in
-- The valuation-integer ideal order is inferred through the basic Witt field.
theorem basic_integer_maximal
    (n : ℕ) (u : ℤ_[p]ˣ) :
    basicRootInteger p k n u ∈
      IsLocalRing.maximalIdeal
        (Valuation.integer
          (NormedField.valuation (K := basicWittField p k n u))) := by
  apply norm_integer_maximal
  change ‖basicFieldRoot p k n u‖ < 1
  rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[p]]
  have hequiv := intermediate_witt_absolute p k n
    (basicWittField p k n u)
  apply hequiv.lt_one_iff.mp
  apply ((IsDiscreteValuationRing.maximalIdeal (B p k n))
    |>.adicAbv_coe_lt_one_iff
      (show (1 : NNReal) < (2 : NNReal) by norm_num) _).mpr
  change basicWittRoot p k n u ∈ IsLocalRing.maximalIdeal (B p k n)
  rw [padic_witt_maximal,
    ← Ideal.span_singleton_eq_span_singleton.mpr
      (basic_witt_associated p k n u)]
  exact Ideal.mem_span_singleton_self _

set_option synthInstance.maxHeartbeats 500000 in
-- Principalizing the basic-field maximal ideal uses its valuation-ring order.
theorem witt_integer_maximal
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsLocalRing.maximalIdeal
        (Valuation.integer
          (NormedField.valuation (K := basicWittField p k n u))) =
      Ideal.span {basicRootInteger p k n u} := by
  let F := basicWittField p k n u
  let O := Valuation.integer (NormedField.valuation (K := F))
  let yF := basicFieldRoot p k n u
  apply le_antisymm
  · intro z hz
    have hznorm : ‖(z : F)‖ ≤ 1 := by
      have hzle := z.property
      change (NormedField.valuation (K := F)) (z : F) ≤ 1 at hzle
      rw [NormedField.valuation_apply] at hzle
      exact_mod_cast hzle
    have hzspec : spectralNorm ℚ_[p] F (z : F) ≤ 1 := by
      rw [← NormedAlgebra.norm_eq_spectralNorm ℚ_[p]]
      exact hznorm
    obtain ⟨b, hb⟩ :=
      (intermediate_field_spectral p k n F z).mp hzspec
    have hzlt : spectralNorm ℚ_[p] F (z : F) < 1 := by
      rw [← NormedAlgebra.norm_eq_spectralNorm ℚ_[p]]
      have hzv := ((NormedField.valuation (K := F)).mem_maximalIdeal_iff).mp hz
      rw [NormedField.valuation_apply] at hzv
      exact_mod_cast hzv
    have hbabs : wittAdicAbsolute p k n
        (algebraMap (B p k n) (C p k n) b) < 1 := by
      rw [hb]
      exact (intermediate_witt_absolute p k n F)
        |>.lt_one_iff.mpr hzlt
    have hbmax : b ∈ IsLocalRing.maximalIdeal (B p k n) :=
      ((IsDiscreteValuationRing.maximalIdeal (B p k n))
        |>.adicAbv_coe_lt_one_iff
          (show (1 : NNReal) < (2 : NNReal) by norm_num) _).mp hbabs
    rw [padic_witt_maximal] at hbmax
    rw [← Ideal.span_singleton_eq_span_singleton.mpr
      (basic_witt_associated p k n u)] at hbmax
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hbmax
    let cC : C p k n := algebraMap (B p k n) (C p k n) c
    have hy0 : (yF : C p k n) ≠ 0 :=
      by
        intro hzero
        have hroot : basicWittRoot p k n u ≠ 0 :=
          (basic_witt_associated p k n u).ne_zero_iff.mpr
            ((IsDiscreteValuationRing.irreducible_iff_uniformizer
              (cyclotomicWittRoot p k n)).mpr
                (padic_witt_maximal p k n)).ne_zero
        apply hroot
        apply IsFractionRing.injective (B p k n) (C p k n)
        simpa [yF, basicFieldRoot] using hzero
    have hprod : (z : C p k n) = (yF : C p k n) * cC := by
      rw [← hb, hc, map_mul]
      rfl
    have hcC : cC = (yF : C p k n)⁻¹ * (z : C p k n) := by
      rw [hprod]
      field_simp
    have hcF : cC ∈ F := by
      rw [hcC]
      exact F.mul_mem (F.inv_mem yF.property) z.val.property
    let cF : F := ⟨cC, hcF⟩
    have hcspec : spectralNorm ℚ_[p] F cF ≤ 1 := by
      apply (intermediate_field_spectral p k n F cF).mpr
      exact ⟨c, rfl⟩
    let cO : O := ⟨cF, by
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply,
        ← NNReal.coe_le_coe]
      change ‖cF‖ ≤ 1
      rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[p]]
      exact hcspec⟩
    rw [Ideal.mem_span_singleton]
    refine ⟨cO, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hprod
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact basic_integer_maximal p k n u

/-- The sign in the norm of the distinguished root is cancelled by
negating the root. -/
theorem padic_basic_neg
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let D := padicTateDatum p u
    Algebra.norm ℚ_[p] (-D.root ℚ_[p] n) =
      algebraMap ℤ_[p] ℚ_[p] D.pi := by
  dsimp only
  let D := padicTateDatum p u
  let f := D.reducedPolynomial ℚ_[p] n
  let R := D.RootField ℚ_[p] n
  let pb : PowerBasis ℚ_[p] R :=
    AdjoinRoot.powerBasis (D.reducedPolynomial_irreducible ℚ_[p] n).ne_zero
  have hnormRoot : Algebra.norm ℚ_[p] (D.root ℚ_[p] n) =
      (-1 : ℚ_[p]) ^ f.natDegree * algebraMap ℤ_[p] ℚ_[p] D.pi := by
    have hmin : minpoly ℚ_[p] pb.gen = f := by
      dsimp only [pb, f]
      exact AdjoinRoot.minpoly_powerBasis_gen_of_monic
        (D.reducedPolynomial_monic ℚ_[p] n)
    have hpbdim : pb.dim = f.natDegree := by
      dsimp only [pb, f]
      exact AdjoinRoot.powerBasis_dim _
    change Algebra.norm ℚ_[p] pb.gen = _
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
    rw [hmin, hpbdim]
    exact congrArg ((-1 : ℚ_[p]) ^ f.natDegree * ·)
      (D.reduced_coeff_zero ℚ_[p] n)
  rw [show -D.root ℚ_[p] n =
      algebraMap ℚ_[p] R (-1) * D.root ℚ_[p] n by
        rw [map_neg, map_one, neg_one_mul],
    (Algebra.norm ℚ_[p]).map_mul, Algebra.norm_algebraMap, hnormRoot]
  have hdim : Module.finrank ℚ_[p] R = f.natDegree := by
    exact (D.finrank_rootField ℚ_[p] n).trans
      (D.reduced_nat_degree ℚ_[p] n).symm
  rw [hdim, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num
  simp [D]

theorem basic_ne_zero (n : ℕ) (u : ℤ_[p]ˣ) :
    basicFieldRoot p k n u ≠ 0 := by
  intro h
  have hB : basicWittRoot p k n u = 0 := by
    apply (IsFractionRing.injective (B p k n) (C p k n))
    simpa [basicFieldRoot] using congrArg Subtype.val h
  exact (basic_witt_associated p k n u).ne_zero_iff.mpr
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer
      (cyclotomicWittRoot p k n)).mpr
        (padic_witt_maximal p k n)).ne_zero hB

noncomputable def basicComparisonPrime
    (n : ℕ) (u : ℤ_[p]ˣ) : (basicWittField p k n u)ˣ :=
  Units.mk0 (-basicFieldRoot p k n u)
    (neg_ne_zero.mpr (basic_ne_zero p k n u))

set_option maxHeartbeats 3000000 in
-- Comparing the two equivalent valuations requires normalization through their value groups.
set_option synthInstance.maxHeartbeats 500000 in
-- The local valuation-ring order is inferred through the basic Witt field.
theorem basic_comparison_order (n : ℕ) (u : ℤ_[p]ˣ) :
    localUnitOrder (basicWittField p k n u)
      (Additive.ofMul (basicComparisonPrime p k n u)) = 1 := by
  apply (Submission.CField.NCorr.local_element_order
    (basicWittField p k n u) (basicComparisonPrime p k n u)).mp
  let F := basicWittField p k n u
  let OF := Valuation.integer (NormedField.valuation (K := F))
  let y : OF := -basicRootInteger p k n u
  have hspan : IsLocalRing.maximalIdeal OF = Ideal.span {y} := by
    rw [witt_integer_maximal]
    exact (Ideal.span_singleton_neg _).symm
  letI : ValuativeRel F := basic_valuative_rel p k n u
  change ValuativeRel.valuation F (-(basicFieldRoot p k n u)) =
    ValuativeRel.uniformizer F
  have hyNorm : ‖-(basicFieldRoot p k n u)‖ < 1 := by
    rw [norm_neg, NormedAlgebra.norm_eq_spectralNorm ℚ_[p]]
    apply (intermediate_witt_absolute p k n F)
      |>.lt_one_iff.mp
    apply ((IsDiscreteValuationRing.maximalIdeal (B p k n))
      |>.adicAbv_coe_lt_one_iff
        (show (1 : NNReal) < (2 : NNReal) by norm_num) _).mpr
    change basicWittRoot p k n u ∈ IsLocalRing.maximalIdeal (B p k n)
    rw [padic_witt_maximal,
      ← Ideal.span_singleton_eq_span_singleton.mpr
        (basic_witt_associated p k n u)]
    exact Ideal.mem_span_singleton_self _
  have hyNormVal : (NormedField.valuation (K := F))
      (-(basicFieldRoot p k n u)) < 1 := by
    rw [NormedField.valuation_apply, ← NNReal.coe_lt_coe]
    exact_mod_cast hyNorm
  have hylt : ValuativeRel.valuation F (-(basicFieldRoot p k n u)) < 1 :=
    (ValuativeRel.isEquiv (NormedField.valuation (K := F))
      (ValuativeRel.valuation F)).lt_one_iff_lt_one.mp hyNormVal
  apply le_antisymm
  · exact ValuativeRel.le_uniformizer_iff.mpr hylt
  · obtain ⟨pi, hpi⟩ :=
      ValuativeRel.valuation_surjective (K := F) (ValuativeRel.uniformizer F)
    have hpiValLt : ValuativeRel.valuation F pi < 1 := by
      rw [hpi]
      exact ValuativeRel.uniformizer_lt_one
    have hpiNormVal : (NormedField.valuation (K := F)) pi < 1 :=
      (ValuativeRel.isEquiv (NormedField.valuation (K := F))
        (ValuativeRel.valuation F)).lt_one_iff_lt_one.mpr hpiValLt
    have hpiNorm : ‖pi‖ < 1 := by
      rw [NormedField.valuation_apply, ← NNReal.coe_lt_coe] at hpiNormVal
      exact_mod_cast hpiNormVal
    let piO : OF := ⟨pi, le_of_lt hpiNormVal⟩
    have hpiMax : piO ∈ IsLocalRing.maximalIdeal OF :=
      norm_integer_maximal piO hpiNorm
    rw [hspan, Ideal.mem_span_singleton] at hpiMax
    obtain ⟨c, hc⟩ := hpiMax
    have hpiField : pi = -(basicFieldRoot p k n u) * (c : F) := by
      exact congrArg Subtype.val hc
    have hcNormVal : (NormedField.valuation (K := F)) (c : F) ≤ 1 :=
      c.property
    have hcVal : ValuativeRel.valuation F (c : F) ≤ 1 :=
      (ValuativeRel.isEquiv (NormedField.valuation (K := F))
        (ValuativeRel.valuation F)).le_one_iff_le_one.mp hcNormVal
    calc
      ValuativeRel.uniformizer F = ValuativeRel.valuation F pi := hpi.symm
      _ = ValuativeRel.valuation F (-(basicFieldRoot p k n u)) *
          ValuativeRel.valuation F (c : F) := by rw [hpiField, map_mul]
      _ ≤ ValuativeRel.valuation F (-(basicFieldRoot p k n u)) * 1 :=
        mul_le_mul_right hcVal _
      _ = ValuativeRel.valuation F (-(basicFieldRoot p k n u)) := mul_one _

noncomputable def padicUniformizerUnit (u : ℤ_[p]ˣ) : ℚ_[p]ˣ :=
  Units.mk0 (algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) * (u : ℤ_[p])))
    (by
      intro hzero
      apply mul_ne_zero (padic_int_ne p) u.ne_zero
      apply IsFractionRing.injective ℤ_[p] ℚ_[p]
      simpa using hzero)

theorem units_comparison_prime
    (n : ℕ) (u : ℤ_[p]ˣ) :
    normOnUnits ℚ_[p] (basicWittField p k n u)
        (basicComparisonPrime p k n u) =
      padicUniformizerUnit p u := by
  let D := padicTateDatum p u
  let R := D.RootField ℚ_[p] n
  let F := basicWittField p k n u
  let e : R ≃ₐ[ℚ_[p]] F := AlgEquiv.ofInjectiveField (basicAlgHom p k n u)
  apply Units.ext
  change Algebra.norm ℚ_[p] (-basicFieldRoot p k n u) =
    algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) * (u : ℤ_[p]))
  have heroot : e (D.root ℚ_[p] n) = basicFieldRoot p k n u := by
    apply Subtype.ext
    exact basic_witt_fraction p k n u
  have he : (algebraMap ℚ_[p] F).comp (RingEquiv.refl ℚ_[p]).toRingHom =
      e.toRingEquiv.toRingHom.comp (algebraMap ℚ_[p] R) := by
    apply RingHom.ext
    intro a
    exact (e.commutes a).symm
  calc
    Algebra.norm ℚ_[p] (-basicFieldRoot p k n u) =
        Algebra.norm ℚ_[p] (e (-D.root ℚ_[p] n)) := by
      apply congrArg (Algebra.norm ℚ_[p])
      rw [map_neg, heroot]
    _ = Algebra.norm ℚ_[p] (-D.root ℚ_[p] n) := by
      symm
      exact Algebra.norm_eq_of_equiv_equiv
        (RingEquiv.refl ℚ_[p]) e.toRingEquiv he (-D.root ℚ_[p] n)
    _ = algebraMap ℤ_[p] ℚ_[p] D.pi :=
      padic_basic_neg p n u
    _ = algebraMap ℤ_[p] ℚ_[p] ((p : ℤ_[p]) * (u : ℤ_[p])) := rfl

private abbrev comparisonNormInteger (n : ℕ) (u : ℤ_[p]ˣ) :=
  Valuation.integer
    (NormedField.valuation (K := comparisonWittField p k n u))

set_option maxHeartbeats 3000000 in
-- The ramification criterion unfolds both spectral integer rings.
set_option synthInstance.maxHeartbeats 300000 in
-- Finiteness of the integral closure is inferred through the comparison tower.
/-- The compositum of the cyclotomic and basic Lubin--Tate root fields is
unramified over the basic root field.  The point is that their spectral
integer rings have the same chosen uniformizer. -/
theorem comparison_witt_basic
    (n : ℕ) (u : ℤ_[p]ˣ) :
    FUExt.IsUnramified
      (basicWittField p k n u) (comparisonWittField p k n u) := by
  let F := basicWittField p k n u
  let M := comparisonWittField p k n u
  letI : Algebra F M := wittComparisonAlgebra p k n u
  letI : FiniteDimensional F M := wittComparisonDimensional p k n u
  let O₀ := comparisonNormInteger p k n u
  letI : IsDiscreteValuationRing O₀ :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (valuativeIntegerNorm M)
  letI : Finite (IsLocalRing.ResidueField O₀) :=
    Finite.of_equiv
      (IsLocalRing.ResidueField
        (Valuation.integer (ValuativeRel.valuation M)))
      (IsLocalRing.ResidueField.mapEquiv
        (valuativeIntegerNorm M)).toEquiv
  unfold FUExt.IsUnramified
  letI : Algebra.IsAlgebraic F M := Algebra.IsAlgebraic.of_finite F M
  letI hMfield : NormedField M := spectralNorm.normedField F M
  letI hMnorm : NontriviallyNormedField M :=
    spectralNorm.nontriviallyNormedField F M
  letI hMring : SeminormedRing M := spectralNorm.seminormedRing F M
  letI : NormedAlgebra F M := spectralNorm.normedAlgebra F M
  letI : IsUltrametricDist M := IsUltrametricDist.of_normedAlgebra F
  letI : (NormedField.valuation (K := F)).HasExtension
      (NormedField.valuation (K := M)) := spectralValuationExtension F M
  let OF := Valuation.integer (NormedField.valuation (K := F))
  let OM := Valuation.integer (NormedField.valuation (K := M))
  letI : IsDiscreteValuationRing OF :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (valuativeIntegerNorm F)
  have hOM : O₀ = OM := by
    ext x
    change spectralNorm ℚ_[p] M x ≤ 1 ↔ spectralNorm F M x ≤ 1
    rw [comparison_spectral_relative p k n u]
  let eO : O₀ ≃+* OM := RingEquiv.subringCongr hOM
  letI : IsDiscreteValuationRing OM :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eO
  letI : IsIntegralClosure OM OF M :=
    FLExt.spectral_integer_closure F M
  letI : Module.Finite OF OM := IsIntegralClosure.finite OF F M OM
  refine ⟨inferInstance, ?_⟩
  letI : Finite (IsLocalRing.ResidueField OF) :=
    Finite.of_equiv
      (IsLocalRing.ResidueField
        (Valuation.integer (ValuativeRel.valuation F)))
      (IsLocalRing.ResidueField.mapEquiv
        (valuativeIntegerNorm F)).toEquiv
  letI : Finite (IsLocalRing.ResidueField OM) :=
    Finite.of_equiv
      (IsLocalRing.ResidueField O₀)
      (IsLocalRing.ResidueField.mapEquiv eO).toEquiv
  letI : Algebra.IsSeparable (IsLocalRing.ResidueField OF)
      (IsLocalRing.ResidueField OM) := by infer_instance
  letI : IsLocalHom (algebraMap OF OM) :=
    Algebra.IsIntegral.isLocalHom OF OM
  apply Algebra.FormallyUnramified.of_map_maximalIdeal
  have hmaxM : IsLocalRing.maximalIdeal OM =
      Ideal.span {eO (comparisonRootInteger p k n u)} := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal eO,
      comparison_witt_maximal,
      Ideal.map_span, Set.image_singleton]
  rw [witt_integer_maximal, hmaxM,
    Ideal.map_span, Set.image_singleton]
  congr 2

noncomputable instance comparison_witt_galois
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsGalois (basicWittField p k n u) (comparisonWittField p k n u) :=
  FUExt.galoisUnramified
    (basicWittField p k n u) (comparisonWittField p k n u)
      (comparison_witt_basic p k n u)

set_option maxHeartbeats 3000000 in
-- Transporting commutativity through the canonical unramified level unfolds its Galois model.
set_option synthInstance.maxHeartbeats 500000 in
-- The relative module and canonical level form a deep finite-extension tower.
noncomputable instance comparison_witt_commutative
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsMulCommutative
      Gal(comparisonWittField p k n u/basicWittField p k n u) := by
  let F := basicWittField p k n u
  let M := comparisonWittField p k n u
  letI : Algebra F M := wittComparisonAlgebra p k n u
  letI : FiniteDimensional F M := wittComparisonDimensional p k n u
  have hU : FUExt.IsUnramified F M :=
    comparison_witt_basic p k n u
  let d := Module.finrank F M
  letI : NeZero d := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨e⟩ :=
    alg_unramified_level F M hU
  let U := canonicalUnramifiedLevel F d
  letI : IsMulCommutative Gal(U/F) := by
    letI : IsCyclic Gal(U/F) := unramified_level_cyclic F d
    exact IsCyclic.isMulCommutative
  exact ⟨⟨fun sigma tau ↦ by
    apply e.autCongr.injective
    simpa only [map_mul] using
      mul_comm (e.autCongr sigma) (e.autCongr tau)⟩⟩

/-- In the intrinsic spectral norm for the relative extension, the explicit
Witt automorphism is arithmetic Frobenius. -/
theorem comparison_witt_arithmetic
    (n : ℕ) (u : ℤ_[p]ˣ) (x : comparisonWittField p k n u)
    (hx : spectralNorm (basicWittField p k n u)
      (comparisonWittField p k n u) x ≤ 1) :
    spectralNorm (basicWittField p k n u)
        (comparisonWittField p k n u)
        (comparisonRelativeFrobenius p k n u x -
          x ^ localResidueCardinality (basicWittField p k n u)) < 1 := by
  rw [basic_witt_cardinality p k n u]
  rw [comparison_spectral_relative p k n u] at hx ⊢
  exact comparison_witt_relative p k n u x hx

set_option maxHeartbeats 5000000 in
-- Transporting arithmetic Frobenius through the canonical unramified level is expensive.
set_option synthInstance.maxHeartbeats 500000 in
-- The comparison-field algebra and finite-dimensional instances form a deep tower.
/-- Relative local reciprocity sends every normalized prime of the basic
field to the explicit Witt Frobenius on the unramified compositum. -/
theorem abelian_witt_uniformizer
    (n : ℕ) (u : ℤ_[p]ˣ)
    (varpi : (basicWittField p k n u)ˣ)
    (hvarpi : localUnitOrder (basicWittField p k n u)
      (Additive.ofMul varpi) = 1) :
    abelianArtinHom (basicWittField p k n u)
        (comparisonWittField p k n u) varpi =
      comparisonRelativeFrobenius p k n u := by
  let F := basicWittField p k n u
  let M := comparisonWittField p k n u
  letI : Algebra F M := wittComparisonAlgebra p k n u
  letI : FiniteDimensional F M := wittComparisonDimensional p k n u
  have hU : FUExt.IsUnramified F M :=
    comparison_witt_basic p k n u
  letI : Algebra.IsAlgebraic F M := Algebra.IsAlgebraic.of_finite F M
  letI hMfield : NormedField M := spectralNorm.normedField F M
  letI hMnorm : NontriviallyNormedField M :=
    spectralNorm.nontriviallyNormedField F M
  letI hMring : SeminormedRing M := spectralNorm.seminormedRing F M
  letI : NormedAlgebra F M := spectralNorm.normedAlgebra F M
  letI : IsUltrametricDist M := IsUltrametricDist.of_normedAlgebra F
  letI : ValuativeRel M := FLExt.valuativeRel F M
  letI : IsGalois F M :=
    FUExt.galoisUnramified F M hU
  let d := Module.finrank F M
  letI : NeZero d := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨e⟩ := alg_unramified_level
    F M hU
  let U := canonicalUnramifiedLevel F d
  letI : IsMulCommutative Gal(U/F) := by
    letI : IsCyclic Gal(U/F) := unramified_level_cyclic F d
    exact IsCyclic.isMulCommutative
  letI : IsMulCommutative Gal(M/F) := ⟨⟨fun sigma tau ↦ by
    apply e.autCongr.injective
    simpa only [map_mul] using mul_comm (e.autCongr sigma) (e.autCongr tau)⟩⟩
  apply abelian_artin_arithmetic
    F M d e (comparisonRelativeFrobenius p k n u)
  · exact comparison_witt_arithmetic p k n u
  · exact hvarpi

noncomputable instance basic_witt_dimensional
    (n : ℕ) (u : ℤ_[p]ˣ) :
    FiniteDimensional ℚ_[p] (wittFieldComparison p k n u) :=
  Module.Finite.equiv
    (basicWittComparison p k n u).toLinearEquiv

noncomputable instance (priority := 3000)
    basicWittFieldInComparison_isUltrametricDist
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsUltrametricDist (wittFieldComparison p k n u) := by
  constructor
  intro x y z
  change dist (x : comparisonWittField p k n u)
      (z : comparisonWittField p k n u) ≤
    max (dist (x : comparisonWittField p k n u)
      (y : comparisonWittField p k n u))
      (dist (y : comparisonWittField p k n u)
        (z : comparisonWittField p k n u))
  exact dist_triangle_max _ _ _

noncomputable instance comparison_valuative_rel
    (n : ℕ) (u : ℤ_[p]ˣ) :
    ValuativeRel (wittFieldComparison p k n u) := by
  letI : IsUltrametricDist (wittFieldComparison p k n u) :=
    basicWittFieldInComparison_isUltrametricDist p k n u
  exact ValuativeRel.ofValuation
    (@NormedField.valuation (wittFieldComparison p k n u)
      (inferInstance : NormedField (wittFieldComparison p k n u))
      (basicWittFieldInComparison_isUltrametricDist p k n u))

noncomputable instance witt_comparison_compatible
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Valuation.Compatible
      (@NormedField.valuation (wittFieldComparison p k n u)
        (inferInstance : NormedField (wittFieldComparison p k n u))
        (basicWittFieldInComparison_isUltrametricDist p k n u)) :=
  by
    letI : IsUltrametricDist (wittFieldComparison p k n u) :=
      basicWittFieldInComparison_isUltrametricDist p k n u
    exact Valuation.Compatible.ofValuation _

noncomputable instance basic_witt_comparison
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsNonarchimedeanLocalField (wittFieldComparison p k n u) := by
  let L := wittFieldComparison p k n u
  letI : IsUltrametricDist L := by
    dsimp only [L]
    exact basicWittFieldInComparison_isUltrametricDist p k n u
  letI : ValuativeRel L := by
    dsimp only [L]
    exact comparison_valuative_rel p k n u
  let hNF : NormedField L := inferInstance
  let hUltra : IsUltrametricDist L := inferInstance
  let v : Valuation L NNReal := @NormedField.valuation L hNF hUltra
  let valued : Valued L NNReal := @NormedField.toValued L hNF hUltra
  letI : v.Compatible := by
    dsimp only [v, hUltra, hNF, L]
    exact witt_comparison_compatible p k n u
  letI : ContinuousConstVAdd L L :=
    ⟨fun gamma ↦ by
      change Continuous (fun x : L ↦ gamma + x)
      exact Continuous.subtype_mk
        (continuous_const.add continuous_subtype_val) _⟩
  haveI htop : IsValuativeTopology L := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [show s ∈ nhds (0 : L) ↔
        ∃ gamma : (MonoidWithZeroHom.ValueGroup₀
            v)ˣ,
          {x | v.restrict x < gamma.1} ⊆ s from
      valued.is_topological_valuation s]
    simpa using
      v.exists_setOf_restrict_le_iff 0 s
  let F := basicWittField p k n u
  let eF : F ≃ₐ[ℚ_[p]] L := basicWittComparison p k n u
  have heNorm (x : F) : ‖eF x‖ = ‖x‖ := by
    change ‖algebraMap F (comparisonWittField p k n u) x‖ = ‖x‖
    exact algebra_spectral_tower
      (K := ℚ_[p]) (F := F) (E := comparisonWittField p k n u) x
  let ie : F ≃ᵢ L :=
    { eF.toEquiv with
      isometry_toFun := AddMonoidHomClass.isometry_of_norm eF heNorm }
  letI hlocallyCompact : LocallyCompactSpace L :=
    (ie.toHomeomorph.locallyCompactSpace_iff).mp inferInstance
  haveI hnontrivial : ValuativeRel.IsNontrivial L :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      v).mpr inferInstance
  exact
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := hnontrivial }

noncomputable instance witt_comparison_dimensional
    (n : ℕ) (u : ℤ_[p]ˣ) :
    FiniteDimensional (wittFieldComparison p k n u)
      (comparisonWittField p k n u) :=
  FiniteDimensional.right ℚ_[p] _ _

noncomputable instance witt_comparison_galois
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsGalois (wittFieldComparison p k n u)
      (comparisonWittField p k n u) :=
  IsGalois.tower_top_of_isGalois ℚ_[p]
    (wittFieldComparison p k n u) (comparisonWittField p k n u)

set_option maxHeartbeats 3000000 in
-- The mixed-universe Galois equivalence unfolds both embedded base fields.
set_option synthInstance.maxHeartbeats 500000 in
-- Transporting the Galois group across the embedded basic field needs the full algebra tower.
noncomputable instance witt_comparison_commutative
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsMulCommutative
      Gal(comparisonWittField p k n u/wittFieldComparison p k n u) := by
  let F := basicWittField p k n u
  let M := comparisonWittField p k n u
  letI : Algebra F M := wittComparisonAlgebra p k n u
  letI : IsMulCommutative Gal(M/F) :=
    comparison_witt_commutative p k n u
  let eF : F ≃ₐ[ℚ_[p]] wittFieldComparison p k n u :=
    basicWittComparison p k n u
  letI : Algebra F (wittFieldComparison p k n u) :=
    eF.toAlgHom.toAlgebra
  let eBase : wittFieldComparison p k n u ≃ₐ[F] F :=
    { eF.symm.toRingEquiv with
      commutes' := fun x ↦ eF.symm_apply_apply x }
  let i : M ≃+* M := RingEquiv.refl M
  have hbase (a : F) :
      i (algebraMap F M a) =
        algebraMap (wittFieldComparison p k n u) M
          (algebraMap F (wittFieldComparison p k n u) a) := by
    rfl
  let g : Gal(M/F) ≃* Gal(M/wittFieldComparison p k n u) :=
    mixedUniverseGal eBase i hbase
  exact ⟨⟨fun sigma tau ↦ by
    apply g.symm.injective
    simpa only [map_mul] using mul_comm (g.symm sigma) (g.symm tau)⟩⟩


end
end Submission.CField.LRecip.PNProof
