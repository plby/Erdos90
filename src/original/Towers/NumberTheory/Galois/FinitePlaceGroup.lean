import Towers.NumberTheory.Galois.DecompositionGroup
import Towers.NumberTheory.Locals.NonarchimedeanClassification
import Towers.ClassField.IdeleCohomology.CompletionConjugation
import Towers.ClassField.IdeleCohomology.CompletionProductAction
import Towers.ClassField.Ideles.FinitePlaceCompletion


/-!
# Ideal and finite-place decomposition groups

For a finite place of a number field, the stabilizer of its height-one prime
ideal is the same subgroup as the stabilizer of its normalized absolute value.
This identifies the ideal-theoretic decomposition groups used by ramification
theory with the absolute-value decomposition groups acting on completions.
-/

namespace Towers.NumberTheory.Milne

open AbsoluteValue IsDedekindDomain NumberField
open Towers.CField.ICohomo
open Towers.CField.Ideles
open scoped Pointwise

noncomputable section

universe u

variable {K L : Type u} [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance ringOfIntegersGaloisAction :
    MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction
    (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L)

omit [NumberField L] [FiniteDimensional K L] in
private theorem fixed_inv_smul
    (P : HeightOneSpectrum (NumberField.RingOfIntegers L))
    (sigma : Gal(L/K)) (hP : sigma • P.asIdeal = P.asIdeal)
    (x : NumberField.RingOfIntegers L) (n : ℕ) :
    sigma⁻¹ • x ∈ P.asIdeal ^ n ↔ x ∈ P.asIdeal ^ n := by
  have hPinv : sigma⁻¹ • P.asIdeal = P.asIdeal := by
    calc
      sigma⁻¹ • P.asIdeal = sigma⁻¹ • (sigma • P.asIdeal) := by rw [hP]
      _ = P.asIdeal := inv_smul_smul sigma P.asIdeal
  have hPpow : sigma⁻¹ • (P.asIdeal ^ n) = P.asIdeal ^ n := by
    change Ideal.map (MulSemiringAction.toRingHom _ _ sigma⁻¹)
        (P.asIdeal ^ n) = P.asIdeal ^ n
    rw [Ideal.map_pow]
    change (sigma⁻¹ • P.asIdeal) ^ n = P.asIdeal ^ n
    rw [hPinv]
  conv_lhs => rw [← hPpow]
  exact Ideal.smul_mem_pointwise_smul_iff

omit [FiniteDimensional K L] in
private theorem fixed_valuation_smul
    (P : HeightOneSpectrum (NumberField.RingOfIntegers L))
    (sigma : Gal(L/K)) (hP : sigma • P.asIdeal = P.asIdeal)
    (x : NumberField.RingOfIntegers L) :
    P.intValuation (sigma⁻¹ • x) = P.intValuation x := by
  by_cases hx : x = 0
  · subst x
    simp
  have hsx : sigma⁻¹ • x ≠ 0 := by
    intro hzero
    apply hx
    have := congrArg (fun y => sigma • y) hzero
    simpa using this
  let nx : ℕ :=
    (Associates.mk P.asIdeal).count
      (Associates.mk (Ideal.span {x} : Ideal (NumberField.RingOfIntegers L))).factors
  let nsx : ℕ :=
    (Associates.mk P.asIdeal).count
      (Associates.mk (Ideal.span {sigma⁻¹ • x} :
        Ideal (NumberField.RingOfIntegers L))).factors
  have hxval : P.intValuation x = WithZero.exp (-(nx : ℤ)) := by
    simpa [nx] using P.intValuation_if_neg hx
  have hsxval : P.intValuation (sigma⁻¹ • x) =
      WithZero.exp (-(nsx : ℤ)) := by
    simpa [nsx] using P.intValuation_if_neg hsx
  apply le_antisymm
  · rw [hxval]
    apply (P.intValuation_le_pow_iff_mem (sigma⁻¹ • x) nx).2
    exact (fixed_inv_smul P sigma hP x nx).2
      ((P.intValuation_le_pow_iff_mem x nx).1 (hxval.le))
  · rw [hsxval]
    apply (P.intValuation_le_pow_iff_mem x nsx).2
    exact (fixed_inv_smul P sigma hP x nsx).1
      ((P.intValuation_le_pow_iff_mem (sigma⁻¹ • x) nsx).1 hsxval.le)

omit [FiniteDimensional K L] in
private theorem fixed_valuation_symm
    (P : HeightOneSpectrum (NumberField.RingOfIntegers L))
    (sigma : Gal(L/K)) (hP : sigma • P.asIdeal = P.asIdeal)
    (x : L) :
    P.valuation L (sigma.symm x) = P.valuation L x := by
  obtain ⟨a, b, hb, rfl⟩ :=
    IsFractionRing.div_surjective (NumberField.RingOfIntegers L) x
  rw [map_div₀ sigma.symm]
  rw [map_div₀ (P.valuation L), map_div₀ (P.valuation L)]
  have haMap := algebraMap_galRestrict_apply
    (A := NumberField.RingOfIntegers K) (K := K) (L := L)
    (B := NumberField.RingOfIntegers L) sigma⁻¹ a
  have hbMap := algebraMap_galRestrict_apply
    (A := NumberField.RingOfIntegers K) (K := K) (L := L)
    (B := NumberField.RingOfIntegers L) sigma⁻¹ b
  change P.valuation L
        ((sigma⁻¹ : Gal(L/K)) (algebraMap (NumberField.RingOfIntegers L) L a)) /
      P.valuation L
        ((sigma⁻¹ : Gal(L/K)) (algebraMap (NumberField.RingOfIntegers L) L b)) = _
  rw [← haMap, ← hbMap, P.valuation_of_algebraMap, P.valuation_of_algebraMap,
    P.valuation_of_algebraMap, P.valuation_of_algebraMap]
  change P.intValuation (sigma⁻¹ • a) / P.intValuation (sigma⁻¹ • b) =
    P.intValuation a / P.intValuation b
  rw [
    fixed_valuation_smul P sigma hP a,
    fixed_valuation_smul P sigma hP b]

omit [FiniteDimensional K L] in
/-- An automorphism stabilizing a height-one prime also stabilizes the
normalized finite absolute value attached to it. -/
theorem place_stabilizer_ideal
    (P : HeightOneSpectrum (NumberField.RingOfIntegers L))
    (sigma : Gal(L/K))
    (hP : sigma ∈ MulAction.stabilizer Gal(L/K) P.asIdeal) :
    sigma ∈ MulAction.stabilizer Gal(L/K) (FinitePlace.mk P).val := by
  rw [MulAction.mem_stabilizer_iff] at hP ⊢
  apply AbsoluteValue.ext
  intro x
  change (FinitePlace.mk P).val (sigma.symm x) = (FinitePlace.mk P).val x
  change ‖FinitePlace.embedding P (sigma.symm x)‖ =
    ‖FinitePlace.embedding P x‖
  rw [FinitePlace.norm_embedding', FinitePlace.norm_embedding',
    fixed_valuation_symm P sigma hP x]

omit [FiniteDimensional K L] in
/-- Stabilizing a normalized finite absolute value forces stabilization of
its height-one prime ideal. -/
theorem ideal_stabilizer_place
    (P : HeightOneSpectrum (NumberField.RingOfIntegers L))
    (sigma : Gal(L/K))
    (hP : sigma ∈ MulAction.stabilizer Gal(L/K) (FinitePlace.mk P).val) :
    sigma ∈ MulAction.stabilizer Gal(L/K) P.asIdeal := by
  rw [MulAction.mem_stabilizer_iff] at hP ⊢
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have hval := DFunLike.congr_fun hP
    (algebraMap (NumberField.RingOfIntegers L) L x)
  change (FinitePlace.mk P).val
      (sigma.symm (algebraMap (NumberField.RingOfIntegers L) L x)) =
    (FinitePlace.mk P).val
      (algebraMap (NumberField.RingOfIntegers L) L x) at hval
  have hxMap := algebraMap_galRestrict_apply
    (A := NumberField.RingOfIntegers K) (K := K) (L := L)
    (B := NumberField.RingOfIntegers L) sigma⁻¹ x
  change ‖FinitePlace.embedding P
      ((sigma⁻¹ : Gal(L/K))
        (algebraMap (NumberField.RingOfIntegers L) L x))‖ =
    ‖FinitePlace.embedding P
      (algebraMap (NumberField.RingOfIntegers L) L x)‖ at hval
  rw [← hxMap] at hval
  rw [← FinitePlace.norm_lt_one_iff_mem L P,
    ← FinitePlace.norm_lt_one_iff_mem L P]
  simpa using congrArg (fun r : ℝ => r < 1) hval

omit [FiniteDimensional K L] in
/-- The ideal-theoretic and absolute-value decomposition groups at a finite
place are literally the same subgroup of the global Galois group. -/
theorem stabilizer_finite_place
    (P : HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    MulAction.stabilizer Gal(L/K) P.asIdeal =
      MulAction.stabilizer Gal(L/K) (FinitePlace.mk P).val := by
  ext sigma
  constructor
  · exact place_stabilizer_ideal P sigma
  · exact ideal_stabilizer_place P sigma

omit [FiniteDimensional K L] in
/-- Stabilizing a nontrivial nonarchimedean absolute value stabilizes its
centered height-one prime. -/
theorem centered_stabilizer_absolute
    (w : AbsoluteValue L ℝ) (hw : w.IsNontrivial)
    (hna : IsNonarchimedean w) (sigma : Gal(L/K))
    (hsigma : sigma ∈ MulAction.stabilizer Gal(L/K) w) :
    sigma ∈ MulAction.stabilizer Gal(L/K)
      (nonarchimedeanHeightSpectrum w hw hna).asIdeal := by
  let P := nonarchimedeanHeightSpectrum w hw hna
  rw [MulAction.mem_stabilizer_iff] at hsigma ⊢
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  change
    w (algebraMap (NumberField.RingOfIntegers L) L (sigma⁻¹ • x)) < 1 ↔
      w (algebraMap (NumberField.RingOfIntegers L) L x) < 1
  have hxMap := algebraMap_galRestrict_apply
    (A := NumberField.RingOfIntegers K) (K := K) (L := L)
    (B := NumberField.RingOfIntegers L) sigma⁻¹ x
  change w (algebraMap (NumberField.RingOfIntegers L) L
      ((galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L)) sigma⁻¹ x)) < 1 ↔ _
  rw [hxMap]
  simpa using congrArg (fun r : ℝ => r < 1)
    (DFunLike.congr_fun hsigma
      (algebraMap (NumberField.RingOfIntegers L) L x))

omit [FiniteDimensional K L] in
/-- Stabilizing the centered prime of an extending nonarchimedean absolute
value stabilizes the absolute value itself. -/
theorem absolute_stabilizer_centered
    (w : AbsoluteValue L ℝ) (hw : w.IsNontrivial)
    (hna : IsNonarchimedean w) (sigma : Gal(L/K))
    (hsigma : sigma ∈ MulAction.stabilizer Gal(L/K)
      (nonarchimedeanHeightSpectrum w hw hna).asIdeal) :
    sigma ∈ MulAction.stabilizer Gal(L/K) w := by
  let P := nonarchimedeanHeightSpectrum w hw hna
  have hfinite : sigma ∈ MulAction.stabilizer Gal(L/K) (FinitePlace.mk P).val :=
    place_stabilizer_ideal P sigma hsigma
  have hequiv : w.IsEquiv (FinitePlace.mk P).val :=
    place_centered_prime w hw hna
  obtain ⟨c, hc, hpow⟩ :=
    AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp hequiv
  rw [MulAction.mem_stabilizer_iff] at hfinite ⊢
  apply AbsoluteValue.ext
  intro x
  apply (Real.rpow_left_inj (w.nonneg _) (w.nonneg _) hc.ne').mp
  calc
    w (sigma.symm.toRingEquiv.toRingHom x) ^ c =
        (FinitePlace.mk P).val (sigma.symm.toRingEquiv.toRingHom x) :=
      congrFun hpow _
    _ = (FinitePlace.mk P).val x :=
      congrArg (fun a : AbsoluteValue L ℝ => a x) hfinite
    _ = w x ^ c := (congrFun hpow x).symm

omit [FiniteDimensional K L] in
/-- For an arbitrary nontrivial nonarchimedean absolute value, its
decomposition subgroup is the ideal-theoretic decomposition subgroup of its
centered prime. -/
theorem centered_stabilizer_value
    (w : AbsoluteValue L ℝ) (hw : w.IsNontrivial)
    (hna : IsNonarchimedean w) :
    MulAction.stabilizer Gal(L/K)
        (nonarchimedeanHeightSpectrum w hw hna).asIdeal =
      MulAction.stabilizer Gal(L/K) w := by
  ext sigma
  constructor
  · exact absolute_stabilizer_centered
      w hw hna sigma
  · exact centered_stabilizer_absolute
      w hw hna sigma

omit [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- The pointwise definition of the absolute-value decomposition group agrees
with the stabilizer for the conjugation action on absolute values. -/
theorem absolute_decomposition_stabilizer
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) :
    absoluteValueDecomposition v w =
      MulAction.stabilizer Gal(L/K) w := by
  ext sigma
  constructor
  · intro hsigma
    rw [MulAction.mem_stabilizer_iff]
    apply AbsoluteValue.ext
    intro x
    change w (sigma.symm x) = w x
    simpa using (hsigma (sigma.symm x)).symm
  · intro hsigma x
    rw [MulAction.mem_stabilizer_iff] at hsigma
    have h := congrArg (fun a : AbsoluteValue L ℝ => a (sigma x)) hsigma
    simpa using h.symm

omit [FiniteDimensional K L] in
/-- The ideal decomposition group of the centered prime is the completion
decomposition group attached to the extending absolute value. -/
theorem centered_stabilizer_decomposition
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ)
    (hw : w.IsNontrivial) (hna : IsNonarchimedean w) :
    MulAction.stabilizer Gal(L/K)
        (nonarchimedeanHeightSpectrum w hw hna).asIdeal =
      absoluteValueDecomposition v w := by
  rw [centered_stabilizer_value w hw hna,
    absolute_decomposition_stabilizer v w]

omit [FiniteDimensional K L] in
/-- Galois conjugation transports the centered prime of a nonarchimedean
absolute value by the ideal action. -/
theorem centered_smul_ideal
    (w : AbsoluteValue L ℝ) (hw : w.IsNontrivial)
    (hna : IsNonarchimedean w) (sigma : Gal(L/K)) :
    (nonarchimedeanHeightSpectrum (sigma • w)
        (by
          obtain ⟨x, hx0, hx1⟩ := hw
          refine ⟨sigma x, ?_, ?_⟩
          · simpa only [map_zero] using sigma.injective.ne hx0
          simpa using hx1)
        (by
          intro x y
          change w (sigma.symm (x + y)) ≤
            max (w (sigma.symm x)) (w (sigma.symm y))
          rw [map_add]
          exact hna _ _)).asIdeal =
      sigma • (nonarchimedeanHeightSpectrum w hw hna).asIdeal := by
  apply Ideal.ext
  intro x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  change w (sigma.symm
      (algebraMap (NumberField.RingOfIntegers L) L x)) < 1 ↔
    w (algebraMap (NumberField.RingOfIntegers L) L (sigma⁻¹ • x)) < 1
  have hxMap := algebraMap_galRestrict_apply
    (A := NumberField.RingOfIntegers K) (K := K) (L := L)
    (B := NumberField.RingOfIntegers L) sigma⁻¹ x
  change w ((sigma⁻¹ : Gal(L/K))
      (algebraMap (NumberField.RingOfIntegers L) L x)) < 1 ↔
    w (algebraMap (NumberField.RingOfIntegers L) L
      ((galRestrict (NumberField.RingOfIntegers K) K L
        (NumberField.RingOfIntegers L)) sigma⁻¹ x)) < 1
  rw [hxMap]

/-- The Galois action on the extensions of an arbitrary nontrivial
nonarchimedean absolute value is transitive. -/
theorem above_pretr_nonar
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion] (hvna : IsNonarchimedean v) :
    MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v) := by
  let hv : v.IsNontrivial := Fact.out
  let p := nonarchimedeanHeightSpectrum v hv hvna
  constructor
  intro w₁ w₂
  have hw₁ : w₁.1.IsNontrivial := absolute_extension_nontrivial v w₁
  have hw₂ : w₂.1.IsNontrivial := absolute_extension_nontrivial v w₂
  have hna₁ : IsNonarchimedean w₁.1 :=
    absolute_extension_nonarchimedean v w₁
  have hna₂ : IsNonarchimedean w₂.1 :=
    absolute_extension_nonarchimedean v w₂
  let P₁ := nonarchimedeanHeightSpectrum w₁.1 hw₁ hna₁
  let P₂ := nonarchimedeanHeightSpectrum w₂.1 hw₂ hna₂
  letI : P₁.asIdeal.LiesOver p.asIdeal :=
    nonarchimedean_spectrum_centered
      v w₁.1 w₁.2 hv hvna hw₁ hna₁
  letI : P₂.asIdeal.LiesOver p.asIdeal :=
    nonarchimedean_spectrum_centered
      v w₂.1 w₂.2 hv hvna hw₂ hna₂
  letI : IsGaloisGroup Gal(L/K)
      (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K)
      (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) K L
  obtain ⟨sigma, hsigma⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    p.asIdeal P₁.asIdeal P₂.asIdeal Gal(L/K)
  refine ⟨sigma, Subtype.ext ?_⟩
  have hswNontrivial : (sigma • w₁.1).IsNontrivial := by
    obtain ⟨x, hx0, hx1⟩ := hw₁
    refine ⟨sigma x, ?_, ?_⟩
    · simpa only [map_zero] using sigma.injective.ne hx0
    simpa using hx1
  have hswNonarch : IsNonarchimedean (sigma • w₁.1) := by
    intro x y
    change w₁.1 (sigma.symm (x + y)) ≤
      max (w₁.1 (sigma.symm x)) (w₁.1 (sigma.symm y))
    rw [map_add]
    exact hna₁ _ _
  have hcenter :
      (nonarchimedeanHeightSpectrum (sigma • w₁.1)
          hswNontrivial hswNonarch).asIdeal = P₂.asIdeal := by
    rw [centered_smul_ideal w₁.1 hw₁ hna₁ sigma]
    exact hsigma
  have hequiv₁ :
      (sigma • w₁.1).IsEquiv (FinitePlace.mk P₂).val := by
    have h := place_centered_prime
      (sigma • w₁.1) hswNontrivial hswNonarch
    rw [HeightOneSpectrum.ext_iff.mpr hcenter] at h
    exact h
  have hequiv₂ : w₂.1.IsEquiv (FinitePlace.mk P₂).val :=
    place_centered_prime w₂.1 hw₂ hna₂
  apply absolute_value_lies
    (v := v) (sigma • w₁.1) w₂.1
      (sigma • w₁).2 w₂.2
  exact hequiv₁.trans hequiv₂.symm

/-- The Galois action on the extensions of a finite place is transitive. -/
theorem completion_above_pretransitive
    (p : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) (FinitePlace.mk p).val) := by
  let v := (FinitePlace.mk p).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial p⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist p
  constructor
  intro w₁ w₂
  have hw₁ : w₁.1.IsNontrivial := absolute_extension_nontrivial v w₁
  have hw₂ : w₂.1.IsNontrivial := absolute_extension_nontrivial v w₂
  have hna₁ : IsNonarchimedean w₁.1 :=
    absolute_extension_nonarchimedean v w₁
  have hna₂ : IsNonarchimedean w₂.1 :=
    absolute_extension_nonarchimedean v w₂
  let P₁ := nonarchimedeanHeightSpectrum w₁.1 hw₁ hna₁
  let P₂ := nonarchimedeanHeightSpectrum w₂.1 hw₂ hna₂
  letI : P₁.asIdeal.LiesOver p.asIdeal :=
    nonarchimedean_spectrum_lies p w₁.1 w₁.2 hw₁ hna₁
  letI : P₂.asIdeal.LiesOver p.asIdeal :=
    nonarchimedean_spectrum_lies p w₂.1 w₂.2 hw₂ hna₂
  letI : IsGaloisGroup Gal(L/K)
      (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K)
      (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) K L
  obtain ⟨sigma, hsigma⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    p.asIdeal P₁.asIdeal P₂.asIdeal Gal(L/K)
  refine ⟨sigma, Subtype.ext ?_⟩
  have hswNontrivial : (sigma • w₁.1).IsNontrivial := by
    obtain ⟨x, hx0, hx1⟩ := hw₁
    refine ⟨sigma x, ?_, ?_⟩
    · simpa only [map_zero] using sigma.injective.ne hx0
    simpa using hx1
  have hswNonarch : IsNonarchimedean (sigma • w₁.1) := by
    intro x y
    change w₁.1 (sigma.symm (x + y)) ≤
      max (w₁.1 (sigma.symm x)) (w₁.1 (sigma.symm y))
    rw [map_add]
    exact hna₁ _ _
  have hcenter :
      (nonarchimedeanHeightSpectrum (sigma • w₁.1)
          hswNontrivial hswNonarch).asIdeal = P₂.asIdeal := by
    rw [centered_smul_ideal w₁.1 hw₁ hna₁ sigma]
    exact hsigma
  have hequiv₁ :
      (sigma • w₁.1).IsEquiv (FinitePlace.mk P₂).val := by
    have h := place_centered_prime
      (sigma • w₁.1) hswNontrivial hswNonarch
    rw [HeightOneSpectrum.ext_iff.mpr hcenter] at h
    exact h
  have hequiv₂ : w₂.1.IsEquiv (FinitePlace.mk P₂).val :=
    place_centered_prime w₂.1 hw₂ hna₂
  apply absolute_value_lies
    (v := v) (sigma • w₁.1) w₂.1
      (sigma • w₁).2 w₂.2
  exact hequiv₁.trans hequiv₂.symm

end

end Towers.NumberTheory.Milne
