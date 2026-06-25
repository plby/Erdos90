import Towers.ClassField.GrunwaldWang.LocalArtinKernel
import Towers.ClassField.GrunwaldWang.AlgebraGlobalCompatibility
import Towers.NumberTheory.Locals.ArchimedeanPlaceClassification
import Towers.ClassField.Ideles.FinitePlaceCompletion

/-!
# Theorem VIII.2.3: comparison of finite completion norm models

The finite local Artin API uses absolute-value completions, whereas the idèle
norm uses the prime-adic factors of the semilocal completion.  This file
compares the two algebra structures and transports their norm ranges.
-/

namespace Towers.CField.GWang

open Ideal IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.LFTheory
open Towers.CField.Ideles

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- The canonical comparison from the absolute-value completion to the
prime-adic completion is continuous. -/
private theorem continuous_place_adic
    (P : HeightOneSpectrum (RingOfIntegers K)) :
    Continuous (placeCompletionAdic P) := by
  let h := completion_universal (FinitePlace.mk P).val
    (FinitePlace.embedding P) (by
      intro x
      exact (FinitePlace.mk_apply P x).symm)
  change Continuous h.choose
  exact h.choose_spec.1.1.continuous

set_option backward.isDefEq.respectTransparency false in
/-- Equivalent absolute values induce the identity on the dense copy of the
underlying field inside their completions. -/
private theorem completion_equiv_embedding
    {F : Type*} [Field F] {v u : AbsoluteValue F ℝ}
    (h : v.IsEquiv u) (x : F) :
    completionRing h (completionEmbedding v x) =
      completionEmbedding u x := by
  have hc : Continuous (WithAbs.congr v u (.refl F)) :=
    ((AbsoluteValue.isEquiv_iff_isHomeomorph v u).1 h).continuous
  rw [completionEmbedding_apply, completionEmbedding_apply]
  unfold completionRing
  rw [UniformSpace.Completion.mapRingEquiv_apply]
  exact UniformSpace.Completion.map_coe
    (uniformContinuous_addMonoidHom_of_continuous hc) _

set_option maxHeartbeats 1000000 in
-- Transporting both the base and extension fields transports the algebra
-- norm and hence its range on unit groups.
private theorem norm_comap_units
    {A₁ B₁ A₂ B₂ : Type*}
    [Field A₁] [Field B₁] [Field A₂] [Field B₂]
    [Algebra A₁ B₁] [Algebra A₂ B₂]
    [FiniteDimensional A₁ B₁] [FiniteDimensional A₂ B₂]
    (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : (algebraMap A₂ B₂).comp e₁.toRingHom =
      e₂.toRingHom.comp (algebraMap A₁ B₁)) :
    (normSubgroup A₁ B₁).comap (Units.map e₁.symm.toRingHom) =
      normSubgroup A₂ B₂ := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Units.map e₂.toRingHom y, ?_⟩
    apply Units.ext
    change Algebra.norm A₂ (e₂ (y : B₁)) = (x : A₂)
    have hn := Algebra.norm_eq_of_equiv_equiv e₁ e₂ he (y : B₁)
    change Algebra.norm A₁ (y : B₁) =
      e₁.symm (Algebra.norm A₂ (e₂ (y : B₁))) at hn
    have hy' := congrArg Units.val hy
    change Algebra.norm A₁ (y : B₁) = e₁.symm (x : A₂) at hy'
    apply e₁.symm.injective
    rw [← hn, ← hy']
  · rintro ⟨y, hy⟩
    refine ⟨Units.map e₂.symm.toRingHom y, ?_⟩
    apply Units.ext
    change Algebra.norm A₁ (e₂.symm (y : B₂)) = e₁.symm (x : A₂)
    have hn := Algebra.norm_eq_of_equiv_equiv e₁ e₂ he
      (e₂.symm (y : B₂))
    rw [e₂.apply_symm_apply] at hn
    have hy' := congrArg Units.val hy
    change Algebra.norm A₂ (y : B₂) = (x : A₂) at hy'
    rw [hn, hy']

set_option synthInstance.maxHeartbeats 300000 in
-- The absolute-value and prime-adic completion models synthesize together here.
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
omit [FiniteDimensional K L] in
/-- The norm range in an absolute-value completion above a finite place,
transported to the prime-adic base completion, is the concrete norm range
used in the idèle norm. -/
theorem completion_norm_range
    (P : HeightOneSpectrum (RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L) P)
    (w : AbsoluteValue L ℝ)
    (hwv : AbsoluteValue.LiesOver w (FinitePlace.mk P).val)
    (hwq : w.IsEquiv
      (FinitePlace.mk (upperPrime (K := K) (L := L) P Q)).val)
    (hfinite : let v := (FinitePlace.mk P).val
      letI : Algebra v.Completion w.Completion :=
        (completionLies v w hwv).toAlgebra
      Module.Finite v.Completion w.Completion) :
    let v := (FinitePlace.mk P).val
    letI : Algebra v.Completion w.Completion :=
      (completionLies v w hwv).toAlgebra
    (normSubgroup v.Completion w.Completion).comap
        (Units.map
          (placeCompletionAdic P).symm.toRingHom) =
      (finiteCompletionNorm (K := K) (L := L) P Q).range := by
  let v := (FinitePlace.mk P).val
  let q := upperPrime (K := K) (L := L) P Q
  let eK := placeCompletionAdic P
  let eL := (completionRing hwq).trans
    (placeCompletionAdic q)
  let C := P.adicCompletionIntegers K
  let D := q.adicCompletionIntegers L
  let hP : P.asIdeal.map
      (algebraMap (RingOfIntegers K) (RingOfIntegers L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot P.ne_bot
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Algebra v.Completion w.Completion :=
    (completionLies v w hwv).toAlgebra
  letI : Module.Finite v.Completion w.Completion := hfinite
  letI : Algebra (P.adicCompletion K) (q.adicCompletion L) :=
    adicFactorAlgebra
      (K := K) (L := L) P hP Q
  letI : Module.Finite (P.adicCompletion K) (q.adicCompletion L) :=
    finite_completion_module (K := K) (L := L) P Q
  letI : Algebra C D :=
    adicCompletionAlgebra
      (K := K) (L := L) P hP Q
  letI : Algebra C (q.adicCompletion L) :=
    adicIntegerAlgebra
      (K := K) (L := L) P hP Q
  have hfield := factor_algebra_global
    (K := K) (L := L) P Q
  have hintegers (c : C) :
      algebraMap (P.adicCompletion K) (q.adicCompletion L) (c : P.adicCompletion K) =
        algebraMap D (q.adicCompletion L) (algebraMap C D c) := by
    calc
      algebraMap (P.adicCompletion K) (q.adicCompletion L)
          (c : P.adicCompletion K) = algebraMap C (q.adicCompletion L) c :=
        (adic_integer_algebra
          (K := K) (L := L) P hP Q c).symm
      _ = algebraMap D (q.adicCompletion L) (algebraMap C D c) := by
        rfl
  obtain ⟨r, hr0⟩ := Submodule.nonzero_mem_of_bot_lt
    (bot_lt_iff_ne_bot.mpr P.ne_bot)
  let pi : P.adicCompletion K :=
    FinitePlace.embedding P (algebraMap (RingOfIntegers K) K (r : RingOfIntegers K))
  have hpi : pi ≠ 0 := by
    dsimp only [pi]
    apply (map_ne_zero (FinitePlace.embedding P)).2
    intro h
    have hr : (r : RingOfIntegers K) = 0 :=
      (FaithfulSMul.algebraMap_injective (RingOfIntegers K) K)
        (h.trans (map_zero _).symm)
    exact hr0 (Subtype.ext hr)
  have hrq : algebraMap (RingOfIntegers K) (RingOfIntegers L)
      (r : RingOfIntegers K) ∈ q.asIdeal := by
    change (r : RingOfIntegers K) ∈
      q.asIdeal.comap
        (algebraMap (RingOfIntegers K) (RingOfIntegers L))
    change (r : RingOfIntegers K) ∈
      (q.under (RingOfIntegers K)).asIdeal
    rw [upperPrime_under (K := K) (L := L) P Q]
    exact r.property
  have hpiUpper :
      (Valued.v : Valuation (q.adicCompletion L)
        (WithZero (Multiplicative ℤ)))
          (algebraMap (P.adicCompletion K) (q.adicCompletion L) pi) < 1 := by
    rw [show algebraMap (P.adicCompletion K) (q.adicCompletion L) pi =
        FinitePlace.embedding q
          (algebraMap K L
            (algebraMap (RingOfIntegers K) K (r : RingOfIntegers K))) by
      exact RingHom.congr_fun hfield
        (algebraMap (RingOfIntegers K) K (r : RingOfIntegers K))]
    rw [FinitePlace.embedding_apply,
      q.valuedAdicCompletion_eq_valuation']
    change q.valuation L
      (algebraMap (RingOfIntegers L) L
        (algebraMap (RingOfIntegers K) (RingOfIntegers L)
          (r : RingOfIntegers K))) < 1
    exact (q.valuation_lt_one_iff_mem _).2 hrq
  have hcontinuous : Continuous
      (algebraMap (P.adicCompletion K) (q.adicCompletion L)) := by
    apply continuous_of_tendsto_nhds_zero
      (algebraMap (P.adicCompletion K) (q.adicCompletion L))
    rw [(Valued.hasBasis_nhds_zero
        (P.adicCompletion K) (WithZero (Multiplicative ℤ))).tendsto_iff
      (Valued.hasBasis_nhds_zero
        (q.adicCompletion L) (WithZero (Multiplicative ℤ)))]
    intro gamma _
    let vUpper : Valuation (q.adicCompletion L)
        (WithZero (Multiplicative ℤ)) := Valued.v
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hpiUpper
      (Units.map
        (MonoidWithZeroHom.ValueGroup₀.embedding (f := vUpper)) gamma)
    let delta : (MonoidWithZeroHom.ValueGroup₀
        (Valued.v : Valuation (P.adicCompletion K)
          (WithZero (Multiplicative ℤ))))ˣ :=
      Units.mk0
        ((Valued.v : Valuation (P.adicCompletion K)
          (WithZero (Multiplicative ℤ))).restrict (pi ^ n))
        ((Valued.v : Valuation (P.adicCompletion K)
          (WithZero (Multiplicative ℤ))).restrict.ne_zero_iff.mpr
            (pow_ne_zero n hpi))
    refine ⟨delta, trivial, ?_⟩
    intro x hx
    simp only [Set.mem_setOf_eq, delta, Units.val_mk0] at hx ⊢
    let y := x / pi ^ n
    have hy' :
        (Valued.v : Valuation (P.adicCompletion K)
          (WithZero (Multiplicative ℤ))).restrict y < 1 := by
      rw [map_div₀, map_pow, div_lt_one₀]
      · rw [map_pow] at hx
        exact hx
      · exact pow_pos
          (((Valued.v : Valuation (P.adicCompletion K)
            (WithZero (Multiplicative ℤ))).restrict_pos_iff pi).mpr
              (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).2 hpi))) n
    have hy :
        (Valued.v : Valuation (P.adicCompletion K)
          (WithZero (Multiplicative ℤ))) y ≤ 1 :=
      (Valued.v : Valuation (P.adicCompletion K)
        (WithZero (Multiplicative ℤ))).restrict_le_one_iff.mp hy'.le
    let c : C := ⟨y, hy⟩
    have hfy : vUpper
        (algebraMap (P.adicCompletion K) (q.adicCompletion L) y) ≤ 1 := by
      rw [show algebraMap (P.adicCompletion K) (q.adicCompletion L) y =
          algebraMap D (q.adicCompletion L) (algebraMap C D c) by
        exact hintegers c]
      exact (algebraMap C D c).property
    have hxy : x = pi ^ n * y := by
      rw [show y = x / pi ^ n by rfl, mul_div_cancel₀ x (pow_ne_zero n hpi)]
    apply vUpper.restrict_lt_iff_lt_embedding.mpr
    calc
      vUpper (algebraMap (P.adicCompletion K) (q.adicCompletion L) x) =
          vUpper (algebraMap (P.adicCompletion K) (q.adicCompletion L) pi) ^ n *
            vUpper (algebraMap (P.adicCompletion K) (q.adicCompletion L) y) := by
        rw [hxy, map_mul, map_pow, map_mul, map_pow]
      _ ≤ vUpper
            (algebraMap (P.adicCompletion K) (q.adicCompletion L) pi) ^ n * 1 :=
        mul_le_mul_right hfy _
      _ = vUpper
            (algebraMap (P.adicCompletion K) (q.adicCompletion L) pi) ^ n :=
        mul_one _
      _ < (MonoidWithZeroHom.ValueGroup₀.embedding (f := vUpper)) gamma := by
        simpa using hn
  have hsquare :
      (algebraMap (P.adicCompletion K) (q.adicCompletion L)).comp
          eK.toRingHom =
        eL.toRingHom.comp (algebraMap v.Completion w.Completion) := by
    apply DFunLike.ext _ _
    intro x
    exact congrFun ((dense_range_embedding v).equalizer
      (hcontinuous.comp
        (continuous_place_adic P))
      (((continuous_place_adic q).comp
          (continuous_ring_equiv hwq)).comp
        (completion_lies_isometry v w hwv).continuous)
      (funext fun a => by
        change algebraMap (P.adicCompletion K) (q.adicCompletion L)
            (eK (completionEmbedding v a)) =
          eL (algebraMap v.Completion w.Completion
            (completionEmbedding v a))
        rw [show eK (completionEmbedding v a) = FinitePlace.embedding P a by
          exact finite_place_adic P a]
        rw [show algebraMap v.Completion w.Completion
            (completionEmbedding v a) =
              completionEmbedding w (algebraMap K L a) by
          exact RingHom.congr_fun (completion_lies_comp v w hwv) a]
        change algebraMap (P.adicCompletion K) (q.adicCompletion L)
            (FinitePlace.embedding P a) =
          placeCompletionAdic q
            (completionRing hwq
              (completionEmbedding w (algebraMap K L a)))
        rw [completion_equiv_embedding,
          finite_place_adic]
        exact RingHom.congr_fun hfield a)) x
  change (normSubgroup v.Completion w.Completion).comap
      (Units.map eK.symm.toRingHom) =
    normSubgroup (P.adicCompletion K) (q.adicCompletion L)
  exact norm_comap_units eK eL hsquare

end

end Towers.CField.GWang
