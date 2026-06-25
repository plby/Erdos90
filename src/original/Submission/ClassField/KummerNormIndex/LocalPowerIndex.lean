import Submission.NumberTheory.Completions.AdicLocalRing
import Submission.ClassField.Ideles.FinitePlaceCompletion
import Submission.ClassField.KummerNormIndex.PlaceUnits
import Submission.ClassField.KummerNormIndex.ComplexAbsoluteValue

/-!
# Local power indices for Lemma VII.6.6

This file transports Proposition VII.6.8 to the canonical finite and
infinite completions of a number field.  The finite-place normalization is
proved by comparing the quotient of local integers by `(n)` with the
normalized adic norm.
-/

namespace Submission.CField.KNIndex

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.LTate
open Submission.CField.LBrauer
open Submission.CField.Ideles
open Submission.CField.ICohomo
open ValuativeRel
open Filter
open scoped NNReal Topology Valued WithZero

noncomputable section

universe u w

private abbrev OK (K : Type u) [Field K] [ValuativeRel K] :=
  Valuation.integer (valuation K)

/-- Compatible rank-one valuations have the same integer ring. -/
noncomputable def integerEquivNormed
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [ValuativeRel K] [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))] :
    OK K ≃+* Valuation.integer (NormedField.valuation (K := K)) :=
  RingEquiv.subringCongr <| by
    ext x
    rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff]
    constructor
    · intro hx
      have hrel : x ≤ᵥ (1 : K) :=
        (Valuation.Compatible.vle_iff_le
          (v := valuation K) x 1).2 (by simpa using hx)
      simpa using (Valuation.Compatible.vle_iff_le
        (v := NormedField.valuation (K := K)) x 1).1 hrel
    · intro hx
      have hrel : x ≤ᵥ (1 : K) :=
        (Valuation.Compatible.vle_iff_le
          (v := NormedField.valuation (K := K)) x 1).2 (by simpa using hx)
      exact (Valuation.Compatible.vle_iff_le
        (v := valuation K) x 1).1 hrel

/-- The norm-valuative relation on the adic completion used by local class
field theory. -/
@[reducible]
noncomputable def completionNontriviallyNormed
    {K : Type u} [Field K] [NumberField K] (P : FinitePrime K) :
    NontriviallyNormedField (P.adicCompletion K) := by
  let C := P.adicCompletion K
  let hnormed : NormedField C :=
    { (inferInstance : NormedField C) with
      toField := (inferInstance : Field C) }
  let hnontriviallyNormed : NontriviallyNormedField C :=
    Valued.toNontriviallyNormedField C ℤᵐ⁰
  have hnormWitness : ∃ x : C, x ≠ 0 ∧ ‖x‖ ≠ 1 := by
    letI := hnontriviallyNormed
    obtain ⟨x, hxpos, hxlt⟩ := NormedField.exists_norm_lt_one C
    exact ⟨x, norm_pos_iff.mp hxpos, ne_of_lt hxlt⟩
  exact @NontriviallyNormedField.ofNormNeOne C hnormed hnormWitness

@[reducible]
noncomputable def completionValuativeRel
    {K : Type u} [Field K] [NumberField K] (P : FinitePrime K) :
    letI : NontriviallyNormedField (P.adicCompletion K) :=
      completionNontriviallyNormed P
    ValuativeRel (P.adicCompletion K) :=
  ValuativeRel.ofValuation
    (NormedField.valuation (K := P.adicCompletion K))

@[reducible]
noncomputable def adicCompletionField
    {K : Type u} [Field K] [NumberField K] (P : FinitePrime K) :
    letI : NontriviallyNormedField (P.adicCompletion K) :=
      completionNontriviallyNormed P
    letI : ValuativeRel (P.adicCompletion K) :=
      completionValuativeRel P
    IsNonarchimedeanLocalField (P.adicCompletion K) := by
  letI : NontriviallyNormedField (P.adicCompletion K) :=
    completionNontriviallyNormed P
  letI : IsUltrametricDist (P.adicCompletion K) := by infer_instance
  letI : ValuativeRel (P.adicCompletion K) :=
    completionValuativeRel P
  letI : Valuation.Compatible
      (NormedField.valuation (K := P.adicCompletion K)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := P.adicCompletion K))
  haveI htop : IsValuativeTopology (P.adicCompletion K) := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [show s ∈ 𝓝 (0 : P.adicCompletion K) ↔
        ∃ γ : (MonoidWithZeroHom.ValueGroup₀
            (NormedField.valuation (K := P.adicCompletion K)))ˣ,
          {x | (NormedField.valuation
            (K := P.adicCompletion K)).restrict x < γ.1} ⊆ s from
      (NormedField.toValued
        (K := P.adicCompletion K)).is_topological_valuation s]
    simpa using (NormedField.valuation (K := P.adicCompletion K))
      |>.exists_setOf_restrict_le_iff 0 s
  letI hcompact : LocallyCompactSpace (P.adicCompletion K) :=
    adicLocallySpace P
  haveI hnontrivial : ValuativeRel.IsNontrivial (P.adicCompletion K) :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := P.adicCompletion K))).mpr inferInstance
  exact
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := hcompact
      toIsNontrivial := hnontrivial }

set_option maxHeartbeats 4000000 in
-- Relating the quotient cardinality to the normalized finite-place absolute
-- value unfolds both local unit and residue-field index calculations.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The quotient-cardinality normalization used in Proposition 6.8 agrees
with the normalized finite-place absolute value. -/
theorem normalized_absolute_value
    (K : Type u) [Field K] [NumberField K]
    (P : FinitePrime K) (n : ℕ) (hn : 0 < n) :
    @normalizedAbsoluteValue (P.adicCompletion K)
      inferInstance (completionValuativeRel P) n =
      (FinitePlace.equivHeightOneSpectrum.symm P) (n : K) := by
  let C := P.adicCompletion K
  let B := P.adicCompletionIntegers K
  let R := NumberField.RingOfIntegers K
  letI : NontriviallyNormedField C :=
    completionNontriviallyNormed P
  letI : ValuativeRel C := completionValuativeRel P
  letI : IsNonarchimedeanLocalField C :=
    adicCompletionField P
  letI : Valuation.Compatible (NormedField.valuation (K := C)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := C))
  have hFiniteEmbeddingInjective :
      Function.Injective (FinitePlace.embedding (K := K) P) :=
    (FinitePlace.embedding (K := K) P).injective
  letI : CharZero C :=
    charZero_of_injective_ringHom hFiniteEmbeddingInjective
  let eCB : OK C ≃+* B :=
    (integerEquivNormed C).trans
      (normedIntegerIntegers P)
  let rC : OK C := (n : OK C)
  let rB : B := eCB rC
  have hrB : (rB : C) = (n : C) := by
    rfl
  have hnC : (n : C) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr hn.ne'
  have hrB0 : rB ≠ 0 := by
    intro h
    apply hnC
    rw [← hrB, h]
    rfl
  obtain ⟨pi, hpi⟩ := P.intValuation_exists_uniformizer
  let pihat : B := algebraMap R B pi
  have hpihatVal :
      Valued.v (pihat : C) = WithZero.exp (-1 : ℤ) := by
    calc
      Valued.v (pihat : C) = P.valuation K pi := by
        exact P.valuedAdicCompletion_eq_valuation pi
      _ = P.intValuation pi := P.valuation_of_algebraMap pi
      _ = WithZero.exp (-1 : ℤ) := hpi
  have hpihatUniformizer :
      (Valued.v : Valuation C ℤᵐ⁰).IsUniformizer (pihat : C) := by
    rw [Valuation.IsUniformizer.iff]
    rw [Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (P.valuedAdicCompletion_surjective K)]
    exact hpihatVal
  have hpihatIrred : Irreducible pihat := by
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer pihat).2
    simpa only [B] using hpihatUniformizer.is_generator
  obtain ⟨m, hm⟩ :=
    IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
      (s := Ideal.span {rB})
      (by
        intro h
        exact hrB0 (Ideal.span_singleton_eq_bot.mp h)) hpihatIrred
  letI : Finite (B ⧸ Ideal.span {pihat}) := by
    rw [← hpihatIrred.maximalIdeal_eq]
    exact adicResidueField P
  have hresidue : Nat.card (B ⧸ Ideal.span {pihat}) =
      Ideal.absNorm P.asIdeal := by
    rw [← hpihatIrred.maximalIdeal_eq]
    exact adic_abs_norm P
  have hcardB : Nat.card (B ⧸ Ideal.span {rB}) =
      Ideal.absNorm P.asIdeal ^ m := by
    rw [hm]
    simpa [hresidue] using card_span_pow hpihatIrred m
  have hassoc : Associated rB (pihat ^ m) := by
    exact Ideal.span_singleton_eq_span_singleton.mp hm
  obtain ⟨ub, hub⟩ := hassoc
  have hnormB : ‖(rB : C)‖ = ‖(pihat : C)‖ ^ m := by
    have hubC : (rB : C) * (((ub : B) : C)) = (pihat : C) ^ m :=
      congrArg (fun x : B ↦ (x : C)) hub
    have hubNorm := congrArg norm hubC
    let ub' : (OK C)ˣ := Units.map eCB.symm.toRingHom ub
    let ubNorm :
        (Valuation.integer (NormedField.valuation (K := C)))ˣ :=
      Units.map (integerEquivNormed C).toRingHom ub'
    have hubNormOne : ‖((ubNorm :
        Valuation.integer (NormedField.valuation (K := C))) : C)‖ = 1 :=
      Valued.integer.norm_coe_unit ubNorm
    change ‖(((ub : B) : C))‖ = 1 at hubNormOne
    rw [norm_mul, hubNormOne, mul_one, norm_pow] at hubNorm
    exact hubNorm
  have hpihatNorm : ‖(pihat : C)‖ =
      (Ideal.absNorm P.asIdeal : ℝ)⁻¹ := by
    rw [FinitePlace.norm_def]
    change ((WithZeroMulInt.toNNReal
      (HeightOneSpectrum.absNorm_ne_zero P))
        (Valued.v (pihat : C)) : ℝ) = _
    rw [hpihatVal]
    rw [WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
    change (((Ideal.absNorm P.asIdeal : ℝ≥0) ^ (-1 : ℤ) : ℝ≥0) : ℝ) = _
    rw [NNReal.coe_zpow]
    simp
  have hnorm : ‖(n : C)‖ =
      (Ideal.absNorm P.asIdeal : ℝ) ^ (-(m : ℤ)) := by
    rw [← hrB, hnormB, hpihatNorm]
    simp [zpow_neg, inv_pow]
  let I : Ideal (OK C) := Ideal.span {rC}
  let J : Ideal B := Ideal.span {rB}
  have hmap : J = I.map eCB.toRingHom := by
    change Ideal.span {rB} =
      Ideal.map eCB.toRingHom (Ideal.span {rC})
    rw [Ideal.map_span]
    change Ideal.span {rB} = Ideal.span (eCB '' {rC})
    rw [Set.image_singleton]
  let eQ : (OK C ⧸ I) ≃+* (B ⧸ J) :=
    Ideal.quotientEquiv I J eCB hmap
  have hcardC : Nat.card (OK C ⧸ I) =
      Ideal.absNorm P.asIdeal ^ m := by
    rw [Nat.card_congr eQ.toEquiv]
    exact hcardB
  change ((Nat.card (OK C ⧸ Ideal.span {(n : OK C)}) : ℝ)⁻¹) = _
  rw [show Ideal.span {(n : OK C)} = I from rfl, hcardC,
    Nat.cast_pow]
  have hnorm' : ‖(n : C)‖ =
      ((Ideal.absNorm P.asIdeal : ℝ) ^ m)⁻¹ := by
    simpa [zpow_neg] using hnorm
  rw [← hnorm']
  simpa [C] using (FinitePlace.equivHeightOneSpectrum_symm_apply P (n : K)).symm

set_option maxHeartbeats 4000000 in
-- Transporting the local power-index formula to the canonical completion
-- requires the full finite-place topology and primitive-root instance tower.
set_option synthInstance.maxHeartbeats 1000000 in
/-- Proposition 6.8 at the canonical completion of a finite number-field
place.  A primitive `p`th root in the number field remains primitive in the
completion, so the root-of-unity factor has cardinality `p`. -/
theorem place_power_index
    (p : ℕ) (K : Type u) [Field K] [NumberField K]
    (hp : p.Prime) (hroots : (primitiveRoots p K).Nonempty)
    (P : FinitePrime K) :
    (((pthPowerSubgroup p (P.adicCompletion K)ˣ).index : ℕ) : ℝ) *
        (FinitePlace.equivHeightOneSpectrum.symm P) (p : K) =
      (p : ℝ) ^ 2 := by
  let C := P.adicCompletion K
  letI : NontriviallyNormedField C :=
    completionNontriviallyNormed P
  letI : ValuativeRel C := completionValuativeRel P
  letI : IsNonarchimedeanLocalField C :=
    adicCompletionField P
  letI : Valuation.Compatible (NormedField.valuation (K := C)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := C))
  have hFiniteEmbeddingInjective :
      Function.Injective (FinitePlace.embedding (K := K) P) :=
    (FinitePlace.embedding (K := K) P).injective
  letI : CharZero C :=
    charZero_of_injective_ringHom hFiniteEmbeddingInjective
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hroots
  have hprimitiveK : IsPrimitiveRoot ζ p :=
    (mem_primitiveRoots hp.pos).mp hζ
  have hprimitiveC : IsPrimitiveRoot (FinitePlace.embedding P ζ) p :=
    have hinjective : Function.Injective (FinitePlace.embedding P) :=
      hFiniteEmbeddingInjective
    hprimitiveK.map_of_injective hinjective
  have hcard : Nat.card (rootsOfUnity p C) = p := by
    rw [Nat.card_eq_fintype_card]
    exact hprimitiveC.card_rootsOfUnity
  have hformula :=
    complexAbsoluteStatement.2.2 C p hp.pos |>.1
  calc
    (((pthPowerSubgroup p Cˣ).index : ℕ) : ℝ) *
          (FinitePlace.equivHeightOneSpectrum.symm P) (p : K) =
        (((pthPowerSubgroup p Cˣ).index : ℕ) : ℝ) *
          normalizedAbsoluteValue C p := by
            rw [normalized_absolute_value K P p hp.pos]
    _ = (p : ℝ) * Nat.card (rootsOfUnity p C) := hformula
    _ = (p : ℝ) ^ 2 := by rw [hcard, pow_two]

/-- Power-subgroup index is invariant under a multiplicative equivalence. -/
theorem power_index_equiv
    {M : Type u} {N : Type w} [CommGroup M] [CommGroup N]
    (e : M ≃* N) (n : ℕ) :
    (pthPowerSubgroup n M).index = (pthPowerSubgroup n N).index := by
  have htransport := MulEquiv.map_range_powMonoidHom e n
  change (powMonoidHom n : M →* M).range.index =
    (powMonoidHom n : N →* N).range.index
  rw [← htransport, Subgroup.index_map_equiv]

/-- At a real infinite place, the local power-index identity is transported
from `ℝ`.  The global primitive root maps injectively to `ℝ`, so its
`p`th roots of unity have cardinality `p`. -/
theorem real_place_index
    (p : ℕ) (K : Type u) [Field K] [NumberField K]
    (hp : p.Prime) (hroots : (primitiveRoots p K).Nonempty)
    (v : InfinitePlace K) (hv : v.IsReal) :
    (((pthPowerSubgroup p v.Completionˣ).index : ℕ) : ℝ) *
        normalizedPlaceValue K (Sum.inr v) (p : K) =
      (p : ℝ) ^ 2 := by
  let C := v.Completion
  let e : C ≃+* ℝ :=
    InfinitePlace.Completion.ringEquivRealOfIsReal hv
  let eu : Cˣ ≃* ℝˣ := Units.mapEquiv e.toMulEquiv
  have hindex : (pthPowerSubgroup p Cˣ).index =
      (pthPowerSubgroup p ℝˣ).index :=
    power_index_equiv eu p
  have hvalue : realAbsoluteValue (p : ℝ) =
      v.1 (p : K) := by
    unfold realAbsoluteValue
    rw [← map_natCast e.toRingHom p]
    change ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
      (p : C)‖ = _
    rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero
      (map_zero e) (p : C)]
    rw [← map_natCast (completionEmbedding v.1) p,
      norm_completionEmbedding]
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hroots
  have hprimitiveK : IsPrimitiveRoot ζ p :=
    (mem_primitiveRoots hp.pos).mp hζ
  have hprimitiveR : IsPrimitiveRoot (v.embedding_of_isReal hv ζ) p :=
    hprimitiveK.map_of_injective (v.embedding_of_isReal hv).injective
  have hcard : Nat.card (rootsOfUnity p ℝ) = p := by
    rw [Nat.card_eq_fintype_card]
    exact hprimitiveR.card_rootsOfUnity
  have hformula := complexAbsoluteStatement.{0}.2.1 p hp.pos
  rw [normalizedPlaceValue,
    InfinitePlace.mult_isReal ⟨v, hv⟩, pow_one, ← hvalue, hindex]
  calc
    (((pthPowerSubgroup p ℝˣ).index : ℕ) : ℝ) *
          realAbsoluteValue (p : ℝ) =
        (p : ℝ) * Nat.card (rootsOfUnity p ℝ) := hformula
    _ = (p : ℝ) ^ 2 := by rw [hcard, pow_two]

/-- At a complex infinite place, the local power-index identity is
transported from `ℂ`; the multiplicity two in the normalized place value is
exactly Milne's squared complex absolute value. -/
theorem complex_place_index
    (p : ℕ) (K : Type u) [Field K] [NumberField K]
    (hp : p.Prime) (hroots : (primitiveRoots p K).Nonempty)
    (v : InfinitePlace K) (hv : v.IsComplex) :
    (((pthPowerSubgroup p v.Completionˣ).index : ℕ) : ℝ) *
        normalizedPlaceValue K (Sum.inr v) (p : K) =
      (p : ℝ) ^ 2 := by
  let C := v.Completion
  let e : C ≃+* ℂ :=
    InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
  let eu : Cˣ ≃* ℂˣ := Units.mapEquiv e.toMulEquiv
  have hindex : (pthPowerSubgroup p Cˣ).index =
      (pthPowerSubgroup p ℂˣ).index :=
    power_index_equiv eu p
  have hvalue : complexAbsoluteValue (p : ℂ) =
      v.1 (p : K) ^ 2 := by
    unfold complexAbsoluteValue
    rw [← map_natCast e.toRingHom p]
    change ‖InfinitePlace.Completion.extensionEmbedding v (p : C)‖ ^ 2 = _
    rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
      (map_zero e) (p : C)]
    rw [← map_natCast (completionEmbedding v.1) p,
      norm_completionEmbedding]
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := hroots
  have hprimitiveK : IsPrimitiveRoot ζ p :=
    (mem_primitiveRoots hp.pos).mp hζ
  have hprimitiveC : IsPrimitiveRoot (v.embedding ζ) p :=
    hprimitiveK.map_of_injective v.embedding.injective
  have hcard : Nat.card (rootsOfUnity p ℂ) = p := by
    rw [Nat.card_eq_fintype_card]
    exact hprimitiveC.card_rootsOfUnity
  have hformula := complexAbsoluteStatement.{0}.1 p hp.pos
  rw [normalizedPlaceValue,
    InfinitePlace.mult_isComplex ⟨v, hv⟩, ← hvalue, hindex]
  calc
    (((pthPowerSubgroup p ℂˣ).index : ℕ) : ℝ) *
          complexAbsoluteValue (p : ℂ) =
        (p : ℝ) * Nat.card (rootsOfUnity p ℂ) := hformula
    _ = (p : ℝ) ^ 2 := by rw [hcard, pow_two]

/-- Proposition 6.8 in exactly the local form consumed by Lemma 6.6. -/
theorem localIndexBridge : LocalIndexBridge.{u} := by
  intro p K _ _ hp hroots v
  cases v with
  | inl P => exact place_power_index p K hp hroots P
  | inr v =>
      rcases v.isReal_or_isComplex with hv | hv
      · exact real_place_index p K hp hroots v hv
      · exact complex_place_index p K hp hroots v hv

/-- **Lemma VII.6.6.** -/
theorem localIndexStatement : (∀ (p : ℕ) (K : Type u) [Field K] [NumberField K],
      p.Prime → (primitiveRoots p K).Nonempty →
      ∀ (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K)),
        (∀ v : InfinitePlace K,
          (Sum.inr v : NumberFieldPlace K) ∈ S) →
        (∀ v : NumberFieldPlace K,
          normalizedPlaceValue K v (p : K) ≠ 1 → v ∈ S) →
        (∀ P : FinitePrime K, P ∈ T →
          (Sum.inl P : NumberFieldPlace K) ∉ S) →
        (ideleSubgroup K p S T).relIndex
            (idelesAtPlaces (K := K) (L := K)
              (combinedPlaces K S T)) =
          p ^ (2 * S.card)) :=
  place_units_index localIndexBridge

end

end Submission.CField.KNIndex
