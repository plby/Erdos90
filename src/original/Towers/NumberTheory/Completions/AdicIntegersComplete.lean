import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.AdicCompletion.Topology

/-!
# Adic completeness of completed valuation rings

For the completion at a height-one prime, the native valuation topology on
the integer ring is the topology defined by powers of its maximal ideal.
The integer ring is a closed subspace of the complete valued field, hence is
complete for that adic topology.
-/

namespace Towers.NumberTheory.Milne

open Ideal IsDedekindDomain HeightOneSpectrum WithZeroMulInt WithZero
open scoped WithZero Valued algebraMap Topology Pointwise

noncomputable section

universe u

variable {R K : Type u} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Every power of the maximal ideal is open in the completed valuation
ring. -/
theorem open_maximal_integers
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] (n : ℕ) :
    IsOpen (((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n :
      Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K)) := by
  letI : IsDiscreteValuationRing
      ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).integer) := by
    change IsDiscreteValuationRing (v.adicCompletionIntegers K)
    infer_instance
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible
    (v.adicCompletionIntegers K)
  have hpow :
      (((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n :
          Ideal (v.adicCompletionIntegers K)) :
        Set (v.adicCompletionIntegers K)) =
        {y : v.adicCompletionIntegers K |
          (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
            (y : v.adicCompletion K) ≤
          (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
            (pi : v.adicCompletion K) ^ n} := by
    simpa only [HeightOneSpectrum.adicCompletionIntegers] using
      hpi.maximalIdeal_pow_eq_setOf_le_v_coe_pow
        (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) n
  rw [hpow]
  have hr : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict
      ((pi : v.adicCompletion K) ^ n) ≠ 0 := by
    simp [hpi.ne_zero]
  have hopenAmbient : IsOpen
      {x : v.adicCompletion K |
        (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict x ≤
          (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict
            ((pi : v.adicCompletion K) ^ n)} :=
    Valued.isOpen_closedBall (v.adicCompletion K) hr
  have hopenSubtype : IsOpen
      {y : v.adicCompletionIntegers K |
        (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict
            (y : v.adicCompletion K) ≤
          (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict
            ((pi : v.adicCompletion K) ^ n)} :=
    hopenAmbient.preimage continuous_subtype_val
  simpa only [← map_pow, Valuation.restrict_le_iff] using hopenSubtype

/-- The native topology on the completed valuation ring is its
maximal-ideal-adic topology. -/
theorem adic_completion_integers
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    IsAdic (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) := by
  let C := v.adicCompletion K
  let B := v.adicCompletionIntegers K
  let M : Ideal B := IsLocalRing.maximalIdeal B
  letI : IsTopologicalRing B :=
    Subring.instIsTopologicalRing
      (Valued.v : Valuation C ℤᵐ⁰).integer
  letI : IsDiscreteValuationRing
      ((Valued.v : Valuation C ℤᵐ⁰).integer) := by
    change IsDiscreteValuationRing (v.adicCompletionIntegers K)
    infer_instance
  rw [isAdic_iff]
  constructor
  · intro n
    exact open_maximal_integers (K := K) v n
  · intro s hs
    obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible B
    have hpow (n : ℕ) :
        ((M ^ n : Ideal B) : Set B) =
          {y : B | (Valued.v : Valuation C ℤᵐ⁰) (y : C) ≤
            (Valued.v : Valuation C ℤᵐ⁰) (pi : C) ^ n} := by
      simpa only [B, C, M, HeightOneSpectrum.adicCompletionIntegers] using
        hpi.maximalIdeal_pow_eq_setOf_le_v_coe_pow
          (v := (Valued.v : Valuation C ℤᵐ⁰)) n
    obtain ⟨t, ht, hts⟩ :=
      (mem_nhds_subtype ((Valued.v : Valuation C ℤᵐ⁰).integer : Set C)
        (0 : B) s).mp hs
    obtain ⟨gamma, hgamma⟩ := (Valued.mem_nhds_zero (R := C)).mp ht
    have hpilt : (Valued.v : Valuation C ℤᵐ⁰) (pi : C) < 1 := by
      apply ((Valued.v : Valuation C ℤᵐ⁰).mem_maximalIdeal_iff).mp
      exact (IsLocalRing.mem_maximalIdeal pi).mpr hpi.not_isUnit
    have hpine : (Valued.v : Valuation C ℤᵐ⁰).restrict (pi : C) ≠ 0 := by
      simp [hpi.ne_zero]
    let delta : (MonoidWithZeroHom.ValueGroup₀
        (Valued.v : Valuation C ℤᵐ⁰))ˣ :=
      Units.mk0 ((Valued.v : Valuation C ℤᵐ⁰).restrict (pi : C)) hpine
    have hdelta : delta < 1 := by
      have hpilt' : (Valued.v : Valuation C ℤᵐ⁰).restrict (pi : C) < 1 := by
        rw [← map_one (Valued.v : Valuation C ℤᵐ⁰).restrict]
        exact (Valuation.restrict_lt_iff
          (Valued.v : Valuation C ℤᵐ⁰)).mpr (by simpa only [map_one] using hpilt)
      apply Units.val_lt_val.mp
      simpa only [delta, Units.val_mk0, Units.val_one] using hpilt'
    obtain ⟨n, hn⟩ := exists_pow_lt hdelta gamma
    refine ⟨n, ?_⟩
    intro y hy
    apply hts
    apply hgamma
    have hyv : (Valued.v : Valuation C ℤᵐ⁰) (y : C) ≤
        (Valued.v : Valuation C ℤᵐ⁰) (pi : C) ^ n := by
      change y ∈ ((M ^ n : Ideal B) : Set B) at hy
      rw [hpow n] at hy
      exact hy
    change (Valued.v : Valuation C ℤᵐ⁰).restrict (y : C) < gamma.1
    have hyv' : (Valued.v : Valuation C ℤᵐ⁰).restrict (y : C) ≤
        (Valued.v : Valuation C ℤᵐ⁰).restrict ((pi : C) ^ n) :=
      (Valuation.restrict_le_iff
        (Valued.v : Valuation C ℤᵐ⁰)).mpr (by simpa only [map_pow] using hyv)
    have hle : (Valued.v : Valuation C ℤᵐ⁰).restrict (y : C) ≤
        ((delta ^ n : (MonoidWithZeroHom.ValueGroup₀
          (Valued.v : Valuation C ℤᵐ⁰))ˣ) :
            MonoidWithZeroHom.ValueGroup₀
              (Valued.v : Valuation C ℤᵐ⁰)) := by
      calc
        _ ≤ (Valued.v : Valuation C ℤᵐ⁰).restrict ((pi : C) ^ n) := hyv'
        _ = _ := by
          change (Valued.v : Valuation C ℤᵐ⁰).restrict ((pi : C) ^ n) =
            (Valued.v : Valuation C ℤᵐ⁰).restrict (pi : C) ^ n
          exact map_pow _ _ _
    exact hle.trans_lt (Units.val_lt_val.mpr hn)

set_option synthInstance.maxHeartbeats 200000 in
-- The subtype separation instance unfolds the completed valuation ring.
/-- The completed valuation ring is complete for its maximal-ideal-adic
filtration. -/
theorem adic_integers_complete
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)] :
    IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) := by
  let C := v.adicCompletion K
  let B := v.adicCompletionIntegers K
  letI : IsUniformAddGroup B :=
    ((Valued.v : Valuation C ℤᵐ⁰).integer.toAddSubgroup).isUniformAddGroup
  have hclosed : IsClosed ((Valued.v : Valuation C ℤᵐ⁰).integer : Set C) :=
    Valued.isClosed_integer C
  letI : CompleteSpace B := hclosed.completeSpace_coe
  exact (adic_completion_integers (K := K) v).isAdicComplete_iff.mpr
    ⟨inferInstance, inferInstance⟩

end

end Towers.NumberTheory.Milne
