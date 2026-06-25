import Submission.NumberTheory.Locals.ExtensionsFixedDegree

/-!
# Transporting total ramification from an integral model

The maximal-unramified decomposition naturally produces an abstract DVR
whose fraction field is the unramified intermediate field.  Uniqueness of
integral closure identifies that DVR with the norm-defined integer ring.
This file transports the ideal-theoretic total-ramification statement across
that identification.
-/

namespace Submission.CField.LClass

noncomputable section

open Algebra IsLocalRing
open Submission.NumberTheory.Milne
open scoped NNReal NormedField

attribute [local instance] NormedField.toValued

set_option maxHeartbeats 1000000 in
-- Several DVR and fraction-field structures coexist in this comparison.
set_option synthInstance.maxHeartbeats 200000 in
/-- Total ramification over an abstract integral DVR transports to the
norm-defined integer ring of its fraction field. -/
theorem totally_valued_model
    (K₀ U F L : Type*)
    [NontriviallyNormedField K₀] [CompleteSpace K₀]
    [IsUltrametricDist K₀]
    [NontriviallyNormedField F] [IsUltrametricDist F]
    [NormedAlgebra K₀ F] [Algebra.IsAlgebraic K₀ F]
    [IsDiscreteValuationRing (Valued.integer F)]
    [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    [Algebra (Valued.integer K₀) U] [Algebra U F] [IsFractionRing U F]
    [IsScalarTower (Valued.integer K₀) U F]
    [Algebra.IsIntegral (Valued.integer K₀) U]
    [NontriviallyNormedField L] [IsUltrametricDist L]
    [IsDiscreteValuationRing (Valued.integer L)]
    [Algebra F L] [FiniteDimensional F L]
    [Algebra U (Valued.integer L)] [Module.Finite U (Valued.integer L)]
    [Module.IsTorsionFree U (Valued.integer L)]
    [Algebra (Valued.integer L) L] [IsFractionRing (Valued.integer L) L]
    [Algebra U L] [IsScalarTower U (Valued.integer L) L]
    [IsScalarTower U F L]
    [Algebra (Valued.integer F) (Valued.integer L)]
    [Module.Finite (Valued.integer F) (Valued.integer L)]
    [Module.IsTorsionFree (Valued.integer F) (Valued.integer L)]
    [Algebra (Valued.integer F) L]
    [IsScalarTower (Valued.integer F) (Valued.integer L) L]
    [IsScalarTower (Valued.integer F) F L]
    (hcompat : (algebraMap (Valued.integer F) (Valued.integer L)).comp
        (dvrValuedInteger K₀ U F).toRingHom =
      algebraMap U (Valued.integer L))
    (htotal : TotallyRamified U (Valued.integer L) (maximalIdeal U)) :
    TotallyRamified (Valued.integer F) (Valued.integer L)
      (maximalIdeal (Valued.integer F)) := by
  let B := Valued.integer L
  let A' := Valued.integer F
  let e : U ≃+* A' := dvrValuedInteger K₀ U F
  have hmax : (maximalIdeal U).map e.toRingHom = maximalIdeal A' :=
    IsLocalRing.eq_maximalIdeal
      ((inferInstance : (maximalIdeal U).IsMaximal).map_bijective
        e.toRingHom e.bijective)
  have hmaps : (maximalIdeal A').map (algebraMap A' B) =
      (maximalIdeal U).map (algebraMap U B) := by
    rw [← hmax, Ideal.map_map, hcompat]
  have hrankU : Module.finrank U B = Module.finrank F L :=
    (Algebra.IsAlgebraic.finrank_of_isFractionRing U F B L).symm
  have hrankA' : Module.finrank A' B = Module.finrank F L :=
    (Algebra.IsAlgebraic.finrank_of_isFractionRing A' F B L).symm
  obtain ⟨P, hPprime, hPover, hpow, hram, _hunique⟩ := htotal
  have hp0 : maximalIdeal U ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field U
  have hP0 : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P
  have hPmax : P = maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (hPprime.isMaximal hP0)
  have hp0' : maximalIdeal A' ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field A'
  have hmapU0 : (maximalIdeal U).map (algebraMap U B) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hp0
  have hmapA'0 : (maximalIdeal A').map (algebraMap A' B) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hp0'
  have hramEq : Ideal.ramificationIdx (maximalIdeal A') (maximalIdeal B) =
      Ideal.ramificationIdx (maximalIdeal U) (maximalIdeal B) := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
        hmapA'0 (inferInstance : (IsLocalRing.maximalIdeal B).IsPrime)
          (IsDiscreteValuationRing.not_a_field B),
      Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
        hmapU0 (inferInstance : (IsLocalRing.maximalIdeal B).IsPrime)
          (IsDiscreteValuationRing.not_a_field B),
      hmaps]
  letI : IsLocalHom (algebraMap A' B) :=
    Algebra.IsIntegral.isLocalHom A' B
  refine ⟨maximalIdeal B,
    (inferInstance : (IsLocalRing.maximalIdeal B).IsPrime),
    inferInstance, ?_, ?_, ?_⟩
  · rw [hmaps, hrankA', ← hrankU, ← hPmax]
    exact hpow
  · rw [hrankA', ← hrankU, hramEq, ← hPmax]
    exact hram
  · intro Q hQprime hQover
    have hQ0 : Q ≠ ⊥ :=
      Ideal.ne_bot_of_liesOver_of_ne_bot hp0' Q
    exact IsLocalRing.eq_maximalIdeal (hQprime.isMaximal hQ0)

end

end Submission.CField.LClass
