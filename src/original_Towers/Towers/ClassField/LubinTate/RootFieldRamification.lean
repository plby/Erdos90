import Towers.ClassField.LubinTate.RootFieldAdic
import Towers.NumberTheory.Locals.TotallyRamifiedEisenstein
import Towers.NumberTheory.Locals.LocalUnramifiedDecomposition
import Towers.NumberTheory.Ramification.EisensteinTotal

/-!
# Total ramification of finite Lubin--Tate levels

The reduced Lubin--Tate polynomial is Eisenstein and its distinguished root
generates the concrete root field.  Applying the integral-closure form of the
Eisenstein ramification theorem therefore proves the ideal-theoretic total
ramification assertion in Theorem I.3.6(a).
-/

namespace Towers.CField.LTate

noncomputable section

open Towers.CField.FGroups
open Polynomial
open scoped NormedField

universe v

namespace LTDatum

/-- If the root ideal of a polynomial is prime and the root divides the
mapped generator of the base maximal ideal, then that root is an upstairs
uniformizer.  The divisibility is automatic from the root equation and the
constant coefficient. -/
theorem maximal_span_prime
    {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    {pi : A} {f : A[X]} {alpha : B}
    (hmax : IsLocalRing.maximalIdeal A = Ideal.span {pi})
    (hcoeff : f.coeff 0 = pi)
    (hroot : Polynomial.aeval alpha f = 0)
    (halpha : alpha ≠ 0)
    (hprime : ((IsLocalRing.maximalIdeal A).map (algebraMap A B) ⊔
      Ideal.span {alpha}).IsPrime) :
    IsLocalRing.maximalIdeal B = Ideal.span {alpha} := by
  have hrootMap : (f.map (algebraMap A B)).IsRoot alpha := by
    simpa only [Polynomial.IsRoot, Polynomial.aeval_def,
      Polynomial.eval₂_eq_eval_map] using hroot
  have hdvd : alpha ∣ algebraMap A B pi := by
    have := hrootMap.dvd_coeff_zero
    simpa only [Polynomial.coeff_map, hcoeff] using this
  have hmap_le :
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤
        Ideal.span {alpha} := by
    rw [hmax, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact hdvd
  have hrootIdeal :
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) ⊔
          Ideal.span {alpha} =
        Ideal.span {alpha} := sup_eq_right.mpr hmap_le
  have hspanPrime : (Ideal.span {alpha}).IsPrime := hrootIdeal ▸ hprime
  have hspan0 : Ideal.span ({alpha} : Set B) ≠ ⊥ := by
    intro h
    exact halpha (Ideal.span_singleton_eq_bot.mp h)
  exact (IsLocalRing.eq_maximalIdeal (hspanPrime.isMaximal hspan0)).symm

set_option maxHeartbeats 4000000 in
-- The spectral local-field, integral-ring, and ideal-ramification instance
-- telescope is substantially deeper than the default elaboration budget.
set_option synthInstance.maxHeartbeats 200000 in
/-- Theorem I.3.6(a), total-ramification clause, for the distinguished root
field.  The conclusion uses the norm-defined integer rings and the exact
ideal-theoretic predicate from the Eisenstein ramification theorem. -/
theorem root_totally_ramified
    (K : Type v) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [ProperSpace K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsDiscreteValuationRing
      (Valuation.integer (NormedField.valuation (K := K)))]
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    let A := Valuation.integer (NormedField.valuation (K := K))
    let E := D.RootField K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      spectralNorm.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E :=
      LBrauer.FLExt.valuativeRel K E
    letI : IsNonarchimedeanLocalField E :=
      LBrauer.FLExt.nonarchimedeanLocalField K E
    letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
    letI : CompleteSpace E := spectralNorm.completeSpace K E
    letI : ProperSpace E := FiniteDimensional.proper K E
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := E)) :=
      LBrauer.spectralValuationExtension K E
    let B := Valuation.integer (NormedField.valuation (K := E))
    Towers.NumberTheory.Milne.TotallyRamified A B
      (IsLocalRing.maximalIdeal A) := by
  let A := Valuation.integer (NormedField.valuation (K := K))
  letI : Finite (A ⧸ Ideal.span {D.pi}) := D.finiteResidue
  letI : Fintype (A ⧸ Ideal.span {D.pi}) := Fintype.ofFinite _
  let E := D.RootField K n
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E :=
    LBrauer.FLExt.valuativeRel K E
  letI : IsNonarchimedeanLocalField E :=
    LBrauer.FLExt.nonarchimedeanLocalField K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : CompleteSpace E := spectralNorm.completeSpace K E
  letI : ProperSpace E := FiniteDimensional.proper K E
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := E)) :=
    LBrauer.spectralValuationExtension K E
  let B := Valuation.integer (NormedField.valuation (K := E))
  letI : IsDiscreteValuationRing B := by
    letI : IsDiscreteValuationRing
        (Valuation.integer (ValuativeRel.valuation E)) :=
      LBrauer.discrete_valuation_ring E
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (LBrauer.valuativeIntegerNorm E)
  letI : IsUniformAddGroup A := A.toAddSubgroup.isUniformAddGroup
  letI : IsUniformAddGroup B := B.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace B := (Valued.isClosed_integer E).completeSpace_coe
  letI : IsGalois K E := D.root_field_galois K hfield n
  letI : Module.Finite A B :=
    Towers.NumberTheory.Milne.valued_integer_module K E
  letI : IsFractionRing B E :=
    (Valuation.integer.integers
      (NormedField.valuation (K := E))).isFractionRing
  letI : IsScalarTower A B E :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext a
      rfl
  let hI : IsAdic (IsLocalRing.maximalIdeal B) :=
    Towers.NumberTheory.Milne.valued_integer_adic E
  let rho : A →+* B := algebraMap A B
  let F := lubinFormalLaw D.pi D.pi_irreducible.ne_zero
    D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
      D.lubin_tate_card
  let point : RelativeLubinPoints hI rho D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card → B := fun z ↦
    FGLaw.APts.toIdeal hI (F.map rho) z
  obtain ⟨y, hy, hyroot⟩ :=
    D.spectral_point_maps K hfield n
  change B.subtype (point y) = D.root K n at hyroot
  let alpha : B := point y
  let fA : A[X] := reducedLubinIterate D.f n
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
      IntermediateField.adjoin K ({algebraMap B E alpha} : Set E) = ⊤ := by
    rw [show algebraMap B E alpha = D.root K n by exact hyroot]
    exact D.adjoin_root_top K n
  have hp0 : IsLocalRing.maximalIdeal A ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field A
  have hfA_degree_pos : 0 < fA.natDegree := by
    rw [hfA_degree]
    exact Nat.mul_pos (Nat.sub_pos_of_lt D.one_lt_q)
      (pow_pos (Nat.zero_lt_of_lt D.one_lt_q) n)
  have hram :=
    Towers.NumberTheory.Milne.eisenstein_total_ramification
      A B K E hp0 hfA_eisenstein hfA_monic
        hfA_degree_pos halpha_root halpha_gen
  let P : Ideal B :=
    (IsLocalRing.maximalIdeal A).map (algebraMap A B) ⊔
      Ideal.span {alpha}
  change P.IsPrime ∧
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
        P ^ fA.natDegree ∧
      Ideal.ramificationIdx (IsLocalRing.maximalIdeal A) P =
        fA.natDegree ∧
      ∀ Q : Ideal B, Q.IsPrime →
        Q.LiesOver (IsLocalRing.maximalIdeal A) → Q = P at hram
  rcases hram with ⟨hPprime, hpow, hidx, hunique⟩
  have hfieldRank : Module.finrank K E = Module.finrank A B :=
    Algebra.IsAlgebraic.finrank_of_isFractionRing A K B E
  have hdegree : Module.finrank K E = fA.natDegree := by
    calc
      Module.finrank K E = (D.q - 1) * D.q ^ n :=
        D.finrank_rootField K n
      _ = fA.natDegree := hfA_degree.symm
  have hfinrank : Module.finrank A B = fA.natDegree :=
    hfieldRank.symm.trans hdegree
  have hmap_le :
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ P :=
    le_sup_left
  have hcomap_prime : (P.comap (algebraMap A B)).IsPrime :=
    hPprime.comap (algebraMap A B)
  have hcomap : P.comap (algebraMap A B) =
      IsLocalRing.maximalIdeal A := by
    exact ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le
      hcomap_prime.ne_top (Ideal.map_le_iff_le_comap.mp hmap_le)).symm
  refine ⟨P, hPprime, ⟨hcomap.symm⟩, ?_, ?_, hunique⟩
  · rw [hfinrank]
    exact hpow
  · rw [hfinrank]
    exact hidx

set_option maxHeartbeats 4000000 in
-- As above, the spectral integer-ring instance telescope needs a larger
-- elaboration budget than the project default.
set_option synthInstance.maxHeartbeats 200000 in
/-- The distinguished Lubin--Tate root is an upstairs uniformizer.  More
precisely, it has an integral lift whose principal ideal is the maximal ideal
of the norm-defined integer ring of the root field.  This is the maximal-ideal
assertion in Summary I.3.7. -/
theorem root_field_uniformizer
    (K : Type v) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [ProperSpace K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsDiscreteValuationRing
      (Valuation.integer (NormedField.valuation (K := K)))]
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    (n : ℕ) :
    let E := D.RootField K n
    letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
    letI : NontriviallyNormedField E :=
      spectralNorm.nontriviallyNormedField K E
    letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
    letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
    letI : ValuativeRel E :=
      LBrauer.FLExt.valuativeRel K E
    letI : IsNonarchimedeanLocalField E :=
      LBrauer.FLExt.nonarchimedeanLocalField K E
    letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
      Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
    letI : CompleteSpace E := spectralNorm.completeSpace K E
    letI : ProperSpace E := FiniteDimensional.proper K E
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := E)) :=
      LBrauer.spectralValuationExtension K E
    let B := Valuation.integer (NormedField.valuation (K := E))
    ∃ alpha : B, B.subtype alpha = D.root K n ∧
      IsLocalRing.maximalIdeal B = Ideal.span {alpha} := by
  let A := Valuation.integer (NormedField.valuation (K := K))
  letI : Finite (A ⧸ Ideal.span {D.pi}) := D.finiteResidue
  letI : Fintype (A ⧸ Ideal.span {D.pi}) := Fintype.ofFinite _
  let E := D.RootField K n
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : NontriviallyNormedField E :=
    spectralNorm.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E :=
    LBrauer.FLExt.valuativeRel K E
  letI : IsNonarchimedeanLocalField E :=
    LBrauer.FLExt.nonarchimedeanLocalField K E
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : CompleteSpace E := spectralNorm.completeSpace K E
  letI : ProperSpace E := FiniteDimensional.proper K E
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := E)) :=
    LBrauer.spectralValuationExtension K E
  let B := Valuation.integer (NormedField.valuation (K := E))
  letI : IsDiscreteValuationRing B := by
    letI : IsDiscreteValuationRing
        (Valuation.integer (ValuativeRel.valuation E)) :=
      LBrauer.discrete_valuation_ring E
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (LBrauer.valuativeIntegerNorm E)
  letI : IsUniformAddGroup A := A.toAddSubgroup.isUniformAddGroup
  letI : IsUniformAddGroup B := B.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace B := (Valued.isClosed_integer E).completeSpace_coe
  letI : IsGalois K E := D.root_field_galois K hfield n
  letI : Module.Finite A B :=
    Towers.NumberTheory.Milne.valued_integer_module K E
  letI : IsFractionRing B E :=
    (Valuation.integer.integers
      (NormedField.valuation (K := E))).isFractionRing
  letI : IsScalarTower A B E :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext a
      rfl
  let hI : IsAdic (IsLocalRing.maximalIdeal B) :=
    Towers.NumberTheory.Milne.valued_integer_adic E
  let rho : A →+* B := algebraMap A B
  let F := lubinFormalLaw D.pi D.pi_irreducible.ne_zero
    D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
      D.lubin_tate_card
  let point : RelativeLubinPoints hI rho D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card → B := fun z ↦
    FGLaw.APts.toIdeal hI (F.map rho) z
  obtain ⟨y, hy, hyroot⟩ :=
    D.spectral_point_maps K hfield n
  change B.subtype (point y) = D.root K n at hyroot
  let alpha : B := point y
  let fA : A[X] := reducedLubinIterate D.f n
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
      IntermediateField.adjoin K ({algebraMap B E alpha} : Set E) = ⊤ := by
    rw [show algebraMap B E alpha = D.root K n by exact hyroot]
    exact D.adjoin_root_top K n
  have hp0 : IsLocalRing.maximalIdeal A ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field A
  have hfA_degree_pos : 0 < fA.natDegree := by
    dsimp only [fA]
    rw [reduced_iterate_degree, D.f_natDegree]
    exact Nat.mul_pos (Nat.sub_pos_of_lt D.one_lt_q)
      (pow_pos (Nat.zero_lt_of_lt D.one_lt_q) n)
  have hram :=
    Towers.NumberTheory.Milne.eisenstein_total_ramification
      A B K E hp0 hfA_eisenstein hfA_monic
        hfA_degree_pos halpha_root halpha_gen
  have hrootPrime :
      ((IsLocalRing.maximalIdeal A).map (algebraMap A B) ⊔
        Ideal.span {alpha}).IsPrime := hram.1
  have hfA_coeff : fA.coeff 0 = D.pi := by
    dsimp only [fA]
    rw [reduced_iterate_coeff D.f
      (by simpa using D.lubinTateSeries.1)]
    simpa using D.lubinTateSeries.2.1
  have halpha_ne : alpha ≠ 0 := by
    intro ha
    apply D.root_ne_zero K n
    change point y = 0 at ha
    rw [← hyroot, ha, map_zero]
  refine ⟨alpha, hyroot, ?_⟩
  exact maximal_span_prime
    D.pi_irreducible.maximalIdeal_eq hfA_coeff halpha_root
      halpha_ne hrootPrime

end LTDatum

end

end Towers.CField.LTate
