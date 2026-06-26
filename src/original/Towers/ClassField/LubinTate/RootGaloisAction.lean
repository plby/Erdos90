import Towers.ClassField.LubinTate.RootFieldAdic
import Towers.ClassField.LocalBrauer.FiniteExtensionNorm

/-!
# The finite Lubin--Tate Galois action

This file upgrades the degree-sized quotient-unit orbit from a bijection with
the automorphism group to the multiplicative equivalence asserted in Theorem
I.3.6(b).  The analytic input is Lemma I.3.5: a continuous automorphism of the
spectral integer ring commutes with convergent evaluation of the scalar
endomorphisms `[a]_f`.
-/

namespace Towers.CField.LTate

noncomputable section

open Towers.CField.FGroups
open scoped NormedField

universe u v

namespace LTDatum

set_option maxHeartbeats 4000000 in
-- The proof carries the spectral local-field instance telescope twice: once
-- for the root point and once for Galois-invariance of the spectral norm.
/-- Theorem I.3.6(b) for the concrete distinguished root field.  Quotient
units act multiplicatively on the root field, and the resulting action is the
full Galois group.  The bundled witnesses retain the exact root-action formula
used in Milne's proof. -/
theorem root_unit_orbit
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
    [Fintype
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi})]
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
    letI : IsDiscreteValuationRing B := by
      letI : IsDiscreteValuationRing
          (Valuation.integer (ValuativeRel.valuation E)) :=
        LBrauer.discrete_valuation_ring E
      exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
        (LBrauer.valuativeIntegerNorm E)
    letI : IsUniformAddGroup B := B.toAddSubgroup.isUniformAddGroup
    letI : CompleteSpace B := (Valued.isClosed_integer E).completeSpace_coe
    let hI : IsAdic (IsLocalRing.maximalIdeal B) :=
      Towers.NumberTheory.Milne.valued_integer_adic E
    let rho : A →+* B := algebraMap A B
    ∃ (y : RelativeLubinPoints hI rho D.pi
          D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
          (D.f : PowerSeries A) D.lubin_tate_card)
        (hy : Ideal.torsionOf A
          (RelativeLubinPoints hI rho D.pi
            D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
            (D.f : PowerSeries A) D.lubin_tate_card) y =
          Ideal.span {D.pi ^ (n + 1)}),
      B.subtype (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
          D.lubin_tate_card).map rho) y) =
          D.root K n ∧
      ∃ orbit : (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ ≃*
          (D.RootField K n ≃ₐ[K] D.RootField K n),
        ∀ u, orbit u (D.root K n) =
          B.subtype (FGLaw.APts.toIdeal hI
            ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
              D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
              D.lubin_tate_card).map rho)
            (orbitEmbeddingTorsion y hy u)) := by
  let A := Valuation.integer (NormedField.valuation (K := K))
  letI : IsUniformAddGroup A := A.toAddSubgroup.isUniformAddGroup
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
  letI : IsUniformAddGroup B := B.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace B := (Valued.isClosed_integer E).completeSpace_coe
  have hrho_continuous : Continuous (algebraMap A B) := by
    apply Continuous.subtype_mk
    exact (continuous_algebraMap K E).comp continuous_subtype_val
  letI : ContinuousSMul A B :=
    continuousSMul_of_algebraMap A B hrho_continuous
  let hI : IsAdic (IsLocalRing.maximalIdeal B) :=
    Towers.NumberTheory.Milne.valued_integer_adic E
  let rho : A →+* B := algebraMap A B
  let F := lubinFormalLaw D.pi D.pi_irreducible.ne_zero
    D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
      D.lubin_tate_card
  let M := RelativeLubinPoints hI rho D.pi
    D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
    (D.f : PowerSeries A) D.lubin_tate_card
  let point : M → B := fun z ↦
    FGLaw.APts.toIdeal hI (F.map rho) z
  letI : IsGalois K E := D.root_field_galois K hfield n
  obtain ⟨y, hy, hyroot⟩ :=
    D.spectral_point_maps K hfield n
  change B.subtype (point y) = D.root K n at hyroot
  have hcoeff : B.subtype.comp rho =
      (algebraMap K E).comp (algebraMap A K) := by
    ext a
    rfl
  obtain ⟨orbit, horbit⟩ :=
    D.relative_orbit_aut K hI rho hfield n y hy
      B.subtype B.subtype_injective hcoeff
  let q : (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ → M :=
    orbitEmbeddingTorsion y hy
  have horbit' (u : (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ) :
      orbit u (D.root K n) = B.subtype (point (q u)) := by
    exact horbit u
  have hmul (u v : (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ) :
      orbit (u * v) = orbit u * orbit v := by
    let sigma := orbit u
    let hsigma : Isometry sigma :=
      LBrauer.FLExt.isometry_algEquiv K E sigma
    let epsilonRing : B ≃+* B :=
      sigma.toRingEquiv.restrict B B fun x ↦ by
        constructor
        · intro hx
          apply Valued.integer.mem_iff.mpr
          change ‖sigma x‖ ≤ 1
          have hnorm : ‖sigma x‖ = ‖x‖ := by
            exact (spectralNorm_eq_of_equiv sigma x).symm
          rw [hnorm]
          exact Valued.integer.mem_iff.mp hx
        · intro hx
          apply Valued.integer.mem_iff.mpr
          change ‖x‖ ≤ 1
          have hnorm : ‖sigma x‖ = ‖x‖ := by
            exact (spectralNorm_eq_of_equiv sigma x).symm
          rw [← hnorm]
          exact Valued.integer.mem_iff.mp hx
    let epsilon : B ≃ₐ[A] B :=
      { epsilonRing with
        commutes' := by
          intro a
          apply Subtype.ext
          change sigma (algebraMap K E (a : K)) =
            algebraMap K E (a : K)
          exact sigma.commutes (a : K) }
    have hepsilon_continuous : Continuous epsilon :=
      (hsigma.continuous.comp continuous_subtype_val).subtype_mk _
    have hepsilon_mem (x : B) (hx : x ∈ IsLocalRing.maximalIdeal B) :
        epsilon x ∈ IsLocalRing.maximalIdeal B := by
      rw [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff epsilon,
        ← IsLocalRing.mem_maximalIdeal]
      exact hx
    have hepsilon_y : epsilon (point y) = point (q u) := by
      apply Subtype.ext
      change sigma (B.subtype (point y)) = B.subtype (point (q u))
      rw [hyroot]
      exact horbit' u
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
      (v : A ⧸ Ideal.span {D.pi ^ (n + 1)})
    have hv : a • y = q v := by
      change a • y =
        orbitEmbeddingTorsion y hy v
      simpa only [embedding_torsion_one, mul_one] using
        (smul_embedding_torsion y hy a 1 v ha)
    have hpoint_y_mem : point y ∈ IsLocalRing.maximalIdeal B := by
      change (FGLaw.APts.toIdeal hI (F.map rho) y : B) ∈
        IsLocalRing.maximalIdeal B
      exact (FGLaw.APts.toIdeal hI (F.map rho) y).2
    have huPoint :
        FGLaw.APts.ofIdeal hI (F.map rho)
          ⟨epsilon (point y), hepsilon_mem _ hpoint_y_mem⟩ = q u := by
      apply FGLaw.APts.ext hI (F.map rho)
      apply Subtype.ext
      exact hepsilon_y
    have hnatural :=
      relative_points_smul hI D.pi
        D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
        (D.f : PowerSeries A) D.lubin_tate_card epsilon
        hepsilon_continuous hepsilon_mem a y
    change epsilon (point (a • y)) =
      point (a • FGLaw.APts.ofIdeal hI (F.map rho)
        ⟨epsilon (point y), hepsilon_mem _ hpoint_y_mem⟩) at hnatural
    rw [huPoint] at hnatural
    have hau : a • q u = q (v * u) := by
      exact smul_embedding_torsion y hy a u v ha
    apply AlgEquiv.ext
    intro x
    have hhom : (orbit (u * v)).toAlgHom =
        (orbit u * orbit v).toAlgHom := by
      apply AdjoinRoot.algHom_ext
      calc
        orbit (u * v) (D.root K n) = B.subtype (point (q (u * v))) :=
          horbit' (u * v)
        _ = B.subtype (point (q (v * u))) := by rw [mul_comm]
        _ = B.subtype (point (a • q u)) := by rw [hau]
        _ = B.subtype (epsilon (point (a • y))) := by rw [hnatural]
        _ = sigma (B.subtype (point (a • y))) := by rfl
        _ = sigma (B.subtype (point (q v))) := by rw [hv]
        _ = (orbit u * orbit v) (D.root K n) := by
          rw [AlgEquiv.mul_apply, horbit' v]
    exact DFunLike.congr_fun hhom x
  let orbitMul : (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ ≃*
      (D.RootField K n ≃ₐ[K] D.RootField K n) :=
    { orbit with map_mul' := hmul }
  refine ⟨y, hy, hyroot, orbitMul, ?_⟩
  intro u
  exact horbit' u

end LTDatum

end

end Towers.CField.LTate
