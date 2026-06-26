import Submission.ClassField.LubinTate.RootGaloisAction
import Submission.ClassField.LubinTate.RootFieldTower
import Submission.ClassField.LocalBrauer.SpectralIntegerTower

/-!
# The finite Lubin--Tate action in a common algebraic closure

The abstract root-field model carries the explicit quotient-unit action from
Theorem I.3.6(b).  The root-field comparison theorem transports that action to
Milne's actual finite torsion field inside a fixed algebraic closure, retaining
the formula on the chosen primitive torsion generator.
-/

namespace Submission.CField.LTate

noncomputable section

open Submission.CField.FGroups
open scoped NormedField

universe v w

namespace LTDatum

section QuotientUnitTransitions

variable {A : Type*} [CommRing A]

/-- The ideal defining level `n + 2` is contained in the ideal defining
level `n + 1`. -/
theorem span_uniformizer_succ (pi : A) (n : ℕ) :
    Ideal.span {pi ^ (n + 2)} ≤ Ideal.span {pi ^ (n + 1)} := by
  rw [Ideal.span_singleton_le_span_singleton]
  exact pow_dvd_pow pi (by omega)

/-- Reduction of quotient units from level `n + 2` to level `n + 1`. -/
def quotientUnitReduction (pi : A) (n : ℕ) :
    (A ⧸ Ideal.span {pi ^ (n + 2)})ˣ →*
      (A ⧸ Ideal.span {pi ^ (n + 1)})ˣ :=
  Units.map
    (Ideal.Quotient.factor
      (span_uniformizer_succ pi n)).toMonoidHom

/-- Reducing a unit represented by an element of `A` gives the same element
in the lower quotient. -/
@[simp]
theorem reduction_units_mk
    (pi : A) (n : ℕ) (u : Aˣ) :
    quotientUnitReduction pi n
        (Units.map
          (Ideal.Quotient.mk (Ideal.span {pi ^ (n + 2)})).toMonoidHom u) =
      Units.map
        (Ideal.Quotient.mk (Ideal.span {pi ^ (n + 1)})).toMonoidHom u := by
  apply Units.ext
  exact Ideal.Quotient.factor_mk
    (span_uniformizer_succ pi n) u

end QuotientUnitTransitions

section RelativeOrbitTransitions

variable {A B C : Type*} [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [T2Space B] [CompleteSpace B]
  [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
  [IsTopologicalRing C] [T2Space C] [CompleteSpace C]

/-- Exact-level quotient-unit orbits commute with a continuous map of adic
evaluation rings, provided the lower generator maps to `pi` times the upper
generator.  This is the formal-module compatibility underlying restriction
of the finite Lubin--Tate Galois actions. -/
theorem unit_orbit_reduction
    (D : LTDatum A)
    {I : Ideal B} (hI : IsAdic I) {J : Ideal C} (hJ : IsAdic J)
    (rho : A →+* B) (phi : B →+* C) (hphi : Continuous phi)
    (hIJ : ∀ x : B, x ∈ I → phi x ∈ J)
    (hfield : IsField (A ⧸ Ideal.span {D.pi}))
    [Fintype (A ⧸ Ideal.span {D.pi})]
    (n : ℕ)
    (x : RelativeLubinPoints hI rho D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card)
    (hx : Ideal.torsionOf A
        (RelativeLubinPoints hI rho D.pi
          D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
          (D.f : PowerSeries A) D.lubin_tate_card) x =
      Ideal.span {D.pi ^ (n + 1)})
    (z : RelativeLubinPoints hJ (phi.comp rho) D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card)
    (hz : Ideal.torsionOf A
        (RelativeLubinPoints hJ (phi.comp rho) D.pi
          D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
          (D.f : PowerSeries A) D.lubin_tate_card) z =
      Ideal.span {D.pi ^ (n + 2)})
    (hroot : phi (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
          D.lubin_tate_card).map rho) x : B) =
      (FGLaw.APts.toIdeal hJ
        ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
          D.lubin_tate_card).map (phi.comp rho))
        (D.pi • z) : C))
    (u : (A ⧸ Ideal.span {D.pi ^ (n + 2)})ˣ) :
    phi (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
          D.lubin_tate_card).map rho)
        (orbitEmbeddingTorsion x hx
          (quotientUnitReduction D.pi n u)) : B) =
      (FGLaw.APts.toIdeal hJ
        ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
          D.lubin_tate_card).map (phi.comp rho))
        (D.pi • orbitEmbeddingTorsion z hz u) : C) := by
  let F := lubinFormalLaw D.pi D.pi_irreducible.ne_zero
    D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
      D.lubin_tate_card
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (u : A ⧸ Ideal.span {D.pi ^ (n + 2)})
  have haLower :
      Ideal.Quotient.mk (Ideal.span {D.pi ^ (n + 1)}) a =
        (quotientUnitReduction D.pi n u :
          A ⧸ Ideal.span {D.pi ^ (n + 1)}) := by
    change Ideal.Quotient.factor
      (span_uniformizer_succ D.pi n)
        (Ideal.Quotient.mk (Ideal.span {D.pi ^ (n + 2)}) a) = _
    rw [ha]
    rfl
  have hax : a • x = orbitEmbeddingTorsion x hx
      (quotientUnitReduction D.pi n u) := by
    simpa only [embedding_torsion_one, mul_one] using
      (smul_embedding_torsion x hx a 1
        (quotientUnitReduction D.pi n u) haLower)
  have haz : a • z = orbitEmbeddingTorsion z hz u := by
    simpa only [embedding_torsion_one, mul_one] using
      (smul_embedding_torsion z hz a 1 u ha)
  let mappedX : RelativeLubinPoints hJ (phi.comp rho) D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card :=
    FGLaw.APts.ofIdeal hJ (F.map (phi.comp rho))
      ⟨phi (FGLaw.APts.toIdeal hI (F.map rho) x : B),
        hIJ _ (FGLaw.APts.toIdeal hI (F.map rho) x).2⟩
  have hmappedX : mappedX = D.pi • z := by
    apply FGLaw.APts.ext hJ (F.map (phi.comp rho))
    apply Subtype.ext
    exact hroot
  have hsmul : a • (D.pi • z) = D.pi • (a • z) := by
    calc
      a • (D.pi • z) = (a * D.pi) • z := (mul_smul a D.pi z).symm
      _ = (D.pi * a) • z := by rw [mul_comm]
      _ = D.pi • (a • z) := mul_smul D.pi a z
  calc
    phi (FGLaw.APts.toIdeal hI (F.map rho)
        (orbitEmbeddingTorsion x hx
          (quotientUnitReduction D.pi n u)) : B) =
      phi (FGLaw.APts.toIdeal hI (F.map rho) (a • x) : B) := by
        rw [hax]
    _ = (FGLaw.APts.toIdeal hJ (F.map (phi.comp rho))
        (a • mappedX) : C) :=
      lubin_points_smul hI hJ rho phi
        hphi hIJ D.pi D.pi_irreducible.ne_zero
        D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
        D.lubin_tate_card a x
    _ = (FGLaw.APts.toIdeal hJ (F.map (phi.comp rho))
        (D.pi • (a • z)) : C) := by
      rw [hmappedX, hsmul]
    _ = (FGLaw.APts.toIdeal hJ (F.map (phi.comp rho))
        (D.pi • orbitEmbeddingTorsion z hz u) : C) := by
      rw [haz]

set_option maxHeartbeats 1000000 in
-- The base-change evaluation theorem has a large formal-group elaboration footprint.
/-- Algebra-hom form of `unit_orbit_reduction`, with the canonical
coefficient algebra maps on both evaluation rings. -/
theorem reduction_alg_hom
    (D : LTDatum A)
    [UniformSpace A] [IsTopologicalSemiring A] [IsUniformAddGroup A]
    [Algebra A B] [ContinuousSMul A B]
    [Algebra A C] [ContinuousSMul A C]
    {I : Ideal B} (hI : IsAdic I) {J : Ideal C} (hJ : IsAdic J)
    (phi : B →ₐ[A] C) (hphi : Continuous phi)
    (hIJ : ∀ x : B, x ∈ I → phi x ∈ J)
    (hfield : IsField (A ⧸ Ideal.span {D.pi}))
    [Fintype (A ⧸ Ideal.span {D.pi})]
    (n : ℕ)
    (x : RelativeLubinPoints hI (algebraMap A B) D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card)
    (hx : Ideal.torsionOf A
        (RelativeLubinPoints hI (algebraMap A B) D.pi
          D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
          (D.f : PowerSeries A) D.lubin_tate_card) x =
      Ideal.span {D.pi ^ (n + 1)})
    (z : RelativeLubinPoints hJ (algebraMap A C) D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card)
    (hz : Ideal.torsionOf A
        (RelativeLubinPoints hJ (algebraMap A C) D.pi
          D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
          (D.f : PowerSeries A) D.lubin_tate_card) z =
      Ideal.span {D.pi ^ (n + 2)})
    (hroot : phi (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
          D.lubin_tate_card).map (algebraMap A B)) x : B) =
      (FGLaw.APts.toIdeal hJ
        ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
          D.lubin_tate_card).map (algebraMap A C))
        (D.pi • z) : C))
    (u : (A ⧸ Ideal.span {D.pi ^ (n + 2)})ˣ) :
    phi (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
          D.lubin_tate_card).map (algebraMap A B))
        (orbitEmbeddingTorsion x hx
          (quotientUnitReduction D.pi n u)) : B) =
      (FGLaw.APts.toIdeal hJ
        ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
          D.lubin_tate_card).map (algebraMap A C))
        (D.pi • orbitEmbeddingTorsion z hz u) : C) := by
  let F := lubinFormalLaw D.pi D.pi_irreducible.ne_zero
    D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
      D.lubin_tate_card
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (u : A ⧸ Ideal.span {D.pi ^ (n + 2)})
  have haLower :
      Ideal.Quotient.mk (Ideal.span {D.pi ^ (n + 1)}) a =
        (quotientUnitReduction D.pi n u :
          A ⧸ Ideal.span {D.pi ^ (n + 1)}) := by
    change Ideal.Quotient.factor
      (span_uniformizer_succ D.pi n)
        (Ideal.Quotient.mk (Ideal.span {D.pi ^ (n + 2)}) a) = _
    rw [ha]
    rfl
  have hax : a • x = orbitEmbeddingTorsion x hx
      (quotientUnitReduction D.pi n u) := by
    simpa only [embedding_torsion_one, mul_one] using
      (smul_embedding_torsion x hx a 1
        (quotientUnitReduction D.pi n u) haLower)
  have haz : a • z = orbitEmbeddingTorsion z hz u := by
    simpa only [embedding_torsion_one, mul_one] using
      (smul_embedding_torsion z hz a 1 u ha)
  let mappedX : RelativeLubinPoints hJ (algebraMap A C) D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card :=
    FGLaw.APts.ofIdeal hJ (F.map (algebraMap A C))
      ⟨phi (FGLaw.APts.toIdeal hI
        (F.map (algebraMap A B)) x : B),
        hIJ _ (FGLaw.APts.toIdeal hI
          (F.map (algebraMap A B)) x).2⟩
  have hmappedX : mappedX = D.pi • z := by
    apply FGLaw.APts.ext hJ (F.map (algebraMap A C))
    apply Subtype.ext
    exact hroot
  have hsmul : a • (D.pi • z) = D.pi • (a • z) := by
    calc
      a • (D.pi • z) = (a * D.pi) • z := (mul_smul a D.pi z).symm
      _ = (D.pi * a) • z := by rw [mul_comm]
      _ = D.pi • (a • z) := mul_smul D.pi a z
  calc
    phi (FGLaw.APts.toIdeal hI (F.map (algebraMap A B))
        (orbitEmbeddingTorsion x hx
          (quotientUnitReduction D.pi n u)) : B) =
      phi (FGLaw.APts.toIdeal hI
        (F.map (algebraMap A B)) (a • x) : B) := by rw [hax]
    _ = (FGLaw.APts.toIdeal hJ (F.map (algebraMap A C))
        (a • mappedX) : C) :=
      adic_points_smul hI hJ D.pi
        D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
        (D.f : PowerSeries A) D.lubin_tate_card phi
        hphi hIJ a x
    _ = (FGLaw.APts.toIdeal hJ (F.map (algebraMap A C))
        (D.pi • (a • z)) : C) := by rw [hmappedX, hsmul]
    _ = (FGLaw.APts.toIdeal hJ (F.map (algebraMap A C))
        (D.pi • orbitEmbeddingTorsion z hz u) : C) := by
      rw [haz]

end RelativeOrbitTransitions

/-- Compatibility condition needed to pass finite quotient-unit actions to
the inverse limit `Aˣ` acting on the union of finite Lubin--Tate fields. -/
def CompatibleTorsionActions
    {A K Omega : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field Omega] [Algebra K Omega]
    (D : LTDatum A)
    (orbit : ∀ n,
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ →*
        (D.torsionLevelField K Omega n ≃ₐ[K]
          D.torsionLevelField K Omega n)) : Prop :=
  ∀ (n : ℕ)
    (u : (A ⧸ Ideal.span {D.pi ^ (n + 2)})ˣ)
    (x : D.torsionLevelField K Omega n),
    IntermediateField.inclusion
        (D.torsion_mono_succ K Omega n)
        (orbit n (quotientUnitReduction D.pi n u) x) =
      orbit (n + 1) u
        (IntermediateField.inclusion
          (D.torsion_mono_succ K Omega n) x)

set_option maxHeartbeats 5000000 in
-- The statement combines the spectral root-point telescope, the explicit
-- finite Galois action, and both ambient splitting-field equivalences.
set_option synthInstance.maxHeartbeats 200000 in
/-- The quotient-unit action of Theorem I.3.6(b), transported to the actual
finite torsion field in a fixed algebraic closure.  The displayed equation is
Milne's action formula on the transported primitive root. -/
theorem torsion_level_orbit
    (K : Type v) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [ProperSpace K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsDiscreteValuationRing
      (Valuation.integer (NormedField.valuation (K := K)))]
    (Omega : Type w) [Field Omega] [Algebra K Omega] [IsAlgClosure K Omega]
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
      Submission.NumberTheory.Milne.valued_integer_adic E
    let rho : A →+* B := algebraMap A B
    let T := D.torsionLevelField K Omega n
    let e := D.rootTorsionLevel K Omega hfield n
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
          (T ≃ₐ[K] T),
        ∀ u, orbit u (D.torsionLevelPrimitive K Omega hfield n) =
          e (B.subtype (FGLaw.APts.toIdeal hI
            ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
              D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
              D.lubin_tate_card).map rho)
            (orbitEmbeddingTorsion y hy u))) := by
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
    Submission.NumberTheory.Milne.valued_integer_adic E
  let rho : A →+* B := algebraMap A B
  let T := D.torsionLevelField K Omega n
  let e := D.rootTorsionLevel K Omega hfield n
  obtain ⟨y, hy, hyroot, rootOrbit, hrootOrbit⟩ :=
    D.root_unit_orbit K hfield n
  let orbit : (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ ≃* (T ≃ₐ[K] T) :=
    rootOrbit.trans (AlgEquiv.autCongr e)
  refine ⟨y, hy, hyroot, orbit, ?_⟩
  intro u
  change (AlgEquiv.autCongr e (rootOrbit u)) (e (D.root K n)) = _
  rw [AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  rw [hrootOrbit]

set_option maxHeartbeats 8000000 in
-- Building the simultaneous family synthesizes spectral local-field structures at two levels.
set_option synthInstance.maxHeartbeats 300000 in
/-- The finite quotient-unit actions can be chosen simultaneously and compatibly
with the quotient and field transition maps. -/
theorem torsion_level_family
    (K : Type v) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [ProperSpace K] [ValuativeRel K]
    [IsNonarchimedeanLocalField K]
    [Valuation.Compatible (NormedField.valuation (K := K))]
    [IsDiscreteValuationRing
      (Valuation.integer (NormedField.valuation (K := K)))]
    (Omega : Type w) [Field Omega] [Algebra K Omega] [IsAlgClosure K Omega]
    (D : LTDatum
      (Valuation.integer (NormedField.valuation (K := K))))
    (hfield : IsField
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}))
    [Finite
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi})] :
    ∃ orbit : ∀ n,
        (Valuation.integer (NormedField.valuation (K := K)) ⧸
          Ideal.span {D.pi ^ (n + 1)})ˣ ≃*
          (D.torsionLevelField K Omega n ≃ₐ[K]
            D.torsionLevelField K Omega n),
      CompatibleTorsionActions D
        (fun n ↦ (orbit n).toMonoidHom) := by
  classical
  letI : Fintype
      (Valuation.integer (NormedField.valuation (K := K)) ⧸
        Ideal.span {D.pi}) := Fintype.ofFinite _
  let A := Valuation.integer (NormedField.valuation (K := K))
  letI : IsUniformAddGroup A := A.toAddSubgroup.isUniformAddGroup
  have hdata := fun n ↦ D.root_unit_orbit K hfield n
  choose y hy hyroot rootOrbit hrootOrbit using hdata
  let orbit : ∀ n,
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ ≃*
        (D.torsionLevelField K Omega n ≃ₐ[K]
          D.torsionLevelField K Omega n) := fun n ↦
    (rootOrbit n).trans (AlgEquiv.autCongr
      (D.rootTorsionLevel K Omega hfield n))
  refine ⟨orbit, ?_⟩
  intro n u x
  let E := D.RootField K n
  let E' := D.RootField K (n + 1)
  letI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  letI : Algebra.IsAlgebraic K E' := Algebra.IsAlgebraic.of_finite K E'
  letI : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
  letI : NontriviallyNormedField E' := spectralNorm.nontriviallyNormedField K E'
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  letI : NormedAlgebra K E' := spectralNorm.normedAlgebra K E'
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : IsUltrametricDist E' := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := LBrauer.FLExt.valuativeRel K E
  letI : ValuativeRel E' := LBrauer.FLExt.valuativeRel K E'
  letI : IsNonarchimedeanLocalField E :=
    LBrauer.FLExt.nonarchimedeanLocalField K E
  letI : IsNonarchimedeanLocalField E' :=
    LBrauer.FLExt.nonarchimedeanLocalField K E'
  letI : Valuation.Compatible (NormedField.valuation (K := E)) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E))
  letI : Valuation.Compatible (NormedField.valuation (K := E')) :=
    Valuation.Compatible.ofValuation (NormedField.valuation (K := E'))
  letI : CompleteSpace E := spectralNorm.completeSpace K E
  letI : CompleteSpace E' := spectralNorm.completeSpace K E'
  letI : ProperSpace E := FiniteDimensional.proper K E
  letI : ProperSpace E' := FiniteDimensional.proper K E'
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := E)) :=
    LBrauer.spectralValuationExtension K E
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := E')) :=
    LBrauer.spectralValuationExtension K E'
  let i := D.rootAlgHom K n
  letI : Algebra E E' := i.toRingHom.toAlgebra
  letI : IsScalarTower K E E' := IsScalarTower.of_algHom i
  let B := Valuation.integer (NormedField.valuation (K := E))
  let C := Valuation.integer (NormedField.valuation (K := E'))
  letI : IsDiscreteValuationRing B := by
    letI : IsDiscreteValuationRing
        (Valuation.integer (ValuativeRel.valuation E)) :=
      LBrauer.discrete_valuation_ring E
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (LBrauer.valuativeIntegerNorm E)
  letI : IsDiscreteValuationRing C := by
    letI : IsDiscreteValuationRing
        (Valuation.integer (ValuativeRel.valuation E')) :=
      LBrauer.discrete_valuation_ring E'
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (LBrauer.valuativeIntegerNorm E')
  letI : IsUniformAddGroup B := B.toAddSubgroup.isUniformAddGroup
  letI : IsUniformAddGroup C := C.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace B := (Valued.isClosed_integer E).completeSpace_coe
  letI : CompleteSpace C := (Valued.isClosed_integer E').completeSpace_coe
  have hrhoB : Continuous (algebraMap A B) := by
    apply Continuous.subtype_mk
    exact (continuous_algebraMap K E).comp continuous_subtype_val
  have hrhoC : Continuous (algebraMap A C) := by
    apply Continuous.subtype_mk
    exact (continuous_algebraMap K E').comp continuous_subtype_val
  letI : ContinuousSMul A B := continuousSMul_of_algebraMap A B hrhoB
  letI : ContinuousSMul A C := continuousSMul_of_algebraMap A C hrhoC
  let hI : IsAdic (IsLocalRing.maximalIdeal B) :=
    Submission.NumberTheory.Milne.valued_integer_adic E
  let hJ : IsAdic (IsLocalRing.maximalIdeal C) :=
    Submission.NumberTheory.Milne.valued_integer_adic E'
  let phiR : B →+* C := LBrauer.spectralIntegerTower
    (K := K) (F := E) (E := E')
  have hcoeff : phiR.comp (algebraMap A B) = algebraMap A C := by
    ext a
    change i (algebraMap K E (a : K)) = algebraMap K E' (a : K)
    exact i.commutes (a : K)
  let phi : B →ₐ[A] C :=
    LBrauer.spectralTowerCommutes
      (K := K) (F := E) (E := E') hcoeff
  have hphi : Continuous phi :=
    LBrauer.continuous_spectral_tower
      (K := K) (F := E) (E := E')
  have hphiJ (b : B) (hb : b ∈ IsLocalRing.maximalIdeal B) :
      phi b ∈ IsLocalRing.maximalIdeal C :=
    LBrauer.spectral_tower_maximal
      (K := K) (F := E) (E := E') b hb
  let F := lubinFormalLaw D.pi D.pi_irreducible.ne_zero
    D.pi_irreducible.not_isUnit hfield (D.f : PowerSeries A)
      D.lubin_tate_card
  let pointB : RelativeLubinPoints hI (algebraMap A B) D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card → B := fun z ↦
    FGLaw.APts.toIdeal hI (F.map (algebraMap A B)) z
  let pointC : RelativeLubinPoints hJ (algebraMap A C) D.pi
      D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
      (D.f : PowerSeries A) D.lubin_tate_card → C := fun z ↦
    FGLaw.APts.toIdeal hJ (F.map (algebraMap A C)) z
  have hcoeffC : C.subtype.comp (algebraMap A C) =
      (algebraMap K E').comp (algebraMap A K) := by
    ext a
    rfl
  have hpolyEval
      (z : RelativeLubinPoints hJ (algebraMap A C) D.pi
        D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit hfield
        (D.f : PowerSeries A) D.lubin_tate_card) :
      C.subtype (pointC (D.pi • z)) =
        Polynomial.aeval (C.subtype (pointC z))
          (D.f.map (algebraMap A K)) := by
    change C.subtype (FGLaw.APts.toIdeal hJ
        (F.map (algebraMap A C)) (D.pi • z)) =
      Polynomial.aeval (C.subtype (FGLaw.APts.toIdeal hJ
        (F.map (algebraMap A C)) z))
        (D.f.map (algebraMap A K))
    rw [relative_points_uniformizer]
    have hmap : PowerSeries.map (algebraMap A C) (D.f : PowerSeries A) =
        (D.f.map (algebraMap A C) : PowerSeries C) :=
      Polynomial.polynomial_map_coe.symm
    rw [hmap, PowerSeries.eval₂_coe, Polynomial.aeval_def,
      Polynomial.eval₂_map]
    calc
      C.subtype (Polynomial.eval₂ (algebraMap A C) (pointC z) D.f) =
          Polynomial.eval₂ (C.subtype.comp (algebraMap A C))
            (C.subtype (pointC z)) D.f :=
        Polynomial.hom_eval₂ D.f (algebraMap A C) C.subtype (pointC z)
      _ = Polynomial.eval₂
          ((algebraMap K E').comp (algebraMap A K))
            (C.subtype (pointC z)) D.f := by rw [hcoeffC]
      _ = Polynomial.eval₂ (algebraMap K E') (C.subtype (pointC z))
          (D.f.map (algebraMap A K)) :=
        (Polynomial.eval₂_map (p := D.f) (algebraMap A K)
          (algebraMap K E') (C.subtype (pointC z))).symm
  have hroot : phi (pointB (y n)) = pointC (D.pi • y (n + 1)) := by
    apply Subtype.ext
    change i (B.subtype (pointB (y n))) = C.subtype (pointC (D.pi • y (n + 1)))
    rw [hyroot n, D.root_alg_hom K n]
    change Polynomial.aeval (D.root K (n + 1))
        (D.f.map (algebraMap A K)) =
      C.subtype (FGLaw.APts.toIdeal hJ
        (F.map (algebraMap A C)) (D.pi • y (n + 1)))
    rw [hpolyEval, hyroot (n + 1)]
  have hpoint := reduction_alg_hom D hI hJ phi
    hphi hphiJ hfield n (y n) (hy n) (y (n + 1)) (hy (n + 1)) hroot u
  have hrootAction :
      i (rootOrbit n (quotientUnitReduction D.pi n u) (D.root K n)) =
        rootOrbit (n + 1) u (i (D.root K n)) := by
    rw [hrootOrbit n, D.root_alg_hom K n]
    rw [← Polynomial.aeval_algHom_apply, hrootOrbit (n + 1)]
    change C.subtype (phi (pointB
        (orbitEmbeddingTorsion (y n) (hy n)
          (quotientUnitReduction D.pi n u)))) = _
    calc
      C.subtype (phi (pointB
          (orbitEmbeddingTorsion (y n) (hy n)
            (quotientUnitReduction D.pi n u)))) =
          C.subtype (pointC
            (D.pi • orbitEmbeddingTorsion
              (y (n + 1)) (hy (n + 1)) u)) := congrArg C.subtype hpoint
      _ = Polynomial.aeval
          (C.subtype (pointC (orbitEmbeddingTorsion
            (y (n + 1)) (hy (n + 1)) u)))
          (D.f.map (algebraMap A K)) := by
        exact hpolyEval
          (orbitEmbeddingTorsion
            (y (n + 1)) (hy (n + 1)) u)
  have hrootHom :
      i.comp (rootOrbit n (quotientUnitReduction D.pi n u)).toAlgHom =
        (rootOrbit (n + 1) u).toAlgHom.comp i := by
    apply AdjoinRoot.algHom_ext
    exact hrootAction
  let e := D.rootTorsionLevel K Omega hfield n
  let e' := D.rootTorsionLevel K Omega hfield (n + 1)
  obtain ⟨x0, rfl⟩ := e.surjective x
  change IntermediateField.inclusion
      (D.torsion_mono_succ K Omega n)
      ((AlgEquiv.autCongr e
        (rootOrbit n (quotientUnitReduction D.pi n u))) (e x0)) =
    (AlgEquiv.autCongr e' (rootOrbit (n + 1) u))
      (IntermediateField.inclusion
        (D.torsion_mono_succ K Omega n) (e x0))
  simp only [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply]
  change IntermediateField.inclusion
      (D.torsion_mono_succ K Omega n)
      (e (rootOrbit n (quotientUnitReduction D.pi n u) x0)) =
    e' (rootOrbit (n + 1) u
      (e'.symm (IntermediateField.inclusion
        (D.torsion_mono_succ K Omega n) (e x0))))
  have hsquare := D.torsion_level_succ K Omega hfield n
  have hsquare_x0 := DFunLike.congr_fun hsquare x0
  have hsquare_orbit := DFunLike.congr_fun hsquare
    (rootOrbit n (quotientUnitReduction D.pi n u) x0)
  change IntermediateField.inclusion
      (D.torsion_mono_succ K Omega n) (e x0) =
    e' (i x0) at hsquare_x0
  change IntermediateField.inclusion
      (D.torsion_mono_succ K Omega n)
        (e (rootOrbit n (quotientUnitReduction D.pi n u) x0)) =
    e' (i (rootOrbit n (quotientUnitReduction D.pi n u) x0)) at hsquare_orbit
  calc
    IntermediateField.inclusion
        (D.torsion_mono_succ K Omega n)
        (e (rootOrbit n (quotientUnitReduction D.pi n u) x0)) =
      e' (i (rootOrbit n (quotientUnitReduction D.pi n u) x0)) :=
        hsquare_orbit
    _ = e' (rootOrbit (n + 1) u (i x0)) :=
      congrArg e' (DFunLike.congr_fun hrootHom x0)
    _ = e' (rootOrbit (n + 1) u
        (e'.symm (IntermediateField.inclusion
          (D.torsion_mono_succ K Omega n) (e x0)))) := by
      rw [hsquare_x0, e'.symm_apply_apply]

end LTDatum

end

end Submission.CField.LTate
