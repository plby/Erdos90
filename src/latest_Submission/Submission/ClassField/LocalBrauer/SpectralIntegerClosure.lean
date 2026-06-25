import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Valuation.AlgebraInstances
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Integral
import Submission.ClassField.LocalBrauer.FiniteLocalExtension


/-!
# Spectral integers and integral closure

For a finite extension of a complete nonarchimedean normed field, the unit
ball for the spectral norm is the integral closure of the unit ball in the
base field.  This identifies the abstract integral models used to construct
unramified extensions with the spectral valuation integers used for local
field cohomology.
-/

namespace Submission.CField.LBrauer

noncomputable section

universe u v

open Polynomial

private abbrev normInteger (K : Type u) [NormedField K]
    [IsUltrametricDist K] :=
  Valuation.integer (NormedField.valuation (K := K))

namespace FLExt

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]

omit [CompleteSpace K] in
private theorem norm_integer_coeff (c : K) :
    ‖c‖ ≤ 1 ↔ c ∈ normInteger K := by
  rw [Valuation.mem_integer_iff]
  change ‖c‖₊ ≤ 1 ↔ _
  simp only [NormedField.valuation_apply]

omit [CompleteSpace K] in
/-- An element is integral over the norm unit ball exactly when its spectral
norm is at most one. -/
theorem integral_integer_spectral (x : L) :
    IsIntegral (normInteger K) x ↔ spectralNorm K L x ≤ 1 := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  constructor
  · intro hx
    rw [spectralNorm, spectralValue_le_one_iff
      (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)]
    intro n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hx, coeff_map]
    exact (norm_integer_coeff K _).2
      ((minpoly (normInteger K) x).coeff n).property
  · intro hx
    rw [spectralNorm, spectralValue_le_one_iff
      (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)] at hx
    have hlifts : minpoly K x ∈
        Polynomial.lifts (algebraMap (normInteger K) K) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨(minpoly K x).coeff n,
        (norm_integer_coeff K _).1 (hx n)⟩, rfl⟩
    obtain ⟨p, hpmap, _hpdegree, hpmonic⟩ :=
      Polynomial.lifts_and_degree_eq_and_monic hlifts
        (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
    refine ⟨p, hpmonic, ?_⟩
    calc
      eval₂ (algebraMap (normInteger K) L) x p =
          eval₂ (algebraMap K L) x
            (p.map (algebraMap (normInteger K) K)) := by
        rw [eval₂_map, IsScalarTower.algebraMap_eq (normInteger K) K L]
      _ = eval₂ (algebraMap K L) x (minpoly K x) := by rw [hpmap]
      _ = 0 := by simpa [aeval_def] using minpoly.aeval K x

/-- The valuation integers for the canonical spectral norm are the integral
closure of the base norm-integer ring in the finite extension. -/
theorem spectral_integer_closure :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      spectralNorm.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    IsIntegralClosure
      (Valuation.integer (NormedField.valuation (K := L)))
      (normInteger K) L := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  constructor
  · exact Subtype.coe_injective
  · intro x
    rw [integral_integer_spectral K L x]
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      rw [Valuation.mem_integer_iff]
      change ‖x‖₊ ≤ 1
      change ‖x‖ ≤ 1 at hx
      exact_mod_cast hx
    · rintro ⟨y, rfl⟩
      have hy := y.property
      rw [Valuation.mem_integer_iff] at hy
      change ‖(y : L)‖₊ ≤ 1 at hy
      change ‖(y : L)‖ ≤ 1
      exact_mod_cast hy

end FLExt

section ValuativeBase

open ValuativeRel

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]
variable (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]

omit [IsNonarchimedeanLocalField K] in
/-- The valuation-relation integers and the norm-valuation integers of a
local field are the same subring. -/
theorem valuative_integer_norm :
    Valuation.integer (ValuativeRel.valuation K) = normInteger K := by
  ext x
  simp only [Valuation.mem_integer_iff]
  rw [← (ValuativeRel.valuation K).vle_one_iff,
    ← (NormedField.valuation (K := K)).vle_one_iff]

/-- The canonical equivalence between the two presentations of the base
integer ring. -/
noncomputable def valuativeIntegerNorm :
    Valuation.integer (ValuativeRel.valuation K) ≃+* normInteger K :=
  RingEquiv.subringCongr (valuative_integer_norm K)

/-- The spectral norm valuation extends the norm valuation on the base
field. -/
@[implicit_reducible]
noncomputable def spectralValuationExtension :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      spectralNorm.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  apply Valuation.HasExtension.ofComapInteger
  ext x
  simp only [Subring.mem_comap, Valuation.mem_integer_iff,
    NormedField.valuation_apply]
  have h : ‖algebraMap K L x‖₊ = ‖x‖₊ := by
    apply NNReal.eq
    exact FLExt.norm_algebraMap K L x
  rw [h]

/-- The spectral integer ring is also the integral closure of the
valuation-relation integer ring used throughout the local-field files. -/
theorem spectral_integer_valuative :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      spectralNorm.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    IsIntegralClosure
      (Valuation.integer (NormedField.valuation (K := L)))
      (Valuation.integer (ValuativeRel.valuation K)) L := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : IsIntegralClosure
      (Valuation.integer (NormedField.valuation (K := L)))
      (normInteger K) L :=
    FLExt.spectral_integer_closure K L
  let e := valuativeIntegerNorm K
  have he : (algebraMap (normInteger K) L).comp e.toRingHom =
      algebraMap (Valuation.integer (ValuativeRel.valuation K)) L := by
    ext x
    rfl
  constructor
  · exact Subtype.coe_injective
  · intro x
    rw [e.isIntegral_iff he x]
    exact IsIntegralClosure.isIntegral_iff

/-- Any integral-closure model over the norm-integer ring is canonically
equivalent to the spectral valuation integers, and the equivalence commutes
with their embeddings into the fraction field. -/
noncomputable def modelSpectralInteger
    (U : Type*) [CommRing U] [Algebra (normInteger K) U]
    [Algebra U L] [IsScalarTower (normInteger K) U L]
    [IsIntegralClosure U (normInteger K) L] :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      spectralNorm.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := L)) := spectralValuationExtension K L
    U ≃ₐ[normInteger K]
      Valuation.integer (NormedField.valuation (K := L)) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  letI : IsIntegralClosure
      (Valuation.integer (NormedField.valuation (K := L)))
      (normInteger K) L :=
    FLExt.spectral_integer_closure K L
  exact IsIntegralClosure.equiv (normInteger K) U L
    (Valuation.integer (NormedField.valuation (K := L)))

omit [Valuation.Compatible (NormedField.valuation (K := K))] in
@[simp]
theorem model_spectral_integer
    (U : Type*) [CommRing U] [Algebra (normInteger K) U]
    [Algebra U L] [IsScalarTower (normInteger K) U L]
    [IsIntegralClosure U (normInteger K) L] (x : U) :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      spectralNorm.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := L)) := spectralValuationExtension K L
    algebraMap (Valuation.integer (NormedField.valuation (K := L))) L
        (modelSpectralInteger K L U x) = algebraMap U L x := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  letI : IsIntegralClosure
      (Valuation.integer (NormedField.valuation (K := L)))
      (normInteger K) L :=
    FLExt.spectral_integer_closure K L
  exact IsIntegralClosure.algebraMap_equiv (normInteger K) U L
    (Valuation.integer (NormedField.valuation (K := L))) x

/-- The algebra structure on spectral integers over the valuation-relation
integers, obtained from the equality of the two base integer rings. -/
@[implicit_reducible]
noncomputable def valuativeSpectralAlgebra :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      spectralNorm.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := L)) := spectralValuationExtension K L
    Algebra (Valuation.integer (ValuativeRel.valuation K))
      (Valuation.integer (NormedField.valuation (K := L))) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  exact ((algebraMap (normInteger K)
      (Valuation.integer (NormedField.valuation (K := L)))).comp
    (valuativeIntegerNorm K).toRingHom).toAlgebra

/-- The preceding algebra structure is compatible with the inclusions into
the extension field. -/
@[implicit_reducible]
noncomputable def valuativeSpectralTower :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      spectralNorm.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := L)) := spectralValuationExtension K L
    letI : Algebra (Valuation.integer (ValuativeRel.valuation K))
        (Valuation.integer (NormedField.valuation (K := L))) :=
      valuativeSpectralAlgebra K L
    IsScalarTower (Valuation.integer (ValuativeRel.valuation K))
      (Valuation.integer (NormedField.valuation (K := L))) L := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  letI : Algebra (Valuation.integer (ValuativeRel.valuation K))
      (Valuation.integer (NormedField.valuation (K := L))) :=
    valuativeSpectralAlgebra K L
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- Valuation-relation version of `modelSpectralInteger`, ready
for the unramified integral models constructed in this section. -/
noncomputable def valuativeSpectralInteger
    (U : Type*) [CommRing U]
    [Algebra (Valuation.integer (ValuativeRel.valuation K)) U]
    [Algebra U L]
    [IsScalarTower (Valuation.integer (ValuativeRel.valuation K)) U L]
    [IsIntegralClosure U
      (Valuation.integer (ValuativeRel.valuation K)) L] :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      spectralNorm.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := L)) := spectralValuationExtension K L
    letI : Algebra (Valuation.integer (ValuativeRel.valuation K))
        (Valuation.integer (NormedField.valuation (K := L))) :=
      valuativeSpectralAlgebra K L
    U ≃ₐ[Valuation.integer (ValuativeRel.valuation K)]
      Valuation.integer (NormedField.valuation (K := L)) := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  letI : Algebra (Valuation.integer (ValuativeRel.valuation K))
      (Valuation.integer (NormedField.valuation (K := L))) :=
    valuativeSpectralAlgebra K L
  letI : IsScalarTower (Valuation.integer (ValuativeRel.valuation K))
      (Valuation.integer (NormedField.valuation (K := L))) L :=
    valuativeSpectralTower K L
  letI : IsIntegralClosure
      (Valuation.integer (NormedField.valuation (K := L)))
      (Valuation.integer (ValuativeRel.valuation K)) L :=
    spectral_integer_valuative K L
  exact IsIntegralClosure.equiv
    (Valuation.integer (ValuativeRel.valuation K)) U L
    (Valuation.integer (NormedField.valuation (K := L)))

@[simp]
theorem valuative_spectral_integer
    (U : Type*) [CommRing U]
    [Algebra (Valuation.integer (ValuativeRel.valuation K)) U]
    [Algebra U L]
    [IsScalarTower (Valuation.integer (ValuativeRel.valuation K)) U L]
    [IsIntegralClosure U
      (Valuation.integer (ValuativeRel.valuation K)) L] (x : U) :
    letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
    letI : NontriviallyNormedField L :=
      spectralNorm.nontriviallyNormedField K L
    letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
    letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
    letI : (NormedField.valuation (K := K)).HasExtension
        (NormedField.valuation (K := L)) := spectralValuationExtension K L
    letI : Algebra (Valuation.integer (ValuativeRel.valuation K))
        (Valuation.integer (NormedField.valuation (K := L))) :=
      valuativeSpectralAlgebra K L
    algebraMap (Valuation.integer (NormedField.valuation (K := L))) L
        (valuativeSpectralInteger K L U x) =
      algebraMap U L x := by
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : NontriviallyNormedField L :=
    spectralNorm.nontriviallyNormedField K L
  letI : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra K
  letI : (NormedField.valuation (K := K)).HasExtension
      (NormedField.valuation (K := L)) := spectralValuationExtension K L
  letI : Algebra (Valuation.integer (ValuativeRel.valuation K))
      (Valuation.integer (NormedField.valuation (K := L))) :=
    valuativeSpectralAlgebra K L
  letI : IsScalarTower (Valuation.integer (ValuativeRel.valuation K))
      (Valuation.integer (NormedField.valuation (K := L))) L :=
    valuativeSpectralTower K L
  letI : IsIntegralClosure
      (Valuation.integer (NormedField.valuation (K := L)))
      (Valuation.integer (ValuativeRel.valuation K)) L :=
    spectral_integer_valuative K L
  exact IsIntegralClosure.algebraMap_equiv
    (Valuation.integer (ValuativeRel.valuation K)) U L
    (Valuation.integer (NormedField.valuation (K := L))) x

end ValuativeBase

end

end Submission.CField.LBrauer
