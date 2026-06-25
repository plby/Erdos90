import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Towers.NumberTheory.ClassGroup.MinkowskiClassBound

/-!
# Milne, Algebraic Number Theory, Propositions 4.26 and 4.27

The image of a nonzero integral ideal under the mixed canonical embedding is a full lattice.
Its covolume is the numerical ideal norm times the usual discriminant factor.  Minkowski's
theorem then supplies a nonzero element of the ideal whose field norm is bounded by the
Minkowski constant times the numerical ideal norm.
-/

namespace Towers.NumberTheory.Milne

open Module NumberField NumberField.InfinitePlace Ideal MeasureTheory
open scoped nonZeroDivisors NumberField Real

variable (K : Type*) [Field K] [NumberField K]

/-- The lattice `sigma(I)` attached to a nonzero integral ideal `I`. -/
noncomputable abbrev milneIdealLattice (I : (Ideal (𝓞 K))⁰) :
    Submodule ℤ (mixedEmbedding.mixedSpace K) :=
  mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K I)

/-- The points of `milneIdealLattice K I` are exactly the mixed embeddings of elements of
the integral ideal `I`. -/
theorem milne_ideal_lattice {I : (Ideal (𝓞 K))⁰}
    {x : mixedEmbedding.mixedSpace K} :
    x ∈ milneIdealLattice K I ↔
      ∃ a : 𝓞 K, a ∈ (I : Ideal (𝓞 K)) ∧ mixedEmbedding K (a : K) = x := by
  simp only [milneIdealLattice, mixedEmbedding.mem_idealLattice,
    FractionalIdeal.coe_mk0]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, hax⟩
    exact ⟨a, ha, hax⟩
  · rintro ⟨a, ha, hax⟩
    exact ⟨(a : K), ⟨a, ha, rfl⟩, hax⟩

open scoped Classical in
/-- Milne, Proposition 4.26: the image of a nonzero integral ideal under the mixed
canonical embedding is a full lattice. -/
theorem milne_lattice_full (I : (Ideal (𝓞 K))⁰) :
    IsZLattice ℝ
      (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K I)) := by
  infer_instance

open scoped Classical in
/-- Milne, Proposition 4.26: the covolume of `sigma(I)` is
`2^(-s) * N(I) * sqrt(|Delta_K|)`. -/
theorem covolume_milne_lattice (I : (Ideal (𝓞 K))⁰) :
    ZLattice.covolume
        (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K I)) =
      (2 : ℝ)⁻¹ ^ nrComplexPlaces K * Ideal.absNorm (I : Ideal (𝓞 K)) *
        Real.sqrt |NumberField.discr K| := by
  rw [mixedEmbedding.covolume_idealLattice,
    FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
  ring

/-- Milne, Proposition 4.27: a nonzero integral ideal contains a nonzero element whose
absolute field norm is at most the Minkowski bound times the numerical ideal norm. -/
theorem ne_milne_minkowski
    (I : (Ideal (𝓞 K))⁰) :
    ∃ a : 𝓞 K, a ∈ (I : Ideal (𝓞 K)) ∧ a ≠ 0 ∧
      |Algebra.norm ℚ (a : K)| ≤
        milneMinkowskiBound K * Ideal.absNorm (I : Ideal (𝓞 K)) := by
  obtain ⟨a, ha, ha0, haNorm⟩ :=
    NumberField.exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr K
      (FractionalIdeal.mk0 K I)
  rw [FractionalIdeal.coe_mk0] at ha haNorm
  obtain ⟨a, haI, rfl⟩ :=
    (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp ha
  refine ⟨a, haI, ?_, ?_⟩
  · exact RingOfIntegers.coe_ne_zero_iff.mp ha0
  · rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast] at haNorm
    simpa [milneMinkowskiBound, milneMinkowskiConstant, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using haNorm

/-- Proposition 4.27 with a plain ideal and an explicit nonzero hypothesis. -/
theorem milne_minkowski_bound
    (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    ∃ a : 𝓞 K, a ∈ I ∧ a ≠ 0 ∧
      |Algebra.norm ℚ (a : K)| ≤ milneMinkowskiBound K * Ideal.absNorm I := by
  exact ne_milne_minkowski K
    ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩

end Towers.NumberTheory.Milne
