import Submission.NumberTheory.Completions.DifferentCompletionTrace
import Mathlib.RingTheory.Localization.Module

/-!
# Trace-dual bases before and after completion

This file connects the abstract scalar-extension result for trace-dual
lattices with an integral basis.  An integral basis first gives a basis of
the fraction-field extension by localization.  Its trace-dual basis spans
the global codifferent lattice, and extending scalars carries that basis to
the trace-dual of the extended lattice.
-/

namespace Submission.NumberTheory.Milne

open Module Submodule nonZeroDivisors
open scoped TensorProduct

noncomputable section

universe u

variable (A B K L : Type u)
  [CommRing A] [CommRing B] [Field K] [Field L]
  [Algebra A K] [Algebra A B] [Algebra B L] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsFractionRing A K]
  [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L]

/-- If `b` is an integral basis, then the global trace-dual lattice is
spanned over the base ring by the trace-dual of the induced fraction-field
basis. -/
theorem dual_restrict_scalars
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι A B) :
    (Submodule.traceDual A K (1 : Submodule B L)).restrictScalars A =
      Submodule.span A
        (Set.range (b.localizationLocalization K A⁰ L).traceDual) := by
  apply Submodule.traceDual_span_of_basis A
  rw [b.localizationLocalization_span K A⁰ L]
  ext x
  simp

/-- After extending the fraction field, the trace-dual of the lattice
spanned by a localized integral basis is spanned by the scalar extensions
of its global trace-dual basis.  This is the basis-level compatibility used
when the scalar extension is an adic completion. -/
theorem dual_submodule_localization
    (F C : Type u) [Field F] [Algebra K F] [CommRing C] [Algebra C F]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι A B) :
    (Algebra.traceForm F (F ⊗[K] L)).dualSubmodule
        (Submodule.span C
          (Set.range
            (Algebra.TensorProduct.basis F
              (b.localizationLocalization K A⁰ L)))) =
      Submodule.span C
        (Set.range
          (Algebra.TensorProduct.basis F
            (b.localizationLocalization K A⁰ L).traceDual)) := by
  exact dual_submodule_basis K F L
    (b.localizationLocalization K A⁰ L)

/-- The same compatibility, expressed without choosing generators on the
right: the completed trace-dual lattice is the span of the pure-tensor image
of the entire global trace-dual lattice. -/
theorem dual_submodule_image
    (F C : Type u) [Field F] [Algebra K F] [CommRing C] [Algebra C F]
    [Algebra A C] [Algebra A F]
    [IsScalarTower A K F] [IsScalarTower A C F]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {ι : Type*} [Finite ι] (b : Basis ι A B) :
    (Algebra.traceForm F (F ⊗[K] L)).dualSubmodule
        (Submodule.span C
          (Set.range
            (Algebra.TensorProduct.basis F
              (b.localizationLocalization K A⁰ L)))) =
      Submodule.span C
        ((fun x : L => (1 : F) ⊗ₜ[K] x) ''
          (Submodule.traceDual A K (1 : Submodule B L) : Set L)) := by
  classical
  rw [dual_submodule_localization
    A B K L F C b]
  let bK : Basis ι K L := b.localizationLocalization K A⁰ L
  let D : Submodule B L := Submodule.traceDual A K (1 : Submodule B L)
  have hD : D.restrictScalars A =
      Submodule.span A (Set.range bK.traceDual) :=
    dual_restrict_scalars
      A B K L b
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨bK.traceDual i, ?_, ?_⟩
    · change bK.traceDual i ∈ D
      have hi : bK.traceDual i ∈ D.restrictScalars A := by
        rw [hD]
        exact Submodule.subset_span (Set.mem_range_self i)
      exact hi
    · simp [bK]
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Submodule.span A (Set.range bK.traceDual) := by
      rw [← hD]
      exact hx
    refine Submodule.span_induction
      (p := fun y _ => (1 : F) ⊗ₜ[K] y ∈
        Submodule.span C
          (Set.range (Algebra.TensorProduct.basis F bK.traceDual)))
      ?_ ?_ ?_ ?_ hx'
    · rintro _ ⟨i, rfl⟩
      apply Submodule.subset_span
      exact ⟨i, by simp [bK]⟩
    · simp
    · intro x y _ _ hx hy
      simpa only [TensorProduct.tmul_add] using
        Submodule.add_mem _ hx hy
    · intro a x _ ih
      have hmem := Submodule.smul_mem
        (Submodule.span C
          (Set.range (Algebra.TensorProduct.basis F bK.traceDual)))
        (algebraMap A C a) ih
      have heq : (1 : F) ⊗ₜ[K] (a • x) =
          (algebraMap A C a) • ((1 : F) ⊗ₜ[K] x) := by
        calc
          (1 : F) ⊗ₜ[K] (a • x) =
              (1 : F) ⊗ₜ[K] ((algebraMap A K a) • x) := by
                congr 1
                rw [Algebra.smul_def, Algebra.smul_def,
                  IsScalarTower.algebraMap_apply A K L]
          _ = ((algebraMap A K a) • (1 : F)) ⊗ₜ[K] x :=
            TensorProduct.tmul_smul _ _ _
          _ = algebraMap A F a ⊗ₜ[K] x := by
            rw [Algebra.smul_def, mul_one,
              IsScalarTower.algebraMap_apply A K F]
          _ = algebraMap C F (algebraMap A C a) ⊗ₜ[K] x := by
            rw [IsScalarTower.algebraMap_apply A C F]
          _ = (algebraMap A C a) • ((1 : F) ⊗ₜ[K] x) := by
            simp [Algebra.smul_def,
              Algebra.TensorProduct.tmul_mul_tmul]
      rwa [heq]

end

end Submission.NumberTheory.Milne
