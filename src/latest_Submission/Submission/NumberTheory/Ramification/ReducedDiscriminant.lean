import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Discriminant

/-!
# Reduced finite algebras and discriminants

This file formalizes the trace-pairing direction of Milne's Lemma 3.38.  The converse over a
perfect field is obtained by decomposing a reduced finite-dimensional commutative algebra into
a finite product of finite separable field extensions.
-/

namespace Submission.NumberTheory.Milne

open Module

universe u v w

/-- For a basis of a finite-dimensional commutative algebra over a field, nonvanishing of the
discriminant is exactly nondegeneracy of the trace pairing. -/
theorem discr_form_nondegenerate
    (K B : Type*) [Field K] [CommRing B] [Algebra K B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K B) :
    Algebra.discr K b ≠ 0 ↔ (Algebra.traceForm K B).Nondegenerate := by
  rw [Algebra.discr_def, Algebra.traceMatrix_of_basis]
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
    (B := Algebra.traceForm K B) b).symm

/-- The nonvanishing-discriminant implication in Milne's Lemma 3.38 does not require the base
field to be perfect. -/
theorem reduced_discr_zero
    (K B : Type*) [Field K] [CommRing B] [Algebra K B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K B) (hdisc : Algebra.discr K b ≠ 0) :
    IsReduced B := by
  have hnondeg : (Algebra.traceForm K B).Nondegenerate :=
    (discr_form_nondegenerate K B b).mp hdisc
  constructor
  intro x hx
  apply hnondeg.1 x
  intro y
  rw [Algebra.traceForm_apply]
  exact (Algebra.isNilpotent_trace_of_isNilpotent
    ((Commute.all x y).isNilpotent_mul_right hx)).eq_zero

/-- Nondegeneracy of the trace pairing is preserved by an algebra equivalence. -/
theorem form_nondegenerate_alg
    (K B C : Type*) [Field K]
    [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
    (e : B ≃ₐ[K] C)
    (h : (Algebra.traceForm K C).Nondegenerate) :
    (Algebra.traceForm K B).Nondegenerate := by
  constructor
  · intro x hx
    apply e.injective
    rw [map_zero]
    apply h.1 (e x)
    intro z
    obtain ⟨y, rfl⟩ := e.surjective z
    rw [Algebra.traceForm_apply, ← map_mul, Algebra.trace_eq_of_algEquiv]
    exact hx y
  · intro y hy
    apply e.injective
    rw [map_zero]
    apply h.2 (e y)
    intro z
    obtain ⟨x, rfl⟩ := e.surjective z
    rw [Algebra.traceForm_apply, ← map_mul, Algebra.trace_eq_of_algEquiv]
    exact hy x

/-- The trace pairing on a binary product is nondegenerate when the trace pairings on both
factors are nondegenerate. -/
theorem form_prod_nondegenerate
    (K B C : Type*) [Field K]
    [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
    [Module.Free K B] [Module.Finite K B]
    [Module.Free K C] [Module.Finite K C]
    (hB : (Algebra.traceForm K B).Nondegenerate)
    (hC : (Algebra.traceForm K C).Nondegenerate) :
    (Algebra.traceForm K (B × C)).Nondegenerate := by
  constructor
  · intro x hx
    apply Prod.ext
    · apply hB.1 x.1
      intro y
      have h := hx (y, 0)
      simpa [Algebra.traceForm_apply, Algebra.trace_prod_apply] using h
    · apply hC.1 x.2
      intro y
      have h := hx (0, y)
      simpa [Algebra.traceForm_apply, Algebra.trace_prod_apply] using h
  · intro y hy
    apply Prod.ext
    · apply hB.2 y.1
      intro x
      have h := hy (x, 0)
      simpa [Algebra.traceForm_apply, Algebra.trace_prod_apply] using h
    · apply hC.2 y.2
      intro x
      have h := hy (0, x)
      simpa [Algebra.traceForm_apply, Algebra.trace_prod_apply] using h

/-- A finite product of finite separable field extensions has nondegenerate trace pairing. -/
private theorem form_pi_nondegenerate
    (K : Type u) [Field K] :
    ∀ (n : ℕ) (L : Fin n → Type v)
      [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
      [∀ i, Module.Finite K (L i)] [∀ i, Algebra.IsSeparable K (L i)],
      (Algebra.traceForm K (∀ i, L i)).Nondegenerate := by
  intro n
  induction n with
  | zero =>
      intro L instField instAlgebra instFinite instSeparable
      constructor <;> intro x _ <;> exact Subsingleton.elim x 0
  | succ n ih =>
      intro L instField instAlgebra instFinite instSeparable
      let L' : Option (Fin n) → Type v := fun o => L (finSuccEquivLast.symm o)
      letI (o : Option (Fin n)) : Field (L' o) := instField _
      letI (o : Option (Fin n)) : Algebra K (L' o) := instAlgebra _
      letI (o : Option (Fin n)) : Module.Finite K (L' o) := instFinite _
      letI (o : Option (Fin n)) : Algebra.IsSeparable K (L' o) := instSeparable _
      let reindex : (∀ i, L i) ≃ₐ[K] ∀ o, L' o :=
        AlgEquiv.piCongrLeft' K L finSuccEquivLast
      let split : (∀ o, L' o) ≃ₐ[K]
          L' none × (∀ i, L' (some i)) :=
        { __ := RingEquiv.piOptionEquivProd
          commutes' := fun _ => rfl }
      have hlast : (Algebra.traceForm K (L' none)).Nondegenerate := by
        exact traceForm_nondegenerate K (L' none)
      have hprefix :
          (Algebra.traceForm K (∀ i, L' (some i))).Nondegenerate := by
        exact ih (fun i => L' (some i))
      have hprod :
          (Algebra.traceForm K (L' none × (∀ i, L' (some i)))).Nondegenerate :=
        form_prod_nondegenerate K _ _ hlast hprefix
      exact form_nondegenerate_alg K _ _ (reindex.trans split) hprod

/-- The reduced implication in Milne's Lemma 3.38: over a perfect field, a reduced
finite-dimensional commutative algebra has nonzero discriminant in every basis. -/
theorem discr_ne_reduced
    (K : Type u) (B : Type v) [Field K] [PerfectField K]
    [CommRing B] [Algebra K B] [Module.Finite K B] [IsReduced B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K B) :
    Algebra.discr K b ≠ 0 := by
  classical
  letI : IsArtinianRing B := IsArtinianRing.of_finite K B
  letI (I : MaximalSpectrum B) : Field (B ⧸ I.asIdeal) :=
    Ideal.Quotient.field I.asIdeal
  letI (I : MaximalSpectrum B) : Module.Finite K (B ⧸ I.asIdeal) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  letI (I : MaximalSpectrum B) : Algebra.IsSeparable K (B ⧸ I.asIdeal) :=
    inferInstance
  let e : B ≃ₐ[K] ∀ I : MaximalSpectrum B, B ⧸ I.asIdeal :=
    (IsArtinianRing.equivPi B).restrictScalars K
  have hprod :
      (Algebra.traceForm K (∀ I : MaximalSpectrum B, B ⧸ I.asIdeal)).Nondegenerate := by
    letI := Fintype.ofFinite (MaximalSpectrum B)
    let idx := Fintype.equivFin (MaximalSpectrum B)
    let reindex : (∀ I : MaximalSpectrum B, B ⧸ I.asIdeal) ≃ₐ[K]
        ∀ j : Fin (Fintype.card (MaximalSpectrum B)), B ⧸ (idx.symm j).asIdeal :=
      AlgEquiv.piCongrLeft' K (fun I : MaximalSpectrum B => B ⧸ I.asIdeal) idx
    have hfin :
        (Algebra.traceForm K
          (∀ j : Fin (Fintype.card (MaximalSpectrum B)),
            B ⧸ (idx.symm j).asIdeal)).Nondegenerate := by
      apply form_pi_nondegenerate K
    exact form_nondegenerate_alg K _ _ reindex hfin
  apply (discr_form_nondegenerate K B b).mpr
  exact form_nondegenerate_alg K B _ e hprod

/-- **Lemma 3.38.** A finite-dimensional commutative algebra over a perfect field is reduced if
and only if its discriminant in a basis is nonzero. -/
theorem reduced_discr_ne
    (K : Type u) (B : Type v) [Field K] [PerfectField K]
    [CommRing B] [Algebra K B] [Module.Finite K B]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K B) :
    IsReduced B ↔ Algebra.discr K b ≠ 0 := by
  constructor
  · intro h
    letI : IsReduced B := h
    exact discr_ne_reduced K B b
  · exact reduced_discr_zero K B b

end Submission.NumberTheory.Milne
