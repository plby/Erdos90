import Mathlib.FieldTheory.JacobsonNoether
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# Chapter IV, Lemma 3.9

The Jacobson--Noether theorem supplies a noncentral separable element in every
nontrivial finite-dimensional central division algebra.  The subfield it
generates is the proper separable subfield asserted by Milne's lemma.
-/

namespace Towers.CField.CProduca

universe u

variable (k D : Type u) [Field k] [DivisionRing D] [Algebra k D]
  [Algebra.IsCentral k D] [Module.Finite k D]

/-- Milne, Lemma IV.3.9, in its equivalent primitive-element form: a central
division algebra other than its base field contains a separable element not
belonging to the base field. -/
theorem separable_not_base
    (hneq : (⊥ : Subalgebra k D) ≠ ⊤) :
    ∃ x : D, x ∉ (⊥ : Subalgebra k D) ∧ IsSeparable k x := by
  letI : Algebra.IsAlgebraic k D := Algebra.IsAlgebraic.of_finite k D
  exact JacobsonNoether.exists_separable_and_not_isCentral' hneq

/-- Milne, Lemma IV.3.9: a nontrivial central division algebra contains a
proper commutative simple subalgebra which is separable over the base field.
Thus this subalgebra is the required proper separable subfield. -/
theorem proper_separable_subfield
    (hneq : (⊥ : Subalgebra k D) ≠ ⊤) :
    ∃ L : Subalgebra k D, L ≠ ⊥ ∧ IsSimpleRing L ∧
      (∀ a b : L, a * b = b * a) ∧ Algebra.IsSeparable k L := by
  obtain ⟨x, hxbot, hxsep⟩ := separable_not_base k D hneq
  let L : Subalgebra k D := Algebra.adjoin k {x}
  let xL : L := ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩
  letI : Module.Finite k L :=
    Module.Finite.of_injective L.val.toLinearMap Subtype.val_injective
  letI : Field L := fieldOfFiniteDimensional k L
  have hxLsep : IsSeparable k xL := by
    rw [← isSeparable_map_iff L.val Subtype.val_injective]
    exact hxsep
  have hadjoin : Algebra.adjoin k ({xL} : Set L) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rcases y with ⟨y, hy⟩
    exact Algebra.adjoin_induction
      (p := fun y hy => (⟨y, hy⟩ : L) ∈ Algebra.adjoin k ({xL} : Set L))
      (fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact Algebra.subset_adjoin (Set.mem_singleton xL))
      (fun r => (Algebra.adjoin k ({xL} : Set L)).algebraMap_mem r)
      (fun _ _ _ _ iy iz => (Algebra.adjoin k ({xL} : Set L)).add_mem iy iz)
      (fun _ _ _ _ iy iz => (Algebra.adjoin k ({xL} : Set L)).mul_mem iy iz)
      hy
  have hsepL : Algebra.IsSeparable k L := by
    have hif : IntermediateField.adjoin k ({xL} : Set L) = ⊤ :=
      (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic
        (F := k) (E := L) (by
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst y
          exact hxLsep.isIntegral.isAlgebraic)).2 hadjoin
    have hsepif : Algebra.IsSeparable k
        (IntermediateField.adjoin k ({xL} : Set L)) :=
      (IntermediateField.isSeparable_adjoin_iff_isSeparable k _).2 (by
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact hxLsep)
    rw [hif] at hsepif
    letI := hsepif
    exact AlgEquiv.Algebra.isSeparable (IntermediateField.topEquiv :
      (⊤ : IntermediateField k L) ≃ₐ[k] L)
  have hLne : L ≠ ⊥ := by
    intro hL
    apply hxbot
    have hxmem : x ∈ L := Algebra.subset_adjoin (Set.mem_singleton x)
    rw [hL] at hxmem
    exact hxmem
  exact ⟨L, hLne, inferInstance, fun a b => mul_comm a b, hsepL⟩

end Towers.CField.CProduca
