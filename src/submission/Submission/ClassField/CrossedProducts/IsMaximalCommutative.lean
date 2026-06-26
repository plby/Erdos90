import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Submission.ClassField.CrossedProducts.EndRestrictScalars


/-!
# Chapter IV, Corollary 3.4

Maximal subfields of a central simple algebra are characterized both by their
centralizers and by their dimensions.
-/

namespace Submission.CField.CProduca

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]

/-- A commutative subalgebra is maximal when it has no larger commutative
subalgebra. The commutativity of the specified subalgebra is kept as a
hypothesis, matching the use for subfields below. -/
def IsMaximalCommutative (L : Subalgebra k A) : Prop :=
  ∀ M : Subalgebra k A, L ≤ M → (∀ x y : M, x * y = y * x) → M = L

variable (k A) [IsSimpleRing A] [Algebra.IsCentral k A] [Module.Finite k A]
variable (L : Subalgebra k A) [IsSimpleRing L]
  (hL : ∀ x y : L, x * y = y * x)

include hL

private abbrev Centralizer := Subalgebra.centralizer k (L : Set A)

omit [IsSimpleRing A] [Algebra.IsCentral k A] [Module.Finite k A] [IsSimpleRing ↥L] in
private theorem le_centralizer : L ≤ Centralizer k A L := by
  intro x hx
  rw [Subalgebra.mem_centralizer_iff]
  intro y hy
  simpa using congrArg Subtype.val
    (hL (⟨y, hy⟩ : L) (⟨x, hx⟩ : L))

/-- For a subfield, being self-centralizing is equivalent to having square
dimension in the ambient central simple algebra. -/
theorem centralizer_finrank_sq :
    Centralizer k A L = L ↔
      Module.finrank k A = (Module.finrank k L) ^ 2 := by
  let C := Centralizer k A L
  letI : Module.Finite k L :=
    Module.Finite.of_injective L.val.toLinearMap Subtype.val_injective
  letI : Module.Finite k C :=
    Module.Finite.of_injective C.val.toLinearMap Subtype.val_injective
  constructor
  · intro hC
    have hdim : Module.finrank k L * Module.finrank k C =
        Module.finrank k A := by
      simpa [C, Centralizer] using finrank_mul_centralizer k A L
    change C = L at hC
    rw [hC] at hdim
    simpa [pow_two] using hdim.symm
  · intro hdim
    have hprod : Module.finrank k L * Module.finrank k C =
        Module.finrank k A := by
      simpa [C, Centralizer] using finrank_mul_centralizer k A L
    have hmul : Module.finrank k L * Module.finrank k C =
        Module.finrank k L * Module.finrank k L := by
      calc
        Module.finrank k L * Module.finrank k C = Module.finrank k A := hprod
        _ = (Module.finrank k L) ^ 2 := hdim
        _ = Module.finrank k L * Module.finrank k L := by rw [pow_two]
    have hCdim : Module.finrank k C = Module.finrank k L :=
      Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := k) (M := L)) hmul
    exact (Subalgebra.eq_of_le_of_finrank_eq
      (le_centralizer k A L hL) hCdim.symm).symm

/-- Milne, Corollary IV.3.4: self-centralizing, square dimension, and maximal
commutativity are equivalent for a subfield of a central simple algebra. -/
theorem self_centralizing_commutative :
    (Centralizer k A L = L ↔
      Module.finrank k A = (Module.finrank k L) ^ 2) ∧
    (Module.finrank k A = (Module.finrank k L) ^ 2 ↔
      IsMaximalCommutative L) := by
  refine ⟨centralizer_finrank_sq k A L hL, ?_⟩
  let C := Centralizer k A L
  constructor
  · intro hdim M hLM hMcomm
    have hC : C = L := (centralizer_finrank_sq k A L hL).2 hdim
    apply le_antisymm
    · intro x hx
      rw [← hC]
      rw [Subalgebra.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val
        (hMcomm ⟨y, hLM hy⟩ ⟨x, hx⟩)
    · exact hLM
  · intro hmax
    apply (centralizer_finrank_sq k A L hL).1
    apply le_antisymm
    · intro z hz
      let s : Set A := (L : Set A) ∪ {z}
      have hscomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
        intro x hx y hy
        rcases hx with hxL | rfl <;> rcases hy with hyL | rfl
        · simpa using congrArg Subtype.val
            (hL (⟨x, hxL⟩ : L) (⟨y, hyL⟩ : L))
        · exact Iff.mp (Subalgebra.mem_centralizer_iff k) hz x hxL
        · exact (Iff.mp (Subalgebra.mem_centralizer_iff k) hz y hyL).symm
        · rfl
      let M := Algebra.adjoin k s
      letI : IsMulCommutative M := Algebra.isMulCommutative_adjoin k hscomm
      letI : CommRing M :=
        { (inferInstance : Ring M) with mul_comm := mul_comm' }
      have hLM : L ≤ M := by
        intro x hx
        exact Algebra.subset_adjoin (Or.inl hx)
      have hML : M = L := hmax M hLM fun x y => mul_comm x y
      have hzM : z ∈ M := Algebra.subset_adjoin (Or.inr (Set.mem_singleton z))
      rw [hML] at hzM
      exact hzM
    · exact le_centralizer k A L hL

end Submission.CField.CProduca
