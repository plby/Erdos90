import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.GroupTheory.Index
import Mathlib.Order.ModularLattice

/-!
# Chapter VII, Section 6: a subgroup-index identity

This is Lemma 6.5 in the source.  Mathlib defines `Subgroup.relIndex H K`
as the cardinality of the coset space of `H` in `K`; its value is `0` when
that coset space is infinite.  Consequently the identity below simultaneously
contains the finite-index statement in the book: if two of the three indices
are nonzero, the equality forces the expected finiteness of the third.
-/

namespace Submission.CField.KNIndex

variable {G : Type*} [CommGroup G]

/-- **Lemma VII.6.5.** If `B ≤ A` are subgroups of an abelian group, then

`[A C : B C] * [A ∩ C : B ∩ C] = [A : B]`.

Products of subgroups are joins in the subgroup lattice. -/
theorem subgroup_relIndex
    (A B C : Subgroup G) (hBA : B ≤ A) :
    (B ⊔ C).relIndex (A ⊔ C) *
        (B ⊓ C).relIndex (A ⊓ C) =
      B.relIndex A := by
  have hBmid : B ≤ B ⊔ (A ⊓ C) := le_sup_left
  have hmidA : B ⊔ (A ⊓ C) ≤ A :=
    sup_le hBA inf_le_left
  rw [show A ⊔ C = A ⊔ (B ⊔ C) by
    rw [← sup_assoc, sup_eq_left.mpr hBA]]
  rw [Subgroup.relIndex_sup_right]
  rw [← Subgroup.inf_relIndex_right (B ⊔ C) A]
  have hmodular : (B ⊔ C) ⊓ A = B ⊔ (A ⊓ C) := by
    ext x
    constructor
    · rintro ⟨hx, hxA⟩
      rcases Subgroup.mem_sup.mp hx with ⟨b, hb, c, hc, rfl⟩
      have hcA : c ∈ A := by
        have hbA : b ∈ A := hBA hb
        simpa using A.mul_mem (A.inv_mem hbA) hxA
      exact Subgroup.mem_sup.mpr ⟨b, hb, c, ⟨hcA, hc⟩, rfl⟩
    · intro hx
      rcases Subgroup.mem_sup.mp hx with ⟨b, hb, c, hc, rfl⟩
      exact ⟨Subgroup.mem_sup.mpr ⟨b, hb, c, hc.2, rfl⟩,
        A.mul_mem (hBA hb) hc.1⟩
  rw [hmodular]
  rw [mul_comm]
  rw [← Subgroup.relIndex_mul_relIndex B (B ⊔ (A ⊓ C)) A hBmid hmidA]
  congr 1
  rw [Subgroup.relIndex_sup_left]
  rw [← Subgroup.inf_relIndex_right B (A ⊓ C)]
  have hBC : B ⊓ C = B ⊓ (A ⊓ C) := by
    rw [← inf_assoc, inf_eq_left.mpr hBA]
  rw [hBC]

/-- If `[A : B]` is finite, then both factors in Lemma 6.5 are finite.  For
`Subgroup.relIndex`, nonzero is the finite-index condition. -/
theorem factor_indices_ne
    (A B C : Subgroup G) (hBA : B ≤ A)
    (hfinite : B.relIndex A ≠ 0) :
    (B ⊔ C).relIndex (A ⊔ C) ≠ 0 ∧
      (B ⊓ C).relIndex (A ⊓ C) ≠ 0 := by
  apply mul_ne_zero_iff.mp
  rwa [subgroup_relIndex A B C hBA]

/-- If the two factor indices in Lemma 6.5 are finite, then `[A : B]` is
finite as well. -/
theorem total_index_ne
    (A B C : Subgroup G) (hBA : B ≤ A)
    (hprod : (B ⊔ C).relIndex (A ⊔ C) ≠ 0)
    (hinter : (B ⊓ C).relIndex (A ⊓ C) ≠ 0) :
    B.relIndex A ≠ 0 := by
  rw [← subgroup_relIndex A B C hBA]
  exact mul_ne_zero hprod hinter

end Submission.CField.KNIndex
