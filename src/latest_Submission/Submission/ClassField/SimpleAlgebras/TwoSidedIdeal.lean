import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Milne, Class Field Theory, Proposition IV.1.9

For a semisimple ring, the isotypic components of its left regular module are
exactly its minimal nonzero two-sided ideals. Every two-sided ideal is their
independent sum.
-/

namespace Submission.CField.SAlgebr

universe u

variable {A : Type u} [Ring A]

/-- A minimal nonzero two-sided ideal, phrased in the lattice of left ideals. -/
def MinimalSidedIdeal (I : Ideal A) : Prop :=
  I.IsTwoSided ∧ I ≠ ⊥ ∧
    ∀ J : Ideal A, J.IsTwoSided → J ≤ I → J = ⊥ ∨ J = I

variable [IsSemisimpleModule A A]

/-- **Proposition IV.1.9, first part.** The isotypic components of the left
regular module are exactly the minimal nonzero two-sided ideals. -/
theorem isotypic_components_sided (I : Ideal A) :
    I ∈ isotypicComponents A A ↔ MinimalSidedIdeal I := by
  constructor
  · intro hI
    refine ⟨isFullyInvariant_iff_isTwoSided.mp
      (.of_mem_isotypicComponents hI),
      (bot_lt_isotypicComponents hI).ne', ?_⟩
    intro J hJtwo hJI
    by_cases hJ : J = ⊥
    · exact Or.inl hJ
    · right
      obtain ⟨S, hSJ, hS⟩ :=
        (IsSemisimpleModule.eq_bot_or_exists_simple_le J).resolve_left hJ
      letI : IsSimpleModule A S := hS
      have hcompJ : isotypicComponent A A S ≤ J :=
        isFullyInvariant_iff_le_imp_isotypicComponent_le.mp
          (isFullyInvariant_iff_isTwoSided.mpr hJtwo) S hSJ
      exact le_antisymm hJI
        ((eq_isotypicComponent_of_le hI (hSJ.trans hJI)).trans_le hcompJ)
  · rintro ⟨hItwo, hI, hmin⟩
    obtain ⟨S, hSI, hS⟩ :=
      (IsSemisimpleModule.eq_bot_or_exists_simple_le I).resolve_left hI
    letI : IsSimpleModule A S := hS
    have hcompI : isotypicComponent A A S ≤ I :=
      isFullyInvariant_iff_le_imp_isotypicComponent_le.mp
        (isFullyInvariant_iff_isTwoSided.mpr hItwo) S hSI
    have hcompTwo : Ideal.IsTwoSided (isotypicComponent A A S : Ideal A) :=
      isFullyInvariant_iff_isTwoSided.mp
        (.isotypicComponent A A S)
    have hcomp : isotypicComponent A A S = I :=
      (hmin _ hcompTwo hcompI).resolve_left
        (bot_lt_isotypicComponent S).ne'
    exact ⟨S, inferInstance, hcomp.symm⟩

/-- **Proposition IV.1.9, second part.** Every two-sided ideal is the supremum
of an independent set of minimal two-sided ideals. -/
theorem independent_sided_ideals (I : Ideal A)
    (hI : I.IsTwoSided) :
    ∃ C : Set (Ideal A),
      (∀ J ∈ C, MinimalSidedIdeal J) ∧
      sSupIndep C ∧ I = sSup C := by
  obtain ⟨C, hC, hIC⟩ :=
    isFullyInvariant_iff_sSup_isotypicComponents.mp
      (isFullyInvariant_iff_isTwoSided.mpr hI)
  refine ⟨C, fun J hJ ↦
    (isotypic_components_sided J).mp (hC hJ),
    (sSupIndep_isotypicComponents A A).mono hC, hIC⟩

end Submission.CField.SAlgebr
