import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Milne, Algebraic Number Theory, Proposition 5.8 and Theorem 5.9

The logarithmic image of the unit group is a discrete full lattice, and its kernel is the
finite torsion subgroup.
-/

namespace Submission.NumberTheory.Milne

open Module NumberField NumberField.InfinitePlace
open NumberField.Units
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The discreteness part of Proposition 5.8. -/
theorem log_discrete_topology :
    DiscreteTopology (NumberField.Units.unitLattice K) := by
  infer_instance

/-- **Milne, Proposition 5.8.** The kernel of the logarithmic embedding is exactly the
torsion subgroup, i.e. the roots of unity. -/
theorem log_embedding_torsion :
    (NumberField.Units.logEmbedding K).ker =
      (NumberField.Units.torsion K).toAddSubgroup :=
  NumberField.Units.dirichletUnitTheorem.logEmbedding_ker

/-- The kernel in Proposition 5.8 is finite. -/
theorem log_embedding_finite :
    Finite (NumberField.Units.logEmbedding K).ker := by
  rw [log_embedding_torsion K]
  exact Finite.of_injective
    (fun x : (NumberField.Units.torsion K).toAddSubgroup ↦
      (⟨x.1, x.2⟩ : NumberField.Units.torsion K))
    (fun _ _ h ↦ Subtype.ext (congrArg Subtype.val h))

/-- **Milne, Theorem 5.9 (fullness).** The logarithmic image spans the entire logarithmic
space over `ℝ`. -/
theorem log_image_top :
    Submodule.span ℝ
        (NumberField.Units.unitLattice K :
          Set (NumberField.Units.dirichletUnitTheorem.logSpace K)) = ⊤ :=
  NumberField.Units.dirichletUnitTheorem.unitLattice_span_eq_top K

/-- The rank of the logarithmic unit lattice is `r + s - 1`. -/
theorem log_real_complex :
    finrank ℤ (NumberField.Units.unitLattice K) =
      nrRealPlaces K + nrComplexPlaces K - 1 := by
  rw [NumberField.Units.unitLattice_rank, NumberField.Units.rank,
    card_eq_nrRealPlaces_add_nrComplexPlaces]

end Submission.NumberTheory.Milne
