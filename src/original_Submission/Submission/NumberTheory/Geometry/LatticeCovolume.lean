import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# Milne, Algebraic Number Theory, Remark 4.16

The covolume of a full lattice is the absolute determinant of a lattice basis and is therefore
independent of the chosen basis.  For nested full lattices, the ratio of covolumes is the relative
index.
-/

namespace Submission.NumberTheory.Milne

open Module Submodule

/-- Remark 4.16(a): the covolume of a full lattice in `ℝ^ι` is the absolute determinant
of any `ℤ`-basis of the lattice. -/
theorem covolume_abs_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis ι ℤ L) :
    ZLattice.covolume L = |(Matrix.of ((↑) ∘ b)).det| :=
  ZLattice.covolume_eq_det L b

/-- Remark 4.16(b): for full lattices `L₁ ⊆ L₂`, the ratio of covolumes is the
relative index `[L₂ : L₁]`. -/
theorem covolume_div_rel
    {ι : Type*} [Fintype ι]
    (L₁ L₂ : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L₁] [IsZLattice ℝ L₁]
    [DiscreteTopology L₂] [IsZLattice ℝ L₂]
    (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ / ZLattice.covolume L₂ =
      L₁.toAddSubgroup.relIndex L₂.toAddSubgroup :=
  ZLattice.covolume_div_covolume_eq_relIndex L₁ L₂ h

end Submission.NumberTheory.Milne
