import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Chapter IV, Example 1.1

The concrete two-dimensional examples at the start of Chapter IV are most naturally
stated in terms of invariant subspaces of the displayed matrices.  This file records the
Jordan-block and diagonal classifications, as well as the scalar-matrix special case.
-/

namespace Submission.CField.SAlgebr

open Matrix

variable {k : Type*} [Field k]

/-- The first standard basis vector of `k^2`. -/
def e0 : Fin 2 -> k := ![1, 0]

/-- The second standard basis vector of `k^2`. -/
def e1 : Fin 2 -> k := ![0, 1]

/-- The first coordinate axis in `k^2`. -/
def firstAxis : Submodule k (Fin 2 -> k) where
  carrier := {x | x 1 = 0}
  zero_mem' := by simp
  add_mem' := by simp_all
  smul_mem' := by simp_all

/-- The second coordinate axis in `k^2`. -/
def secondAxis : Submodule k (Fin 2 -> k) where
  carrier := {x | x 0 = 0}
  zero_mem' := by simp
  add_mem' := by simp_all
  smul_mem' := by simp_all

@[simp]
theorem mem_firstAxis {x : Fin 2 -> k} : x ∈ firstAxis (k := k) ↔ x 1 = 0 :=
  Iff.rfl

@[simp]
theorem mem_secondAxis {x : Fin 2 -> k} : x ∈ secondAxis (k := k) ↔ x 0 = 0 :=
  Iff.rfl

theorem vector_eq_coordinates (x : Fin 2 -> k) :
    x = x 0 • e0 + x 1 • e1 := by
  ext i
  fin_cases i <;> simp [e0, e1]

theorem axis_e_0 {x : Fin 2 -> k} :
    x ∈ firstAxis (k := k) ↔ ∃ c : k, x = c • e0 := by
  constructor
  · intro hx
    change x 1 = 0 at hx
    refine ⟨x 0, ?_⟩
    ext i
    fin_cases i <;> simp [e0, hx]
  · rintro ⟨c, rfl⟩
    simp [firstAxis, e0]

theorem second_axis_e {x : Fin 2 -> k} :
    x ∈ secondAxis (k := k) ↔ ∃ c : k, x = c • e1 := by
  constructor
  · intro hx
    change x 0 = 0 at hx
    refine ⟨x 1, ?_⟩
    ext i
    fin_cases i <;> simp [e1, hx]
  · rintro ⟨c, rfl⟩
    simp [secondAxis, e1]

/-- A subspace is invariant under an endomorphism if the endomorphism maps it into itself. -/
def IsInvariantSubmodule (f : Module.End k (Fin 2 -> k))
    (W : Submodule k (Fin 2 -> k)) : Prop :=
  ∀ x, x ∈ W → f x ∈ W

/-- The nontrivial Jordan block from Example IV.1.1. -/
def jordanEnd (a : k) : Module.End k (Fin 2 -> k) :=
  (!![a, 1; 0, a] : Matrix (Fin 2) (Fin 2) k).mulVecLin

@[simp]
theorem jordanEnd_apply (a : k) (x : Fin 2 -> k) :
    jordanEnd a x = ![a * x 0 + x 1, a * x 1] := by
  ext i
  fin_cases i <;>
    simp [jordanEnd, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem axis_jordan_invariant (a : k) :
    IsInvariantSubmodule (jordanEnd a) firstAxis := by
  intro x hx
  change x 1 = 0 at hx
  change (jordanEnd a x) 1 = 0
  simp [hx]

/-- The Jordan block has exactly one nonzero proper invariant subspace. -/
theorem jordan_submodule_classification (a : k)
    (W : Submodule k (Fin 2 -> k)) (hW : IsInvariantSubmodule (jordanEnd a) W) :
    W = ⊥ ∨ W = firstAxis ∨ W = ⊤ := by
  by_cases hsecond : ∃ x, x ∈ W ∧ x 1 ≠ 0
  · obtain ⟨x, hxW, hx1⟩ := hsecond
    have hdelta : jordanEnd a x - a • x ∈ W :=
      W.sub_mem (hW x hxW) (W.smul_mem a hxW)
    have hdelta_eq : jordanEnd a x - a • x = x 1 • e0 := by
      ext i
      fin_cases i <;> simp [jordanEnd_apply, e0]
    rw [hdelta_eq] at hdelta
    have he0 : e0 ∈ W := by
      have := W.smul_mem (x 1)⁻¹ hdelta
      simpa [smul_smul, hx1] using this
    have htail : x - x 0 • e0 ∈ W := W.sub_mem hxW (W.smul_mem (x 0) he0)
    have htail_eq : x - x 0 • e0 = x 1 • e1 := by
      ext i
      fin_cases i <;> simp [e0, e1]
    rw [htail_eq] at htail
    have he1 : e1 ∈ W := by
      have := W.smul_mem (x 1)⁻¹ htail
      simpa [smul_smul, hx1] using this
    right
    right
    apply top_unique
    intro y _
    rw [vector_eq_coordinates y]
    exact W.add_mem (W.smul_mem _ he0) (W.smul_mem _ he1)
  · have hle : W ≤ firstAxis := by
      intro x hxW
      simp only [mem_firstAxis]
      by_contra hx1
      exact hsecond ⟨x, hxW, hx1⟩
    by_cases hbot : W = ⊥
    · exact Or.inl hbot
    · right
      left
      apply le_antisymm hle
      obtain ⟨x, hxW, hx0⟩ := W.ne_bot_iff.mp hbot
      obtain ⟨c, hxc⟩ := axis_e_0.mp (hle hxW)
      have hc : c ≠ 0 := by
        intro hc
        apply hx0
        rw [hxc, hc, zero_smul]
      have he0 : e0 ∈ W := by
        have := W.smul_mem c⁻¹ hxW
        rw [hxc] at this
        simpa [smul_smul, hc] using this
      intro y hy
      obtain ⟨d, rfl⟩ := axis_e_0.mp hy
      exact W.smul_mem d he0

/-- A diagonal endomorphism of `k^2`. -/
def diagonalEnd (a b : k) : Module.End k (Fin 2 -> k) :=
  (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) k).mulVecLin

@[simp]
theorem diagonalEnd_apply (a b : k) (x : Fin 2 -> k) :
    diagonalEnd a b x = ![a * x 0, b * x 1] := by
  ext i
  fin_cases i <;>
    simp [diagonalEnd, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem axis_diagonal_invariant (a b : k) :
    IsInvariantSubmodule (diagonalEnd a b) firstAxis := by
  intro x hx
  change x 1 = 0 at hx
  change (diagonalEnd a b x) 1 = 0
  simp [hx]

theorem second_axis_diagonal (a b : k) :
    IsInvariantSubmodule (diagonalEnd a b) secondAxis := by
  intro x hx
  change x 0 = 0 at hx
  change (diagonalEnd a b x) 0 = 0
  simp [hx]

/-- When the diagonal entries are distinct, the invariant subspaces are the two axes,
the zero subspace, and the whole space. -/
theorem diagonal_submodule_classification {a b : k} (hab : a ≠ b)
    (W : Submodule k (Fin 2 -> k)) (hW : IsInvariantSubmodule (diagonalEnd a b) W) :
    W = ⊥ ∨ W = firstAxis ∨ W = secondAxis ∨ W = ⊤ := by
  by_cases hfirst : ∃ x, x ∈ W ∧ x 0 ≠ 0
  · obtain ⟨x, hxW, hx0⟩ := hfirst
    have hdelta : diagonalEnd a b x - b • x ∈ W :=
      W.sub_mem (hW x hxW) (W.smul_mem b hxW)
    have hdelta_eq : diagonalEnd a b x - b • x = ((a - b) * x 0) • e0 := by
      ext i
      fin_cases i <;> simp [diagonalEnd_apply, e0, sub_mul]
    rw [hdelta_eq] at hdelta
    have hcoef0 : (a - b) * x 0 ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hab) hx0
    have he0 : e0 ∈ W := by
      have := W.smul_mem (((a - b) * x 0)⁻¹) hdelta
      simpa only [smul_smul, inv_mul_cancel₀ hcoef0, one_smul] using this
    by_cases hsecond : ∃ y, y ∈ W ∧ y 1 ≠ 0
    · obtain ⟨y, hyW, hy1⟩ := hsecond
      have hdelta' : diagonalEnd a b y - a • y ∈ W :=
        W.sub_mem (hW y hyW) (W.smul_mem a hyW)
      have hdelta'_eq : diagonalEnd a b y - a • y = ((b - a) * y 1) • e1 := by
        ext i
        fin_cases i <;> simp [diagonalEnd_apply, e1, sub_mul]
      rw [hdelta'_eq] at hdelta'
      have hcoef1 : (b - a) * y 1 ≠ 0 :=
        mul_ne_zero (sub_ne_zero.mpr hab.symm) hy1
      have he1 : e1 ∈ W := by
        have := W.smul_mem (((b - a) * y 1)⁻¹) hdelta'
        simpa only [smul_smul, inv_mul_cancel₀ hcoef1, one_smul] using this
      right
      right
      right
      apply top_unique
      intro z _
      rw [vector_eq_coordinates z]
      exact W.add_mem (W.smul_mem _ he0) (W.smul_mem _ he1)
    · right
      left
      apply le_antisymm
      · intro y hyW
        simp only [mem_firstAxis]
        by_contra hy1
        exact hsecond ⟨y, hyW, hy1⟩
      · intro y hy
        obtain ⟨c, rfl⟩ := axis_e_0.mp hy
        exact W.smul_mem c he0
  · have hle : W ≤ secondAxis := by
      intro x hxW
      simp only [mem_secondAxis]
      by_contra hx0
      exact hfirst ⟨x, hxW, hx0⟩
    by_cases hbot : W = ⊥
    · exact Or.inl hbot
    · right
      right
      left
      apply le_antisymm hle
      obtain ⟨x, hxW, hx0⟩ := W.ne_bot_iff.mp hbot
      obtain ⟨c, hxc⟩ := second_axis_e.mp (hle hxW)
      have hc : c ≠ 0 := by
        intro hc
        apply hx0
        rw [hxc, hc, zero_smul]
      have he1 : e1 ∈ W := by
        have := W.smul_mem c⁻¹ hxW
        rw [hxc] at this
        simpa [smul_smul, hc] using this
      intro y hy
      obtain ⟨d, rfl⟩ := second_axis_e.mp hy
      exact W.smul_mem d he1

/-- Every subspace is invariant under a scalar matrix. -/
theorem scalar_every_submodule (a : k) (W : Submodule k (Fin 2 -> k)) :
    IsInvariantSubmodule (diagonalEnd a a) W := by
  intro x hx
  rw [show diagonalEnd a a x = a • x by
    ext i
    fin_cases i <;> simp]
  exact W.smul_mem a hx

end Submission.CField.SAlgebr
