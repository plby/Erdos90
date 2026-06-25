import Mathlib.Analysis.Quaternion
import Mathlib.Algebra.Central.Basic
import Towers.ClassField.BrauerGroups.BrauerGroup

/-!
# Chapter IV, Section 4: Hamilton's quaternions over the real numbers

Milne identifies the nontrivial crossed product for `Complex/Real` with
Hamilton's quaternion algebra.  This file records the algebraic part of that
example: the quaternions form a four-dimensional central simple real algebra.
-/

namespace Towers.CField.LBrauer

noncomputable section

open scoped ComplexConjugate Quaternion

private def quatI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩

def quatJ : ℍ[ℝ] := ⟨0, 0, 1, 0⟩

@[simp]
theorem quatJ_sq : quatJ * quatJ = (-1 : ℍ[ℝ]) := by
  ext <;> simp [quatJ]

/-- The relation `jz = conjugate(z)j` in Hamilton's quaternion algebra. -/
theorem quat_j_complex (z : ℂ) :
    quatJ * Quaternion.ofComplex z =
      Quaternion.ofComplex (conj z) * quatJ := by
  ext <;> simp [quatJ]

/-- The embedded complex unit and `j` anticommute. -/
theorem quat_j_i :
    quatJ * Quaternion.ofComplex Complex.I =
      -(Quaternion.ofComplex Complex.I * quatJ) := by
  rw [quat_j_complex, Complex.conj_I, map_neg]
  exact neg_mul _ _

/-- Every Hamilton quaternion has a unique crossed-product expansion
`z + wj` with complex coefficients on the left. -/
theorem unique_quat_j (q : ℍ[ℝ]) :
    ∃! zw : ℂ × ℂ,
      q = Quaternion.ofComplex zw.1 + Quaternion.ofComplex zw.2 * quatJ := by
  refine ⟨⟨⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩⟩, ?_, ?_⟩
  · ext <;> simp [quatJ]
  · rintro ⟨z, w⟩ h
    apply Prod.ext
    · apply Complex.ext
      · simpa [quatJ] using (congrArg (fun x : ℍ[ℝ] ↦ x.re) h).symm
      · simpa [quatJ] using (congrArg (fun x : ℍ[ℝ] ↦ x.imI) h).symm
    · apply Complex.ext
      · simpa [quatJ] using (congrArg (fun x : ℍ[ℝ] ↦ x.imJ) h).symm
      · simpa [quatJ] using (congrArg (fun x : ℍ[ℝ] ↦ x.imK) h).symm

/-- A real quaternion commuting with every quaternion is real. -/
theorem algebra_re_center (q : ℍ[ℝ])
    (hq : q ∈ Subalgebra.center ℝ ℍ[ℝ]) :
    q = algebraMap ℝ ℍ[ℝ] q.re := by
  have hcentral : IsMulCentral q := hq
  have hi : q * quatI = quatI * q := (hcentral.comm quatI).eq
  have hj : q * quatJ = quatJ * q := (hcentral.comm quatJ).eq
  have himJ := congrArg (fun x : ℍ[ℝ] ↦ x.imJ) hi
  have himK := congrArg (fun x : ℍ[ℝ] ↦ x.imK) hi
  have himI := congrArg (fun x : ℍ[ℝ] ↦ x.imK) hj
  have hJ : q.imJ = 0 := by
    simp [quatI] at himK
    linarith
  have hK : q.imK = 0 := by
    simp [quatI] at himJ
    linarith
  have hI : q.imI = 0 := by
    simp [quatJ] at himI
    linarith
  apply Quaternion.ext
  · rfl
  · simp [hI]
  · simp [hJ]
  · simp [hK]

/-- Hamilton's quaternion algebra has centre exactly `Real`. -/
instance : Algebra.IsCentral ℝ ℍ[ℝ] where
  out q hq := by
    rw [Algebra.mem_bot]
    exact ⟨q.re, (algebra_re_center q hq).symm⟩

/-- Hamilton's quaternions are a central simple real algebra. -/
theorem hamilton_central_simple :
    IsSimpleRing ℍ[ℝ] ∧ Algebra.IsCentral ℝ ℍ[ℝ] :=
  ⟨inferInstance, inferInstance⟩

/-- Hamilton's quaternion algebra has real dimension four. -/
theorem hamilton_finrank : Module.finrank ℝ ℍ[ℝ] = 4 :=
  Quaternion.finrank_eq_four

/-- Hamilton's quaternions, packaged as a central simple algebra over `Real`. -/
def hamiltonCSA : CSA.{0, 0} ℝ :=
  BGroups.centralSimpleCSA ℝ ℍ[ℝ]

end

end Towers.CField.LBrauer
