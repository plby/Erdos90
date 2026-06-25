import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Appendix exercise A-8: elementary quaternion algebra calculations

This exercise repeats parts (a)--(d) of IV.5.7.  Mathlib has Hamilton's
quaternions, but not the two-parameter quaternion algebra `H(a,b)` over an
arbitrary field.  We therefore record the concrete matrix calculation proving
the split case `H(1,1)`, and the norm-form scaling identity underlying part
(d).  The Wedderburn and Noether--Skolem steps in parts (a) and (b) require a
generic quaternion-algebra interface.
-/

namespace Towers.CField.SAlgebr.QNCalcul

section Matrices

variable (R : Type*) [Field R]

/-- The matrix representing the first generator of `H(1,1)`. -/
def splitQuaternionI : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 1, 0]

/-- The matrix representing the second generator of `H(1,1)`. -/
def splitQuaternionJ : Matrix (Fin 2) (Fin 2) R :=
  !![1, 0; 0, -1]

/-- The first displayed generator squares to one. -/
@[simp]
theorem quaternion_i_sq : splitQuaternionI R ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitQuaternionI, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- The second displayed generator squares to one. -/
@[simp]
theorem quaternion_j_sq : splitQuaternionJ R ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitQuaternionJ, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two displayed generators anticommute. -/
theorem quaternion_i_j :
    splitQuaternionI R * splitQuaternionJ R =
      -(splitQuaternionJ R * splitQuaternionI R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [splitQuaternionI, splitQuaternionJ, Matrix.mul_apply, Fin.sum_univ_two]

variable [NeZero (2 : R)]

/-- The four matrices `1`, `i`, `j`, and `ij` are linearly independent, in
the coefficient form used in Milne's solution. -/
theorem split_quate_coeff {c d e f : R}
    (h : c • (1 : Matrix (Fin 2) (Fin 2) R) +
          d • splitQuaternionI R + e • splitQuaternionJ R +
          f • (splitQuaternionI R * splitQuaternionJ R) = 0) :
    c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 := by
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  have h10 := congrFun (congrFun h (1 : Fin 2)) (0 : Fin 2)
  have h11 := congrFun (congrFun h (1 : Fin 2)) (1 : Fin 2)
  have h00' : c + e = 0 := by
    simpa [splitQuaternionI, splitQuaternionJ] using h00
  have h01' : d + -f = 0 := by
    simpa [splitQuaternionI, splitQuaternionJ] using h01
  have h10' : d + f = 0 := by
    simpa [splitQuaternionI, splitQuaternionJ] using h10
  have h11' : c + -e = 0 := by
    simpa [splitQuaternionI, splitQuaternionJ] using h11
  have hcTwo : (2 : R) * c = 0 := by
    calc
      (2 : R) * c = (c + e) + (c + -e) := by ring
      _ = 0 := by simp [h00', h11']
  have hdTwo : (2 : R) * d = 0 := by
    calc
      (2 : R) * d = (d + -f) + (d + f) := by ring
      _ = 0 := by simp [h01', h10']
  have hc : c = 0 := (mul_eq_zero.mp hcTwo).resolve_left (NeZero.ne 2)
  have hd : d = 0 := (mul_eq_zero.mp hdTwo).resolve_left (NeZero.ne 2)
  have he : e = 0 := by simpa [hc] using h00'
  have hf : f = 0 := by simpa [hd] using h01'
  exact ⟨hc, hd, he, hf⟩

end Matrices

section NormForm

variable {F : Type*} [Field F]

/-- The reduced norm form of the quaternion algebra `H(a,b)`. -/
def quaternionNormForm (a b w x y z : F) : F :=
  w ^ 2 - a * x ^ 2 - b * y ^ 2 + a * b * z ^ 2

/-- Scaling the quaternion generators by nonzero `r` and `s` gives the
coordinate change used in Exercise IV.5.7(d). -/
theorem quaternion_form_scale (a b w x y z r s : F)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    quaternionNormForm (a * r ^ 2) (b * s ^ 2)
        w (x / r) (y / s) (z / (r * s)) =
      quaternionNormForm a b w x y z := by
  simp only [quaternionNormForm]
  field_simp [hr, hs]

end NormForm

end Towers.CField.SAlgebr.QNCalcul
