import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Chapter VIII, Section 6: orthogonal complements under ambient isometries

Proposition 6.2 is Witt cancellation: an isometry between nondegenerate
subspaces extends far enough to identify their orthogonal complements.  The
full extension theorem is not currently packaged in Mathlib.  This file proves
the exact complement statement once the subspace isometry is induced by an
ambient isometry.  It is also the final step of the source's reflection proof.
-/

namespace Towers.CField.QForms

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

private abbrev QOrthogonal (Q : QuadraticForm k V) (U : Submodule k V) :
    Submodule k V :=
  LinearMap.BilinForm.orthogonal Q.polarBilin U

/-- An isometry preserves the polar bilinear form. -/
theorem polar_isometry_equiv (Q : QuadraticForm k V)
    (f : Q.IsometryEquiv Q) (x y : V) :
    QuadraticMap.polar Q (f x) (f y) = QuadraticMap.polar Q x y := by
  rw [QuadraticMap.polar, QuadraticMap.polar]
  rw [← map_add f, f.map_app, f.map_app, f.map_app]

/-- An ambient isometry carrying `U` to `W` restricts to a linear equivalence
between their orthogonal complements. -/
noncomputable def orthogonalComplementIsometry
    (Q : QuadraticForm k V) (f : Q.IsometryEquiv Q)
    (U W : Submodule k V)
    (hmap : U.map f.toLinearEquiv.toLinearMap = W) :
    QOrthogonal Q U ≃ₗ[k] QOrthogonal Q W where
  toFun x := ⟨f x, by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    have hw' : w ∈ U.map f.toLinearEquiv.toLinearMap := by simpa [hmap] using hw
    obtain ⟨u, hu, rfl⟩ := hw'
    change QuadraticMap.polar Q (f u) (f x) = 0
    rw [polar_isometry_equiv]
    have hx := (LinearMap.BilinForm.mem_orthogonal_iff.mp x.property) u hu
    change QuadraticMap.polar Q u x = 0 at hx
    exact hx⟩
  invFun y := ⟨f.symm y, by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have hfu : f u ∈ W := by
      rw [← hmap]
      exact ⟨u, hu, rfl⟩
    change QuadraticMap.polar Q u (f.symm y) = 0
    have hpolar := polar_isometry_equiv Q f u (f.symm y)
    rw [f.apply_symm_apply] at hpolar
    rw [← hpolar]
    have hy := (LinearMap.BilinForm.mem_orthogonal_iff.mp y.property) (f u) hfu
    change QuadraticMap.polar Q (f u) y = 0 at hy
    exact hy⟩
  left_inv x := Subtype.ext (f.symm_apply_apply x)
  right_inv y := Subtype.ext (f.apply_symm_apply y)
  map_add' x y := Subtype.ext (map_add f x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul f c x.1)

/-- **Proposition 6.2, ambient-isometry form.** Orthogonal complements are
isometric when the given subspace isometry is the restriction of an ambient
isometry. -/
noncomputable def of_ambient_isometry
    (Q : QuadraticForm k V) (f : Q.IsometryEquiv Q)
    (U W : Submodule k V)
    (hmap : U.map f.toLinearEquiv.toLinearMap = W) :
    (Q.restrict (QOrthogonal Q U)).IsometryEquiv
      (Q.restrict (QOrthogonal Q W)) where
  toLinearEquiv := orthogonalComplementIsometry Q f U W hmap
  map_app' x := f.map_app x

end Towers.CField.QForms
