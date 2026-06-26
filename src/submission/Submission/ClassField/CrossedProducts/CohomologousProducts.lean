import Mathlib.LinearAlgebra.Basis.SMul
import Submission.ClassField.CrossedProducts.CrossedProductGalois
import Submission.ClassField.CrossedProducts.UniquenessFactorSet

/-!
# Chapter IV, Section 3: cohomologous crossed products

Milne completes Theorem 3.11 by observing that cohomologous normalized
factor sets give isomorphic crossed-product algebras.  The isomorphism
rescales the standard basis by a multiplicative `1`-cochain.
-/

namespace Submission.CField.CProduca

noncomputable section

open groupCohomology

universe u

attribute [local instance] Units.mulDistribMulActionRight

namespace CProduc

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  (c c' : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))

/-- Cohomologous normalized cocycles define isomorphic crossed products.
The chosen coboundary witness `a` sends the standard basis vector `e_σ` to
`a(σ) e'_σ`. -/
def algMulCoboundary₂
    (hcoh : IsMulCoboundary₂ (fun p ↦ c p / c' p)) :
    CProduc c ≃ₐ[k] CProduc c' := by
  classical
  let a := hcoh.choose
  have ha := hcoh.choose_spec
  have ha_one : a 1 = 1 := by
    have h := ha 1 1
    simpa using h
  have hfactor (sigma tau : Gal(L/k)) :
      (a sigma : L) * (sigma • (a tau : L)) * (c' (sigma, tau) : L) =
        (c (sigma, tau) : L) * (a (sigma * tau) : L) := by
    have hdiv :
        (a sigma * (sigma • a tau)) / a (sigma * tau) =
          c (sigma, tau) / c' (sigma, tau) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        ha sigma tau
    have hu :
        a sigma * (sigma • a tau) * c' (sigma, tau) =
          c (sigma, tau) * a (sigma * tau) :=
      div_eq_div_iff_mul_eq_mul.mp hdiv
    exact congrArg Units.val hu
  letI : IsScalarTower k L (CProduc c) := ⟨fun r a x ↦ by
    change (r • a) • x = algebraMap k L r • (a • x)
    rw [Algebra.smul_def]
    exact mul_smul _ _ _⟩
  letI : IsScalarTower k L (CProduc c') := ⟨fun r a x ↦ by
    change (r • a) • x = algebraMap k L r • (a • x)
    rw [Algebra.smul_def]
    exact mul_smul _ _ _⟩
  apply sameScalarActions k L
    (CProduc c) (CProduc c')
    (fieldEmbedding k L c) (fieldEmbedding k L c')
    (basis c) ((basis c').unitsSMul a) c
  · intro x y
    change coefficientRingHom c x * y = x • y
    exact coefficient_mul c x y
  · intro x y
    change coefficientRingHom c' x * y = x • y
    exact coefficient_mul c' x y
  · simp [basis_apply]
  · simp [Module.Basis.unitsSMul_apply, basis_apply, ha_one]
  · intro sigma x
    exact basis_mul_include k L c sigma x
  · intro sigma x
    simp [Module.Basis.unitsSMul_apply, Units.smul_def, basis_apply,
      fieldEmbedding_apply, smul_single, single_mul_single, mul_comm]
  · intro sigma tau
    exact basis_mul_basis k L c sigma tau
  · intro sigma tau
    simp only [Module.Basis.unitsSMul_apply, Units.smul_def, basis_apply,
      smul_single, single_mul_single, fieldEmbedding_apply,
      mul_one]
    simp only [one_smul, NMCocycl₂.apply_one_fst, Units.val_one,
      mul_one]
    apply congrArg (single c' (sigma * tau))
    exact hfactor sigma tau

end CProduc

end

end Submission.CField.CProduca
