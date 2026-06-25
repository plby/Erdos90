import Towers.ClassField.BrauerGroups.SkolemNoether
import Towers.ClassField.CrossedProducts.CohomologyClass

/-!
# Chapter IV, Theorem 3.11: injectivity of the crossed-product construction

An isomorphism between two crossed products carries the embedded coefficient
field to a conjugate copy.  After applying Skolem--Noether, it therefore fixes
the coefficient field.  Its effect on each standard basis vector is then
scaling by a unit of the coefficient field, and compatibility with
multiplication says exactly that the two factor sets differ by a coboundary.
-/

namespace Towers.CField.CProduca

noncomputable section

open groupCohomology

universe u

attribute [local instance] Units.mulDistribMulActionRight

namespace CProduc

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]

omit [FiniteDimensional k L] [IsGalois k L] in
/-- An element satisfying the `sigma`-twisted commutation relation with the
embedded coefficient field is supported only at the standard basis vector
indexed by `sigma`. -/
theorem coeff_smul_embedding
    (d : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))
    (x : CProduc d) (sigma : Gal(L/k))
    (hx : ∀ a : L,
      x * fieldEmbedding k L d a =
        fieldEmbedding k L d (sigma a) * x) :
    x = coeff d x sigma • basis d sigma := by
  classical
  apply ext_coeff d
  intro tau
  by_cases htau : tau = sigma
  · subst tau
    simp [basis_apply, coeff_single]
  · have hex : ∃ a : L, tau a ≠ sigma a := by
      by_contra h
      push Not at h
      apply htau
      ext a
      exact h a
    obtain ⟨a, ha⟩ := hex
    have hcoeff := congrArg (fun y : CProduc d ↦ coeff d y tau) (hx a)
    change coeff d (x * fieldEmbedding k L d a) tau =
      coeff d (fieldEmbedding k L d (sigma a) * x) tau at hcoeff
    rw [coeff_field_embedding, fieldEmbedding_mul, coeff_smul] at hcoeff
    have hzero : coeff d x tau = 0 := by
      by_contra hne
      apply ha
      apply mul_left_cancel₀ hne
      calc
        coeff d x tau * tau a = sigma a * coeff d x tau := hcoeff
        _ = coeff d x tau * sigma a := mul_comm _ _
    rw [hzero]
    simp [basis_apply, coeff_single, Ne.symm htau]

omit [FiniteDimensional k L] [IsGalois k L] in
/-- If an algebra equivalence of crossed products fixes their embedded copies
of `L`, then its basis rescaling coefficients exhibit the two factor sets as
cohomologous. -/
theorem cohomologous_alg_embedding
    (c d : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))
    (e : CProduc c ≃ₐ[k] CProduc d)
    (hfix : ∀ a : L,
      e (fieldEmbedding k L c a) = fieldEmbedding k L d a) :
    MHTwo.IsCohomologous c d := by
  classical
  have htwist (sigma : Gal(L/k)) (a : L) :
      e (basis c sigma) * fieldEmbedding k L d a =
        fieldEmbedding k L d (sigma a) * e (basis c sigma) := by
    calc
      e (basis c sigma) * fieldEmbedding k L d a =
          e (basis c sigma) * e (fieldEmbedding k L c a) := by rw [hfix]
      _ = e (basis c sigma * fieldEmbedding k L c a) := (e.map_mul _ _).symm
      _ = e (fieldEmbedding k L c (sigma a) * basis c sigma) := by
        rw [basis_mul_include]
      _ = e (fieldEmbedding k L c (sigma a)) * e (basis c sigma) :=
        e.map_mul _ _
      _ = fieldEmbedding k L d (sigma a) * e (basis c sigma) := by rw [hfix]
  have hform (sigma : Gal(L/k)) :
      e (basis c sigma) =
        coeff d (e (basis c sigma)) sigma • basis d sigma :=
    coeff_smul_embedding k L d _ sigma (htwist sigma)
  have hcoeff_ne (sigma : Gal(L/k)) :
      coeff d (e (basis c sigma)) sigma ≠ 0 := by
    intro hzero
    have h := hform sigma
    rw [hzero, zero_smul] at h
    have hne : e (basis c sigma) ≠ 0 := by
      simpa using e.injective.ne ((basis c).ne_zero sigma)
    exact hne h
  let a : Gal(L/k) → Lˣ := fun sigma ↦
    Units.mk0 (coeff d (e (basis c sigma)) sigma) (hcoeff_ne sigma)
  have hmap_basis (sigma : Gal(L/k)) :
      e (basis c sigma) =
        fieldEmbedding k L d (a sigma : L) * basis d sigma := by
    rw [fieldEmbedding_mul]
    exact hform sigma
  have hfactor (sigma tau : Gal(L/k)) :
      (a sigma : L) * sigma (a tau : L) * (d (sigma, tau) : L) =
        (c (sigma, tau) : L) * (a (sigma * tau) : L) := by
    have heq :
        fieldEmbedding k L d (c (sigma, tau) : L) *
            (fieldEmbedding k L d (a (sigma * tau) : L) * basis d (sigma * tau)) =
          (fieldEmbedding k L d (a sigma : L) * basis d sigma) *
            (fieldEmbedding k L d (a tau : L) * basis d tau) := by
      calc
        _ = e (fieldEmbedding k L c (c (sigma, tau) : L) *
              basis c (sigma * tau)) := by
              symm
              calc
                e (fieldEmbedding k L c (c (sigma, tau) : L) *
                    basis c (sigma * tau)) =
                    e (fieldEmbedding k L c (c (sigma, tau) : L)) *
                      e (basis c (sigma * tau)) := e.map_mul _ _
                _ = _ := by rw [hfix, hmap_basis]
        _ = e (basis c sigma * basis c tau) := by
              rw [basis_mul_basis]
        _ = _ := by
              calc
                e (basis c sigma * basis c tau) =
                    e (basis c sigma) * e (basis c tau) := e.map_mul _ _
                _ = _ := by rw [hmap_basis, hmap_basis]
    have hleft :
        fieldEmbedding k L d (c (sigma, tau) : L) *
            (fieldEmbedding k L d (a (sigma * tau) : L) * basis d (sigma * tau)) =
          ((c (sigma, tau) : L) * (a (sigma * tau) : L)) •
            basis d (sigma * tau) := by
      rw [fieldEmbedding_mul, fieldEmbedding_mul, smul_smul]
    have hright :
        (fieldEmbedding k L d (a sigma : L) * basis d sigma) *
            (fieldEmbedding k L d (a tau : L) * basis d tau) =
          ((a sigma : L) * sigma (a tau : L) * (d (sigma, tau) : L)) •
            basis d (sigma * tau) := by
      calc
        _ = fieldEmbedding k L d (a sigma : L) *
              (basis d sigma * fieldEmbedding k L d (a tau : L)) *
                basis d tau := by ac_rfl
        _ = fieldEmbedding k L d (a sigma : L) *
              (fieldEmbedding k L d (sigma (a tau : L)) * basis d sigma) *
                basis d tau := by rw [basis_mul_include]
        _ = (fieldEmbedding k L d (a sigma : L) *
              fieldEmbedding k L d (sigma (a tau : L))) *
                (basis d sigma * basis d tau) := by ac_rfl
        _ = fieldEmbedding k L d
              ((a sigma : L) * sigma (a tau : L)) *
                (fieldEmbedding k L d (d (sigma, tau) : L) *
                  basis d (sigma * tau)) := by
              rw [map_mul, basis_mul_basis]
        _ = fieldEmbedding k L d
              (((a sigma : L) * sigma (a tau : L)) *
                (d (sigma, tau) : L)) * basis d (sigma * tau) := by
              rw [← mul_assoc, ← map_mul]
        _ = _ := fieldEmbedding_mul k L d _ _
    rw [hleft, hright] at heq
    have hcoeff := congrArg
      (fun y : CProduc d ↦ coeff d y (sigma * tau)) heq
    simp [basis_apply, coeff_single] at hcoeff
    exact hcoeff.symm
  refine ⟨a, ?_⟩
  intro sigma tau
  have hu :
      a sigma * (sigma • a tau) * d (sigma, tau) =
        c (sigma, tau) * a (sigma * tau) := by
    apply Units.ext
    simpa using hfactor sigma tau
  have hdiv :
      (a sigma * (sigma • a tau)) / a (sigma * tau) =
        c (sigma, tau) / d (sigma, tau) :=
    div_eq_div_iff_mul_eq_mul.mpr hu
  rw [div_eq_mul_inv] at hdiv ⊢
  calc
    (sigma • a tau) * (a (sigma * tau))⁻¹ * a sigma =
        (a sigma * (sigma • a tau)) * (a (sigma * tau))⁻¹ := by ac_rfl
    _ = c (sigma, tau) * (d (sigma, tau))⁻¹ := hdiv

/-- The injectivity direction in Milne's Theorem IV.3.11: isomorphic crossed
products have cohomologous normalized factor sets. -/
theorem cohomologous_alg_equiv
    (c d : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))
    (e : CProduc c ≃ₐ[k] CProduc d) :
    MHTwo.IsCohomologous c d := by
  let f : L →ₐ[k] CProduc d :=
    e.toAlgHom.comp (fieldEmbedding k L c)
  let g : L →ₐ[k] CProduc d := fieldEmbedding k L d
  obtain ⟨b, hb⟩ := BGroups.skolemNoether k L (CProduc d) f g
  let inner : CProduc d ≃ₐ[k] CProduc d :=
    MulSemiringAction.toAlgEquiv k (CProduc d) (ConjAct.toConjAct b⁻¹)
  let e' : CProduc c ≃ₐ[k] CProduc d := e.trans inner
  have hfix (x : L) :
      e' (fieldEmbedding k L c x) = fieldEmbedding k L d x := by
    change inner (f x) = g x
    change (((b⁻¹ : (CProduc d)ˣ) : CProduc d) * f x) *
      (b : CProduc d) = g x
    rw [hb]
    rw [mul_assoc (b : CProduc d) (g x)
      (((b⁻¹ : (CProduc d)ˣ) : CProduc d))]
    rw [Units.inv_mul_cancel_left]
    rw [mul_assoc, Units.inv_mul, mul_one]
  exact cohomologous_alg_embedding k L c d e' hfix

end CProduc

end

end Towers.CField.CProduca
