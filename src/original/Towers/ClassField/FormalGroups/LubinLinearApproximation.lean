import Towers.ClassField.FormalGroups.LubinTateIntertwiner

/-!
# Class Field Theory, Chapter I, Lemma 2.11: the linear approximation

This file packages the degree-one starting point in Milne's successive
approximation proof.  A finite linear form is represented directly as a
multivariable power series, and substitution into it is computed exactly.
-/

namespace Towers.CField.FGroups

open scoped BigOperators

noncomputable section

/-- The multivariable linear form with coefficient vector `a`. -/
def mvLinearForm {R σ : Type*} [CommRing R] [Fintype σ]
    (a : σ → R) : MvPowerSeries σ R :=
  ∑ i, a i • MvPowerSeries.X i

@[simp]
theorem mv_constant_coeff
    {R σ : Type*} [CommRing R] [Fintype σ] (a : σ → R) :
    MvPowerSeries.constantCoeff (mvLinearForm a) = 0 := by
  simp [mvLinearForm]

/-- A linear form is homogeneous of total degree one. -/
theorem mv_form_homogeneous
    {R σ : Type*} [CommRing R] [Fintype σ] (a : σ → R) :
    MvPowerSeries.IsHomogeneous (mvLinearForm a) 1 := by
  classical
  intro d hd
  simp only [mvLinearForm, map_sum, map_smul, MvPowerSeries.coeff_X,
    smul_eq_mul] at hd
  change Finsupp.weight (fun _ : σ ↦ (1 : ℕ)) d = 1
  rw [← Finsupp.degree_eq_weight_one (R := ℕ), Finsupp.degree_eq_sum]
  by_contra hdegree
  have hsingle : ∀ i : σ, d ≠ Finsupp.single i 1 := by
    intro i hi
    subst d
    simp at hdegree
  simp [hsingle] at hd

/-- Substitution into a finite linear form is the corresponding linear
combination of the substituted coordinates. -/
theorem subst_mv_form
    {R σ τ : Type*} [CommRing R] [Fintype σ]
    (a : σ → R) (b : σ → MvPowerSeries τ R)
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (mvLinearForm a) = ∑ i, a i • b i := by
  rw [← MvPowerSeries.substAlgHom_apply hb, mvLinearForm, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, MvPowerSeries.substAlgHom_X]

/-- The right side of the intertwining equation in Lemma 2.11, evaluated on
the initial linear approximation. -/
theorem subst_coordinatewise_mv
    {R σ : Type*} [CommRing R] [Fintype σ]
    (a : σ → R) {g : PowerSeries R}
    (hg : PowerSeries.constantCoeff g = 0) :
    MvPowerSeries.subst (coordinatewiseSubst g) (mvLinearForm a) =
      ∑ i, a i • PowerSeries.subst (MvPowerSeries.X i) g := by
  exact subst_mv_form a (coordinatewiseSubst g)
    (coordinatewise_subst hg)

/-- Rescaling every variable of a linear form multiplies the form by the
same scalar.  This is the degree-one identity used in the base case of
Milne's induction. -/
theorem rescale_mv_form
    {R σ : Type*} [CommRing R] [Fintype σ]
    (a : σ → R) (r : R) :
    MvPowerSeries.rescale (Function.const σ r) (mvLinearForm a) =
      r • mvLinearForm a := by
  simpa only [pow_one] using
    MvPowerSeries.rescale_homogeneous_eq_smul
      (n := 1) (f := mvLinearForm a) (r := r) (by
        intro d hd
        rw [Finsupp.degree_eq_weight_one (R := ℕ)]
        exact mv_form_homogeneous a hd)

end

end Towers.CField.FGroups
