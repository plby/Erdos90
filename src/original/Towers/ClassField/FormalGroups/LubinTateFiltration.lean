import Towers.ClassField.FormalGroups.LubinHomogeneousCorrection

/-!
# Class Field Theory, Chapter I, Lemma 2.11: filtration lemmas

This file records the elementary facts about the total-degree filtration used
in the successive homogeneous correction.  In particular, equality modulo
terms of degree greater than `n` identifies the `n`th homogeneous components,
and division by Milne's nonzero scalar preserves homogeneity.
-/

namespace Towers.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R σ : Type*} [CommRing R]

/-- A homogeneous series of degree `n` has order at least `n`. -/
theorem nat_order_homogeneous {H : MvPowerSeries σ R} {n : ℕ}
    (hH : IsHomogeneous H n) : (n : ℕ∞) ≤ H.order := by
  apply MvPowerSeries.nat_le_order
  intro d hd
  apply hH.coeff_eq_zero
  exact ne_of_lt hd

/-- A homogeneous series of positive degree has zero constant coefficient. -/
theorem constant_coeff_homogeneous {H : MvPowerSeries σ R} {n : ℕ}
    (hH : IsHomogeneous H n) (hn : n ≠ 0) : constantCoeff H = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  apply hH.coeff_eq_zero
  simpa only [map_zero, ne_eq] using hn.symm

/-- If the difference of two power series has order greater than the degree
of a monomial, then their coefficients at that monomial agree. -/
theorem coeff_degree_sub {F G : MvPowerSeries σ R}
    {d : σ →₀ ℕ} (h : d.degree < (F - G).order) :
    coeff d F = coeff d G := by
  have hz := coeff_of_lt_order (f := F - G) h
  simpa only [map_sub, sub_eq_zero] using hz

/-- Agreement modulo terms of degree greater than `n` identifies the `n`th
homogeneous components. -/
theorem homogeneous_component_nat
    {F G : MvPowerSeries σ R} {n : ℕ}
    (h : (n : ℕ∞) < (F - G).order) :
    homogeneousComponent n F = homogeneousComponent n G := by
  ext d
  rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
  split_ifs with hd
  · apply coeff_degree_sub
    simpa only [hd] using h
  · rfl

/-- To improve an approximation from precision `n` to precision `n+1`, it is
enough to preserve all lower coefficients and kill the degree-`n`
homogeneous component. -/
theorem nat_component_zero
    {E E' : MvPowerSeries σ R} {n : ℕ}
    (hE : (n : ℕ∞) ≤ E.order)
    (hlower : ∀ d, d.degree < n → coeff d E' = coeff d E)
    (hcomponent : homogeneousComponent n E' = 0) :
    (n + 1 : ℕ) ≤ E'.order := by
  apply MvPowerSeries.nat_le_order
  intro d hd
  have hd' : d.degree < n + 1 := by exact_mod_cast hd
  by_cases hdn : d.degree < n
  · rw [hlower d hdn]
    apply coeff_of_lt_order
    exact lt_of_lt_of_le (by exact_mod_cast hdn) hE
  · have hdegree : d.degree = n := by omega
    have hc := congrArg (coeff d) hcomponent
    simpa only [coeff_homogeneousComponent, hdegree, if_pos, map_zero] using hc

/-- The correction equation cancels the degree-`n` perturbation term. -/
theorem homogeneous_component_corrected
    {E E' Q : MvPowerSeries σ R} {pi : R} {n : ℕ}
    (hperturb : homogeneousComponent n E' =
      homogeneousComponent n E + (pi - pi ^ n) • Q)
    (hcorrect : (pi ^ n - pi) • Q = homogeneousComponent n E) :
    homogeneousComponent n E' = 0 := by
  rw [hperturb, ← hcorrect]
  have hscalar : pi - pi ^ n = -(pi ^ n - pi) := by ring
  rw [hscalar, neg_smul]
  exact add_neg_cancel _

/-- A quotient by a nonzero scalar of a homogeneous power series is again
homogeneous. -/
theorem homogeneous_smul [IsDomain R]
    {a : R} (ha : a ≠ 0) {Q H : MvPowerSeries σ R} {n : ℕ}
    (hH : IsHomogeneous H n) (hQ : a • Q = H) :
    IsHomogeneous Q n := by
  intro d hd
  have hc := congrArg (coeff d) hQ
  simp only [coeff_smul] at hc
  apply hH
  rw [← hc]
  exact mul_ne_zero ha hd

/-- The unique quotient used for a homogeneous Lubin--Tate correction can be
chosen homogeneous of the same degree. -/
theorem unique_homogeneous_span
    [IsDomain R] {pi : R} (hpi : pi ≠ 0) (u : Rˣ)
    {H : MvPowerSeries σ R} {n : ℕ} (hH : IsHomogeneous H n)
    (hdiv : ∀ d, coeff d H ∈ Ideal.span {pi}) :
    ∃! Q : MvPowerSeries σ R,
      IsHomogeneous Q n ∧ ((u : R) * pi) • Q = H := by
  obtain ⟨Q, hQ, huniq⟩ :=
    unique_coeff_span hpi u H hdiv
  have hscalar : (u : R) * pi ≠ 0 := mul_ne_zero (Units.ne_zero u) hpi
  refine ⟨Q, ⟨homogeneous_smul hscalar hH hQ, hQ⟩, ?_⟩
  intro P hP
  exact huniq P hP.2

/-- Milne's degree-`r+1` correction exists uniquely once the current error is
known coefficientwise divisible by `pi`.  The denominator is written in the
same form `pi^(r+1) - pi` as in the perturbation calculation. -/
theorem unique_next_homogeneous
    [IsDomain R] [IsLocalRing R] {pi : R}
    (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi) {r : ℕ} (hr : r ≠ 0)
    (E : MvPowerSeries σ R)
    (hdiv : ∀ d, coeff d E ∈ Ideal.span {pi}) :
    ∃! Q : MvPowerSeries σ R,
      IsHomogeneous Q (r + 1) ∧
        (pi ^ (r + 1) - pi) • Q = homogeneousComponent (r + 1) E := by
  have hu : IsUnit (pi ^ r - 1) :=
    pow_sub_not hpi hr
  let u : Rˣ := hu.unit
  have huval : (u : R) = pi ^ r - 1 := hu.unit_spec
  have hcomponentDiv :
      ∀ d, coeff d (homogeneousComponent (r + 1) E) ∈ Ideal.span {pi} := by
    intro d
    rw [coeff_homogeneousComponent]
    split_ifs
    · exact hdiv d
    · exact Submodule.zero_mem _
  have h := unique_homogeneous_span
    (σ := σ) hpi0 u (isHomogeneous_homogeneousComponent E (r + 1))
    hcomponentDiv
  simpa only [huval, ← succ_sub_factor pi r] using h

/-- Specialized correction step for the error attached to two Lubin--Tate
series and a zero-constant current approximation. -/
theorem unique_lubin_homogeneous
    [IsDomain R] [IsLocalRing R] [Finite σ] {pi : R}
    (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    {f g : PowerSeries R}
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    {phi : MvPowerSeries σ R} (hphi : constantCoeff phi = 0)
    {r : ℕ} (hr : r ≠ 0) :
    ∃! Q : MvPowerSeries σ R,
      IsHomogeneous Q (r + 1) ∧
        (pi ^ (r + 1) - pi) • Q =
          homogeneousComponent (r + 1)
            (PowerSeries.subst phi f -
              subst (coordinatewiseSubst g) phi) := by
  apply unique_next_homogeneous hpi0 hpi hr
  intro d
  exact intertwining_error_span
    pi hfield hf hg hphi d

end

end Towers.CField.FGroups
