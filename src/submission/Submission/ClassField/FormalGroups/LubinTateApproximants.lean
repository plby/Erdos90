import Submission.ClassField.FormalGroups.LubinTatePerturbation

/-!
# Class Field Theory, Chapter I, Lemma 2.11: the approximating sequence

The degreewise correction theorem is noncomputably chosen at each stage.  We
package the approximants together with their zero-constant-term invariant and
record that the step from stage `r` to `r+1` changes only total degree `r+2`.
-/

namespace Submission.CField.FGroups

open MvPowerSeries

noncomputable section

namespace LTApprox

variable {R σ : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Fintype σ]

variable (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)

/-- A multivariable power series with the zero constant term needed for all
substitutions in Lemma 2.11. -/
abbrev ZeroConstantSeries :=
  {phi : MvPowerSeries σ R // constantCoeff phi = 0}

/-- The unique correction chosen at total degree `n`. -/
def degreeCorrection (phi : ZeroConstantSeries (R := R) (σ := σ))
    (n : ℕ) (hn : 2 ≤ n) : MvPowerSeries σ R :=
  Classical.choose
    (unique_lubin_correction
      hpi0 hpi hfield hf hg phi.property hn)

theorem degreeCorrection_spec
    (phi : ZeroConstantSeries (R := R) (σ := σ))
    (n : ℕ) (hn : 2 ≤ n) :
    IsHomogeneous (degreeCorrection pi hpi0 hpi hfield f g hf hg phi n hn) n ∧
      ((pi ^ (n - 1) - 1) * pi) •
          degreeCorrection pi hpi0 hpi hfield f g hf hg phi n hn =
        homogeneousComponent n
          (lubinIntertwiningError f g phi) :=
  (Classical.choose_spec
    (unique_lubin_correction
      hpi0 hpi hfield hf hg phi.property hn)).1

theorem degree_constant_coeff
    (phi : ZeroConstantSeries (R := R) (σ := σ))
    (n : ℕ) (hn : 2 ≤ n) :
    constantCoeff
        (degreeCorrection pi hpi0 hpi hfield f g hf hg phi n hn) = 0 := by
  exact IsHomogeneous.constant_coeff_zero
    (degreeCorrection_spec pi hpi0 hpi hfield f g hf hg phi n hn).1
    (by omega)

/-- Milne's successive approximants.  Stage zero is the prescribed linear
form; stage `r+1` adds the unique correction of total degree `r+2`. -/
def approximation (a : σ → R) : ℕ → ZeroConstantSeries (R := R) (σ := σ)
  | 0 => ⟨mvLinearForm a, mv_constant_coeff a⟩
  | r + 1 =>
      let phi := approximation a r
      let Q := degreeCorrection pi hpi0 hpi hfield f g hf hg phi (r + 2) (by omega)
      ⟨phi + Q, by
        rw [map_add, phi.property,
          degree_constant_coeff
            pi hpi0 hpi hfield f g hf hg phi (r + 2) (by omega)]
        exact add_zero 0⟩

@[simp]
theorem approximation_zero (a : σ → R) :
    approximation pi hpi0 hpi hfield f g hf hg a 0 =
      ⟨mvLinearForm a, mv_constant_coeff a⟩ := rfl

theorem approximation_succ (a : σ → R) (r : ℕ) :
    (approximation pi hpi0 hpi hfield f g hf hg a (r + 1) :
        MvPowerSeries σ R) =
      approximation pi hpi0 hpi hfield f g hf hg a r +
        degreeCorrection pi hpi0 hpi hfield f g hf hg
          (approximation pi hpi0 hpi hfield f g hf hg a r)
          (r + 2) (by omega) := rfl

@[simp]
theorem approximation_constantCoeff (a : σ → R) (r : ℕ) :
    constantCoeff
        (approximation pi hpi0 hpi hfield f g hf hg a r :
          MvPowerSeries σ R) = 0 :=
  (approximation pi hpi0 hpi hfield f g hf hg a r).property

/-- One correction step leaves all coefficients of total degree below the
new correction degree unchanged. -/
theorem coeff_approximation_degree
    (a : σ → R) (r : ℕ) (d : σ →₀ ℕ) (hd : d.degree < r + 2) :
    coeff d
        (approximation pi hpi0 hpi hfield f g hf hg a (r + 1) :
          MvPowerSeries σ R) =
      coeff d
        (approximation pi hpi0 hpi hfield f g hf hg a r :
          MvPowerSeries σ R) := by
  rw [approximation_succ, map_add]
  rw [IsHomogeneous.coeff_zero_below
    (degreeCorrection_spec pi hpi0 hpi hfield f g hf hg
      (approximation pi hpi0 hpi hfield f g hf hg a r)
      (r + 2) (by omega)).1 hd]
  exact add_zero _

/-- Once a coefficient lies below the next correction degree, it remains
unchanged at every later stage. -/
theorem approximation_eq_le
    (a : σ → R) {r s : ℕ} (hrs : r ≤ s)
    (d : σ →₀ ℕ) (hd : d.degree < r + 2) :
    coeff d
        (approximation pi hpi0 hpi hfield f g hf hg a s :
          MvPowerSeries σ R) =
      coeff d
        (approximation pi hpi0 hpi hfield f g hf hg a r :
          MvPowerSeries σ R) := by
  induction s, hrs using Nat.le_induction with
  | base => rfl
  | succ s hrs ih =>
      rw [coeff_approximation_degree
        pi hpi0 hpi hfield f g hf hg a s d (by omega)]
      exact ih

/-- The initial approximation already satisfies the intertwining identity
through total degree one. -/
theorem error_approximation_zero (a : σ → R) :
    2 ≤ (lubinIntertwiningError f g
      (approximation pi hpi0 hpi hfield f g hf hg a 0 :
        MvPowerSeries σ R)).order := by
  simpa [lubinIntertwiningError] using
    form_intertwining_error
      (f := f) (g := g)
      (by simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf.1)
      hf.2.1
      (by simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hg.1)
      hg.2.1 a

/-- The error of the stage-`r` approximant vanishes through total degree
`r+1`. -/
theorem nat_error_approximation (a : σ → R) (r : ℕ) :
    (r + 2 : ℕ) ≤
      (lubinIntertwiningError f g
        (approximation pi hpi0 hpi hfield f g hf hg a r :
          MvPowerSeries σ R)).order := by
  induction r with
  | zero =>
      simpa using error_approximation_zero
        pi hpi0 hpi hfield f g hf hg a
  | succ r ih =>
      rw [approximation_succ]
      apply lubin_intertwining_error
        hf.2.1
        (by simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hg.1)
        hg.2.1
        (approximation_constantCoeff pi hpi0 hpi hfield f g hf hg a r)
        (by omega)
        (degreeCorrection_spec pi hpi0 hpi hfield f g hf hg
          (approximation pi hpi0 hpi hfield f g hf hg a r)
          (r + 2) (by omega)).1
        ih
      have hspec := (degreeCorrection_spec pi hpi0 hpi hfield f g hf hg
        (approximation pi hpi0 hpi hfield f g hf hg a r)
        (r + 2) (by omega)).2
      have hpow : pi ^ (r + 2) = pi ^ (r + 1) * pi := by
        rw [show r + 2 = (r + 1) + 1 by omega, pow_succ]
      rw [show r + 2 - 1 = r + 1 by omega] at hspec
      have hscalar : pi ^ (r + 2) - pi = (pi ^ (r + 1) - 1) * pi := by
        rw [hpow, sub_mul, one_mul]
      rw [hscalar]
      exact hspec

end LTApprox

end

end Submission.CField.FGroups
