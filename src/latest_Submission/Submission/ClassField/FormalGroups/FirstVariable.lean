import Submission.ClassField.FormalGroups.FormalGroupLaw
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Class Field Theory, Chapter I, Exercise 2.21

The inverse series required in the definition of a one-parameter formal group
law follows already from the two identity axioms.  We construct it by
successive approximation: at stage `n` we add one monomial which corrects the
coefficient of degree `n` in `F(X,G(X))`.
-/

namespace Submission.CField.FGroups

open scoped PowerSeries
open MvPowerSeries

noncomputable section

namespace FGSeries

variable {R : Type*} [CommRing R]

/-- The inclusion of the first variable in a binary power-series ring. -/
def firstVariable : Fin 1 ↪ Fin 2 :=
  ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩

/-- The inclusion of the second variable in a binary power-series ring. -/
def secondVariable : Fin 1 ↪ Fin 2 :=
  ⟨fun _ ↦ 1, fun _ _ _ ↦ Subsingleton.elim _ _⟩

/-- Evaluate a binary series at `(X,g(X))`. -/
def applySeries (F : BinarySeries R) (g : PowerSeries R) : PowerSeries R :=
  subst (Fin.cases PowerSeries.X (fun _ ↦ g)) F

/-- The exponent of the second binary variable to the first power. -/
def secondLinearExponent : Fin 2 →₀ ℕ := Finsupp.single 1 1

private lemma emb_domain_single (n : ℕ) :
    Finsupp.embDomain secondVariable (Finsupp.single (0 : Fin 1) n) =
      Finsupp.single (1 : Fin 2) n := by
  classical
  ext i
  fin_cases i
  · simp [secondVariable]
  · simp [secondVariable]

private lemma coeff_second_one {F : BinarySeries R}
    (hleft : killCompl (R := R) secondVariable F = FGLaw.unaryX) :
    coeff secondLinearExponent F = 1 := by
  have h := congrArg (coeff (Finsupp.single (0 : Fin 1) 1)) hleft
  simpa [secondLinearExponent, FGLaw.unaryX, coeff_killCompl,
    emb_domain_single] using h

private lemma constant_coeff_zero {F : BinarySeries R}
    (hleft : killCompl (R := R) secondVariable F = FGLaw.unaryX) :
    constantCoeff F = 0 := by
  have h := congrArg (coeff (0 : Fin 1 →₀ ℕ)) hleft
  rw [coeff_killCompl] at h
  simpa [FGLaw.unaryX, coeff_zero_eq_constantCoeff_apply] using h

private lemma series_constant_coeff {F : BinarySeries R}
    (hleft : killCompl (R := R) secondVariable F = FGLaw.unaryX)
    {g : PowerSeries R} (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.constantCoeff (applySeries F g) = 0 := by
  let a : Fin 2 → PowerSeries R := Fin.cases PowerSeries.X (fun _ ↦ g)
  have ha0 : ∀ i, constantCoeff (a i) = 0 := by
    intro i
    fin_cases i
    · exact constantCoeff_X ()
    · exact hg
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  exact constantCoeff_subst_eq_zero ha ha0 (constant_coeff_zero hleft)

private lemma prod_apply_eq (d : Fin 2 →₀ ℕ) (g : PowerSeries R) :
    d.prod (fun s e ↦ (Fin.cases PowerSeries.X (fun _ ↦ g) s) ^ e) =
      PowerSeries.X ^ d 0 * g ^ d 1 := by
  classical
  rw [d.prod_fintype _ (fun _ ↦ pow_zero _), Fin.prod_univ_two]
  rfl

private lemma coeff_mul_zero
    {p q : PowerSeries R} {n : ℕ} (hp : ∀ k < n, PowerSeries.coeff k p = 0)
    (hq : PowerSeries.constantCoeff q = 0) : PowerSeries.coeff n (p * q) = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun ij hij ↦ ?_
  have hij' : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  by_cases hj : ij.2 = 0
  · simp [hj, PowerSeries.coeff_zero_eq_constantCoeff, hq]
  · have hi : ij.1 < n := by omega
    rw [hp ij.1 hi, zero_mul]

private lemma constant_coeff_geom₂_eq_zero {g h : PowerSeries R}
    (hg : PowerSeries.constantCoeff g = 0) (hh : PowerSeries.constantCoeff h = 0)
    {d : ℕ} (hd : d ≠ 1) :
    PowerSeries.constantCoeff
      (∑ i ∈ Finset.range d, g ^ i * h ^ (d - 1 - i)) = 0 := by
  cases d with
  | zero => simp
  | succ d =>
      have hd0 : d ≠ 0 := by
        intro hd'
        apply hd
        simp [hd']
      rw [map_sum]
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      rw [map_mul, map_pow, map_pow, hg, hh]
      by_cases hi0 : i = 0
      · subst i
        simp [hd0]
      · simp [hi0]

private lemma eq_eq_lt {g h : PowerSeries R} {n d : ℕ}
    (hg : PowerSeries.constantCoeff g = 0) (hh : PowerSeries.constantCoeff h = 0)
    (hcoeff : ∀ k < n, PowerSeries.coeff k g = PowerSeries.coeff k h) (hd : d ≠ 1) :
    PowerSeries.coeff n (g ^ d) = PowerSeries.coeff n (h ^ d) := by
  let s : PowerSeries R := ∑ i ∈ Finset.range d, g ^ i * h ^ (d - 1 - i)
  have hs : PowerSeries.constantCoeff s = 0 := constant_coeff_geom₂_eq_zero hg hh hd
  have hp : ∀ k < n, PowerSeries.coeff k (g - h) = 0 := by
    intro k hk
    rw [map_sub, hcoeff k hk, sub_self]
  have hz : PowerSeries.coeff n ((g - h) * s) = 0 :=
    coeff_mul_zero hp hs
  rw [mul_comm, geom_sum₂_mul] at hz
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz)

private lemma coeff_x_zero
    {g h : PowerSeries R} {n a b : ℕ}
    (hg : PowerSeries.constantCoeff g = 0)
    (hh : PowerSeries.constantCoeff h = 0)
    (hcoeff : ∀ k < n, PowerSeries.coeff k g = PowerSeries.coeff k h)
    (ha : a ≠ 0) :
    PowerSeries.coeff n (PowerSeries.X ^ a * g ^ b) =
      PowerSeries.coeff n (PowerSeries.X ^ a * h ^ b) := by
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  split_ifs with han
  · by_cases hb : b = 1
    · subst b
      simp only [pow_one]
      exact hcoeff _ (by omega)
    · exact eq_eq_lt hg hh
        (fun k hk ↦ hcoeff k (lt_of_lt_of_le hk (Nat.sub_le _ _))) hb
  · rfl

private lemma coeff_second_linear
    {g h : PowerSeries R} {n : ℕ}
    (hg : PowerSeries.constantCoeff g = 0)
    (hh : PowerSeries.constantCoeff h = 0)
    (hcoeff : ∀ k < n, PowerSeries.coeff k g = PowerSeries.coeff k h)
    (d : Fin 2 →₀ ℕ) (hd : d ≠ secondLinearExponent) :
    PowerSeries.coeff n
        (d.prod (fun s e ↦ (Fin.cases PowerSeries.X (fun _ ↦ g) s) ^ e)) =
      PowerSeries.coeff n
        (d.prod (fun s e ↦ (Fin.cases PowerSeries.X (fun _ ↦ h) s) ^ e)) := by
  rw [prod_apply_eq, prod_apply_eq]
  by_cases ha : d 0 = 0
  · rw [ha, pow_zero, one_mul, one_mul]
    apply eq_eq_lt hg hh hcoeff
    intro hb
    apply hd
    ext i
    fin_cases i
    · simp [secondLinearExponent, ha]
    · simp [secondLinearExponent, hb]
  · exact coeff_x_zero hg hh hcoeff ha

private lemma coeff_series_sub
    {F : BinarySeries R}
    (hleft : killCompl (R := R) secondVariable F = FGLaw.unaryX)
    {g h : PowerSeries R} {n : ℕ}
    (hg : PowerSeries.constantCoeff g = 0)
    (hh : PowerSeries.constantCoeff h = 0)
    (hcoeff : ∀ k < n, PowerSeries.coeff k g = PowerSeries.coeff k h) :
    PowerSeries.coeff n (applySeries F g) - PowerSeries.coeff n (applySeries F h) =
      PowerSeries.coeff n g - PowerSeries.coeff n h := by
  let ag : Fin 2 → PowerSeries R := Fin.cases PowerSeries.X (fun _ ↦ g)
  let ah : Fin 2 → PowerSeries R := Fin.cases PowerSeries.X (fun _ ↦ h)
  have hag0 : ∀ i, constantCoeff (ag i) = 0 := by
    intro i
    fin_cases i
    · exact constantCoeff_X ()
    · exact hg
  have hah0 : ∀ i, constantCoeff (ah i) = 0 := by
    intro i
    fin_cases i
    · exact constantCoeff_X ()
    · exact hh
  have hag : HasSubst ag := hasSubst_of_constantCoeff_zero hag0
  have hah : HasSubst ah := hasSubst_of_constantCoeff_zero hah0
  let A : (Fin 2 →₀ ℕ) → R := fun d ↦
    coeff d F * PowerSeries.coeff n
      (d.prod fun s e ↦ (ag s) ^ e)
  let B : (Fin 2 →₀ ℕ) → R := fun d ↦
    coeff d F * PowerSeries.coeff n
      (d.prod fun s e ↦ (ah s) ^ e)
  have hA : A.HasFiniteSupport := by
    simpa only [A, smul_eq_mul] using coeff_subst_finite hag F (Finsupp.single () n)
  have hB : B.HasFiniteSupport := by
    simpa only [B, smul_eq_mul] using coeff_subst_finite hah F (Finsupp.single () n)
  change PowerSeries.coeff n (subst ag F) - PowerSeries.coeff n (subst ah F) = _
  rw [PowerSeries.coeff, coeff_subst hag, coeff_subst hah]
  change finsum A - finsum B = _
  rw [← finsum_sub_distrib hA hB]
  rw [finsum_eq_single (fun d ↦ A d - B d) secondLinearExponent]
  · dsimp only [A, B, ag, ah]
    rw [prod_apply_eq secondLinearExponent g, prod_apply_eq secondLinearExponent h]
    rw [coeff_second_one hleft]
    simp [secondLinearExponent]
    rfl
  · intro d hd
    simp only [A, B, ← mul_sub]
    rw [coeff_second_linear hg hh hcoeff d hd, sub_self, mul_zero]

/-- The `n`th approximation corrects the coefficients of degrees below `n`. -/
def approximation (F : BinarySeries R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => approximation F n +
      PowerSeries.monomial n (-PowerSeries.coeff n (applySeries F (approximation F n)))

@[simp]
private lemma approximation_zero (F : BinarySeries R) : approximation F 0 = 0 := rfl

private lemma approximation_succ (F : BinarySeries R) (n : ℕ) :
    approximation F (n + 1) = approximation F n +
      PowerSeries.monomial n (-PowerSeries.coeff n (applySeries F (approximation F n))) := rfl

private lemma coeff_approximation_succ (F : BinarySeries R) (n k : ℕ) :
    PowerSeries.coeff k (approximation F (n + 1)) =
      PowerSeries.coeff k (approximation F n) +
        if k = n then -PowerSeries.coeff n (applySeries F (approximation F n)) else 0 := by
  rw [approximation_succ, map_add, PowerSeries.coeff_monomial]

private lemma approximation_constant_coeff {F : BinarySeries R}
    (hleft : killCompl (R := R) secondVariable F = FGLaw.unaryX) :
    ∀ n, PowerSeries.constantCoeff (approximation F n) = 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [approximation_succ, map_add, ih]
      by_cases hn : n = 0
      · subst n
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
          PowerSeries.coeff_monomial_same]
        have hz := series_constant_coeff hleft ih
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at hz
        simpa using hz
      · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
          PowerSeries.coeff_monomial]
        rw [if_neg (Ne.symm hn)]
        simp

private lemma coeff_approximation (F : BinarySeries R) {k n : ℕ} (hkn : k < n) :
    PowerSeries.coeff k (approximation F (n + 1)) =
      PowerSeries.coeff k (approximation F n) := by
  rw [coeff_approximation_succ, if_neg (Nat.ne_of_lt hkn)]
  simp

private lemma approximation_spec {F : BinarySeries R}
    (hleft : killCompl (R := R) secondVariable F = FGLaw.unaryX) :
    ∀ n k, k < n → PowerSeries.coeff k (applySeries F (approximation F n)) = 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro k hk
      have hconstSucc := approximation_constant_coeff hleft (n + 1)
      have hconst := approximation_constant_coeff hleft n
      by_cases hkn : k < n
      · have hchange := coeff_series_sub hleft hconstSucc hconst
          (n := k) (fun j hj ↦ coeff_approximation F (lt_trans hj hkn))
        have hcoeff : PowerSeries.coeff k (approximation F (n + 1)) =
            PowerSeries.coeff k (approximation F n) :=
          coeff_approximation F hkn
        rw [hcoeff, sub_self] at hchange
        rw [sub_eq_zero] at hchange
        rw [hchange, ih k hkn]
      · have hkeq : k = n := by omega
        subst k
        have hchange := coeff_series_sub hleft hconstSucc hconst
          (n := n) (fun j hj ↦ coeff_approximation F hj)
        rw [coeff_approximation_succ, if_pos rfl] at hchange
        have hrhs : PowerSeries.coeff n (approximation F n) +
              -PowerSeries.coeff n (applySeries F (approximation F n)) -
              PowerSeries.coeff n (approximation F n) =
            -PowerSeries.coeff n (applySeries F (approximation F n)) := by
          abel
        rw [hrhs] at hchange
        have h := congrArg
          (fun x ↦ x + PowerSeries.coeff n (applySeries F (approximation F n))) hchange
        simpa only [sub_add_cancel, neg_add_cancel] using h

private lemma coeff_approximation_stable (F : BinarySeries R) {k n : ℕ} (hkn : k < n) :
    PowerSeries.coeff k (approximation F n) =
      PowerSeries.coeff k (approximation F (k + 1)) := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : k < n
      · rw [coeff_approximation F h, ih h]
      · have : k = n := by omega
        subst k
        rfl

/-- The inverse series obtained as the stable diagonal of the approximations. -/
def inverseSeries (F : BinarySeries R) : PowerSeries R :=
  PowerSeries.mk fun n ↦ PowerSeries.coeff n (approximation F (n + 1))

@[simp]
theorem coeff_inverseSeries (F : BinarySeries R) (n : ℕ) :
    PowerSeries.coeff n (inverseSeries F) =
      PowerSeries.coeff n (approximation F (n + 1)) := by
  simp [inverseSeries]

theorem inverse_constant_coeff {F : BinarySeries R}
    (hleft : killCompl (R := R) secondVariable F = FGLaw.unaryX) :
    PowerSeries.constantCoeff (inverseSeries F) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_inverseSeries]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact approximation_constant_coeff hleft 1

private lemma coeff_series_approximation {F : BinarySeries R} {k n : ℕ}
    (hkn : k < n) :
    PowerSeries.coeff k (inverseSeries F) = PowerSeries.coeff k (approximation F n) := by
  rw [coeff_inverseSeries]
  exact (coeff_approximation_stable F hkn).symm

theorem inverseSeries_law {F : BinarySeries R}
    (hleft : killCompl (R := R) secondVariable F = FGLaw.unaryX) :
    applySeries F (inverseSeries F) = 0 := by
  apply PowerSeries.ext
  intro n
  have hconstInv := inverse_constant_coeff hleft
  have hconstApprox := approximation_constant_coeff hleft (n + 1)
  have hchange := coeff_series_sub hleft hconstInv hconstApprox
    (n := n) (fun k hk ↦ coeff_series_approximation (Nat.lt_succ_of_lt hk))
  have hn : PowerSeries.coeff n (inverseSeries F) =
      PowerSeries.coeff n (approximation F (n + 1)) := by
    exact coeff_series_approximation (Nat.lt_succ_self n)
  rw [hn, sub_self] at hchange
  rw [map_zero]
  rw [sub_eq_zero] at hchange
  rw [hchange]
  exact approximation_spec hleft (n + 1) n (Nat.lt_succ_self n)

theorem inverseSeries_unique {F : BinarySeries R}
    (hleft : killCompl (R := R) secondVariable F = FGLaw.unaryX)
    {g : PowerSeries R} (hg0 : PowerSeries.constantCoeff g = 0)
    (hg : applySeries F g = 0) : g = inverseSeries F := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strongRec with
  | ind n ih =>
      have hchange := coeff_series_sub hleft hg0 (inverse_constant_coeff hleft)
        (n := n) (fun k hk ↦ ih k hk)
      rw [hg, inverseSeries_law hleft] at hchange
      apply sub_eq_zero.mp
      simpa only [map_zero, sub_self] using hchange.symm

theorem inverse_series_coeff {F : BinarySeries R}
    (hleft : killCompl (R := R) secondVariable F = FGLaw.unaryX)
    (hright : applySeries F 0 = PowerSeries.X) :
    PowerSeries.coeff 1 (inverseSeries F) = -1 := by
  have hchange := coeff_series_sub hleft (inverse_constant_coeff hleft)
    (show PowerSeries.constantCoeff (0 : PowerSeries R) = 0 by simp)
    (n := 1) (fun k hk ↦ by
      have hk0 : k = 0 := by omega
      subst k
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
        inverse_constant_coeff hleft]
      simp)
  rw [inverseSeries_law hleft, hright] at hchange
  simpa using hchange.symm

/-- Exercise 2.21: the inverse series exists uniquely, has constant term zero
and linear term `-1`, and annihilates `F(X,-)` under substitution. -/
theorem unique_inverse_series {F : BinarySeries R}
    (hleft : killCompl (R := R) secondVariable F = FGLaw.unaryX)
    (hright : applySeries F 0 = PowerSeries.X) :
    ∃! g : PowerSeries R,
      PowerSeries.constantCoeff g = 0 ∧ applySeries F g = 0 ∧ PowerSeries.coeff 1 g = -1 := by
  refine ⟨inverseSeries F, ?_, ?_⟩
  · exact ⟨inverse_constant_coeff hleft, inverseSeries_law hleft,
      inverse_series_coeff hleft hright⟩
  · intro g hg
    exact inverseSeries_unique hleft hg.1 hg.2.1

end FGSeries

end

end Submission.CField.FGroups
