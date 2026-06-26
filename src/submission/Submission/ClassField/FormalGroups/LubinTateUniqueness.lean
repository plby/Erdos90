import Submission.ClassField.FormalGroups.LubinCorrectionUnits
import Mathlib.RingTheory.MvPowerSeries.Order


/-!
# Class Field Theory, Chapter I, Lemma 2.11: uniqueness by degree

Milne's uniqueness argument compares two candidate intertwiners in the first
total degree where they could differ.  In degree `n >= 2`, the intertwining
identity says that their discrepancy is killed by `pi ^ n - pi`.  This file
packages the algebraic conclusion of that argument: the scalar is nonzero in
a local domain, so the discrepancy vanishes, and equality in every
homogeneous degree implies equality of the original series.
-/

namespace Submission.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R sigma : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]

omit [IsDomain R] [IsLocalRing R] in
private theorem mv_homogeneous_component
    {F G : MvPowerSeries sigma R}
    (h : forall n, homogeneousComponent n F = homogeneousComponent n G) :
    F = G := by
  apply MvPowerSeries.ext
  intro d
  have hd := congrArg (coeff d) (h d.degree)
  simpa only [coeff_homogeneousComponent, if_pos rfl] using hd

/-- For `n >= 2`, Milne's uniqueness scalar `pi ^ n - pi` is nonzero. -/
theorem lubin_uniqueness_scalar
    {pi : R} (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    {n : Nat} (hn : 2 <= n) :
    pi ^ n - pi ≠ 0 := by
  have hn1 : n - 1 ≠ 0 := by omega
  have h := sub_self_ne
    (R := R) hpi0 hpi (r := n - 1) hn1
  simpa only [Nat.sub_add_cancel (by omega : 1 <= n)] using h

/-- Scalar multiplication by `pi ^ n - pi` is injective for `n >= 2`. -/
theorem lubin_uniqueness_smul
    {pi : R} (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    {n : Nat} (hn : 2 <= n) {F G : MvPowerSeries sigma R}
    (h : (pi ^ n - pi) • F = (pi ^ n - pi) • G) :
    F = G := by
  apply MvPowerSeries.ext
  intro d
  have hd := congrArg (coeff d) h
  simp only [coeff_smul] at hd
  exact mul_left_cancel₀
    (lubin_uniqueness_scalar hpi0 hpi hn) hd

/-- A series killed by Milne's uniqueness scalar is zero. -/
theorem uniqueness_scalar_smul
    {pi : R} (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    {n : Nat} (hn : 2 <= n) {F : MvPowerSeries sigma R}
    (h : (pi ^ n - pi) • F = 0) :
    F = 0 := by
  apply lubin_uniqueness_smul hpi0 hpi hn
  simpa only [smul_zero] using h

/-- Equivalent form of the cancellation used in the least-degree argument:
if scaling a series by `pi` agrees with scaling it by `pi ^ n`, then the
series is zero. -/
theorem uniformizer_smul_pow
    {pi : R} (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    {n : Nat} (hn : 2 <= n) {F : MvPowerSeries sigma R}
    (h : pi • F = pi ^ n • F) :
    F = 0 := by
  apply uniqueness_scalar_smul hpi0 hpi hn
  apply MvPowerSeries.ext
  intro d
  have hd := congrArg (coeff d) h
  simp only [coeff_smul] at hd
  simp only [coeff_smul, coeff_zero]
  rw [sub_mul, hd, sub_self]

omit [IsDomain R] [IsLocalRing R] in
/-- A multivariable power series is zero when all of its homogeneous
components are zero. -/
theorem zero_homogeneous_component
    {F : MvPowerSeries sigma R}
    (hF : forall n, homogeneousComponent n F = 0) :
    F = 0 := by
  apply mv_homogeneous_component
  intro n
  simpa only [map_zero] using hF n

/-- Degreewise form of Milne's uniqueness argument.  Once the constant and
linear components agree, it suffices to know that the degree-`n`
discrepancy is killed by `pi ^ n - pi` for every `n >= 2`. -/
theorem lubin_degreewise_uniqueness
    {pi : R} (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    {F G : MvPowerSeries sigma R}
    (hzero : homogeneousComponent 0 F = homogeneousComponent 0 G)
    (hone : homogeneousComponent 1 F = homogeneousComponent 1 G)
    (hhigh : forall n, 2 <= n ->
      (pi ^ n - pi) • homogeneousComponent n (F - G) = 0) :
    F = G := by
  apply mv_homogeneous_component
  intro n
  by_cases hn0 : n = 0
  · simpa only [hn0] using hzero
  by_cases hn1 : n = 1
  · simpa only [hn1] using hone
  have hn : 2 <= n := by omega
  have hz : homogeneousComponent n (F - G) = 0 :=
    uniqueness_scalar_smul
      hpi0 hpi hn (hhigh n hn)
  rw [map_sub, sub_eq_zero] at hz
  exact hz

end

end Submission.CField.FGroups
