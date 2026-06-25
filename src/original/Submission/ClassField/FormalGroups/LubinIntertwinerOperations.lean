import Submission.ClassField.FormalGroups.LubinIntertwinerComposition
import Submission.ClassField.FormalGroups.LubinIntertwinerPredicate

/-!
# Class Field Theory, Chapter I, Section 2: operations on intertwiners

An exact intertwiner is recorded together with its prescribed linear
coefficient vector.  Substitution composes such intertwiners, and the new
linear coefficients are obtained by the expected matrix product.  This is
the reusable algebra behind Propositions 2.12, 2.14, and 2.15.
-/

namespace Submission.CField.FGroups

open MvPowerSeries
open scoped BigOperators

noncomputable section

variable {R sigma tau : Type*} [CommRing R]

/-- Linear forms turn matrix multiplication of coefficient families into
substitution of their degree-one parts. -/
theorem smul_mv_form
    [Fintype sigma] [Fintype tau]
    (a : sigma -> R) (b : sigma -> tau -> R) :
    ∑ i, a i • mvLinearForm (b i) =
      mvLinearForm (fun j => ∑ i, a i * b i j) := by
  simp only [mvLinearForm, Finset.smul_sum, smul_smul]
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]

/-- Substitution composes exact intertwiners.  On linear coefficients this
is the ordinary row-vector by matrix product. -/
theorem LIntert.subst
    [Fintype sigma] [Fintype tau]
    {f g h : PowerSeries R} {a : sigma -> R}
    {phi : MvPowerSeries sigma R}
    {b : sigma -> tau -> R} {x : sigma -> MvPowerSeries tau R}
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hh0 : PowerSeries.constantCoeff h = 0)
    (hphi : LIntert f g a phi)
    (hx : forall i, LIntert g h (b i) (x i)) :
    LIntert f h
      (fun j => ∑ i, a i * b i j) (MvPowerSeries.subst x phi) := by
  have hx0 : forall i, constantCoeff (x i) = 0 :=
    fun i => (hx i).constant_coeff_zero
  have hxSubst : HasSubst x := hasSubst_of_constantCoeff_zero hx0
  refine ⟨constantCoeff_subst_eq_zero hxSubst hx0
      hphi.constant_coeff_zero, ?_, ?_⟩
  · rw [homogeneous_component_subst
      hphi.constant_coeff_zero hphi.homogeneousComponent_one hx0]
    simp_rw [(hx _).homogeneousComponent_one]
    exact smul_mv_form a b
  · exact intertwining_error_subst
      hphi.constant_coeff_zero hx0 hg0 hh0 hphi.error_eq_zero
      (fun i => (hx i).error_eq_zero)

/-- The zero series is the zero-linear intertwiner between any two
zero-constant unary series. -/
theorem lubin_intertwiner_zero
    [Fintype sigma] {f g : PowerSeries R}
    (hf0 : PowerSeries.constantCoeff f = 0)
    (hg0 : PowerSeries.constantCoeff g = 0) :
    LIntert f g (fun _ => 0)
      (0 : MvPowerSeries sigma R) := by
  refine ⟨by simp, ?_, intertwining_error_zero hf0 hg0⟩
  simp [mvLinearForm]

/-- The `i`th coordinate is the identity intertwiner, with the `i`th
standard basis vector as its linear coefficient vector. -/
theorem lubin_intertwiner_x
    [Fintype sigma] [DecidableEq sigma]
    {g : PowerSeries R} (hg0 : PowerSeries.constantCoeff g = 0)
    (i : sigma) :
    LIntert g g (fun j => if j = i then 1 else 0)
      (X i : MvPowerSeries sigma R) := by
  refine ⟨by simp, ?_, intertwining_error_x hg0 i⟩
  have hlinear : mvLinearForm (fun j : sigma => if j = i then 1 else 0) =
      (X i : MvPowerSeries sigma R) := by
    classical
    simp [mvLinearForm]
  rw [<- hlinear]
  exact (MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp
    (mv_form_homogeneous
      (fun j : sigma => if j = i then 1 else 0))).symm

end

end Submission.CField.FGroups
