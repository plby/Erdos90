import Towers.ClassField.FormalGroups.LubinDegreeCorrection
import Towers.ClassField.FormalGroups.SubstitutionCongruence

/-!
# Class Field Theory, Chapter I, Section 2: composition of intertwiners

The formal-group constructions after Lemma 2.11 repeatedly use the same
substitution argument.  If `phi` intertwines `f` with `g`, and every member
of a family `x` intertwines `g` with `h`, then substituting `x` into `phi`
intertwines `f` with `h`.
-/

namespace Towers.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R sigma tau : Type*} [CommRing R]

/-- Equality of the constant and linear homogeneous parts is exactly
agreement through total degree one. -/
theorem constant_homogeneous_component
    {F G : MvPowerSeries sigma R}
    (hzero : constantCoeff F = constantCoeff G)
    (hone : homogeneousComponent 1 F = homogeneousComponent 1 G) :
    (2 : ℕ) <= (F - G).order := by
  apply MvPowerSeries.nat_le_order
  intro d hd
  have hdegree : d.degree < 2 := by exact_mod_cast hd
  rw [map_sub]
  by_cases hd0 : d.degree = 0
  · have hdzero : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hd0
    subst d
    simp [coeff_zero_eq_constantCoeff_apply, hzero]
  · have hd1 : d.degree = 1 := by omega
    rw [sub_eq_zero]
    have h := congrArg (coeff d) hone
    simpa only [coeff_homogeneousComponent, if_pos hd1] using h

/-- The degree-one part of a substituted series is obtained by substituting
the degree-one parts of the inner family into its prescribed linear form. -/
theorem homogeneous_component_subst
    [Fintype sigma] [Finite tau]
    {phi : MvPowerSeries sigma R} {a : sigma -> R}
    {x : sigma -> MvPowerSeries tau R}
    (hphi0 : constantCoeff phi = 0)
    (hphi1 : homogeneousComponent 1 phi = mvLinearForm a)
    (hx0 : forall i, constantCoeff (x i) = 0) :
    homogeneousComponent 1 (subst x phi) =
      ∑ i, a i • homogeneousComponent 1 (x i) := by
  have hxSubst : HasSubst x := hasSubst_of_constantCoeff_zero hx0
  have hlinear : (2 : ℕ) <= (phi - mvLinearForm a).order :=
    constant_homogeneous_component
      (by rw [hphi0, mv_constant_coeff]) (by
        rw [<- (MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp
          (mv_form_homogeneous a))]
        exact hphi1)
  have hsubst : (2 : ℕ) <=
      (subst x phi - subst x (mvLinearForm a)).order := by
    rw [<- subst_sub hxSubst]
    exact hlinear.trans (order_subst_orders hxSubst
      (fun i => one_le_order_iff_constCoeff_eq_zero.mpr (hx0 i)) _)
  have hone : homogeneousComponent 1 (subst x phi) =
      homogeneousComponent 1 (subst x (mvLinearForm a)) :=
    homogeneous_component_nat
      (show (1 : ℕ∞) < (subst x phi - subst x (mvLinearForm a)).order by
        exact (show (1 : ℕ∞) < 2 by norm_num).trans_le hsubst)
  rw [hone, subst_mv_form a x hxSubst, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]

/-- The zero-error formulation is the literal intertwining identity. -/
theorem lubin_tate_intertwining
    {f g : PowerSeries R} {phi : MvPowerSeries sigma R} :
    lubinIntertwiningError f g phi = 0 <->
      PowerSeries.subst phi f = subst (coordinatewiseSubst g) phi := by
  exact sub_eq_zero

/-- Every coordinate variable intertwines a unary series with itself. -/
theorem intertwining_error_x
    [Finite sigma] {g : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0) (i : sigma) :
    lubinIntertwiningError g g (X i) = 0 := by
  rw [lubinIntertwiningError]
  rw [subst_X (coordinatewise_subst (σ := sigma) hg0)]
  exact sub_self _

/-- The zero series intertwines any two zero-constant unary series. -/
theorem intertwining_error_zero
    [Finite sigma] {f g : PowerSeries R}
    (hf0 : PowerSeries.constantCoeff f = 0)
    (hg0 : PowerSeries.constantCoeff g = 0) :
    lubinIntertwiningError f g (0 : MvPowerSeries sigma R) = 0 := by
  rw [lubinIntertwiningError]
  have hleft : PowerSeries.subst (0 : MvPowerSeries sigma R) f = 0 := by
    apply MvPowerSeries.ext
    intro d
    rw [PowerSeries.coeff_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
    rw [finsum_eq_single _ 0]
    · simp [PowerSeries.coeff_zero_eq_constantCoeff, hf0]
    · intro n hn
      simp [zero_pow hn]
  have hright : subst (coordinatewiseSubst g)
      (0 : MvPowerSeries sigma R) = 0 := by
    rw [<- MvPowerSeries.substAlgHom_apply
      (coordinatewise_subst (σ := sigma) hg0), map_zero]
  rw [hleft, hright, sub_self]

/-- Exact Lubin--Tate intertwiners are closed under multivariable
substitution.  This is the common calculation behind Proposition 2.12's
formal-group axioms and Proposition 2.14's homomorphism assertion. -/
theorem intertwining_error_subst
    [Finite sigma] [Finite tau]
    {f g h : PowerSeries R} {phi : MvPowerSeries sigma R}
    {x : sigma -> MvPowerSeries tau R}
    (hphi0 : constantCoeff phi = 0)
    (hx0 : forall i, constantCoeff (x i) = 0)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hh0 : PowerSeries.constantCoeff h = 0)
    (hphi : lubinIntertwiningError f g phi = 0)
    (hx : forall i, lubinIntertwiningError g h (x i) = 0) :
    lubinIntertwiningError f h (subst x phi) = 0 := by
  have hphiSubst : PowerSeries.HasSubst phi :=
    PowerSeries.HasSubst.of_constantCoeff_zero hphi0
  have hxSubst : HasSubst x := hasSubst_of_constantCoeff_zero hx0
  have hcoordG : HasSubst
      (coordinatewiseSubst (σ := sigma) g :
        sigma -> MvPowerSeries sigma R) :=
    coordinatewise_subst hg0
  have hcoordH : HasSubst
      (coordinatewiseSubst (σ := tau) h :
        tau -> MvPowerSeries tau R) :=
    coordinatewise_subst hh0
  have hphi' :=
    lubin_tate_intertwining.mp hphi
  have hx' : forall i,
      PowerSeries.subst (x i) g =
        subst (coordinatewiseSubst h) (x i) := fun i =>
    lubin_tate_intertwining.mp (hx i)
  apply lubin_tate_intertwining.mpr
  calc
    PowerSeries.subst (subst x phi) f =
        subst x (PowerSeries.subst phi f) := by
          simpa only [PowerSeries.subst_def] using
            (MvPowerSeries.subst_comp_subst_apply
              hphiSubst.const hxSubst f).symm
    _ = subst x (subst (coordinatewiseSubst g) phi) := by rw [hphi']
    _ = subst (fun i => subst x (coordinatewiseSubst g i)) phi := by
          exact MvPowerSeries.subst_comp_subst_apply hcoordG hxSubst phi
    _ = subst (fun i => PowerSeries.subst (x i) g) phi := by
          congr 1
          funext i
          simpa only [coordinatewiseSubst, PowerSeries.subst_def,
            MvPowerSeries.subst_X hxSubst] using
            MvPowerSeries.subst_comp_subst_apply
              (PowerSeries.HasSubst.X i).const hxSubst g
    _ = subst (fun i => subst (coordinatewiseSubst h) (x i)) phi := by
          congr 1
          funext i
          exact hx' i
    _ = subst (coordinatewiseSubst h) (subst x phi) := by
          exact (MvPowerSeries.subst_comp_subst_apply
            hxSubst hcoordH phi).symm

end

end Towers.CField.FGroups
