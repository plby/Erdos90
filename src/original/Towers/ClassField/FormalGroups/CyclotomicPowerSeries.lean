import Towers.ClassField.FormalGroups.LubinGroupLaw
import Towers.ClassField.FormalGroups.Homomorphisms

/-!
# Class Field Theory, Chapter I, Example 2.13

The cyclotomic series `(1+T)^p-1` is an endomorphism of the multiplicative
formal group law.  Consequently, whenever it is a Lubin--Tate series, the
uniqueness in Proposition 2.12 identifies its canonical Lubin--Tate law with
`X+Y+XY`.
-/

namespace Towers.CField.FGroups

open MvPowerSeries

noncomputable section

/-- The cyclotomic power series `(1+T)^n-1` over an arbitrary coefficient
ring. -/
def cyclotomicPowerSeries
    {R : Type*} [CommRing R] (n : ℕ) : PowerSeries R :=
  (1 + PowerSeries.X) ^ n - 1

/-- Example 2.13's elementary identity: `(1+T)^n-1` is an endomorphism of
the multiplicative formal group law. -/
theorem cyclotomic_series_endomorphism
    {R : Type*} [CommRing R] (n : ℕ) :
    PowerSeries.subst (FGLaw.multiplicativeLaw (R := R))
        (cyclotomicPowerSeries (R := R) n) =
      MvPowerSeries.subst
        (coordinatewiseSubst (cyclotomicPowerSeries (R := R) n))
        (FGLaw.multiplicativeLaw (R := R)) := by
  let F : BinarySeries R := FGLaw.multiplicativeLaw
  have hF0 : constantCoeff F = 0 := by
    simp [F, FGLaw.multiplicativeLaw]
  have hFSubst : PowerSeries.HasSubst F :=
    PowerSeries.HasSubst.of_constantCoeff_zero hF0
  have hcoord0 (i : Fin 2) : constantCoeff (X i : BinarySeries R) = 0 := by simp
  have hcoordSubst (i : Fin 2) : PowerSeries.HasSubst (X i : BinarySeries R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (hcoord0 i)
  have heval (x : BinarySeries R) (hx : constantCoeff x = 0) :
      PowerSeries.subst x (cyclotomicPowerSeries (R := R) n) =
        (1 + x) ^ n - 1 := by
    have hs : PowerSeries.HasSubst x :=
      PowerSeries.HasSubst.of_constantCoeff_zero hx
    rw [cyclotomicPowerSeries, PowerSeries.subst_sub hs,
      PowerSeries.subst_pow hs, PowerSeries.subst_add hs]
    rw [PowerSeries.subst_X hs]
    have hone : PowerSeries.subst x (1 : PowerSeries R) = 1 := by
      rw [← PowerSeries.coe_substAlgHom hs]
      exact map_one _
    rw [hone]
  rw [heval F hF0]
  have hfamily : coordinatewiseSubst (σ := Fin 2)
      (cyclotomicPowerSeries (R := R) n) =
      Fin.cases
        (PowerSeries.subst (X (0 : Fin 2))
          (cyclotomicPowerSeries (R := R) n))
        (fun _ : Fin 1 =>
          PowerSeries.subst (X (1 : Fin 2))
            (cyclotomicPowerSeries (R := R) n)) := by
    funext i
    fin_cases i <;> rfl
  rw [hfamily]
  change (1 + F) ^ n - 1 = FGLaw.substitute
    (FGLaw.multiplicativeLaw (R := R))
    (PowerSeries.subst (X (0 : Fin 2))
      (cyclotomicPowerSeries (R := R) n))
    (PowerSeries.subst (X (1 : Fin 2))
      (cyclotomicPowerSeries (R := R) n))
  rw [FGLaw.substitute_multiplicativeLaw]
  rw [heval (X (0 : Fin 2)) (hcoord0 0),
    heval (X (1 : Fin 2)) (hcoord0 1)]
  have hF : F = X (0 : Fin 2) + X (1 : Fin 2) + X 0 * X 1 := by
    change (((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) +
      MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) R) :
        BinarySeries R) = _)
    simp only [MvPolynomial.coe_add, MvPolynomial.coe_mul,
      MvPolynomial.coe_X]
  rw [hF]
  rw [show (1 : BinarySeries R) +
      (X (0 : Fin 2) + X (1 : Fin 2) + X (0 : Fin 2) * X (1 : Fin 2)) =
      (1 + X (0 : Fin 2)) * (1 + X (1 : Fin 2)) by ring, mul_pow]
  ring

/-- Any Lubin--Tate series which is an endomorphism of the multiplicative
law has the multiplicative law as its canonical Lubin--Tate law. -/
theorem multiplicative_formal_law
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hendo :
      PowerSeries.subst (FGLaw.multiplicativeLaw (R := R)) f =
        MvPowerSeries.subst (coordinatewiseSubst f)
          (FGLaw.multiplicativeLaw (R := R))) :
    FGLaw.multiplicative (R := R) =
      lubinFormalLaw pi hpi0 hpi hfield f hf := by
  apply FLConstr.ext_law
  change FGLaw.multiplicativeLaw =
    lubinTateLaw pi hpi0 hpi hfield f hf
  apply lubin_law pi hpi0 hpi hfield f hf
  refine ⟨?_, ?_, sub_eq_zero.mpr hendo⟩
  · simp [FGLaw.multiplicativeLaw]
  · have hlaw : FGLaw.multiplicativeLaw (R := R) =
        mvLinearForm (fun _ : Fin 2 => (1 : R)) +
          X (0 : Fin 2) * X (1 : Fin 2) := by
      simp [FGLaw.multiplicativeLaw, mvLinearForm, Fin.sum_univ_two]
    have hlin : homogeneousComponent 1
        (mvLinearForm (fun _ : Fin 2 => (1 : R))) =
          mvLinearForm (fun _ : Fin 2 => (1 : R)) :=
      (MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp
        (mv_form_homogeneous (fun _ : Fin 2 => (1 : R)))).symm
    have hx : (1 : ℕ∞) <= (X (0 : Fin 2) : BinarySeries R).order :=
      one_le_order_iff_constCoeff_eq_zero.mpr (by simp)
    have hy : (1 : ℕ∞) <= (X (1 : Fin 2) : BinarySeries R).order :=
      one_le_order_iff_constCoeff_eq_zero.mpr (by simp)
    have hprodOrder : (2 : ℕ∞) <=
        ((X (0 : Fin 2) * X (1 : Fin 2)) : BinarySeries R).order := by
      calc
        (2 : ℕ∞) = 1 + 1 := by norm_num
        _ <= (X (0 : Fin 2) : BinarySeries R).order +
            (X (1 : Fin 2) : BinarySeries R).order := add_le_add hx hy
        _ <= ((X (0 : Fin 2) * X (1 : Fin 2)) : BinarySeries R).order :=
          MvPowerSeries.le_order_mul
    have hprod : homogeneousComponent 1
        ((X (0 : Fin 2) * X (1 : Fin 2)) : BinarySeries R) = 0 :=
      homogeneousComponent_of_lt_order_eq_zero
        ((show (1 : ℕ∞) < 2 by norm_num).trans_le hprodOrder)
    rw [hlaw, map_add, hlin, hprod, add_zero]

/-- Example 2.13 in its reusable algebraic form: if `(1+T)^p-1` satisfies
the Lubin--Tate congruences for `pi`, then its canonical law is precisely the
multiplicative formal group law. -/
theorem lubin_law_multiplicative
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (p : ℕ)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi}))
      (cyclotomicPowerSeries (R := R) p : PowerSeries R)) :
    lubinFormalLaw pi hpi0 hpi hfield
        (cyclotomicPowerSeries (R := R) p) hf =
      FGLaw.multiplicative (R := R) := by
  exact (multiplicative_formal_law
    pi hpi0 hpi hfield _ hf
      (cyclotomic_series_endomorphism (R := R) p)).symm

end

end Towers.CField.FGroups
