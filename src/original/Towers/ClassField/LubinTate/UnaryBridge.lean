import Towers.ClassField.LubinTate.SemilinearConjugate
import Towers.ClassField.FormalGroups.LubinTateIsomorphism
import Towers.ClassField.FormalGroups.PowerSeriesUnary

/-!
# Class Field Theory, Chapter I, Proposition 3.10: unary-series bridge

Step 2 uses ordinary power series, while Lemma 2.11 and the canonical series
`[1]_{g,h}` use `Fin 1`-indexed multivariable power series.  This file gives
the variable-renaming equivalence needed to pass between those presentations
and packages `[1]_{g,h}` as an ordinary power series.
-/

namespace Towers.CField.LTate

open MvPowerSeries
open Towers.CField.FGroups
open scoped MvPowerSeries.WithPiTopology

noncomputable section

private theorem continuous_rename_equiv
    {R sigma tau : Type*} [CommRing R] [TopologicalSpace R] [ContinuousAdd R]
    (e : sigma ≃ tau) :
    Continuous (MvPowerSeries.rename (R := R) e) := by
  apply continuous_pi
  intro d
  change Continuous (fun p : MvPowerSeries sigma R ↦
    coeff d (MvPowerSeries.rename (R := R) e p))
  simp_rw [coeff_rename]
  apply continuous_finsetSum
  intro x _
  exact MvPowerSeries.WithPiTopology.continuous_coeff R x

private theorem rename_subst_equiv
    {R sigma tau iota : Type*} [CommRing R]
    (e : sigma ≃ tau) {a : iota → MvPowerSeries sigma R}
    (ha : MvPowerSeries.HasSubst a) (f : MvPowerSeries iota R) :
    MvPowerSeries.rename (R := R) e (MvPowerSeries.subst a f) =
      MvPowerSeries.subst
        (fun i ↦ MvPowerSeries.rename (R := R) e (a i)) f := by
  letI : UniformSpace R := ⊥
  have hrename : Continuous (MvPowerSeries.rename (R := R) e) :=
    continuous_rename_equiv e
  have hcomp := MvPowerSeries.comp_subst_apply (R := R) ha hrename f
  have hb : MvPowerSeries.HasSubst
      (fun i ↦ MvPowerSeries.rename (R := R) e (a i)) := by
    rw [MvPowerSeries.hasSubst_iff_hasEval_of_discreteTopology]
    exact ha.hasEval.map hrename
  rw [hcomp]
  rw [← MvPowerSeries.substAlgHom_apply hb]
  rw [MvPowerSeries.substAlgHom_eq_aeval hb]

private theorem rename_subst_x
    {R sigma tau : Type*} [CommRing R] (e : sigma ≃ tau)
    (f : MvPowerSeries sigma R) :
    MvPowerSeries.rename (R := R) e f =
      MvPowerSeries.subst (fun i ↦ MvPowerSeries.X (e i)) f := by
  calc
    MvPowerSeries.rename (R := R) e f =
        MvPowerSeries.rename (R := R) e
          (MvPowerSeries.subst MvPowerSeries.X f) := by
      rw [MvPowerSeries.subst_self]
      rfl
    _ = MvPowerSeries.subst
        (fun i ↦ MvPowerSeries.rename (R := R) e (MvPowerSeries.X i)) f :=
      rename_subst_equiv e MvPowerSeries.HasSubst.X f
    _ = MvPowerSeries.subst (fun i ↦ MvPowerSeries.X (e i)) f := by
      congr 1
      funext i
      rw [MvPowerSeries.rename_X]

private theorem rename_subst_rename
    {R sigma tau : Type*} [CommRing R] [Finite sigma] (e : sigma ≃ tau)
    {a : tau → MvPowerSeries tau R} (ha : MvPowerSeries.HasSubst a)
    (f : MvPowerSeries sigma R) :
    MvPowerSeries.subst a (MvPowerSeries.rename (R := R) e f) =
      MvPowerSeries.subst (fun i ↦ a (e i)) f := by
  rw [rename_subst_x e f]
  rw [MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i ↦ by simp)) ha]
  congr 1
  funext i
  rw [MvPowerSeries.subst_X ha]

/-- Reindex a `Fin 1`-indexed unary series by the unique `Unit` variable,
thereby viewing it as an ordinary power series. -/
def unarySeriesPower
    {R : Type*} [CommRing R] (f : UnarySeries R) : PowerSeries R :=
  MvPowerSeries.rename (R := R)
    (FLConstr.unitFinOne.symm : Fin 1 ≃ Unit) f

theorem unary_constant_coeff
    {R : Type*} [CommRing R] (f : UnarySeries R) :
    PowerSeries.constantCoeff (unarySeriesPower f) =
      MvPowerSeries.constantCoeff f := by
  simpa only [unarySeriesPower] using
    (MvPowerSeries.constantCoeff_rename
      (f := (FLConstr.unitFinOne.symm : Fin 1 ≃ Unit)) f)

/-- The linear coefficient is unchanged by the unique-variable renaming. -/
theorem unary_series_coeff
    {R : Type*} [CommRing R] (f : UnarySeries R) :
    PowerSeries.coeff 1 (unarySeriesPower f) =
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 1) f := by
  simpa [unarySeriesPower, PowerSeries.coeff] using
    (MvPowerSeries.coeff_embDomain_rename
      (FLConstr.unitFinOne.symm.toEmbedding)
      f (Finsupp.single (0 : Fin 1) 1))

/-- Renaming a unary series commutes with substitution of an ordinary
zero-constant series. -/
theorem unary_series_subst
    {R : Type*} [CommRing R] {f : UnarySeries R}
    {g : PowerSeries R} (hg0 : PowerSeries.constantCoeff g = 0) :
    PowerSeries.subst g (unarySeriesPower f) =
      MvPowerSeries.subst (fun _ : Fin 1 ↦ g) f := by
  exact rename_subst_rename FLConstr.unitFinOne.symm
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ ↦ hg0)) f

/-- Renaming carries unary composition to ordinary power-series
composition. -/
theorem unary_series_compose
    {R : Type*} [CommRing R] (f g : UnarySeries R)
    (hg0 : MvPowerSeries.constantCoeff g = 0) :
    PowerSeries.subst (unarySeriesPower g)
        (unarySeriesPower f) =
      unarySeriesPower (FGLaw.compose f g) := by
  rw [unary_series_subst
    (by simpa [unary_constant_coeff] using hg0)]
  change MvPowerSeries.subst (fun _ : Fin 1 ↦ unarySeriesPower g) f =
    MvPowerSeries.rename
      (FLConstr.unitFinOne.symm : Fin 1 ≃ Unit)
      (MvPowerSeries.subst (fun _ : Fin 1 ↦ g) f)
  rw [rename_subst_equiv
    (FLConstr.unitFinOne.symm : Fin 1 ≃ Unit)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ ↦ hg0)) f]
  rfl

@[simp]
theorem unary_series_x
    {R : Type*} [CommRing R] :
    unarySeriesPower (R := R) FGLaw.unaryX = PowerSeries.X := by
  rw [unarySeriesPower, FGLaw.unaryX,
    MvPowerSeries.rename_X, PowerSeries.X]

/-- Reindexing an ordinary power series by the unique `Fin 1` variable and
then reindexing it back is the identity. -/
@[simp]
theorem unary_series_power
    {R : Type*} [CommRing R] (f : PowerSeries R) :
    unarySeriesPower (powerSeriesUnary f) = f := by
  rw [unarySeriesPower, powerSeriesUnary]
  change MvPowerSeries.rename
      (FLConstr.unitFinOne.symm : Fin 1 ≃ Unit)
      (MvPowerSeries.subst
        (fun _ : Unit ↦ MvPowerSeries.X (0 : Fin 1)) f) = f
  rw [rename_subst_equiv
    (FLConstr.unitFinOne.symm : Fin 1 ≃ Unit)
    (PowerSeries.HasSubst.X (0 : Fin 1)).const f]
  convert congrFun (MvPowerSeries.subst_self (R := R)) f using 1
  funext i
  rw [MvPowerSeries.rename_X]

/-- An exact unary Lemma 2.11 intertwiner gives the corresponding ordinary
power-series intertwining equation after reindexing its variable. -/
theorem LIntert.powerSeries_intertwines
    {R : Type*} [CommRing R] {f g : PowerSeries R} {a : Fin 1 → R}
    {phi : UnarySeries R} (h : LIntert f g a phi)
    (hg0 : PowerSeries.constantCoeff g = 0) :
    PowerSeries.subst (unarySeriesPower phi) f =
      PowerSeries.subst g (unarySeriesPower phi) := by
  have herr := lubin_tate_intertwining.mp h.error_eq_zero
  have hphi : MvPowerSeries.HasSubst (fun _ : Unit ↦ phi) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun _ ↦ h.constant_coeff_zero)
  have hcoord : MvPowerSeries.HasSubst (coordinatewiseSubst (σ := Fin 1) g) :=
    coordinatewise_subst (σ := Fin 1) hg0
  have hrenamed := congrArg
    (MvPowerSeries.rename (R := R)
      (FLConstr.unitFinOne.symm : Fin 1 ≃ Unit)) herr
  change MvPowerSeries.rename
      (FLConstr.unitFinOne.symm : Fin 1 ≃ Unit)
        (MvPowerSeries.subst (fun _ : Unit ↦ phi) f) =
    MvPowerSeries.rename
      (FLConstr.unitFinOne.symm : Fin 1 ≃ Unit)
        (MvPowerSeries.subst (coordinatewiseSubst g) phi) at hrenamed
  rw [rename_subst_equiv
    (FLConstr.unitFinOne.symm : Fin 1 ≃ Unit)
    hphi f] at hrenamed
  rw [rename_subst_equiv
    (FLConstr.unitFinOne.symm : Fin 1 ≃ Unit)
    hcoord phi] at hrenamed
  have hcoordinate (k : Fin 1) :
      MvPowerSeries.rename (R := R)
          (FLConstr.unitFinOne.symm : Fin 1 ≃ Unit)
          (coordinatewiseSubst g k) = g := by
    rw [coordinatewiseSubst]
    change MvPowerSeries.rename
        (FLConstr.unitFinOne.symm : Fin 1 ≃ Unit)
          (MvPowerSeries.subst (fun _ : Unit ↦ MvPowerSeries.X k) g) = g
    rw [rename_subst_equiv
      (FLConstr.unitFinOne.symm : Fin 1 ≃ Unit)
      (PowerSeries.HasSubst.X k).const g]
    convert congrFun (MvPowerSeries.subst_self (R := R)) g using 1
    funext i
    rw [MvPowerSeries.rename_X]
  simp_rw [hcoordinate] at hrenamed
  rw [unary_series_subst hg0]
  exact hrenamed

/-- Conversely, an ordinary exact intertwining equation becomes the unary
Lemma 2.11 predicate after reindexing the unique variable by `Fin 1`. -/
theorem unary_intertwiner_intertwines
    {R : Type*} [CommRing R]
    (f g theta : PowerSeries R) (a : R)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (htheta0 : PowerSeries.constantCoeff theta = 0)
    (htheta1 : PowerSeries.coeff 1 theta = a)
    (hintertwines : PowerSeries.subst theta f = PowerSeries.subst g theta) :
    LIntert f g (fun _ : Fin 1 ↦ a)
      (powerSeriesUnary theta) := by
  let x : UnarySeries R := FGLaw.unaryX
  let phi : UnarySeries R := PowerSeries.subst x theta
  let psi : UnarySeries R := PowerSeries.subst x g
  have hx0 : constantCoeff x = 0 := by
    simp [x, FGLaw.unaryX]
  have hphi0 : constantCoeff phi = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hx0 theta htheta0
  have hpsi0 : constantCoeff psi = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hx0 g hg0
  have hX1 : homogeneousComponent 1
      (X (0 : Fin 1) : UnarySeries R) = X 0 := by
    ext d
    rw [coeff_homogeneousComponent, coeff_X]
    by_cases hd : d = Finsupp.single (0 : Fin 1) 1
    · subst d
      simp
    · simp [hd]
  refine ⟨by simpa [powerSeriesUnary, phi, x] using hphi0, ?_, ?_⟩
  · rw [powerSeriesUnary,
      homogeneous_series_subst hx0 theta, htheta1]
    simp [x, FGLaw.unaryX, mvLinearForm, hX1]
  · rw [lubinIntertwiningError, sub_eq_zero]
    have hxSubst : PowerSeries.HasSubst x :=
      PowerSeries.HasSubst.of_constantCoeff_zero hx0
    have hthetaSubst : PowerSeries.HasSubst theta :=
      PowerSeries.HasSubst.of_constantCoeff_zero' htheta0
    have hgSubst : PowerSeries.HasSubst g :=
      PowerSeries.HasSubst.of_constantCoeff_zero' hg0
    have hpsiSubst : HasSubst (fun _ : Fin 1 ↦ psi) :=
      hasSubst_of_constantCoeff_zero (fun _ ↦ hpsi0)
    have hcoord : (coordinatewiseSubst (σ := Fin 1) g) =
        fun _ : Fin 1 ↦ psi := by
      funext i
      fin_cases i
      rfl
    change PowerSeries.subst phi f =
      MvPowerSeries.subst (coordinatewiseSubst g) phi
    rw [hcoord]
    change subst (fun _ : Unit ↦ phi) f =
      subst (fun _ : Fin 1 ↦ psi) phi
    calc
      subst (fun _ : Unit ↦ phi) f =
          PowerSeries.subst x (PowerSeries.subst theta f) := by
        exact (PowerSeries.subst_comp_subst_apply
          hthetaSubst hxSubst f).symm
      _ = PowerSeries.subst x (PowerSeries.subst g theta) := by
        rw [hintertwines]
      _ = subst (fun _ : Unit ↦ psi) theta := by
        exact PowerSeries.subst_comp_subst_apply hgSubst hxSubst theta
      _ = subst (fun _ : Fin 1 ↦ psi) phi := by
        change subst (fun _ : Unit ↦ psi) theta =
          subst (fun _ : Fin 1 ↦ psi) (PowerSeries.subst x theta)
        symm
        calc
          subst (fun _ : Fin 1 ↦ psi) (PowerSeries.subst x theta) =
              subst (fun _ : Unit ↦
                subst (fun _ : Fin 1 ↦ psi) x) theta :=
            MvPowerSeries.subst_comp_subst_apply hxSubst.const hpsiSubst theta
          _ = subst (fun _ : Unit ↦ psi) theta := by
            congr 1
            funext i
            change subst (fun _ : Fin 1 ↦ psi)
              FGLaw.unaryX = psi
            exact FGLaw.compose_unaryX psi hpsi0

/-- A two-sided compositional inverse reverses an exact ordinary
power-series intertwining equation. -/
theorem subst_inverse_intertwines
    {R : Type*} [CommRing R]
    {f g theta inverseTheta : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0)
    (htheta0 : PowerSeries.constantCoeff theta = 0)
    (hinverse0 : PowerSeries.constantCoeff inverseTheta = 0)
    (hthetaInverse : PowerSeries.subst inverseTheta theta = PowerSeries.X)
    (hinverseTheta : PowerSeries.subst theta inverseTheta = PowerSeries.X)
    (hintertwines : PowerSeries.subst theta f = PowerSeries.subst g theta) :
    PowerSeries.subst inverseTheta g =
      PowerSeries.subst f inverseTheta := by
  have hthetaSubst : PowerSeries.HasSubst theta :=
    PowerSeries.HasSubst.of_constantCoeff_zero' htheta0
  have hinverseSubst : PowerSeries.HasSubst inverseTheta :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hinverse0
  have hgSubst : PowerSeries.HasSubst g :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hg0
  have hginverse0 :
      PowerSeries.constantCoeff (PowerSeries.subst inverseTheta g) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hinverse0 g hg0
  have hginverseSubst :
      PowerSeries.HasSubst (PowerSeries.subst inverseTheta g) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hginverse0
  have hfirst :
      f = PowerSeries.subst (PowerSeries.subst inverseTheta g) theta := by
    calc
      f = PowerSeries.subst PowerSeries.X f := by
        exact PowerSeries.map_algebraMap_eq_subst_X
          (R := R) (S := R) f
      _ = PowerSeries.subst
          (PowerSeries.subst inverseTheta theta) f := by rw [hthetaInverse]
      _ = PowerSeries.subst inverseTheta (PowerSeries.subst theta f) :=
        (PowerSeries.subst_comp_subst_apply
          hthetaSubst hinverseSubst f).symm
      _ = PowerSeries.subst inverseTheta (PowerSeries.subst g theta) := by
        rw [hintertwines]
      _ = PowerSeries.subst (PowerSeries.subst inverseTheta g) theta :=
        PowerSeries.subst_comp_subst_apply
          hgSubst hinverseSubst theta
  symm
  calc
    PowerSeries.subst f inverseTheta =
        PowerSeries.subst
          (PowerSeries.subst (PowerSeries.subst inverseTheta g) theta)
          inverseTheta := by rw [← hfirst]
    _ = PowerSeries.subst (PowerSeries.subst inverseTheta g)
          (PowerSeries.subst theta inverseTheta) :=
      (PowerSeries.subst_comp_subst_apply
        hthetaSubst
        hginverseSubst
        inverseTheta).symm
    _ = PowerSeries.subst (PowerSeries.subst inverseTheta g)
          PowerSeries.X := by rw [hinverseTheta]
    _ = PowerSeries.subst inverseTheta g := by
      exact PowerSeries.subst_X hginverseSubst

/-- The ordinary compositional inverse of an exact intertwiner becomes the
reverse unary Lemma 2.11 intertwiner. -/
theorem unary_lubin_intertwiner
    {R : Type*} [CommRing R]
    (epsilon : Rˣ) {f g theta inverseTheta : PowerSeries R}
    (hf0 : PowerSeries.constantCoeff f = 0)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (htheta0 : PowerSeries.constantCoeff theta = 0)
    (hinverse0 : PowerSeries.constantCoeff inverseTheta = 0)
    (htheta1 : PowerSeries.coeff 1 theta = (epsilon : R))
    (hthetaInverse : PowerSeries.subst inverseTheta theta = PowerSeries.X)
    (hinverseTheta : PowerSeries.subst theta inverseTheta = PowerSeries.X)
    (hintertwines : PowerSeries.subst theta f = PowerSeries.subst g theta) :
    LIntert g f
      (fun _ : Fin 1 ↦ ((epsilon⁻¹ : Rˣ) : R))
      (powerSeriesUnary inverseTheta) := by
  apply unary_intertwiner_intertwines
  · exact hf0
  · exact hinverse0
  · exact coeff_subst_x
      epsilon htheta1 hinverse0 hthetaInverse
  · exact subst_inverse_intertwines
      hg0 htheta0 hinverse0 hthetaInverse hinverseTheta hintertwines

/-- Milne's canonical scalar intertwiner, represented as an ordinary power
series. -/
def lubinScalarIntertwiner
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (a : R) : PowerSeries R :=
  unarySeriesPower
    (tateScalarIntertwiner pi hpi0 hpi hfield f g hf hg a)

theorem lubin_intertwiner_coeff
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (a : R) :
    PowerSeries.constantCoeff
      (lubinScalarIntertwiner
        pi hpi0 hpi hfield f g hf hg a) = 0 := by
  rw [lubinScalarIntertwiner,
    unary_constant_coeff]
  exact (lubin_intertwiner_spec
    pi hpi0 hpi hfield f g hf hg a).constant_coeff_zero

theorem lubin_tate_intertwiner
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (a : R) :
    PowerSeries.coeff 1
      (lubinScalarIntertwiner
        pi hpi0 hpi hfield f g hf hg a) = a := by
  rw [lubinScalarIntertwiner,
    unary_series_coeff]
  have hlinear := (lubin_intertwiner_spec
    pi hpi0 hpi hfield f g hf hg a).homogeneousComponent_one
  have hcoeff := congrArg
    (MvPowerSeries.coeff (Finsupp.single (0 : Fin 1) 1)) hlinear
  rw [coeff_homogeneousComponent, if_pos (by simp)] at hcoeff
  simpa [mvLinearForm] using hcoeff

/-- The ordinary series representing `[a]_{g,f}` satisfies
`g o [a] = [a] o f`. -/
theorem lubin_intertwiner_intertwines
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (a : R) :
    PowerSeries.subst
        (lubinScalarIntertwiner
          pi hpi0 hpi hfield f g hf hg a) g =
      PowerSeries.subst f
        (lubinScalarIntertwiner
          pi hpi0 hpi hfield f g hf hg a) := by
  unfold lubinScalarIntertwiner
  apply LIntert.powerSeries_intertwines
    (lubin_intertwiner_spec
      pi hpi0 hpi hfield f g hf hg a)
  simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf.1

/-- The ordinary representatives of `[1]_{g,f}` and `[1]_{f,g}` are
compositional inverses in the orientation used by Step 2. -/
theorem lubin_intertwiner_inverse
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g) :
    PowerSeries.subst
        (lubinScalarIntertwiner
          pi hpi0 hpi hfield g f hg hf 1)
        (lubinScalarIntertwiner
          pi hpi0 hpi hfield f g hf hg 1) = PowerSeries.X := by
  let E := canonicalLubinIso pi hpi0 hpi hfield f g hf hg
  have hcomp := congrArg FGLaw.Hom.toSeries E.hom_inv_id
  change FGLaw.compose
      (tateScalarIntertwiner pi hpi0 hpi hfield f g hf hg 1)
      (tateScalarIntertwiner pi hpi0 hpi hfield g f hg hf 1) =
    FGLaw.unaryX at hcomp
  change PowerSeries.subst
      (unarySeriesPower
        (tateScalarIntertwiner pi hpi0 hpi hfield g f hg hf 1))
      (unarySeriesPower
        (tateScalarIntertwiner pi hpi0 hpi hfield f g hf hg 1)) =
    PowerSeries.X
  rw [unary_series_compose, hcomp,
    unary_series_x]
  exact (lubin_intertwiner_spec
      pi hpi0 hpi hfield g f hg hf 1).constant_coeff_zero

/-- The final canonical adjustment in Proposition 3.10, Step 2.  This is the
generic conjugation theorem specialized to Milne's actual series
`[1]_{g,h}` and its canonical reverse `[1]_{h,g}`. -/
theorem semilinear_conjugate_adjustment
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (varpi : R) (hvarpi0 : varpi ≠ 0) (hvarpi : ¬ IsUnit varpi)
    (hfield : IsField (R ⧸ Ideal.span {varpi}))
    [Fintype (R ⧸ Ideal.span {varpi})]
    (h g : PowerSeries R)
    (hh : LubinSeries varpi
      (Fintype.card (R ⧸ Ideal.span {varpi})) h)
    (hg : LubinSeries varpi
      (Fintype.card (R ⧸ Ideal.span {varpi})) g)
    (sigma : R →+* R)
    {theta inverseTheta f : PowerSeries R}
    (htheta0 : PowerSeries.constantCoeff theta = 0)
    (hinverse0 : PowerSeries.constantCoeff inverseTheta = 0)
    (hf0 : PowerSeries.constantCoeff f = 0)
    (hconjugate : semilinearConjugate sigma theta inverseTheta f = h)
    (hfixi :
      PowerSeries.map sigma
          (lubinScalarIntertwiner
            varpi hvarpi0 hvarpi hfield h g hh hg 1) =
        lubinScalarIntertwiner
          varpi hvarpi0 hvarpi hfield h g hh hg 1) :
    semilinearConjugate sigma
        (PowerSeries.subst theta
          (lubinScalarIntertwiner
            varpi hvarpi0 hvarpi hfield h g hh hg 1))
        (PowerSeries.subst
          (lubinScalarIntertwiner
            varpi hvarpi0 hvarpi hfield g h hg hh 1)
          inverseTheta)
        f = g := by
  apply semilinear_subst_intertwines sigma
  · exact lubin_intertwiner_coeff
      varpi hvarpi0 hvarpi hfield h g hh hg 1
  · exact lubin_intertwiner_coeff
      varpi hvarpi0 hvarpi hfield g h hg hh 1
  · exact htheta0
  · exact hinverse0
  · exact hf0
  · exact hfixi
  · exact lubin_intertwiner_inverse
      varpi hvarpi0 hvarpi hfield h g hh hg
  · rw [hconjugate]
    exact lubin_intertwiner_intertwines
      varpi hvarpi0 hvarpi hfield h g hh hg 1

end

end Towers.CField.LTate
