import Towers.ClassField.LubinTate.UnaryBridge

/-!
# Class Field Theory, Chapter I, Proposition 3.10, Steps 3 and 4

Milne leaves Steps 3 and 4 to the reader as applications of Lemma 2.11.  The
common argument is that conjugation by mutually inverse exact unary
intertwiners transports every self-intertwiner and preserves its prescribed
linear coefficient vector.  Lemma 2.11 then identifies the transported
binary law and scalar endomorphisms with the canonical ones.
-/

namespace Towers.CField.LTate

open MvPowerSeries
open Towers.CField.FGroups

noncomputable section

variable {R sigma : Type*} [CommRing R]

/-- Conjugation by mutually inverse exact unary intertwiners transports any
self-intertwiner, preserving its prescribed linear coefficient vector. -/
theorem lubin_intertwiner_conjugate
    [Fintype sigma]
    {f g : PowerSeries R} {theta inverseTheta : UnarySeries R}
    {epsilon inverseEpsilon : R} {a : sigma -> R}
    {phi : MvPowerSeries sigma R}
    (hf0 : PowerSeries.constantCoeff f = 0)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (htheta : LIntert g f
      (fun _ : Fin 1 => epsilon) theta)
    (hinverseTheta : LIntert f g
      (fun _ : Fin 1 => inverseEpsilon) inverseTheta)
    (hepsilon : epsilon * inverseEpsilon = 1)
    (hphi : LIntert f f a phi) :
    LIntert g g a
      (FGLaw.compose theta
        (MvPowerSeries.subst
          (fun i => FGLaw.compose inverseTheta (X i)) phi)) := by
  classical
  have hinverseCoordinate : forall i : sigma,
      LIntert f g
        (fun j => inverseEpsilon * if j = i then 1 else 0)
        (FGLaw.compose inverseTheta (X i)) := by
    intro i
    let x : Fin 1 -> MvPowerSeries sigma R := fun _ => X i
    let b : Fin 1 -> sigma -> R :=
      fun _ j => if j = i then 1 else 0
    have hx : forall k, LIntert g g (b k) (x k) := by
      intro k
      exact lubin_intertwiner_x hg0 i
    have h := hinverseTheta.subst hg0 hg0 hx
    simpa [FGLaw.compose, x, b] using h
  have hinner : LIntert f g
      (fun j => a j * inverseEpsilon)
      (MvPowerSeries.subst
        (fun i => FGLaw.compose inverseTheta (X i)) phi) := by
    have h := hphi.subst hf0 hg0 hinverseCoordinate
    convert h using 1
    funext j
    simp [mul_ite]
  let x : Fin 1 -> MvPowerSeries sigma R := fun _ =>
    MvPowerSeries.subst
      (fun i => FGLaw.compose inverseTheta (X i)) phi
  let b : Fin 1 -> sigma -> R := fun _ j => a j * inverseEpsilon
  have hx : forall k, LIntert f g (b k) (x k) := by
    intro k
    exact hinner
  have h := htheta.subst hf0 hg0 hx
  convert h using 1
  · funext j
    rw [Fin.sum_univ_one]
    change a j = epsilon * (a j * inverseEpsilon)
    symm
    calc
      epsilon * (a j * inverseEpsilon) =
          a j * (epsilon * inverseEpsilon) := by ac_rfl
      _ = a j := by rw [hepsilon, mul_one]

/-- Proposition 3.10, Step 3: the transported binary law is the canonical
Lubin--Tate law for `g`. -/
theorem conjugate_tate_law
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (varpi : R) (hvarpi0 : varpi ≠ 0) (hvarpi : ¬ IsUnit varpi)
    (hfield : IsField (R ⧸ Ideal.span {varpi}))
    [Fintype (R ⧸ Ideal.span {varpi})]
    (g : PowerSeries R)
    (hg : LubinSeries varpi
      (Fintype.card (R ⧸ Ideal.span {varpi})) g)
    {f : PowerSeries R} {theta inverseTheta : UnarySeries R}
    {epsilon inverseEpsilon : R} {F : BinarySeries R}
    (hf0 : PowerSeries.constantCoeff f = 0)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (htheta : LIntert g f
      (fun _ : Fin 1 => epsilon) theta)
    (hinverseTheta : LIntert f g
      (fun _ : Fin 1 => inverseEpsilon) inverseTheta)
    (hepsilon : epsilon * inverseEpsilon = 1)
    (hF : LIntert f f (fun _ : Fin 2 => 1) F) :
    FGLaw.compose theta
        (MvPowerSeries.subst
          (fun i => FGLaw.compose inverseTheta (X i)) F) =
      lubinTateLaw varpi hvarpi0 hvarpi hfield g hg := by
  apply lubin_law varpi hvarpi0 hvarpi hfield g hg
  exact lubin_intertwiner_conjugate hf0 hg0 htheta
    hinverseTheta hepsilon hF

/-- Proposition 3.10, Step 4: conjugating a scalar self-intertwiner gives the
canonical scalar endomorphism of the Lubin--Tate law for `g`. -/
theorem conjugate_lubin_intertwiner
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (varpi : R) (hvarpi0 : varpi ≠ 0) (hvarpi : ¬ IsUnit varpi)
    (hfield : IsField (R ⧸ Ideal.span {varpi}))
    [Fintype (R ⧸ Ideal.span {varpi})]
    (g : PowerSeries R)
    (hg : LubinSeries varpi
      (Fintype.card (R ⧸ Ideal.span {varpi})) g)
    {f : PowerSeries R} {theta inverseTheta : UnarySeries R}
    {epsilon inverseEpsilon a : R} {phi : UnarySeries R}
    (hf0 : PowerSeries.constantCoeff f = 0)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (htheta : LIntert g f
      (fun _ : Fin 1 => epsilon) theta)
    (hinverseTheta : LIntert f g
      (fun _ : Fin 1 => inverseEpsilon) inverseTheta)
    (hepsilon : epsilon * inverseEpsilon = 1)
    (hphi : LIntert f f (fun _ : Fin 1 => a) phi) :
    FGLaw.compose theta
        (MvPowerSeries.subst
          (fun i => FGLaw.compose inverseTheta (X i)) phi) =
      tateScalarIntertwiner varpi hvarpi0 hvarpi hfield
        g g hg hg a := by
  apply tate_intertwiner varpi hvarpi0 hvarpi hfield
    g g hg hg (fun _ : Fin 1 => a)
  exact lubin_intertwiner_conjugate hf0 hg0 htheta
    hinverseTheta hepsilon hphi

/-- Proposition 3.10, Step 3, stated in the ordinary `PowerSeries` language
used in Steps 1 and 2. -/
theorem conjugate_lubin_law
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (varpi : R) (hvarpi0 : varpi ≠ 0) (hvarpi : ¬ IsUnit varpi)
    (hfield : IsField (R ⧸ Ideal.span {varpi}))
    [Fintype (R ⧸ Ideal.span {varpi})]
    (g : PowerSeries R)
    (hg : LubinSeries varpi
      (Fintype.card (R ⧸ Ideal.span {varpi})) g)
    (epsilon : Rˣ)
    {w theta inverseTheta : PowerSeries R} {F : BinarySeries R}
    (hw0 : PowerSeries.constantCoeff w = 0)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (htheta0 : PowerSeries.constantCoeff theta = 0)
    (hinverse0 : PowerSeries.constantCoeff inverseTheta = 0)
    (htheta1 : PowerSeries.coeff 1 theta = (epsilon : R))
    (hthetaInverse : PowerSeries.subst inverseTheta theta = PowerSeries.X)
    (hinverseTheta : PowerSeries.subst theta inverseTheta = PowerSeries.X)
    (hintertwines : PowerSeries.subst theta g = PowerSeries.subst w theta)
    (hF : LIntert w w (fun _ : Fin 2 => 1) F) :
    FGLaw.compose (powerSeriesUnary theta)
        (MvPowerSeries.subst
          (fun i => FGLaw.compose
            (powerSeriesUnary inverseTheta) (X i)) F) =
      lubinTateLaw varpi hvarpi0 hvarpi hfield g hg := by
  apply conjugate_tate_law
    varpi hvarpi0 hvarpi hfield g hg hw0 hg0
  · exact unary_intertwiner_intertwines
      g w theta (epsilon : R) hw0 htheta0 htheta1 hintertwines
  · exact unary_lubin_intertwiner
      epsilon hg0 hw0 htheta0 hinverse0 htheta1
      hthetaInverse hinverseTheta hintertwines
  · exact epsilon.mul_inv
  · exact hF

/-- Proposition 3.10, Step 4, stated in the ordinary `PowerSeries` language
used in Steps 1 and 2. -/
theorem conjugate_scalar_intertwiner
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (varpi : R) (hvarpi0 : varpi ≠ 0) (hvarpi : ¬ IsUnit varpi)
    (hfield : IsField (R ⧸ Ideal.span {varpi}))
    [Fintype (R ⧸ Ideal.span {varpi})]
    (g : PowerSeries R)
    (hg : LubinSeries varpi
      (Fintype.card (R ⧸ Ideal.span {varpi})) g)
    (epsilon : Rˣ)
    {w theta inverseTheta : PowerSeries R}
    {a : R} {phi : UnarySeries R}
    (hw0 : PowerSeries.constantCoeff w = 0)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (htheta0 : PowerSeries.constantCoeff theta = 0)
    (hinverse0 : PowerSeries.constantCoeff inverseTheta = 0)
    (htheta1 : PowerSeries.coeff 1 theta = (epsilon : R))
    (hthetaInverse : PowerSeries.subst inverseTheta theta = PowerSeries.X)
    (hinverseTheta : PowerSeries.subst theta inverseTheta = PowerSeries.X)
    (hintertwines : PowerSeries.subst theta g = PowerSeries.subst w theta)
    (hphi : LIntert w w (fun _ : Fin 1 => a) phi) :
    FGLaw.compose (powerSeriesUnary theta)
        (MvPowerSeries.subst
          (fun i => FGLaw.compose
            (powerSeriesUnary inverseTheta) (X i)) phi) =
      tateScalarIntertwiner varpi hvarpi0 hvarpi hfield
        g g hg hg a := by
  apply conjugate_lubin_intertwiner
    varpi hvarpi0 hvarpi hfield g hg hw0 hg0
  · exact unary_intertwiner_intertwines
      g w theta (epsilon : R) hw0 htheta0 htheta1 hintertwines
  · exact unary_lubin_intertwiner
      epsilon hg0 hw0 htheta0 hinverse0 htheta1
      hthetaInverse hinverseTheta hintertwines
  · exact epsilon.mul_inv
  · exact hphi

end

end Towers.CField.LTate
