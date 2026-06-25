import Towers.ClassField.FormalGroups.HomGroupRing
import Towers.ClassField.FormalGroups.LubinTateHomomorphism
import Towers.ClassField.FormalGroups.LubinIntertwinerArithmetic

/-!
# Class Field Theory, Chapter I, Corollary 2.16

The canonical Lubin--Tate intertwiners attached to a unit and its inverse
give mutually inverse homomorphisms between the formal group laws attached
to any two series in `\mathcal F_\pi`.
-/

namespace Towers.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]

/-- The coefficient-one self-intertwiner is the identity series. -/
theorem scalar_intertwiner_self
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    tateScalarIntertwiner pi hpi0 hpi hfield f f hf hf 1 =
      FGLaw.unaryX := by
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf.1
  have hX : LIntert f f (fun _ : Fin 1 ↦ 1)
      (FGLaw.unaryX : UnarySeries R) := by
    simpa [FGLaw.unaryX] using
      (lubin_intertwiner_x (sigma := Fin 1) hf0 (0 : Fin 1))
  exact (tate_intertwiner pi hpi0 hpi hfield f f hf hf _ hX).symm

/-- Proposition 2.15 at the level of formal-group homomorphisms: addition
of coefficients is addition using the target Lubin--Tate law. -/
theorem lubin_tate_scalar
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (a b : R) :
    lubinTateScalar pi hpi0 hpi hfield f g hf hg (a + b) =
      lubinTateScalar pi hpi0 hpi hfield f g hf hg a +
        lubinTateScalar pi hpi0 hpi hfield f g hf hg b := by
  apply FGLaw.Hom.ext
  exact (lubin_intertwiner_add
    pi hpi0 hpi hfield f g hf hg a b).symm

/-- Proposition 2.15 at the level of formal-group homomorphisms:
multiplication of coefficients is composition. -/
theorem lubin_scalar_comp
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g h : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (hh : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) h)
    (a b : R) :
    FGLaw.Hom.comp
        (lubinTateScalar pi hpi0 hpi hfield g h hg hh a)
        (lubinTateScalar pi hpi0 hpi hfield f g hf hg b) =
      lubinTateScalar pi hpi0 hpi hfield f h hf hh (a * b) := by
  apply FGLaw.Hom.ext
  exact lubin_intertwiner_mul
    pi hpi0 hpi hfield f g h hf hg hh a b

/-- Every unit gives Milne's pair of inverse Lubin--Tate isomorphisms. -/
noncomputable def lubinTateIso
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (u : Rˣ) :
    FGLaw.Iso
      (lubinFormalLaw pi hpi0 hpi hfield f hf)
      (lubinFormalLaw pi hpi0 hpi hfield g hg) where
  hom := lubinTateScalar pi hpi0 hpi hfield f g hf hg u
  inv := lubinTateScalar pi hpi0 hpi hfield g f hg hf ↑(u⁻¹)
  inv_hom_id := by
    rw [lubin_scalar_comp]
    simp only [Units.inv_mul]
    apply FGLaw.Hom.ext
    exact scalar_intertwiner_self pi hpi0 hpi hfield f hf
  hom_inv_id := by
    rw [lubin_scalar_comp]
    simp only [Units.mul_inv]
    apply FGLaw.Hom.ext
    exact scalar_intertwiner_self pi hpi0 hpi hfield g hg

/-- Corollary 2.16: any two Lubin--Tate formal group laws for the same
uniformizer are canonically isomorphic.  This is the unit construction for
`u = 1`. -/
noncomputable def canonicalLubinIso
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g) :
    FGLaw.Iso
      (lubinFormalLaw pi hpi0 hpi hfield f hf)
      (lubinFormalLaw pi hpi0 hpi hfield g hg) :=
  lubinTateIso pi hpi0 hpi hfield f g hf hg 1

@[simp]
theorem lubin_iso_series
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g) :
    (canonicalLubinIso pi hpi0 hpi hfield f g hf hg).hom.toSeries =
      tateScalarIntertwiner pi hpi0 hpi hfield f g hf hg 1 := rfl

/-- The uniqueness assertion following Corollary 2.16: a homomorphism with
linear term `T` which intertwines `f` and `g` is the canonical isomorphism. -/
theorem lubin_tate_iso
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (h : FGLaw.Hom
      (lubinFormalLaw pi hpi0 hpi hfield f hf)
      (lubinFormalLaw pi hpi0 hpi hfield g hg))
    (hh : LIntert g f (fun _ : Fin 1 ↦ 1) h.toSeries) :
    h = (canonicalLubinIso pi hpi0 hpi hfield f g hf hg).hom := by
  apply FGLaw.Hom.ext
  exact tate_intertwiner pi hpi0 hpi hfield g f hg hf _ hh

end

end Towers.CField.FGroups
