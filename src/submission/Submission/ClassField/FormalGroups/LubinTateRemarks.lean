import Submission.ClassField.FormalGroups.LubinEndomorphismRing
import Submission.ClassField.FormalGroups.PowerSeriesUnary


/-!
# Class Field Theory, Chapter I, Remark 2.19 and Summary 2.20

The scalar action sends the uniformizer to the chosen Lubin--Tate series,
is faithful, and is respected by the canonical isomorphisms. Together with
the preceding construction, these are the assertions collected in Milne's
Summary 2.20.
-/

namespace Submission.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]

omit [IsDomain R] [IsLocalRing R] in
/-- A Lubin--Tate series, viewed as a `Fin 1`-indexed series, is the exact
self-intertwiner with linear coefficient `pi`. -/
theorem unary_tate_intertwiner
    (pi : R) (f : PowerSeries R)
    (hf : LubinSeries pi q f) :
    LIntert f f (fun _ : Fin 1 ↦ pi)
      (powerSeriesUnary f) := by
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf.1
  exact unary_intertwiner_commutes
    f f pi hf0 hf0 hf.2.1 rfl

/-- Remark 2.19(a): the scalar endomorphism attached to the uniformizer is
the chosen Lubin--Tate series itself. -/
theorem lubin_intertwiner_uniformizer
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    tateScalarIntertwiner pi hpi0 hpi hfield f f hf hf pi =
      powerSeriesUnary f := by
  exact (tate_intertwiner pi hpi0 hpi hfield f f hf hf _
    (unary_tate_intertwiner pi f hf)).symm

/-- Remark 2.19(c): the canonical coefficient-one isomorphism commutes with
the scalar actions on the two Lubin--Tate formal group laws. -/
theorem lubin_iso_commutes
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (a : R) :
    FGLaw.Hom.comp
        (lubinTateEndomorphism pi hpi0 hpi hfield g hg a)
        (canonicalLubinIso pi hpi0 hpi hfield f g hf hg).hom =
      FGLaw.Hom.comp
        (canonicalLubinIso pi hpi0 hpi hfield f g hf hg).hom
        (lubinTateEndomorphism pi hpi0 hpi hfield f hf a) := by
  calc
    FGLaw.Hom.comp
        (lubinTateEndomorphism pi hpi0 hpi hfield g hg a)
        (canonicalLubinIso pi hpi0 hpi hfield f g hf hg).hom =
        lubinTateScalar pi hpi0 hpi hfield f g hf hg (a * 1) := by
          exact lubin_scalar_comp
            pi hpi0 hpi hfield f g g hf hg hg a 1
    _ = lubinTateScalar pi hpi0 hpi hfield f g hf hg (1 * a) := by simp
    _ = FGLaw.Hom.comp
        (canonicalLubinIso pi hpi0 hpi hfield f g hf hg).hom
        (lubinTateEndomorphism pi hpi0 hpi hfield f hf a) := by
          exact (lubin_scalar_comp
            pi hpi0 hpi hfield f f g hf hf hg 1 a).symm

end

end Submission.CField.FGroups
