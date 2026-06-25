import Mathlib.Algebra.Module.Hom
import Mathlib.Algebra.Module.RingHom
import Towers.ClassField.FormalGroups.AdicHomRing
import Towers.ClassField.FormalGroups.LubinEndomorphismRing
import Towers.ClassField.FormalGroups.LubinTateRemarks
import Towers.ClassField.LubinTate.AdicEvaluation

/-!
# Class Field Theory, Chapter I, Section 3: the adic Lubin--Tate module

The ring homomorphism `a ↦ [a]_f` acts on the adic formal group by
evaluation.  This gives the group of points in an ideal of definition its
natural module structure over the coefficient ring.  The canonical
isomorphisms between Lubin--Tate formal groups evaluate to linear
equivalences for these module structures.
-/

namespace Towers.CField.LTate

open Towers.CField.FGroups

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [T2Space R] [CompleteSpace R]

/-- The points of the Lubin--Tate formal group attached to `f` in an ideal
of definition.  This is the complete-adic analogue of Milne's
`\mathfrak m_L` and of the finite-layer pieces of `\Lambda_f`. -/
abbrev LubinAdicPoints
    {I : Ideal R} (hI : IsAdic I)
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :=
  FGLaw.APts hI
    (lubinFormalLaw pi hpi0 hpi hfield f hf)

/-- Evaluation of the Lubin--Tate endomorphism ring on adic points. -/
noncomputable def lubinAdicEnd
    {I : Ideal R} (hI : IsAdic I)
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    R →+* AddMonoid.End
      (LubinAdicPoints hI pi hpi0 hpi hfield f hf) :=
  (FGLaw.Hom.adicEndHom hI
      (lubinFormalLaw pi hpi0 hpi hfield f hf)).comp
    (lubinTateEndomorphism pi hpi0 hpi hfield f hf)

@[simp]
theorem lubin_adic_end
    {I : Ideal R} (hI : IsAdic I)
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (a : R) :
    lubinAdicEnd hI pi hpi0 hpi hfield f hf a =
      (lubinTateScalar pi hpi0 hpi hfield f f hf hf a).adicMap hI :=
  rfl

/-- The scalar action on adic Lubin--Tate points is evaluation of `[a]_f`. -/
noncomputable instance lubinPointsS
    {I : Ideal R} (hI : IsAdic I)
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    SMul R (LubinAdicPoints hI pi hpi0 hpi hfield f hf) :=
  SMul.comp _ (lubinAdicEnd hI pi hpi0 hpi hfield f hf)

/-- The natural coefficient-ring module structure on the evaluated
Lubin--Tate formal group. -/
noncomputable instance lubinPointsModule
    {I : Ideal R} (hI : IsAdic I)
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    Module R (LubinAdicPoints hI pi hpi0 hpi hfield f hf) :=
  Module.compHom _ (lubinAdicEnd hI pi hpi0 hpi hfield f hf)

/-- On underlying ideal elements, the module action is the convergent value
`[a]_f(alpha)`. -/
@[simp]
theorem lubin_adic_points
    {I : Ideal R} (hI : IsAdic I)
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (a : R)
    (x : LubinAdicPoints hI pi hpi0 hpi hfield f hf) :
    FGLaw.APts.toIdeal hI
        (lubinFormalLaw pi hpi0 hpi hfield f hf) (a • x) =
      lubinScalarValue hI pi hpi0 hpi hfield f hf a
        (FGLaw.APts.toIdeal hI
          (lubinFormalLaw pi hpi0 hpi hfield f hf) x) :=
  rfl

/-- The canonical isomorphism between two Lubin--Tate formal groups induces
an isomorphism of their modules of adic points. -/
noncomputable def canonicalLubinTate
    {I : Ideal R} (hI : IsAdic I)
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g) :
    LubinAdicPoints hI pi hpi0 hpi hfield f hf ≃ₗ[R]
      LubinAdicPoints hI pi hpi0 hpi hfield g hg where
  __ := (canonicalLubinIso pi hpi0 hpi hfield f g hf hg).adicEquiv hI
  map_smul' a x := by
    change
      (canonicalLubinIso pi hpi0 hpi hfield f g hf hg).hom.adicMap hI
          ((lubinTateEndomorphism
            pi hpi0 hpi hfield f hf a).adicMap hI x) =
        (lubinTateEndomorphism
          pi hpi0 hpi hfield g hg a).adicMap hI
          ((canonicalLubinIso
            pi hpi0 hpi hfield f g hf hg).hom.adicMap hI x)
    have hmaps :
        ((lubinTateEndomorphism
            pi hpi0 hpi hfield g hg a).adicMap hI).comp
          ((canonicalLubinIso
            pi hpi0 hpi hfield f g hf hg).hom.adicMap hI) =
        ((canonicalLubinIso
            pi hpi0 hpi hfield f g hf hg).hom.adicMap hI).comp
          ((lubinTateEndomorphism
            pi hpi0 hpi hfield f hf a).adicMap hI) := by
      rw [← FGLaw.Hom.adicMap_comp,
        ← FGLaw.Hom.adicMap_comp]
      exact congrArg
        (fun k : FGLaw.Hom
            (lubinFormalLaw pi hpi0 hpi hfield f hf)
            (lubinFormalLaw pi hpi0 hpi hfield g hg) ↦
          k.adicMap hI)
        (lubin_iso_commutes
          pi hpi0 hpi hfield f g hf hg a)
    exact DFunLike.congr_fun hmaps.symm x

@[simp]
theorem canonical_lubin_tate
    {I : Ideal R} (hI : IsAdic I)
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (x : LubinAdicPoints hI pi hpi0 hpi hfield f hf) :
    canonicalLubinTate
        hI pi hpi0 hpi hfield f g hf hg x =
      (canonicalLubinIso
        pi hpi0 hpi hfield f g hf hg).hom.adicMap hI x :=
  rfl

end

end Towers.CField.LTate
