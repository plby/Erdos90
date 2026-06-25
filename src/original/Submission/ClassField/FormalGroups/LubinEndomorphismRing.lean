import Submission.ClassField.FormalGroups.LubinTateIsomorphism

/-!
# Class Field Theory, Chapter I, Corollary 2.17

For a fixed Lubin--Tate series `f`, the canonical scalar intertwiners define
an injective ring homomorphism from the coefficient ring into the endomorphism
ring of the associated formal group law.
-/

namespace Submission.CField.FGroups

open MvPowerSeries

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]

/-- The coefficient-zero self-intertwiner is the zero series. -/
theorem lubin_intertwiner_self
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    tateScalarIntertwiner pi hpi0 hpi hfield f f hf hf 0 = 0 := by
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf.1
  exact (tate_intertwiner pi hpi0 hpi hfield f f hf hf
    (fun _ : Fin 1 ↦ 0) (lubin_intertwiner_zero hf0 hf0)).symm

/-- The coefficient-zero canonical endomorphism is the zero homomorphism. -/
theorem lubin_scalar_self
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    lubinTateScalar pi hpi0 hpi hfield f f hf hf 0 = 0 := by
  apply FGLaw.Hom.ext
  exact lubin_intertwiner_self pi hpi0 hpi hfield f hf

/-- The coefficient-one canonical endomorphism is the identity
homomorphism. -/
theorem lubin_tate_self
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    lubinTateScalar pi hpi0 hpi hfield f f hf hf 1 =
      FGLaw.Hom.id
        (lubinFormalLaw pi hpi0 hpi hfield f hf) := by
  apply FGLaw.Hom.ext
  exact scalar_intertwiner_self pi hpi0 hpi hfield f hf

/-- Corollary 2.17: `a ↦ [a]_f` is a ring homomorphism into the
endomorphism ring of the Lubin--Tate formal group law. -/
noncomputable def lubinTateEndomorphism
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    R →+* FGLaw.Hom
      (lubinFormalLaw pi hpi0 hpi hfield f hf)
      (lubinFormalLaw pi hpi0 hpi hfield f hf) where
  toFun a := lubinTateScalar pi hpi0 hpi hfield f f hf hf a
  map_zero' := lubin_scalar_self pi hpi0 hpi hfield f hf
  map_one' := lubin_tate_self pi hpi0 hpi hfield f hf
  map_add' a b := lubin_tate_scalar
    pi hpi0 hpi hfield f f hf hf a b
  map_mul' a b := by
    exact (lubin_scalar_comp
      pi hpi0 hpi hfield f f f hf hf hf a b).symm

@[simp]
theorem lubin_tate_endomorphism
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (a : R) :
    lubinTateEndomorphism pi hpi0 hpi hfield f hf a =
      lubinTateScalar pi hpi0 hpi hfield f f hf hf a := rfl

/-- The uniqueness clause in Corollary 2.17, stated using the exact
intertwiner predicate encoding the prescribed linear term and commutation
with `f`. -/
theorem endomorphism_lubin_tate
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (a : R)
    (h : FGLaw.Hom
      (lubinFormalLaw pi hpi0 hpi hfield f hf)
      (lubinFormalLaw pi hpi0 hpi hfield f hf))
    (hh : LIntert f f (fun _ : Fin 1 ↦ a) h.toSeries) :
    h = lubinTateEndomorphism pi hpi0 hpi hfield f hf a := by
  apply FGLaw.Hom.ext
  exact tate_intertwiner pi hpi0 hpi hfield f f hf hf _ hh

/-- Remark 2.19(b): the coefficient ring embeds into the endomorphism ring,
because the scalar is recovered from the degree-one coefficient. -/
theorem lubin_endomorphism_injective
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    Function.Injective
      (lubinTateEndomorphism pi hpi0 hpi hfield f hf) := by
  intro a b hab
  have hseries := congrArg FGLaw.Hom.toSeries hab
  have hdegree := congrArg (homogeneousComponent 1) hseries
  change homogeneousComponent 1
      (tateScalarIntertwiner pi hpi0 hpi hfield f f hf hf a) =
    homogeneousComponent 1
      (tateScalarIntertwiner pi hpi0 hpi hfield f f hf hf b) at hdegree
  have ha := (lubin_intertwiner_spec
    pi hpi0 hpi hfield f f hf hf a).homogeneousComponent_one
  have hb := (lubin_intertwiner_spec
    pi hpi0 hpi hfield f f hf hf b).homogeneousComponent_one
  change homogeneousComponent 1
      (tateScalarIntertwiner pi hpi0 hpi hfield f f hf hf a) =
    homogeneousComponent 1
      (tateScalarIntertwiner pi hpi0 hpi hfield f f hf hf b) at hdegree
  rw [ha, hb] at hdegree
  have hcoeff := congrArg (coeff (Finsupp.single (0 : Fin 1) 1)) hdegree
  simpa [mvLinearForm] using hcoeff

end

end Submission.CField.FGroups
