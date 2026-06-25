import Towers.ClassField.LubinTate.AdicModule
import Towers.ClassField.LubinTate.TorsionKernel
import Towers.ClassField.LubinTate.TorsionSeries

/-!
# Class Field Theory, Chapter I, Remark 3.1: adic torsion

On the adic Lubin--Tate module, multiplication by the uniformizer is
evaluation of the chosen series `f`.  Iterating identifies multiplication by
`pi ^ n` with evaluation of the compositional iterate `f^(n)`.  Consequently,
the abstract torsion kernel from Lemma 3.3 is exactly the zero locus of that
iterate among the adic points.
-/

namespace Towers.CField.LTate

open Towers.CField.FGroups

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [T2Space R] [CompleteSpace R]

omit [IsDomain R] [IsLocalRing R] in
private theorem powerSeries_eval₂_subst_adic
    {I : Ideal R} (hI : IsAdic I)
    (f g : PowerSeries R)
    (hg0 : PowerSeries.constantCoeff g = 0) (x : I) :
    PowerSeries.eval₂ (RingHom.id R) (x : R) (PowerSeries.subst g f) =
      PowerSeries.eval₂ (RingHom.id R)
        (PowerSeries.eval₂ (RingHom.id R) (x : R) g) f := by
  have h := mv_series_eval₂_subst_of_forall_constantCoeff_zero_adic
    (sigma := Unit) (tau := Unit) hI (fun _ => g)
    (fun _ => hg0) (fun _ => (x : R)) (fun _ => x.2) f
  simpa only [PowerSeries.eval₂, PowerSeries.subst] using h

/-- Multiplication by the uniformizer on the adic Lubin--Tate module is
evaluation of the chosen Lubin--Tate series. -/
theorem adic_points_uniformizer
    {I : Ideal R} (hI : IsAdic I)
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (x : LubinAdicPoints hI pi hpi0 hpi hfield f hf) :
    (FGLaw.APts.toIdeal hI
        (lubinFormalLaw pi hpi0 hpi hfield f hf) (pi • x) : R) =
      PowerSeries.eval₂ (RingHom.id R)
        (FGLaw.APts.toIdeal hI
          (lubinFormalLaw pi hpi0 hpi hfield f hf) x : R) f := by
  rw [lubin_adic_points]
  change MvPowerSeries.eval₂ (RingHom.id R) _
      (tateScalarIntertwiner pi hpi0 hpi hfield f f hf hf pi) = _
  rw [lubin_intertwiner_uniformizer]
  change MvPowerSeries.eval₂ (RingHom.id R)
      (fun _ : Fin 1 ↦
        (FGLaw.APts.toIdeal hI
          (lubinFormalLaw pi hpi0 hpi hfield f hf) x : R))
      (PowerSeries.subst FGLaw.unaryX f) =
    MvPowerSeries.eval₂ (RingHom.id R)
      (fun _ : Unit ↦
        (FGLaw.APts.toIdeal hI
          (lubinFormalLaw pi hpi0 hpi hfield f hf) x : R)) f
  have heval := mv_series_eval₂_subst_of_forall_constantCoeff_zero_adic
    hI (fun _ : Unit ↦ FGLaw.unaryX)
    (fun _ ↦ by simp [FGLaw.unaryX])
    (fun _ : Fin 1 ↦
      (FGLaw.APts.toIdeal hI
        (lubinFormalLaw pi hpi0 hpi hfield f hf) x : R))
    (fun _ ↦ (FGLaw.APts.toIdeal hI
      (lubinFormalLaw pi hpi0 hpi hfield f hf) x).2) f
  simpa [PowerSeries.subst, FGLaw.unaryX] using heval

/-- Remark 3.1's identity `[pi ^ n]_f(alpha) = f^(n)(alpha)`, evaluated on
the adic Lubin--Tate module. -/
theorem lubin_points_uniformizer
    {I : Ideal R} (hI : IsAdic I)
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (n : Nat)
    (x : LubinAdicPoints hI pi hpi0 hpi hfield f hf) :
    (FGLaw.APts.toIdeal hI
        (lubinFormalLaw pi hpi0 hpi hfield f hf) (pi ^ n • x) : R) =
      PowerSeries.eval₂ (RingHom.id R)
        (FGLaw.APts.toIdeal hI
          (lubinFormalLaw pi hpi0 hpi hfield f hf) x : R)
        (substitutionIterate f n) := by
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf.1
  induction n with
  | zero =>
      rw [pow_zero]
      change (FGLaw.APts.toIdeal hI
        (lubinFormalLaw pi hpi0 hpi hfield f hf)
          ((1 : R) • x) : R) = _
      rw [show (1 : R) • x = x from one_smul R x,
        substitutionIterate_zero, PowerSeries.eval₂_X]
  | succ n ih =>
      rw [pow_succ']
      rw [show (pi * pi ^ n) • x = pi • (pi ^ n • x) from
        mul_smul pi (pi ^ n) x]
      rw [
        adic_points_uniformizer hI pi hpi0 hpi hfield f hf,
        substitutionIterate_succ,
        powerSeries_eval₂_subst_adic hI f (substitutionIterate f n)
          (substitution_iterate_coeff hf0 n)]
      rw [ih]

/-- The level-`n` adic Lubin--Tate torsion module. -/
abbrev lubinAdicTorsion
    {I : Ideal R} (hI : IsAdic I)
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (n : Nat) :=
  torsionKernel
    (M := LubinAdicPoints hI pi hpi0 hpi hfield f hf) pi n

/-- An adic point belongs to the level-`n` torsion module exactly when it is
a zero of the `n`-fold compositional iterate of `f`. -/
theorem lubin_substitution_iterate
    {I : Ideal R} (hI : IsAdic I)
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (n : Nat)
    (x : LubinAdicPoints hI pi hpi0 hpi hfield f hf) :
    x ∈ lubinAdicTorsion hI pi hpi0 hpi hfield f hf n ↔
      PowerSeries.eval₂ (RingHom.id R)
        (FGLaw.APts.toIdeal hI
          (lubinFormalLaw pi hpi0 hpi hfield f hf) x : R)
        (substitutionIterate f n) = 0 := by
  rw [mem_torsionKernel]
  constructor
  · intro hx
    rw [← lubin_points_uniformizer
      hI pi hpi0 hpi hfield f hf n x]
    simpa using congrArg
      (fun y : LubinAdicPoints hI pi hpi0 hpi hfield f hf ↦
        (FGLaw.APts.toIdeal hI
          (lubinFormalLaw pi hpi0 hpi hfield f hf) y : R)) hx
  · intro hx
    apply FGLaw.APts.ext hI
      (lubinFormalLaw pi hpi0 hpi hfield f hf)
    apply Subtype.ext
    calc
      (FGLaw.APts.toIdeal hI
          (lubinFormalLaw pi hpi0 hpi hfield f hf)
          (pi ^ n • x) : R) =
          PowerSeries.eval₂ (RingHom.id R)
            (FGLaw.APts.toIdeal hI
              (lubinFormalLaw pi hpi0 hpi hfield f hf) x : R)
            (substitutionIterate f n) :=
        lubin_points_uniformizer
          hI pi hpi0 hpi hfield f hf n x
      _ = 0 := hx
      _ = (FGLaw.APts.toIdeal hI
          (lubinFormalLaw pi hpi0 hpi hfield f hf) 0 : R) := rfl

/-- The canonical equivalence between the adic modules attached to two
Lubin--Tate series carries level-`n` torsion onto level-`n` torsion. -/
theorem canonical_lubin_torsion
    {I : Ideal R} (hI : IsAdic I)
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (n : Nat) :
    (lubinAdicTorsion hI pi hpi0 hpi hfield f hf n).map
        (canonicalLubinTate
          hI pi hpi0 hpi hfield f g hf hg).toLinearMap =
      lubinAdicTorsion hI pi hpi0 hpi hfield g hg n := by
  let e := canonicalLubinTate
    hI pi hpi0 hpi hfield f g hf hg
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply mem_torsionKernel.mpr
    change pi ^ n • e x = 0
    calc
      pi ^ n • e x = e (pi ^ n • x) := (e.map_smul (pi ^ n) x).symm
      _ = e 0 := congrArg e (mem_torsionKernel.mp hx)
      _ = 0 := e.map_zero
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply mem_torsionKernel.mpr
    calc
      pi ^ n • e.symm y = e.symm (pi ^ n • y) :=
        (e.symm.map_smul (pi ^ n) y).symm
      _ = e.symm 0 := congrArg e.symm (mem_torsionKernel.mp hy)
      _ = 0 := e.symm.map_zero

/-- The canonical equivalence between two choices of Lubin--Tate series,
restricted to their level-`n` torsion modules. -/
noncomputable def canonicalLubinTorsion
    {I : Ideal R} (hI : IsAdic I)
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (n : Nat) :
    lubinAdicTorsion hI pi hpi0 hpi hfield f hf n ≃ₗ[R]
      lubinAdicTorsion hI pi hpi0 hpi hfield g hg n :=
  let e := canonicalLubinTate
    hI pi hpi0 hpi hfield f g hf hg
  (e.submoduleMap
      (lubinAdicTorsion hI pi hpi0 hpi hfield f hf n)).trans
    (LinearEquiv.ofEq _ _
      (canonical_lubin_torsion
        hI pi hpi0 hpi hfield f g hf hg n))

end

end Towers.CField.LTate
