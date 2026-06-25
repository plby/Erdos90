import Submission.ClassField.FormalGroups.LawBaseChange
import Submission.ClassField.FormalGroups.AdicHomRing
import Submission.ClassField.FormalGroups.LubinEndomorphismRing
import Submission.ClassField.FormalGroups.LubinTateRemarks
import Submission.ClassField.LubinTate.TorsionKernel
import Submission.ClassField.LubinTate.AevalAlgEquiv
import Submission.ClassField.LubinTate.TorsionSeries

/-!
# Relative adic Lubin--Tate modules

Milne evaluates a Lubin--Tate formal group over the valuation ring `A` at
points in the maximal ideal of a finite extension.  The coefficient ring and
the evaluation ring are therefore different.  This file supplies that
relative construction: the formal group law and each scalar endomorphism are
base-changed along `rho : A →+* B`, then evaluated on an adic ideal of the
complete ring `B`.
-/

namespace Submission.CField.LTate

noncomputable section

open Submission.CField.FGroups

variable {A B : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [T2Space B] [CompleteSpace B]

omit [IsDomain A] [IsLocalRing A] in
private theorem powerSeries_eval₂_subst_adic
    {I : Ideal B} (hI : IsAdic I)
    (f g : PowerSeries B)
    (hg0 : PowerSeries.constantCoeff g = 0) (x : I) :
    PowerSeries.eval₂ (RingHom.id B) (x : B) (PowerSeries.subst g f) =
      PowerSeries.eval₂ (RingHom.id B)
        (PowerSeries.eval₂ (RingHom.id B) (x : B) g) f := by
  have h := mv_series_eval₂_subst_of_forall_constantCoeff_zero_adic
    (sigma := Unit) (tau := Unit) hI (fun _ ↦ g)
    (fun _ ↦ hg0) (fun _ ↦ (x : B)) (fun _ ↦ x.2) f
  simpa only [PowerSeries.eval₂, PowerSeries.subst] using h

/-- The points of a Lubin--Tate formal group over `A`, evaluated in an adic
ideal of a complete `A`-algebra `B`. -/
abbrev RelativeLubinPoints
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (pi : A) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (A ⧸ Ideal.span {pi}))
    [Fintype (A ⧸ Ideal.span {pi})]
    (f : PowerSeries A)
    (hf : LubinSeries pi
      (Fintype.card (A ⧸ Ideal.span {pi})) f) :=
  FGLaw.APts hI
    ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho)

/-- Evaluation of the base-changed Lubin--Tate endomorphism ring on relative
adic points. -/
noncomputable def relativeLubinEnd
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (pi : A) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (A ⧸ Ideal.span {pi}))
    [Fintype (A ⧸ Ideal.span {pi})]
    (f : PowerSeries A)
    (hf : LubinSeries pi
      (Fintype.card (A ⧸ Ideal.span {pi})) f) :
    A →+* AddMonoid.End
      (RelativeLubinPoints hI rho pi hpi0 hpi hfield f hf) :=
  let F := lubinFormalLaw pi hpi0 hpi hfield f hf
  ((FGLaw.Hom.adicEndHom hI (F.map rho)).comp
    (FGLaw.Hom.endRingMap rho F)).comp
      (lubinTateEndomorphism pi hpi0 hpi hfield f hf)

@[simp]
theorem relative_lubin_end
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (pi : A) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (A ⧸ Ideal.span {pi}))
    [Fintype (A ⧸ Ideal.span {pi})]
    (f : PowerSeries A)
    (hf : LubinSeries pi
      (Fintype.card (A ⧸ Ideal.span {pi})) f)
    (a : A) :
    relativeLubinEnd hI rho pi hpi0 hpi hfield f hf a =
      ((lubinTateScalar pi hpi0 hpi hfield f f hf hf a).map rho).adicMap hI :=
  rfl

/-- The relative scalar action is obtained by evaluating the base-changed
formal endomorphism `[a]_f`. -/
noncomputable instance relativePointsS
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (pi : A) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (A ⧸ Ideal.span {pi}))
    [Fintype (A ⧸ Ideal.span {pi})]
    (f : PowerSeries A)
    (hf : LubinSeries pi
      (Fintype.card (A ⧸ Ideal.span {pi})) f) :
    SMul A (RelativeLubinPoints
      hI rho pi hpi0 hpi hfield f hf) :=
  SMul.comp _
    (relativeLubinEnd
      hI rho pi hpi0 hpi hfield f hf)

/-- The natural `A`-module structure on relative adic Lubin--Tate points. -/
noncomputable instance relativePointsModule
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (pi : A) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (A ⧸ Ideal.span {pi}))
    [Fintype (A ⧸ Ideal.span {pi})]
    (f : PowerSeries A)
    (hf : LubinSeries pi
      (Fintype.card (A ⧸ Ideal.span {pi})) f) :
    Module A (RelativeLubinPoints
      hI rho pi hpi0 hpi hfield f hf) :=
  Module.compHom _
    (relativeLubinEnd
      hI rho pi hpi0 hpi hfield f hf)

/-- On underlying ideal elements, relative scalar multiplication is the
adic evaluation of the base-changed formal endomorphism. -/
@[simp]
theorem relative_lubin_points
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (pi : A) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (A ⧸ Ideal.span {pi}))
    [Fintype (A ⧸ Ideal.span {pi})]
    (f : PowerSeries A)
    (hf : LubinSeries pi
      (Fintype.card (A ⧸ Ideal.span {pi})) f)
    (a : A)
    (x : RelativeLubinPoints
      hI rho pi hpi0 hpi hfield f hf) :
    FGLaw.APts.toIdeal hI
        ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho)
        (a • x) =
      ((lubinTateScalar pi hpi0 hpi hfield f f hf hf a).map rho).adicValue
        hI (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho) x) :=
  rfl

/-- Multiplication by the source uniformizer is evaluation of the
base-changed Lubin--Tate series. -/
theorem relative_points_uniformizer
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (pi : A) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (A ⧸ Ideal.span {pi}))
    [Fintype (A ⧸ Ideal.span {pi})]
    (f : PowerSeries A)
    (hf : LubinSeries pi
      (Fintype.card (A ⧸ Ideal.span {pi})) f)
    (x : RelativeLubinPoints
      hI rho pi hpi0 hpi hfield f hf) :
    (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho)
        (pi • x) : B) =
      PowerSeries.eval₂ (RingHom.id B)
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho) x : B)
        (PowerSeries.map rho f) := by
  rw [relative_lubin_points]
  change MvPowerSeries.eval₂ (RingHom.id B) _
      (MvPowerSeries.map rho
        (tateScalarIntertwiner pi hpi0 hpi hfield f f hf hf pi)) = _
  rw [lubin_intertwiner_uniformizer]
  have hmap : MvPowerSeries.map rho (powerSeriesUnary f) =
      powerSeriesUnary (PowerSeries.map rho f) := by
    rw [powerSeriesUnary, powerSeriesUnary, PowerSeries.map_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero (by
        simp [FGLaw.unaryX]))]
    simp only [FGLaw.unaryX, MvPowerSeries.map_X]
  rw [hmap, powerSeriesUnary]
  change MvPowerSeries.eval₂ (RingHom.id B)
      (fun _ : Fin 1 ↦
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho) x : B))
      (PowerSeries.subst FGLaw.unaryX
        (PowerSeries.map rho f)) = _
  have heval := mv_series_eval₂_subst_of_forall_constantCoeff_zero_adic
    hI (fun _ : Unit ↦ FGLaw.unaryX)
    (fun _ ↦ by simp [FGLaw.unaryX])
    (fun _ : Fin 1 ↦
      (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho) x : B))
    (fun _ ↦ (FGLaw.APts.toIdeal hI
      ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho) x).2)
    (PowerSeries.map rho f)
  simpa [PowerSeries.subst, FGLaw.unaryX] using heval

/-- Relative form of Milne's identity
`[pi ^ n]_f(alpha) = f^(n)(alpha)`. -/
theorem points_uniformizer_smul
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (pi : A) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (A ⧸ Ideal.span {pi}))
    [Fintype (A ⧸ Ideal.span {pi})]
    (f : PowerSeries A)
    (hf : LubinSeries pi
      (Fintype.card (A ⧸ Ideal.span {pi})) f)
    (n : ℕ)
    (x : RelativeLubinPoints
      hI rho pi hpi0 hpi hfield f hf) :
    (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho)
        (pi ^ n • x) : B) =
      PowerSeries.eval₂ (RingHom.id B)
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho) x : B)
        (substitutionIterate (PowerSeries.map rho f) n) := by
  have hf0 : PowerSeries.constantCoeff (PowerSeries.map rho f) = 0 := by
    simp only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, hf.1, map_zero]
  induction n with
  | zero =>
      rw [pow_zero]
      change (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho)
          ((1 : A) • x) : B) = _
      rw [show (1 : A) • x = x from one_smul A x,
        substitutionIterate_zero, PowerSeries.eval₂_X]
  | succ n ih =>
      rw [pow_succ']
      rw [show (pi * pi ^ n) • x = pi • (pi ^ n • x) from
        mul_smul pi (pi ^ n) x]
      rw [relative_points_uniformizer
        hI rho pi hpi0 hpi hfield f hf,
        substitutionIterate_succ,
        powerSeries_eval₂_subst_adic hI (PowerSeries.map rho f)
          (substitutionIterate (PowerSeries.map rho f) n)
          (substitution_iterate_coeff hf0 n)]
      rw [ih]

/-- The level-`n` torsion submodule of the relative adic Lubin--Tate
module. -/
abbrev relativeLubinTorsion
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (pi : A) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (A ⧸ Ideal.span {pi}))
    [Fintype (A ⧸ Ideal.span {pi})]
    (f : PowerSeries A)
    (hf : LubinSeries pi
      (Fintype.card (A ⧸ Ideal.span {pi})) f)
    (n : ℕ) :=
  torsionKernel
    (M := RelativeLubinPoints
      hI rho pi hpi0 hpi hfield f hf) pi n

/-- A relative adic point belongs to level `n` torsion exactly when the
base-changed `n`-fold iterate vanishes at its underlying ideal element. -/
theorem relative_substitution_iterate
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (pi : A) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (A ⧸ Ideal.span {pi}))
    [Fintype (A ⧸ Ideal.span {pi})]
    (f : PowerSeries A)
    (hf : LubinSeries pi
      (Fintype.card (A ⧸ Ideal.span {pi})) f)
    (n : ℕ)
    (x : RelativeLubinPoints
      hI rho pi hpi0 hpi hfield f hf) :
    x ∈ relativeLubinTorsion
        hI rho pi hpi0 hpi hfield f hf n ↔
      PowerSeries.eval₂ (RingHom.id B)
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho) x : B)
        (substitutionIterate (PowerSeries.map rho f) n) = 0 := by
  rw [mem_torsionKernel]
  constructor
  · intro hx
    rw [← points_uniformizer_smul
      hI rho pi hpi0 hpi hfield f hf n x]
    simpa using congrArg
      (fun y : RelativeLubinPoints
          hI rho pi hpi0 hpi hfield f hf ↦
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho) y : B)) hx
  · intro hx
    apply FGLaw.APts.ext hI
      ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho)
    apply Subtype.ext
    calc
      (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho)
          (pi ^ n • x) : B) =
          PowerSeries.eval₂ (RingHom.id B)
            (FGLaw.APts.toIdeal hI
              ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho)
              x : B)
            (substitutionIterate (PowerSeries.map rho f) n) :=
        points_uniformizer_smul
          hI rho pi hpi0 hpi hfield f hf n x
      _ = 0 := hx
      _ = (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho)
          0 : B) := rfl

/-- A relative Lubin--Tate point of exact level `n + 1` has annihilator
`(pi ^ (n + 1))`.  This converts the two iterate evaluations used to define
primitive torsion into the exact ideal needed for the quotient-unit action
in Theorem I.3.6(b). -/
theorem torsion_exact_level
    [IsDiscreteValuationRing A]
    {I : Ideal B} (hI : IsAdic I) (rho : A →+* B)
    (pi : A) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hpiIrreducible : Irreducible pi)
    (hfield : IsField (A ⧸ Ideal.span {pi}))
    [Fintype (A ⧸ Ideal.span {pi})]
    (f : PowerSeries A)
    (hf : LubinSeries pi
      (Fintype.card (A ⧸ Ideal.span {pi})) f)
    (n : ℕ)
    (y : RelativeLubinPoints
      hI rho pi hpi0 hpi hfield f hf)
    (hlevel :
      PowerSeries.eval₂ (RingHom.id B)
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho) y : B)
        (substitutionIterate (PowerSeries.map rho f) (n + 1)) = 0)
    (hprimitive :
      PowerSeries.eval₂ (RingHom.id B)
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho) y : B)
        (substitutionIterate (PowerSeries.map rho f) n) ≠ 0) :
    Ideal.torsionOf A
        (RelativeLubinPoints
          hI rho pi hpi0 hpi hfield f hf) y =
      Ideal.span {pi ^ (n + 1)} := by
  let M := RelativeLubinPoints
    hI rho pi hpi0 hpi hfield f hf
  let yLevel : torsionKernel (M := M) pi (n + 1) :=
    ⟨y, (relative_substitution_iterate
      hI rho pi hpi0 hpi hfield f hf (n + 1) y).2 hlevel⟩
  let xLevel : torsionKernel (M := M) pi 1 := ⟨pi ^ n • y, by
    apply mem_torsionKernel.mpr
    have hy := mem_torsionKernel.mp yLevel.2
    change pi ^ 1 • (pi ^ n • y) = 0
    calc
      pi ^ 1 • (pi ^ n • y) = (pi ^ 1 * pi ^ n) • y :=
        (mul_smul _ _ _).symm
      _ = pi ^ (n + 1) • y := by rw [pow_one, pow_succ']
      _ = 0 := by simpa [yLevel] using hy⟩
  have hxLevel : (xLevel : M) ≠ 0 := by
    intro hx
    apply hprimitive
    rw [← points_uniformizer_smul
      hI rho pi hpi0 hpi hfield f hf n y]
    simpa [xLevel] using congrArg
      (fun z : M ↦
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho) z : B)) hx
  exact torsion_kernel_generator
    hpiIrreducible xLevel hxLevel n yLevel rfl

/-- A continuous ring homomorphism between complete adic evaluation rings
commutes with the relative Lubin--Tate scalar action. -/
theorem lubin_points_smul
    {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
    [IsTopologicalRing C] [T2Space C] [CompleteSpace C]
    {I : Ideal B} (hI : IsAdic I) {J : Ideal C} (hJ : IsAdic J)
    (rho : A →+* B) (phi : B →+* C) (hphi : Continuous phi)
    (hIJ : ∀ x : B, x ∈ I → phi x ∈ J)
    (pi : A) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (A ⧸ Ideal.span {pi}))
    [Fintype (A ⧸ Ideal.span {pi})]
    (f : PowerSeries A)
    (hf : LubinSeries pi
      (Fintype.card (A ⧸ Ideal.span {pi})) f)
    (a : A)
    (x : RelativeLubinPoints hI rho
      pi hpi0 hpi hfield f hf) :
    phi (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho)
        (a • x) : B) =
      (FGLaw.APts.toIdeal hJ
        ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
          (phi.comp rho))
        (a • FGLaw.APts.ofIdeal hJ
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
            (phi.comp rho))
          ⟨phi (FGLaw.APts.toIdeal hI
            ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho)
            x : B),
            hIJ _ (FGLaw.APts.toIdeal hI
              ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho)
              x).2⟩) : C) := by
  rw [relative_lubin_points,
    relative_lubin_points]
  change phi (MvPowerSeries.eval₂ (RingHom.id B)
      (fun _ : Fin 1 ↦
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho)
          x : B))
      (((lubinTateScalar pi hpi0 hpi hfield f f hf hf a).map rho).toSeries)) = _
  rw [FGLaw.Hom.map_toSeries]
  change phi (MvPowerSeries.eval₂ (RingHom.id B)
      (fun _ : Fin 1 ↦
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho)
          x : B))
      (MvPowerSeries.map rho
        (lubinTateScalar pi hpi0 hpi hfield f f hf hf a).toSeries)) =
    MvPowerSeries.eval₂ (RingHom.id C)
      (fun _ : Fin 1 ↦ phi
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho)
          x : B))
      (MvPowerSeries.map (phi.comp rho)
        (lubinTateScalar pi hpi0 hpi hfield f f hf hf a).toSeries)
  exact eval₂_map_ringHom_of_forall_mem_adic hI hJ rho phi hphi hIJ
    (fun _ : Fin 1 ↦
      (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho)
        x : B))
    (fun _ ↦ (FGLaw.APts.toIdeal hI
      ((lubinFormalLaw pi hpi0 hpi hfield f hf).map rho)
      x).2)
    (lubinTateScalar pi hpi0 hpi hfield f f hf hf a).toSeries

/-- A continuous automorphism of the evaluation algebra that preserves the
adic ideal commutes with the relative Lubin--Tate scalar action. -/
theorem relative_points_smul
    [UniformSpace A] [IsTopologicalSemiring A] [IsUniformAddGroup A]
    [Algebra A B] [ContinuousSMul A B]
    {I : Ideal B} (hI : IsAdic I)
    (pi : A) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (A ⧸ Ideal.span {pi}))
    [Fintype (A ⧸ Ideal.span {pi})]
    (f : PowerSeries A)
    (hf : LubinSeries pi
      (Fintype.card (A ⧸ Ideal.span {pi})) f)
    (tau : B ≃ₐ[A] B) (htau : Continuous tau)
    (hI_tau : ∀ x : B, x ∈ I → tau x ∈ I)
    (a : A)
    (x : RelativeLubinPoints hI (algebraMap A B)
      pi hpi0 hpi hfield f hf) :
    tau (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
          (algebraMap A B)) (a • x) : B) =
      (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
          (algebraMap A B))
        (a • FGLaw.APts.ofIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
            (algebraMap A B))
          ⟨tau (FGLaw.APts.toIdeal hI
            ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
              (algebraMap A B)) x : B),
            hI_tau _ (FGLaw.APts.toIdeal hI
              ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
                (algebraMap A B)) x).2⟩) : B) := by
  rw [relative_lubin_points,
    relative_lubin_points]
  change tau (MvPowerSeries.eval₂ (RingHom.id B)
      (fun _ : Fin 1 ↦
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
            (algebraMap A B)) x : B))
      (((lubinTateScalar pi hpi0 hpi hfield f f hf hf a).map
        (algebraMap A B)).toSeries)) = _
  rw [FGLaw.Hom.map_toSeries]
  exact eval₂_map_algEquiv_of_forall_mem_adic hI tau htau hI_tau
    (fun _ : Fin 1 ↦
      (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
          (algebraMap A B)) x : B))
    (fun _ ↦ (FGLaw.APts.toIdeal hI
      ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
        (algebraMap A B)) x).2)
    (lubinTateScalar pi hpi0 hpi hfield f f hf hf a).toSeries

/-- Relative scalar multiplication is natural along a continuous
`A`-algebra homomorphism that maps one ideal of definition into another. -/
theorem adic_points_smul
    [UniformSpace A] [IsTopologicalSemiring A] [IsUniformAddGroup A]
    [Algebra A B] [ContinuousSMul A B]
    {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
    [IsTopologicalRing C] [T2Space C] [CompleteSpace C]
    [Algebra A C] [ContinuousSMul A C]
    {I : Ideal B} (hI : IsAdic I) {J : Ideal C} (hJ : IsAdic J)
    (pi : A) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (A ⧸ Ideal.span {pi}))
    [Fintype (A ⧸ Ideal.span {pi})]
    (f : PowerSeries A)
    (hf : LubinSeries pi
      (Fintype.card (A ⧸ Ideal.span {pi})) f)
    (tau : B →ₐ[A] C) (htau : Continuous tau)
    (hIJ : ∀ x : B, x ∈ I → tau x ∈ J)
    (a : A)
    (x : RelativeLubinPoints hI (algebraMap A B)
      pi hpi0 hpi hfield f hf) :
    tau (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
          (algebraMap A B)) (a • x) : B) =
      (FGLaw.APts.toIdeal hJ
        ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
          (algebraMap A C))
        (a • FGLaw.APts.ofIdeal hJ
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
            (algebraMap A C))
          ⟨tau (FGLaw.APts.toIdeal hI
            ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
              (algebraMap A B)) x : B),
            hIJ _ (FGLaw.APts.toIdeal hI
              ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
                (algebraMap A B)) x).2⟩) : C) := by
  rw [relative_lubin_points,
    relative_lubin_points]
  change tau (MvPowerSeries.eval₂ (RingHom.id B)
      (fun _ : Fin 1 ↦
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
            (algebraMap A B)) x : B))
      (((lubinTateScalar pi hpi0 hpi hfield f f hf hf a).map
        (algebraMap A B)).toSeries)) = _
  rw [FGLaw.Hom.map_toSeries]
  change tau (MvPowerSeries.eval₂ (RingHom.id B)
      (fun _ : Fin 1 ↦
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
            (algebraMap A B)) x : B))
      (MvPowerSeries.map (algebraMap A B)
        (lubinTateScalar pi hpi0 hpi hfield f f hf hf a).toSeries)) =
    MvPowerSeries.eval₂ (RingHom.id C)
      (fun _ : Fin 1 ↦ tau
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
            (algebraMap A B)) x : B))
      (MvPowerSeries.map (algebraMap A C)
        (lubinTateScalar pi hpi0 hpi hfield f f hf hf a).toSeries)
  exact eval₂_map_algHom_of_forall_mem_adic hI hJ tau htau hIJ
    (fun _ : Fin 1 ↦
      (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
          (algebraMap A B)) x : B))
    (fun _ ↦ (FGLaw.APts.toIdeal hI
      ((lubinFormalLaw pi hpi0 hpi hfield f hf).map
        (algebraMap A B)) x).2)
    (lubinTateScalar pi hpi0 hpi hfield f f hf hf a).toSeries

end

end Submission.CField.LTate
