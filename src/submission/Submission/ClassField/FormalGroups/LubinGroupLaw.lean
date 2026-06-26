import Submission.ClassField.FormalGroups.UniqueTateIntertwiner
import Submission.ClassField.FormalGroups.LubinIntertwinerOperations
import Submission.ClassField.FormalGroups.GroupLawConstructor
import Submission.ClassField.FormalGroups.Homomorphisms


/-!
# Class Field Theory, Chapter I, Proposition 2.12: the Lubin--Tate law

Lemma 2.11 canonically supplies the binary series with linear part `X + Y`
that commutes with a chosen Lubin--Tate series.  The uniqueness clause of that
lemma then proves the identity, commutativity, and associativity equations.

The construction of the inverse series, and hence the packaging into the
local `FGLaw` structure, is separated from these core series-level
arguments.
-/

namespace Submission.CField.FGroups

open MvPowerSeries
open scoped BigOperators

noncomputable section

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]

/-- The canonical intertwiner supplied by Lemma 2.11. -/
noncomputable def lubinTateIntertwiner
    {sigma : Type*} [Fintype sigma]
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (a : sigma -> R) : MvPowerSeries sigma R :=
  Classical.choose
    (unique_lubin_intertwiner hpi0 hpi hfield hf hg a)

/-- The canonical intertwiner has its defining constant, linear, and
intertwining properties. -/
theorem tate_intertwiner_spec
    {sigma : Type*} [Fintype sigma]
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (a : sigma -> R) :
    LIntert f g a
      (lubinTateIntertwiner pi hpi0 hpi hfield f g hf hg a) :=
  (Classical.choose_spec
    (unique_lubin_intertwiner hpi0 hpi hfield hf hg a)).1

/-- Any exact intertwiner with the same linear part is the canonical one. -/
theorem tate_intertwiner
    {sigma : Type*} [Fintype sigma]
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f g : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (hg : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) g)
    (a : sigma -> R) {phi : MvPowerSeries sigma R}
    (hphi : LIntert f g a phi) :
    phi = lubinTateIntertwiner pi hpi0 hpi hfield f g hf hg a :=
  (Classical.choose_spec
    (unique_lubin_intertwiner hpi0 hpi hfield hf hg a)).2 phi hphi

/-- The binary series of Proposition 2.12, characterized by linear part
`X + Y` and by commuting with `f`. -/
noncomputable def lubinTateLaw
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) : BinarySeries R :=
  lubinTateIntertwiner pi hpi0 hpi hfield f f hf hf (fun _ => 1)

/-- The binary Lubin--Tate series satisfies the Lemma 2.11 predicate. -/
theorem lubin_tate_spec
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    LIntert f f (fun _ : Fin 2 => 1)
      (lubinTateLaw pi hpi0 hpi hfield f hf) :=
  tate_intertwiner_spec pi hpi0 hpi hfield f f hf hf _

/-- Uniqueness of the binary series in Proposition 2.12. -/
theorem lubin_law
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    {F : BinarySeries R}
    (hF : LIntert f f (fun _ : Fin 2 => 1) F) :
    F = lubinTateLaw pi hpi0 hpi hfield f hf :=
  tate_intertwiner pi hpi0 hpi hfield f f hf hf _ hF

/-- The law has zero constant coefficient. -/
theorem lubin_law_coeff
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    constantCoeff (lubinTateLaw pi hpi0 hpi hfield f hf) = 0 :=
  (lubin_tate_spec pi hpi0 hpi hfield f hf).constant_coeff_zero

/-- The degree-one part of the law is `X + Y`. -/
theorem law_homogeneous_component
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    homogeneousComponent 1 (lubinTateLaw pi hpi0 hpi hfield f hf) =
      mvLinearForm (fun _ : Fin 2 => 1) :=
  (lubin_tate_spec pi hpi0 hpi hfield f hf).homogeneousComponent_one

/-- The defining endomorphism equation of Proposition 2.12. -/
theorem lubin_law_endomorphism
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    PowerSeries.subst (lubinTateLaw pi hpi0 hpi hfield f hf) f =
      MvPowerSeries.subst (coordinatewiseSubst f)
        (lubinTateLaw pi hpi0 hpi hfield f hf) :=
  lubin_tate_intertwining.mp
    (lubin_tate_spec pi hpi0 hpi hfield f hf).error_eq_zero

private theorem tate_law_spec
    {sigma : Type*} [Fintype sigma]
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    (a : sigma -> R) {phi psi : MvPowerSeries sigma R}
    (hphi : LIntert f f a phi)
    (hpsi : LIntert f f a psi) : phi = psi := by
  rw [tate_intertwiner pi hpi0 hpi hfield f f hf hf a hphi,
    tate_intertwiner pi hpi0 hpi hfield f f hf hf a hpsi]

omit [IsDomain R] [IsLocalRing R] in
private theorem unaryX_intertwiner
    (f : PowerSeries R) (hf0 : PowerSeries.constantCoeff f = 0) :
    LIntert f f (fun _ : Fin 1 => 1)
      (FGLaw.unaryX : UnarySeries R) := by
  simpa [FGLaw.unaryX] using
    (lubin_intertwiner_x (sigma := Fin 1) hf0 (0 : Fin 1))

omit [IsDomain R] [IsLocalRing R] in
private theorem zero_intertwiner
    {sigma : Type*} [Fintype sigma]
    (f : PowerSeries R) (hf0 : PowerSeries.constantCoeff f = 0) :
    LIntert f f (fun _ : sigma => 0)
      (0 : MvPowerSeries sigma R) :=
  lubin_intertwiner_zero hf0 hf0

omit [IsDomain R] [IsLocalRing R] in
private theorem coordinate_intertwiner
    {sigma : Type*} [Fintype sigma] [DecidableEq sigma]
    (f : PowerSeries R) (hf0 : PowerSeries.constantCoeff f = 0)
    (i : sigma) :
    LIntert f f (fun j => if j = i then 1 else 0)
      (X i : MvPowerSeries sigma R) :=
  lubin_intertwiner_x hf0 i

/-- Substituting two exact self-intertwiners into the Lubin--Tate law adds
their linear coefficient vectors. -/
private theorem lubin_law_substitute
    {sigma : Type*} [Fintype sigma]
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f)
    {a b : sigma -> R} {x y : MvPowerSeries sigma R}
    (hx : LIntert f f a x)
    (hy : LIntert f f b y) :
    LIntert f f (fun j => a j + b j)
      (FGLaw.substitute
        (lubinTateLaw pi hpi0 hpi hfield f hf) x y) := by
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf.1
  let c : Fin 2 -> sigma -> R := Fin.cases a (fun _ => b)
  let z : Fin 2 -> MvPowerSeries sigma R := Fin.cases x (fun _ => y)
  have hz : forall i, LIntert f f (c i) (z i) := by
    intro i
    exact Fin.cases hx (fun _ => hy) i
  have h := (lubin_tate_spec pi hpi0 hpi hfield f hf).subst hf0 hf0 hz
  simpa [FGLaw.substitute, c, z] using h

/-- The canonical binary series has zero as a left identity. -/
theorem lubin_law_left
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    FGLaw.substitute (lubinTateLaw pi hpi0 hpi hfield f hf)
      0 FGLaw.unaryX = FGLaw.unaryX := by
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf.1
  apply tate_law_spec pi hpi0 hpi hfield f hf (fun _ => 1)
  · simpa using lubin_law_substitute pi hpi0 hpi hfield f hf
      (zero_intertwiner (sigma := Fin 1) f hf0)
      (unaryX_intertwiner f hf0)
  · exact unaryX_intertwiner f hf0

/-- The canonical binary series has zero as a right identity. -/
theorem lubin_tate_law
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    FGLaw.substitute (lubinTateLaw pi hpi0 hpi hfield f hf)
      FGLaw.unaryX 0 = FGLaw.unaryX := by
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf.1
  apply tate_law_spec pi hpi0 hpi hfield f hf (fun _ => 1)
  · simpa using lubin_law_substitute pi hpi0 hpi hfield f hf
      (unaryX_intertwiner f hf0)
      (zero_intertwiner (sigma := Fin 1) f hf0)
  · exact unaryX_intertwiner f hf0

/-- The canonical binary series is commutative. -/
theorem lubin_law_comm
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    FGLaw.substitute (lubinTateLaw pi hpi0 hpi hfield f hf)
        FGLaw.binaryX FGLaw.binaryY =
      FGLaw.substitute (lubinTateLaw pi hpi0 hpi hfield f hf)
        FGLaw.binaryY FGLaw.binaryX := by
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf.1
  apply tate_law_spec pi hpi0 hpi hfield f hf (fun _ => 1)
  · have h := lubin_law_substitute pi hpi0 hpi hfield f hf
        (coordinate_intertwiner f hf0 (0 : Fin 2))
        (coordinate_intertwiner f hf0 (1 : Fin 2))
    simp only [] at h
    have hcoeff :
        (fun j : Fin 2 => (if j = 0 then 1 else 0) +
          if j = 1 then 1 else 0) = (fun _ => (1 : R)) := by
      funext j
      fin_cases j <;> simp
    rw [hcoeff] at h
    exact h
  · have h := lubin_law_substitute pi hpi0 hpi hfield f hf
        (coordinate_intertwiner f hf0 (1 : Fin 2))
        (coordinate_intertwiner f hf0 (0 : Fin 2))
    simp only [] at h
    have hcoeff :
        (fun j : Fin 2 => (if j = 1 then 1 else 0) +
          if j = 0 then 1 else 0) = (fun _ => (1 : R)) := by
      funext j
      fin_cases j <;> simp
    rw [hcoeff] at h
    exact h

/-- The canonical binary series is associative. -/
theorem lubin_law_assoc
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    FGLaw.substitute (lubinTateLaw pi hpi0 hpi hfield f hf)
        FGLaw.ternaryX
        (FGLaw.substitute (lubinTateLaw pi hpi0 hpi hfield f hf)
          FGLaw.ternaryY FGLaw.ternaryZ) =
      FGLaw.substitute (lubinTateLaw pi hpi0 hpi hfield f hf)
        (FGLaw.substitute (lubinTateLaw pi hpi0 hpi hfield f hf)
          FGLaw.ternaryX FGLaw.ternaryY)
        FGLaw.ternaryZ := by
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf.1
  let e0 : Fin 3 -> R := fun j => if j = 0 then 1 else 0
  let e1 : Fin 3 -> R := fun j => if j = 1 then 1 else 0
  let e2 : Fin 3 -> R := fun j => if j = 2 then 1 else 0
  have hx : LIntert f f e0
      (FGLaw.ternaryX : TernarySeries R) := by
    simpa [e0, FGLaw.ternaryX] using
      coordinate_intertwiner f hf0 (0 : Fin 3)
  have hy : LIntert f f e1
      (FGLaw.ternaryY : TernarySeries R) := by
    simpa [e1, FGLaw.ternaryY] using
      coordinate_intertwiner f hf0 (1 : Fin 3)
  have hz : LIntert f f e2
      (FGLaw.ternaryZ : TernarySeries R) := by
    simpa [e2, FGLaw.ternaryZ] using
      coordinate_intertwiner f hf0 (2 : Fin 3)
  have hyz := lubin_law_substitute pi hpi0 hpi hfield f hf hy hz
  have hxy := lubin_law_substitute pi hpi0 hpi hfield f hf hx hy
  have hleft := lubin_law_substitute pi hpi0 hpi hfield f hf hx hyz
  have hright := lubin_law_substitute pi hpi0 hpi hfield f hf hxy hz
  apply tate_law_spec pi hpi0 hpi hfield f hf (fun _ => 1)
  · have hcoeff :
        (fun j : Fin 3 => e0 j + (e1 j + e2 j)) =
          (fun _ => (1 : R)) := by
      funext j
      fin_cases j <;> simp [e0, e1, e2]
    rw [hcoeff] at hleft
    exact hleft
  · have hcoeff :
        (fun j : Fin 3 => (e0 j + e1 j) + e2 j) =
          (fun _ => (1 : R)) := by
      funext j
      fin_cases j <;> simp [e0, e1, e2]
    rw [hcoeff] at hright
    exact hright

/-- The formal group law of Proposition 2.12, including its uniquely
characterized inverse series. -/
noncomputable def lubinFormalLaw
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) : FGLaw R :=
  FLConstr.ofLaw
    (lubinTateLaw pi hpi0 hpi hfield f hf)
    (lubin_law_left pi hpi0 hpi hfield f hf)
    (lubin_tate_law pi hpi0 hpi hfield f hf)
    (lubin_law_assoc pi hpi0 hpi hfield f hf)
    (lubin_law_comm pi hpi0 hpi hfield f hf)

@[simp]
theorem lubin_formal_law
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    (lubinFormalLaw pi hpi0 hpi hfield f hf).law =
      lubinTateLaw pi hpi0 hpi hfield f hf := rfl

/-- The book's characterization of a formal group law admitting `f`: its
linear part is `X + Y`, and `f` is an endomorphism. -/
def LubinFormalLaw (f : PowerSeries R) (F : FGLaw R) : Prop :=
  homogeneousComponent 1 F.law = mvLinearForm (fun _ : Fin 2 ↦ 1) ∧
    PowerSeries.subst F.law f =
      MvPowerSeries.subst (coordinatewiseSubst f) F.law

theorem lubin_law_spec
    (pi : R) (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    (f : PowerSeries R)
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    LubinFormalLaw f
      (lubinFormalLaw pi hpi0 hpi hfield f hf) := by
  constructor
  · exact law_homogeneous_component pi hpi0 hpi hfield f hf
  · exact lubin_law_endomorphism pi hpi0 hpi hfield f hf

/-- Proposition 2.12: a Lubin--Tate series admits a unique formal group law. -/
theorem unique_formal_law
    {pi : R} (hpi0 : pi ≠ 0) (hpi : ¬ IsUnit pi)
    (hfield : IsField (R ⧸ Ideal.span {pi}))
    [Fintype (R ⧸ Ideal.span {pi})]
    {f : PowerSeries R}
    (hf : LubinSeries pi
      (Fintype.card (R ⧸ Ideal.span {pi})) f) :
    ∃! F : FGLaw R, LubinFormalLaw f F := by
  let F := lubinFormalLaw pi hpi0 hpi hfield f hf
  refine ⟨F, lubin_law_spec pi hpi0 hpi hfield f hf, ?_⟩
  intro G hG
  apply FLConstr.ext_law
  change G.law = lubinTateLaw pi hpi0 hpi hfield f hf
  apply lubin_law pi hpi0 hpi hfield f hf
  refine ⟨FGLaw.law_constant_coeff G, hG.1, ?_⟩
  exact sub_eq_zero.mpr hG.2

end

end Submission.CField.FGroups
