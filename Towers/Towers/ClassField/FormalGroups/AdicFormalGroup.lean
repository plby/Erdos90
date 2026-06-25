import Towers.ClassField.FormalGroups.AdicSubstitutionEvaluation
import Towers.ClassField.FormalGroups.FormalGroupEvaluation

/-!
# Class Field Theory, Chapter I, after Remark 2.4: the adic formal group

A formal group law over a complete adically topologized ring gives an actual
commutative group on every ideal of definition.  We use a type synonym so
that this addition does not conflict with the ideal's ordinary addition.
-/

namespace Towers.CField.FGroups

open Filter MvPowerSeries
open scoped MvPowerSeries.WithPiTopology

variable {R : Type*} [CommRing R] [UniformSpace R]

namespace FGLaw

noncomputable section

/-- An ideal of definition equipped with the group operation induced by a
formal group law.  The proof of adicity and the formal law are retained in
the type so distinct choices receive distinct additive structures. -/
structure APts {I : Ideal R} (hI : IsAdic I) (F : FGLaw R) where
  val : I

namespace APts

variable {I : Ideal R} (hI : IsAdic I) (F : FGLaw R)

/-- Forget the formal group operation and recover the underlying ideal
element. -/
def toIdeal (x : APts hI F) : I := x.val

/-- Regard an element of the ideal as a point of the adic formal group. -/
def ofIdeal (x : I) : APts hI F := ⟨x⟩

/-- The adic formal group is equivalent as a type to its underlying ideal. -/
def equivIdeal : APts hI F ≃ I where
  toFun := toIdeal hI F
  invFun := ofIdeal hI F
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem to_of_ideal (x : I) : toIdeal hI F (ofIdeal hI F x) = x := rfl

@[simp]
theorem of_to_ideal (x : APts hI F) :
    ofIdeal hI F (toIdeal hI F x) = x := by cases x; rfl

@[simp]
theorem equivIdeal_apply (x : APts hI F) :
    equivIdeal hI F x = toIdeal hI F x := rfl

instance : CoeOut (APts hI F) I :=
  ⟨toIdeal hI F⟩

@[simp]
theorem coe_ofIdeal (x : I) : ((ofIdeal hI F x : APts hI F) : I) = x := rfl

@[ext]
theorem ext {x y : APts hI F}
    (h : toIdeal hI F x = toIdeal hI F y) : x = y := by
  cases x
  cases y
  cases h
  rfl

theorem coe_injective : Function.Injective (fun x : APts hI F ↦ (x : R)) := by
  intro x y h
  apply ext hI F
  exact Subtype.ext h

omit [UniformSpace R] in
private theorem constant_coeff_substitute
    {sigma : Type*} (P : BinarySeries R)
    (hP : constantCoeff P = 0) (x y : MvPowerSeries sigma R)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    constantCoeff (substitute P x y) = 0 := by
  apply constantCoeff_subst_eq_zero
    (hasSubst_of_constantCoeff_zero (fun i ↦ Fin.cases hx (fun _ ↦ hy) i))
  · intro i
    exact Fin.cases hx (fun _ ↦ hy) i
  · exact hP

private theorem eval₂_zero
    {sigma : Type*} (a : sigma → R) :
    eval₂ (RingHom.id R) a (0 : MvPowerSeries sigma R) = 0 := by
  change eval₂ (RingHom.id R) a
      ((0 : MvPolynomial sigma R) : MvPowerSeries sigma R) = 0
  rw [eval₂_coe]
  simp

variable [IsUniformAddGroup R] [IsTopologicalRing R]
  [T2Space R] [CompleteSpace R]

private theorem eval₂_substitute_adic
    {sigma : Type*} [Finite sigma]
    (hI : IsAdic I)
    (P : BinarySeries R) (x y : MvPowerSeries sigma R)
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0)
    (a : sigma → R) (ha : ∀ i, a i ∈ I) :
    eval₂ (RingHom.id R) a (substitute P x y) =
      eval₂ (RingHom.id R)
        (Fin.cases (eval₂ (RingHom.id R) a x)
          (fun _ ↦ eval₂ (RingHom.id R) a y)) P := by
  have h := mv_series_eval₂_subst_of_forall_constantCoeff_zero_adic
    hI (Fin.cases x (fun _ ↦ y))
    (fun i ↦ Fin.cases hx (fun _ ↦ hy) i) a ha P
  change eval₂ (RingHom.id R) a (substitute P x y) = _ at h
  rw [h]
  congr 2
  funext i
  fin_cases i <;> rfl

private theorem eval₂_compose_adic
    {sigma : Type*} [Finite sigma]
    (hI : IsAdic I)
    (f : UnarySeries R) (x : MvPowerSeries sigma R)
    (hx : constantCoeff x = 0)
    (a : sigma → R) (ha : ∀ i, a i ∈ I) :
    eval₂ (RingHom.id R) a (compose f x) =
      eval₂ (RingHom.id R)
        (fun _ ↦ eval₂ (RingHom.id R) a x) f := by
  simpa only [compose] using
    mv_series_eval₂_subst_of_forall_constantCoeff_zero_adic
      hI (fun _ : Fin 1 ↦ x) (fun _ ↦ hx) a ha f

private theorem coe_adic_value₂
    (x y : I) :
    (adicValue hI F x y : R) =
      eval₂ (RingHom.id R) (Fin.cases (x : R) (fun _ ↦ (y : R))) F.law := by
  rw [coe_adicValue]
  congr 2
  funext i
  fin_cases i <;> rfl

private theorem coe_adic_inverse₂ (x : I) :
    (adicUnaryValue hI F.inverse F.inverse_constantCoeff x : R) =
      eval₂ (RingHom.id R) (fun _ ↦ (x : R)) F.inverse := by
  rfl

private theorem adic_value_left (x : I) :
    adicValue hI F 0 x = x := by
  apply Subtype.ext
  rw [coe_adic_value₂]
  let a : Fin 1 → R := fun _ ↦ (x : R)
  have ha : ∀ i, a i ∈ I := fun _ ↦ x.2
  have h := congrArg (eval₂ (RingHom.id R) a) F.left_identity
  rw [eval₂_substitute_adic hI F.law 0 unaryX (by simp)
      (by simp [unaryX]) a ha] at h
  have hX : eval₂ (RingHom.id R) a unaryX = (x : R) := by
    simp [unaryX, a]
  rw [eval₂_zero a, hX] at h
  simpa [binaryX, binaryY, a] using h

private theorem adic_value_right (x : I) :
    adicValue hI F x 0 = x := by
  apply Subtype.ext
  rw [coe_adic_value₂]
  let a : Fin 1 → R := fun _ ↦ (x : R)
  have ha : ∀ i, a i ∈ I := fun _ ↦ x.2
  have h := congrArg (eval₂ (RingHom.id R) a) F.right_identity
  rw [eval₂_substitute_adic hI F.law unaryX 0
      (by simp [unaryX]) (by simp) a ha] at h
  have hX : eval₂ (RingHom.id R) a unaryX = (x : R) := by
    simp [unaryX, a]
  rw [eval₂_zero a, hX] at h
  simpa [a] using h

private theorem adicValue_comm (x y : I) :
    adicValue hI F x y = adicValue hI F y x := by
  apply Subtype.ext
  rw [coe_adic_value₂, coe_adic_value₂]
  let a : Fin 2 → R := Fin.cases (x : R) (fun _ ↦ (y : R))
  have ha : ∀ i, a i ∈ I := by
    intro i
    exact Fin.cases x.2 (fun _ ↦ y.2) i
  have h := congrArg (eval₂ (RingHom.id R) a) F.commutativity
  rw [eval₂_substitute_adic hI F.law binaryX binaryY
      (by simp [binaryX]) (by simp [binaryY]) a ha,
    eval₂_substitute_adic hI F.law binaryY binaryX
      (by simp [binaryY]) (by simp [binaryX]) a ha] at h
  simpa [binaryX, binaryY, a] using h

private theorem adicValue_assoc (x y z : I) :
    adicValue hI F (adicValue hI F x y) z =
      adicValue hI F x (adicValue hI F y z) := by
  apply Subtype.ext
  rw [coe_adic_value₂, coe_adic_value₂,
    coe_adic_value₂, coe_adic_value₂]
  let a : Fin 3 → R := ![(x : R), (y : R), (z : R)]
  have ha : ∀ i, a i ∈ I := by
    intro i
    fin_cases i <;> simp [a, x.2, y.2, z.2]
  have h := congrArg (eval₂ (RingHom.id R) a) F.associativity
  have hyz0 : constantCoeff (substitute F.law ternaryY ternaryZ) = 0 :=
    constant_coeff_substitute F.law (law_constant_coeff F)
      ternaryY ternaryZ (by simp [ternaryY]) (by simp [ternaryZ])
  have hxy0 : constantCoeff (substitute F.law ternaryX ternaryY) = 0 :=
    constant_coeff_substitute F.law (law_constant_coeff F)
      ternaryX ternaryY (by simp [ternaryX]) (by simp [ternaryY])
  rw [eval₂_substitute_adic hI F.law ternaryX
      (substitute F.law ternaryY ternaryZ)
      (by simp [ternaryX]) hyz0 a ha,
    eval₂_substitute_adic hI F.law
      (substitute F.law ternaryX ternaryY) ternaryZ
      hxy0 (by simp [ternaryZ]) a ha,
    eval₂_substitute_adic hI F.law ternaryY ternaryZ
      (by simp [ternaryY]) (by simp [ternaryZ]) a ha,
    eval₂_substitute_adic hI F.law ternaryX ternaryY
      (by simp [ternaryX]) (by simp [ternaryY]) a ha] at h
  simpa [ternaryX, ternaryY, ternaryZ, a] using h.symm

private theorem adic_inverse_cancel (x : I) :
    adicValue hI F
      (adicUnaryValue hI F.inverse F.inverse_constantCoeff x) x = 0 := by
  rw [adicValue_comm hI F]
  apply Subtype.ext
  rw [coe_adic_value₂, coe_adic_inverse₂]
  let a : Fin 1 → R := fun _ ↦ (x : R)
  have ha : ∀ i, a i ∈ I := fun _ ↦ x.2
  have h := congrArg (eval₂ (RingHom.id R) a) F.inverse_law
  rw [eval₂_substitute_adic hI F.law unaryX F.inverse
      (by simp [unaryX]) F.inverse_constantCoeff a ha] at h
  have hX : eval₂ (RingHom.id R) a unaryX = (x : R) := by
    simp [unaryX, a]
  rw [hX, eval₂_zero a] at h
  simpa [a] using h

noncomputable instance : Zero (APts hI F) := ⟨ofIdeal hI F 0⟩

noncomputable instance : Add (APts hI F) :=
  ⟨fun x y ↦ ofIdeal hI F
    (adicValue hI F (toIdeal hI F x) (toIdeal hI F y))⟩

noncomputable instance : Neg (APts hI F) :=
  ⟨fun x ↦ ofIdeal hI F
    (adicUnaryValue hI F.inverse F.inverse_constantCoeff (toIdeal hI F x))⟩

omit [IsUniformAddGroup R] [IsTopologicalRing R] [T2Space R]
  [CompleteSpace R] in
@[simp]
theorem toIdeal_zero : toIdeal hI F (0 : APts hI F) = 0 := rfl

@[simp]
theorem toIdeal_add (x y : APts hI F) :
    toIdeal hI F (x + y) =
      adicValue hI F (toIdeal hI F x) (toIdeal hI F y) := rfl

@[simp]
theorem toIdeal_neg (x : APts hI F) :
    toIdeal hI F (-x) =
      adicUnaryValue hI F.inverse F.inverse_constantCoeff (toIdeal hI F x) := rfl

omit [IsUniformAddGroup R] [IsTopologicalRing R] [T2Space R]
  [CompleteSpace R] in
@[simp]
theorem coe_zero : ((0 : APts hI F) : R) = 0 := rfl

@[simp]
theorem coe_add (x y : APts hI F) :
    ((x + y : APts hI F) : R) =
      (adicValue hI F (toIdeal hI F x) (toIdeal hI F y) : R) := rfl

@[simp]
theorem coe_neg (x : APts hI F) :
    ((-x : APts hI F) : R) =
      (adicUnaryValue hI F.inverse F.inverse_constantCoeff
        (toIdeal hI F x) : R) := rfl

noncomputable instance : AddCommGroup (APts hI F) where
  add_assoc x y z := by
    apply ext hI F
    simp only [toIdeal_add]
    exact adicValue_assoc hI F (toIdeal hI F x) (toIdeal hI F y)
      (toIdeal hI F z)
  zero_add x := by
    apply ext hI F
    simp only [toIdeal_add, toIdeal_zero]
    exact adic_value_left hI F (toIdeal hI F x)
  add_zero x := by
    apply ext hI F
    simp only [toIdeal_add, toIdeal_zero]
    exact adic_value_right hI F (toIdeal hI F x)
  neg_add_cancel x := by
    apply ext hI F
    simp only [toIdeal_add, toIdeal_neg, toIdeal_zero]
    exact adic_inverse_cancel hI F (toIdeal hI F x)
  add_comm x y := by
    apply ext hI F
    simp only [toIdeal_add]
    exact adicValue_comm hI F (toIdeal hI F x) (toIdeal hI F y)
  nsmul := nsmulRec
  zsmul := zsmulRec

end APts

end

end FGLaw

end Towers.CField.FGroups
