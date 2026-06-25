import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Chapter II, Section 1: the extension attached to a two-cocycle

This is the explicit construction used in Example 1.18(b).  A multiplicative
two-cocycle `f` gives the twisted product on `M × G`

`(m, g) * (n, h) = (m * (g • n) * f(g,h), gh)`.

The cocycle identity is precisely associativity of this multiplication.  We
do not assume `f(1,1) = 1`: if `q = f(1,1)`, the identity is `(q⁻¹,1)` and
the kernel inclusion sends `m` to `(m q⁻¹,1)`.
-/

namespace Towers.CField.COps

open groupCohomology

variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]

set_option linter.unusedVariables false in
/-- The carrier of the group extension associated to a cocycle.  The cocycle
is retained as a parameter so different cocycles receive different group
structures. -/
def CExt (f : G × G → M) := M × G

namespace CExt

instance (f : G × G → M) : Mul (CExt f) :=
  ⟨fun x y ↦ (x.1 * (x.2 • y.1) * f (x.2, y.2), x.2 * y.2)⟩

instance (f : G × G → M) : One (CExt f) :=
  ⟨((f (1, 1))⁻¹, 1)⟩

instance (f : G × G → M) : Inv (CExt f) :=
  ⟨fun x ↦ ((f (1, 1))⁻¹ * (x.2⁻¹ • x.1⁻¹) *
      (f (x.2⁻¹, x.2))⁻¹, x.2⁻¹)⟩

@[simp]
theorem fst_mul (f : G × G → M) (x y : CExt f) :
    (x * y).1 = x.1 * (x.2 • y.1) * f (x.2, y.2) := rfl

@[simp]
theorem snd_mul (f : G × G → M) (x y : CExt f) :
    (x * y).2 = x.2 * y.2 := rfl

omit [MulDistribMulAction G M] in
@[simp]
theorem fst_one (f : G × G → M) :
    (1 : CExt f).1 = (f (1, 1))⁻¹ := rfl

omit [MulDistribMulAction G M] in
@[simp]
theorem snd_one (f : G × G → M) :
    (1 : CExt f).2 = 1 := rfl

@[simp]
theorem fst_inv (f : G × G → M) (x : CExt f) :
    x⁻¹.1 = (f (1, 1))⁻¹ * (x.2⁻¹ • x.1⁻¹) *
      (f (x.2⁻¹, x.2))⁻¹ := rfl

@[simp]
theorem snd_inv (f : G × G → M) (x : CExt f) :
    x⁻¹.2 = x.2⁻¹ := rfl

/-- The group structure on the twisted product associated to a two-cocycle. -/
@[reducible]
def group (f : G × G → M) (hf : IsMulCocycle₂ f) :
    Group (CExt f) :=
  Group.ofLeftAxioms
    (fun x y z ↦ by
      apply Prod.ext
      · change
          (x.1 * (x.2 • y.1) * f (x.2, y.2)) *
                ((x.2 * y.2) • z.1) * f (x.2 * y.2, z.2) =
            x.1 * (x.2 • (y.1 * (y.2 • z.1) * f (y.2, z.2))) *
              f (x.2, y.2 * z.2)
        rw [mul_smul]
        simp only [smul_mul']
        have hcocycle := hf x.2 y.2 z.2
        calc
          x.1 * (x.2 • y.1) * f (x.2, y.2) * (x.2 • y.2 • z.1) *
                f (x.2 * y.2, z.2) =
              (x.1 * (x.2 • y.1) * (x.2 • y.2 • z.1)) *
                (f (x.2 * y.2, z.2) * f (x.2, y.2)) := by ac_rfl
          _ = (x.1 * (x.2 • y.1) * (x.2 • y.2 • z.1)) *
                ((x.2 • f (y.2, z.2)) * f (x.2, y.2 * z.2)) := by
              rw [hcocycle]
          _ = x.1 * ((x.2 • y.1) * (x.2 • y.2 • z.1) *
                (x.2 • f (y.2, z.2))) * f (x.2, y.2 * z.2) := by ac_rfl
      · exact mul_assoc x.2 y.2 z.2)
    (fun x ↦ by
      apply Prod.ext
      · change (f (1, 1))⁻¹ * (1 • x.1) * f (1, x.2) = x.1
        rw [map_one_fst_of_isMulCocycle₂ hf x.2]
        simp only [one_smul]
        calc
          (f (1, 1))⁻¹ * x.1 * f (1, 1) =
              x.1 * ((f (1, 1))⁻¹ * f (1, 1)) := by ac_rfl
          _ = x.1 := by simp
      · exact one_mul x.2)
    (fun x ↦ by
      apply Prod.ext
      · change
          ((f (1, 1))⁻¹ * (x.2⁻¹ • x.1⁻¹) *
                (f (x.2⁻¹, x.2))⁻¹) *
                (x.2⁻¹ • x.1) * f (x.2⁻¹, x.2) = (f (1, 1))⁻¹
        simp only [smul_inv']
        simp [mul_assoc]
      · exact inv_mul_cancel x.2)

/-- The short exact sequence `1 → M → M ×_f G → G → 1`. -/
def toGroupExtension (f : G × G → M) (hf : IsMulCocycle₂ f) :
    @GroupExtension M (CExt f) G inferInstance
      (group f hf) inferInstance := by
  letI : Group (CExt f) := group f hf
  refine
    { inl :=
        { toFun := fun m ↦ (m * (f (1, 1))⁻¹, 1)
          map_one' := by
            apply Prod.ext
            · change 1 * (f (1, 1))⁻¹ = (f (1, 1))⁻¹
              simp
            · rfl
          map_mul' := fun m n ↦ by
            apply Prod.ext
            · change (m * n) * (f (1, 1))⁻¹ =
                (m * (f (1, 1))⁻¹) *
                  (1 • (n * (f (1, 1))⁻¹)) * f (1, 1)
              simp only [one_smul]
              simp [mul_assoc]
              ac_rfl
            · exact (mul_one 1).symm }
      rightHom :=
        { toFun := Prod.snd
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl }
      inl_injective := fun _ _ h ↦ by
        apply mul_right_cancel (b := (f (1, 1))⁻¹)
        exact congrArg Prod.fst h
      range_inl_eq_ker_rightHom := by
        ext x
        constructor
        · rintro ⟨m, rfl⟩
          rfl
        · intro hx
          change x.2 = 1 at hx
          refine ⟨x.1 * f (1, 1), Prod.ext ?_ hx.symm⟩
          simp [mul_assoc]
      rightHom_surjective := fun g ↦ ⟨(1, g), rfl⟩ }

end CExt

end Towers.CField.COps
