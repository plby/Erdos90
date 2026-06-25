import Submission.ClassField.ReciprocityExistence.MultiplicativeCup
import Submission.ClassField.CrossedProducts.Cohomology

/-!
# The universe-polymorphic field cup map

This is the left vertical arrow of Lemma VII.8.5 in Milne's multiplicative
`H²` presentation.  A base unit `a` and character `chi` give the literal
cocycle `(g,h) |-> a ^ n(g,h)`, followed by the crossed-product equivalence
with the relative Brauer group.
-/

namespace Submission.CField.RExist

open Submission.CField.BGroups
open Submission.CField.CProduca

noncomputable section

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The scalar extension of a base unit is fixed by `Gal(L/K)`. -/
theorem multiplicative_base_fixed (a : Kˣ) (g : Gal(L/K)) :
    g • Units.map (algebraMap K L).toMonoidHom a =
      Units.map (algebraMap K L).toMonoidHom a := by
  apply Units.ext
  exact g.commutes a

/-- The multiplicative class of the literal global cup cocycle. -/
noncomputable def multiplicativeCupClass
    (a : Kˣ) (chi : Additive Gal(L/K) →+ AddCircle (1 : ℚ)) :
    MHTwo Gal(L/K) Lˣ :=
  invariantCharacterCup (Units.map (algebraMap K L).toMonoidHom a)
    (multiplicative_base_fixed K L a) chi

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem global_multiplicative_mul
    (a b : Kˣ) (chi : Additive Gal(L/K) →+ AddCircle (1 : ℚ)) :
    multiplicativeCupClass K L (a * b) chi =
      multiplicativeCupClass K L a chi *
        multiplicativeCupClass K L b chi := by
  rw [multiplicativeCupClass, multiplicativeCupClass,
    multiplicativeCupClass, invariantCharacterCup,
    invariantCharacterCup, invariantCharacterCup,
    ← MHTwo.mk_mul]
  congr 1
  apply NMCocycl₂.ext
  rintro ⟨g, h⟩
  change (Units.map (algebraMap K L).toMonoidHom (a * b)) ^
      rationalBoundaryExponent chi g h =
    (Units.map (algebraMap K L).toMonoidHom a) ^
        rationalBoundaryExponent chi g h *
      (Units.map (algebraMap K L).toMonoidHom b) ^
        rationalBoundaryExponent chi g h
  rw [map_mul, mul_zpow]

omit [FiniteDimensional K L] [IsGalois K L] in
@[simp]
theorem global_multiplicative_one
    (chi : Additive Gal(L/K) →+ AddCircle (1 : ℚ)) :
    multiplicativeCupClass K L 1 chi = 1 := by
  rw [multiplicativeCupClass, invariantCharacterCup]
  change MHTwo.mk _ = MHTwo.mk 1
  congr 1
  apply NMCocycl₂.ext
  rintro ⟨g, h⟩
  change (Units.map (algebraMap K L).toMonoidHom (1 : Kˣ)) ^
      rationalBoundaryExponent chi g h = 1
  rw [map_one, one_zpow]

/-- The universe-polymorphic field-side cup map in Lemma VII.8.5. -/
noncomputable def multiplicativeFieldCup
    (chi : Additive Gal(L/K) →+ AddCircle (1 : ℚ)) :
    Additive Kˣ →+ Additive (relativeBrauerGroup K L) where
  toFun a := Additive.ofMul
    (CProduc.hRelativeBrauer K L
      (multiplicativeCupClass K L a.toMul chi))
  map_zero' := by
    apply Additive.toMul.injective
    change CProduc.hRelativeBrauer K L
      (multiplicativeCupClass K L 1 chi) = 1
    rw [global_multiplicative_one, map_one]
  map_add' a b := by
    apply Additive.toMul.injective
    change CProduc.hRelativeBrauer K L
        (multiplicativeCupClass K L (a.toMul * b.toMul) chi) =
      CProduc.hRelativeBrauer K L
          (multiplicativeCupClass K L a.toMul chi) *
        CProduc.hRelativeBrauer K L
          (multiplicativeCupClass K L b.toMul chi)
    rw [global_multiplicative_mul, map_mul]

@[simp]
theorem multiplicative_field_cup
    (chi : Additive Gal(L/K) →+ AddCircle (1 : ℚ)) (a : Kˣ) :
    (multiplicativeFieldCup K L chi (Additive.ofMul a)).toMul =
      CProduc.hRelativeBrauer K L
        (multiplicativeCupClass K L a chi) :=
  rfl

end

end Submission.CField.RExist
