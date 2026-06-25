import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Towers.ClassField.CrossedProducts.CrossedProduct


/-!
# Chapter IV, Section 3: Galois crossed products

For a finite Galois extension `L/k`, the crossed product of a normalized
`Lˣ`-valued cocycle is naturally a `k`-algebra containing `L`.  This file
records the standard basis relations used in Milne's Lemma IV.3.13.
-/

namespace Towers.CField.CProduca

noncomputable section

universe u

attribute [local instance] Units.mulDistribMulActionRight

namespace CProduc

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  (c : NMCocycl₂ (G := Gal(L/k)) (M := Lˣ))

/-- The central copy of the base field in a Galois crossed product. -/
def baseRingHom : k →+* CProduc c where
  toFun r := single c 1 (algebraMap k L r)
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp
  map_mul' x y := by simp [single_mul_single]

instance : Module k (CProduc c) :=
  Module.compHom (CProduc c) (algebraMap k L)

instance : Algebra k (CProduc c) where
  algebraMap := baseRingHom k L c
  smul_def' r x := by
    change (algebraMap k L r) • x = baseRingHom k L c r * x
    induction x using induction_on c with
    | zero => simp
    | hsingle g a => simp [baseRingHom, single_mul_single, mul_comm]
    | hadd x y hx hy => simp_all [mul_add]
  commutes' r x := by
    induction x using induction_on c with
    | zero => simp
    | hsingle g a =>
      simp [baseRingHom, single_mul_single, mul_comm]
    | hadd x y hx hy => simp_all [mul_add, add_mul]

omit [FiniteDimensional k L] [IsGalois k L] in
@[simp]
theorem algebraMap_apply (r : k) :
    algebraMap k (CProduc c) r = single c 1 (algebraMap k L r) :=
  rfl

/-- The copy of `L` spanned by the identity basis vector. -/
def fieldEmbedding : L →ₐ[k] CProduc c where
  toFun a := single c 1 a
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp
  map_mul' x y := by simp [single_mul_single]
  commutes' r := rfl

omit [FiniteDimensional k L] [IsGalois k L] in
@[simp]
theorem fieldEmbedding_apply (a : L) : fieldEmbedding k L c a = single c 1 a := rfl

omit [FiniteDimensional k L] [IsGalois k L] in
theorem fieldEmbedding_injective : Function.Injective (fieldEmbedding k L c) := by
  intro a b h
  apply SkewMonoidAlgebra.single_injective (1 : Gal(L/k))
  exact congrArg CProduc.skewMonoid h

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Equation (39) for the standard crossed-product basis. -/
theorem basis_mul_include (sigma : Gal(L/k)) (a : L) :
    basis c sigma * fieldEmbedding k L c a =
      fieldEmbedding k L c (sigma a) * basis c sigma := by
  simp [basis_apply, single_mul_single, mul_comm]

omit [FiniteDimensional k L] [IsGalois k L] in
/-- Equation (40) for the standard crossed-product basis. -/
theorem basis_mul_basis (sigma tau : Gal(L/k)) :
    basis c sigma * basis c tau =
      fieldEmbedding k L c (c (sigma, tau) : L) * basis c (sigma * tau) := by
  simp [basis_apply, single_mul_single, mul_comm]

instance : Module.Finite L (CProduc c) :=
  Module.Finite.of_basis (basis c)

theorem finrank_over_extension :
    Module.finrank L (CProduc c) = Module.finrank k L := by
  rw [Module.finrank_eq_card_basis (basis c)]
  exact Fintype.card_eq_nat_card.trans (IsGalois.card_aut_eq_finrank k L)

end CProduc

end

end Towers.CField.CProduca
